"""
Functions for computing lower bounds for density by a discharging argument encoded as a linear program. Uses the Pulp library.
"""

import circuit
from sft import SFT, centered_hypercube
from general import *
import pulp
import frozendict as fd
import time
from fractions import Fraction
from node_automorphism import AffineAutomorphism
import random
from enum import Enum

TOLERANCE = 1e-6
#DENOMINATORS = [25, 50, 75, 100, 150, 200, 350, 500, 750, 1000, 2000, 3500, 5000, 7500,
DENOMINATORS = [10000, 20000, 35000, 50000, 75000, 100000, 200000, 350000, 500000, 750000, 1000000, 2000000, 3500000, 5000000, 7500000, 10000000]#, 20000000, 35000000, 50000000, 75000000, 100000000, 200000000, 350000000, 500000000, 750000000, 1000000000, 2000000000, 3500000000, 5000000000, 7500000000, 10000000000]

# A dict of solvers, type str -> ((solver, args), None | (solver, args))
# The first component is used by default, the second when the first one fails
# If the second is None, we just fail
SOLVER_DICTS = {
    "CBC" : ((pulp.apis.PULP_CBC_CMD,
              {"msg" : False,
               "warmStart" : True,
               "keepFiles" : True
               }),
             None),
    "GLPK" : ((pulp.apis.GLPK_CMD,
               {"msg" : False,
                "options" : ["--primal", "--cbg",  "--xcheck"]
                }),
              None),
    "HiGHS_ipx" : ((pulp.apis.HiGHS,
                    {"msg" : False,
                     "solver" : "ipx"
                     }),
                   None),
    "HiGHS_simplex" : ((pulp.apis.HiGHS,
                        {"msg" : False,
                         "solver" : "simplex",
                         "simplex_strategy" : "primal"
                         }),
                       None),
    "HiGHS_hybrid" : ((pulp.apis.HiGHS,
                       {"msg" : False,
                        "solver" : "ipx"
                        }),
                      (pulp.apis.HiGHS,
                       {"msg" : False,
                        "solver" : "simplex",
                        "simplex_strategy" : "primal"
                        }))
}

def rules_to_tree(dim, alph, node, syms, bigdomain, rules):
    "Transform charge transfer rules into a decision tree, which can be used to extract constraints from bigpats."
    # rules is a list of (node, pattern, nvec).
    # tups will store tuples (source, pat, nvec, away, tr_pat) where:
    # source is the source node,
    # pat is the original pattern,
    # nvec is the nodevector along which we transfer charge,
    # away is True if we transfer away from the origin,
    # tr_pat is the pattern we should look for in a bigpat.
    # It may be transformed by a symmetry.
    tups = []
    for (source, fpat, tr_nvec) in rules:
        for aut in syms:
            (aut_orig_vec, aut_source) = aut(((0,)*dim, source))
            aut_trnvec = (aut_trvec, aut_target) = aut(tr_nvec)
            #aut_fpat = fd.frozendict({aut(nvec) : sym for (nvec, sym) in fpat.items()})
            if aut_source == node:
                tups.append((source, fpat, tr_nvec, True,
                             fd.frozendict({nvsub(aut(nvec), aut_orig_vec) : sym
                                            for (nvec, sym) in fpat.items()})))
            if aut_target == node:
                tups.append((source, fpat, tr_nvec, False,
                             fd.frozendict({nvsub(aut(nvec), aut_trvec) : sym
                                            for (nvec, sym) in fpat.items()})))
    tree, size = tups_to_tree(alph, bigdomain, tups, [])
    assert size == len(tups)
    #print("tree", size, len(tree), [p[:2] for p in tree])
    return tree

def tups_to_tree(alph, bigdomain, tups, tree):
    # tree is a list of tuples: tree := [(nvec, sym, [tree]) | (node, pat, nvec, bool, tr_pat)].
    # the idea is that we iterate the list and test whether bigpat[nvec] = sym.
    # at each match, if the third item is a list we recurse,
    # and otherwise we add the quintuple to the constraint.
    #print("call", quads, tree)
    sumsizes = 0
    while tups:
        #print("tups", len(tups))
        old_len = len(tups)
        if all(tup[4] == tups[0][4] for tup in tups[1:]):
            # all test patterns are equal, cannot differentiate
            for tup in tups:
                tree.append(tup)
                sumsizes += 1
            break
        else:
            # greedily choose nvec and sym that split tups the most evenly
            pair = max(((nvec, sym) for nvec in bigdomain for sym in alph[nvec[1]]
                        if any(tup[4].get(nvec, None) == sym for tup in tups)),
                       key = lambda p: min(n := sum(1 for tup in tups
                                                    if tup[4].get(p[0], None) == p[1]),
                                           len(tups) - n))
            nvec, sym = pair
            chosen = []
            chosen = [(source, pat, tr_nvec, away, testpat.delete(nvec))
                      for (source, pat, tr_nvec, away, testpat) in tups
                      if testpat.get(nvec, None) == sym]
            #print("pair", nvec, sym, old_len, len(chosen))
            #print("lc", len(chosen))
            assert 0 < len(chosen) < len(tups)
            subtree, subsize = tups_to_tree(alph, bigdomain, chosen, [])
            sumsizes += subsize
            tree.append((nvec, sym, subtree))
            tups = [tup for tup in tups if tup[4].get(nvec, None) != sym]
            #print("lens", old_len, len(tups), len(chosen))
            assert old_len == len(tups) + len(chosen)
    #print("ret", tree[::-1])
    return tree[::-1], sumsizes

def print_tree(tree, level=0):
    for nvec, sym, item in reversed(tree):
        print("{}on {} at {}:".format(" "*level, sym, nvec))
        if type(item) == list:
            print_tree(item, level+1)
        else:
            print("{}use {}".format(" "*(level+1), item))

class SimplifierState(Enum):
    "States for the simplifier state machine."
    SIMPLIFY_PHASE1 = 0
    TRIM_PHASE1 = 1
    SIMPLIFY_PHASE2 = 2
    TRIM_PHASE2 = 3
    TRIM_FINAL = 4
    FINISHED = 5

class DischargingSimplifier:
    "A process for siplifying a discharging argument. Can be suspended, saved, loaded and restarted."

    def __init__(self, disc_arg, solver_str, simp_mode="minimize", trim_mode=None, max_split=None, num_split=None, minimize_all=False, trim_initial=True):
        self.disc_arg = disc_arg
        self.orig_bigpats = disc_arg.bigpats
        self.history = []
        if trim_initial:
            self.status = SimplifierState.TRIM_PHASE1
        else:
            self.status = SimplifierState.SIMPLIFY_PHASE1
        self.trim_mode = trim_mode
        self.simp_mode = simp_mode
        self.solver_str = solver_str

        self.max_split = max_split
        self.num_split = num_split
        self.minimize_all = minimize_all

    def is_finished(self):
        return self.status == SimplifierState.FINISHED

    def step(self, verbose=False, print_freq=10000):
        "Apply a single simplifier step/transition."
        self.history.append((self.status, self.disc_arg.trans_rules, self.disc_arg.score))
        if verbose:
            print("Simplification step; number of rules now {} (total {})".format(self.disc_arg.score, sum(self.disc_arg.score)))
        #print("state", self.status)

        # Choose action based on internal state
        if self.status == SimplifierState.SIMPLIFY_PHASE1:
            if verbose:
                print("Splitting rules")
            if self.simp_mode == "minimize":
                self.disc_arg.recompute_with_holes(self.solver_str, verbose=verbose, print_freq=print_freq, max_larges=self.max_split, num_split=self.num_split, minimize_all=self.minimize_all, sort_pats=True)
                if self.trim_mode is not None:
                    self.status = SimplifierState.TRIM_PHASE1
                elif self.disc_arg.score >= self.history[-1][2]:
                    self.status = SimplifierState.SIMPLIFY_PHASE2
                    self.disc_arg.trans_rules = self.history[-1][1]
                    self.disc_arg.update_specs()
                    if verbose:
                        print("Entering phase 2")
                
            elif self.simp_mode == "recompute":
                res = disc_arg.compute_bound(self.solver_str, verbose=verbose, print_freq=print_freq, split=True, num_split=self.num_split, max_split=self.max_split)
                if not res:
                    self.status = SimplifierState.SIMPLIFY_PHASE2
                    if verbose:
                        print("Entering phase 2")
                elif self.trim_mode is not None:
                    self.status = SimplifierState.TRIM_PHASE1

        elif self.status == SimplifierState.TRIM_PHASE1:
            if verbose:
                print("Trimming rules")
            if self.trim_mode in ["minimize", None]:
                self.disc_arg.recompute_with_holes(self.solver_str, verbose=verbose, print_freq=print_freq, num_split=0, max_larges=self.max_split, minimize_all=self.minimize_all)
            elif self.trim_mode == "recompute":
                self.disc_arg.minimize_rule_count(self.solver_str, verbose=verbose, print_freq=print_freq, max_rounds="until_fail")
            if len(self.history) >= 2 and self.disc_arg.score >= self.history[-2][2]:
                self.disc_arg.trans_rules = self.history[-2][1]
                self.disc_arg.update_specs()
                self.status = SimplifierState.SIMPLIFY_PHASE2
                if verbose:
                        print("Entering phase 2")
            else:
                self.status = SimplifierState.SIMPLIFY_PHASE1

        elif self.status == SimplifierState.SIMPLIFY_PHASE2:
            if verbose:
                print("Splitting rules")
            self.disc_arg.recompute_with_holes(self.solver_str, verbose=verbose, print_freq=print_freq, minimize_all=True, sort_pats=True)
            if self.disc_arg.score >= self.history[-1][2]:
                self.status = SimplifierState.TRIM_FINAL

        elif self.status == SimplifierState.TRIM_FINAL:
            if verbose:
                print("Trimming final rules")
            self.disc_arg.minimize_rule_count(self.solver_str, verbose=verbose, print_freq=print_freq, sort_rules=True)
            self.status = SimplifierState.FINISHED
            

class DischargingArgument:
    "A discharging argument for a lower bound on the minimum density of an SFT."

    def __init__(self, sft, specs, radius, weights=None, relevant_nodes=None, symmetries=None):
        self.sft = sft
        if relevant_nodes is None:
            self.relevant_nodes = list(sft.nodes)
        else:
            self.relevant_nodes = relevant_nodes
        self.radius = radius
        #print("specs", specs)
        if weights is None:
            self.weights = {a:int(a)
                            for node in self.relevant_nodes
                            for a in sft.alph[node]}
        else:
            self.weights = weights
        if symmetries is None:
            self.symmetries = AffineAutomorphism.generate_group(dim=sft.dim,
                                                                nodes=sft.nodes)
        else:
            self.symmetries = symmetries
        # compute one node from each symmetry orbit
        # also check that no orbit contains both relevant and irrelevant nodes
        self.sym_nodes = dict()
        for node in self.sft.nodes:
            for aut in self.symmetries:
                img_node = aut(((0,)*self.sft.dim, node))[1]
                if (node in self.relevant_nodes) != (img_node in self.relevant_nodes):
                    n1, n2 = sorted([node, img_node],
                                    key=lambda n: n in self.relevant_nodes)
                    raise GriddyRuntimeError("Irrelevant node {} in symmetry orbit of relevant node {}".format(n1, n2))
                if img_node in self.sym_nodes:
                    break
            else:
                self.sym_nodes[node] = set()
                # filter and translate symmetries to fix this node at origin
                for aut in self.symmetries:
                    new_aut = aut.shift_to_map(((0,)*self.sft.dim, node))
                    if new_aut is not None:
                        self.sym_nodes[node].add(new_aut)
        
        # specs has type dict[node_name : [(nvec, [nvec])]]
        # normalize the specs so that the nodes are in sym_nodes
        self.specs = dict()
        for (node, node_spec) in specs.items():
            for aut in self.symmetries:
                img_node = aut.node_map[node]
                if img_node not in self.sym_nodes:
                    continue
                new_aut = aut.shift_to_map(((0,)*self.sft.dim, node),
                                           ((0,)*self.sft.dim, img_node))
                self.specs[img_node] = [
                    (new_aut(tr_nvec), [new_aut(nvec) for nvec in domain])
                    for (tr_nvec, domain) in node_spec
                ]
                break
                
        self.bound = None
        # trans_rules will be dict[node_name : dict[frozenpattern : dict[vector : number]]]
        self.trans_rules = None
        self.bigpats = {node : None for node in self.sym_nodes}
        self.bigdomain = {node : None for node in self.sym_nodes}
        self.score = None
        self.saved_surroundings = None

    def save_transfer_rules(self, filename):
        "Save transfer rules and bound to a file."
        with open(filename+".output", 'w') as f:
            if type(self.bound) == float:
                f.write(str(self.bound)+'\n')
            else:
                # Fraction
                num, den = self.bound.as_integer_ratio()
                f.write(str(num) + '/' + str(den) + '\n')
            for (source, rules) in self.trans_rules.items():
                for (fpat, nvecs) in rules.items():
                    for (nvec, amount) in nvecs.items():
                        f.write(str(source) + '\n')
                        f.write(str(dict(fpat)) + '\n')
                        f.write(str(nvec) + '\n')
                        if type(amount) == float:
                            f.write(str(amount) + '\n')
                        else:
                            # Fraction
                            num, den = amount.as_integer_ratio()
                            f.write(str(num) + '/' + str(den) + '\n')
            f.write("#end")

    def load_transfer_rules(self, filename):
        "Load transfer rules and bound from a file."
        # TODO: switch to saving and loading the entire state
        self.trans_rules = dict()
        with open(filename+".output", 'r') as f:
            boundln = f.readline()
            if '/' in boundln:
                self.bound = Fraction(*(int(x) for x in boundln.split('/')))
            else:
                self.bound = float(boundln)
            #print("loaded bound", self.bound)
            while True:
                source = f.readline()
                if source[0] == '#':
                    break
                else:
                    source = eval(source)
                fpat = fd.frozendict(eval(f.readline()))
                nvec = eval(f.readline())
                amount = f.readline()
                if '/' in amount:
                    amount = Fraction(*(int(x) for x in amount.split('/')))
                else:
                    amount = float(amount)
                if source not in self.trans_rules:
                    self.trans_rules[source] = dict()
                if fpat not in self.trans_rules[source]:
                    self.trans_rules[source][fpat] = dict()
                self.trans_rules[source][fpat][nvec] = amount
                #print("loaded rule", source, fpat, nvec, amount)

    def bigdomain_from_spec(self, node):
        "Compute bigdomain of node from spec."
        bigdomain = {((0,)*self.sft.dim, node)}
        for (source_node, node_specs) in self.specs.items():
            for ((vec, target_node), domain) in node_specs:
                # we need to consider all symmetries
                for aut in self.symmetries:
                    aut_orig_vec, aut_source = aut(((0,)*self.sft.dim, source_node))
                    aut_domain = [aut(nvec) for nvec in domain]
                    aut_vec, aut_target = aut((vec, target_node))
                    if aut_source == node:
                        bigdomain |= set(nvsub(nvec, aut_orig_vec)
                                         for nvec in aut_domain)
                    if aut_target == node:
                        bigdomain |= set(nvsub(nvec, aut_vec)
                                         for nvec in aut_domain)
        return bigdomain

    # enumerate combined locally correct patterns that affect origin
    def surroundings(self, node, bigpat=None, ret_big=False, rules=None, verbose=False, shuffle=False):
        if self.saved_surroundings is not None:
            if shuffle:
                random.shuffle(self.saved_surroundings[node])
            return self.saved_surroundings[node]
        else:
            return self._surroundings(node, bigpat, ret_big, rules, verbose)

    def _surroundings(self, node, bigpat, ret_big, rules, verbose):
        assert node in self.sym_nodes
        #print("node", node)
        #print("Spec len", len(self.specs))
        # TODO: find a more efficient way to generate these when self.specs is large
        compute_bigpats = False
        if bigpat is not None:
           bigpats = [bigpat]
        elif self.bigpats[node] is None:
            compute_bigpats = True
            self.bigdomain[node] = self.bigdomain_from_spec(node)
            if verbose:
                print("Node {}: considering patterns of size {}".format(node, len(self.bigdomain[node])))
                #print(self.bigdomain[node])
            # only compute one pattern from each symmetry orbit
            bigpats = self.sft.all_patterns(self.bigdomain[node], extra_rad=self.radius, mod_symmetries=self.sym_nodes[node])
            self.bigpats[node] = []
        else:
            bigpats = self.bigpats[node]
        if rules is None or (len(rules) >= 2**sum(len(x) for x in self.specs.values())):
            #print("DIRECT")
            for the_bigpat in bigpats:
                #print("got bigpat", bigpat, len(bigpat), node)
                if compute_bigpats:
                    #found = False
                    #for aut in self.symmetries:
                    #    (aut_orig_vec, aut_node) = aut(((0,)*self.sft.dim, node))
                    #    if aut_node == node:
                    #        aut_bigpat = {nvsub(aut(nvec), aut_orig_vec) : sym
                    #                      for (nvec, sym) in bigpat.items()}
                    #        if aut_bigpat in self.bigpats[node]:
                    #            found = True
                    #            break
                    #if found:
                    #    continue
                    #else:
                    self.bigpats[node].append(the_bigpat)
                surr = []
                #print("accepted bigpat", bigpat)
                if node in self.relevant_nodes:
                    orig_val = the_bigpat[((0,)*self.sft.dim, node)]
                else:
                    orig_val = None
                for (source_node, node_specs) in self.specs.items():
                    for (tr_nvec, domain) in node_specs:
                        #print("transition", source_node, tr_nvec, domain)
                        # here we must consider all symmetries to find transitions
                        # but we return the original, untransformed patterns
                        for aut in self.symmetries:
                            #print("aut", aut)
                            (aut_orig_vec, aut_source) = aut(((0,)*self.sft.dim, source_node))
                            #print("aut source", aut_orig_vec, aut_source)
                            aut_trnvec = (aut_trvec, aut_target) = aut(tr_nvec)
                            #print("aut target", aut_trvec, aut_target)
                            aut_domain = {aut(nvec) : nvec for nvec in domain}
                            #print("aut domain", aut_domain)
                            if aut_source == node:
                                # send charge away from origin node
                                surr.append((source_node, fd.frozendict({nvec : the_bigpat[nvsub(img_nvec, aut_orig_vec)] for (img_nvec, nvec) in aut_domain.items()}), tr_nvec, True))
                            (vec, target_node) = tr_nvec
                            if aut_target == node:
                                # send charge to origin node
                                surr.append((source_node, fd.frozendict({nvec : the_bigpat[nvsub(img_nvec, aut_trvec)] for (img_nvec, nvec) in aut_domain.items()}), tr_nvec, False))
                #print("surr", orig_val, surr)
                if ret_big:
                    yield (orig_val, surr, the_bigpat)
                else:
                    yield (orig_val, surr)
        else:
            #print("TREE")
            tree = rules_to_tree(self.sft.dim, self.sft.alph, node, self.symmetries, self.bigdomain[node], rules)
            for the_bigpat in bigpats:
                #print("new bigpat", bigpat)
                surr = []
                orig_val = the_bigpat[((0,)*self.sft.dim, node)]
                curr_tree = tree.copy()
                while curr_tree:
                    #print("popping", curr_tree[-1])
                    item = curr_tree.pop()
                    # item is either (nvec, sym, subtree) or (source, pat, nvec, away, testpat)
                    if len(item) == 5:
                        if all(the_bigpat[nvec] == sym for (nvec, sym) in item[4].items()):
                            # a rule that matches
                            surr.append(item[:4])
                    elif the_bigpat[item[0]] == item[1]:
                        # a subtree that matches
                        curr_tree.extend(item[2])
                #print("surr", surr)
                if compute_bigpats:
                    self.bigpats[node].append(the_bigpat)
                if ret_big:
                    yield (orig_val, surr, the_bigpat)
                else:
                    yield (orig_val, surr)
    

    def is_valid(self, bigpat=None, give_reason=False, ret_excess=False, shuffle=False):
        "Check that the argument is valid."
        bigpat_given = bigpat is not None
        if self.bound is None:
            if give_reason:
                return True, "uninitialized"
            else:
                return True
        # list all legal combinations of patterns around origin
        excess_pats = dict()
        i = 0
        rules = [(source, fpat, nvec)
                 for (source, node_rules) in self.trans_rules.items()
                 for (fpat, nvecs) in node_rules.items()
                 for nvec in nvecs]
        for node in self.sym_nodes:
            excess_pats[node] = []
            for (orig_val, surr, the_bigpat) in self.surroundings(node, ret_big=True, bigpat=bigpat, rules=rules, shuffle=shuffle):
                # for each legal combo, sum the contributions from each -v
                if isinstance(self.bound, Fraction):
                    summa = Fraction(0)
                else:
                    summa = 0
                for (source, pat, nvec, away) in surr:
                    try:
                        if away:
                            summa -= self.trans_rules[source][pat][nvec]
                        else:
                            summa += self.trans_rules[source][pat][nvec]
                    except KeyError:
                        # missing rules are treated as 0
                        pass
                if type(summa) == float:
                    # reduce float inaccuracies but possibly introduce false positives
                    summa += TOLERANCE
                if node in self.relevant_nodes:
                    good = summa + self.weights[orig_val] >= self.bound
                    if summa + self.weights[orig_val] > self.bound + (TOLERANCE if type(summa) == float else 0):
                        excess_pats[node].append(the_bigpat)
                else:
                    good = summa >= 0
                    if summa > (TOLERANCE if type(summa) == float else 0):
                        #print("excess", the_bigpat)
                        excess_pats[node].append(the_bigpat)
                if not good:
                    if give_reason:
                        return False, (node, the_bigpat, orig_val,
                                       [(source, pat, nvec, away,
                                         self.trans_rules[node][pat][nvec]
                                         if pat in self.trans_rules[node] and nvec in self.trans_rules[node][pat]
                                         else None)
                                        for (source, pat, nvec, away) in surr],
                                       summa + (self.weights[orig_val] if node in self.relevant_nodes else 0),
                                       self.bound, i)
                    elif ret_excess:
                        return False, None
                    else:
                        return False
                i += 1
        if give_reason:
            if bigpat_given:
                return True, (the_bigpat, orig_nodes,
                              [(pat, vec, away,
                                self.trans_rules[pat][vec]
                                if pat in self.trans_rules and vec in self.trans_rules[pat]
                                else None)
                               for (pat, vec, away) in surr],
                              summa,
                              self.bound,
                              0)
            else:
                return True, "valid"
        elif ret_excess:
            # generate symmetric excess patterns
            # first for the representative nodes using their symmetries
            ret_pats = dict()
            for (node, syms) in self.sym_nodes.items():
                ret_pats[node] = set()
                for pat in excess_pats[node]:
                    for aut in syms:
                        ret_pats[node].add(fd.frozendict({aut(nvec) : sym
                                                          for (nvec, sym) in pat.items()}))
            # then for other nodes using the former
            for node in self.sft.nodes:
                if node not in self.sym_nodes:
                    ret_pats[node] = set()
                    for aut in self.symmetries:
                        if aut.inv_node_map[node] in self.sym_nodes:
                            the_aut = aut
                            sym_node = aut.inv_node_map[node]
                            break
                    for pat in ret_pats[sym_node]:
                        ret_pats[node].add(fd.frozendict({the_aut(nvec) : sym
                                                          for (nvec, sym) in pat.items()}))

            return True, set().union(*ret_pats.values())
    
        else:
            return True

    def try_rationalize(self, verbose=False):
        "Attempt to convert into rational numbers. Return whether it was succesful."
        if verbose:
            print("Attempting to rationalize")
        # compute surroundings
        rules = [(source, fpat, nvec)
                 for (source, node_rules) in self.trans_rules.items()
                 for (fpat, nvecs) in node_rules.items()
                 for nvec in nvecs]
        saved_surrs = dict()
        for node in self.sym_nodes:
            saved_surrs[node] = [s for s in self.surroundings(node, ret_big=True, rules=rules)]
        self.saved_surroundings = saved_surrs
        ret = False
        for den_ix in range(len(DENOMINATORS)):
            #if verbose:
            #    print("Attempting to rationalize with denominator {}.".format(DENOMINATORS[den_ix]))
            rat_ok = self.rationalize(den_ix)
            if rat_ok:
                if verbose:
                    print("Succesfully rationalized solution, bound {}".format(self.bound))
                self.saved_surroundings = None
                return True
        #rat_ok = self.rationalize(len(DENOMINATORS)//2, attempt_fix=True)
        #if rat_ok:
        #    if verbose:
        #        print("Succesfully rationalized solution, bound {}".format(self.bound))
        #    self.saved_surroundings = None
        #    return True
        if verbose:
            valid = self.is_valid(give_reason=True)
            if valid:
                print("Could not rationalize solution, but it is approximately valid")
            else:
                print("Could not rationalize solution and it seems to be invalid")
                for r in reason:
                    print(r)
        self.saved_surroundings = None
        return False
    
    def rationalize(self, den_ix, verbose=False, attempt_fix=False):
        "Attempt to convert into rational numbers using given denominator bound. Return whether it was succesful."
        old_bound = self.bound
        self.bound = Fraction(self.bound).limit_denominator(DENOMINATORS[den_ix])
        #print("denom", DENOMINATORS[den_ix], "bound", self.bound)
        old_rules = self.trans_rules
        self.trans_rules = {node :
                            {fpat :
                             {nvec : Fraction(num).limit_denominator(DENOMINATORS[den_ix])
                              for (nvec, num) in nvecs.items()}
                             for (fpat, nvecs) in rules.items()}
                            for (node, rules) in self.trans_rules.items()}
        valid, reason = self.is_valid(give_reason=True)
        if valid:
            return True
        elif not attempt_fix:
            return False
        count = 0
        maxnum = 0
        timer = 20
        lastfew = []
        for i in range(3*sum(self.score)):
            if valid:
                print("good count", count)
                return True
            count += 1
            # Find reason for failure and try to fix it locally
            node, bigpat, orig_val, rules, summa, bound, num = reason
            lastfew = ([num]+lastfew)[:max(20, maxnum//10)]
            if num > maxnum:
                timer = maxnum//10
            elif num == max(lastfew):
                timer = max(0, timer-1)
            elif timer == 0:
                timer = maxnum//10
            maxnum = max(maxnum, num)
            if count % 100 == 0:
                print("Round {}/{}, num {}, maxfew {}, maxnum {}".format(count, sum(self.score)*3, num, max(lastfew), maxnum))
            float_summa = self.weights[orig_val] if node in self.relevant_nodes else 0
            for (source, pat, nvec, away, rule) in rules:
                if rule is not None:
                    if away:
                        float_summa -= old_rules[source][pat][nvec]
                    else:
                        float_summa += old_rules[source][pat][nvec]
            upper_bound = self.bound if node in self.relevant_nodes else 0
            """
            print("new summa {} = {} < {}, float summa {} = {}".format(
                " + ".join(str((-1)**away*self.trans_rules[source][pat][nvec])
                           for (source, pat, nvec, away, rule) in rules
                           if rule is not None),
                summa,
                self.bound,
                " + ".join(str((-1)**away*old_rules[source][pat][nvec])
                           for (source, pat, nvec, away, rule) in rules
                           if rule is not None),
                float_summa))
            """
            found = False
            rules = rules[::1]
            random.shuffle(rules)
            for n in DENOMINATORS[den_ix:]:
                try_charge = dict()
                new_summa = summa
                # try to re-approximate to match bound
                for r in rules:
                    num_r = rules.count(r)
                    (source, pat, nvec, away, rule) = r
                    if rule is not None:
                        old_charge = old_rules[source][pat][nvec]
                        new_charge = self.trans_rules[source][pat][nvec]
                        try_charge[r] = Fraction(old_charge).limit_denominator(n)
                        new_summa = new_summa + num_r*(new_charge - try_charge[r]) if away else new_summa - num_r*(new_charge + try_charge[r])
                        if (new_summa == upper_bound):
                            for r in try_charge:
                                (source, pat, nvec, away, rule) = r
                            self.trans_rules[source][pat][nvec] = try_charge[r]
                            found = True
                            break
                if found:
                    break
            else:
                # reset one rule to match bound
                (source, pat, nvec, away, rule) = r = next(r for r in rules if r[-1] is not None)
                num_r = rules.count(r)
                self.trans_rules[source][pat][nvec] += (-1)**away*(upper_bound - summa)/num_r
                found = True
            if not found:
                break
            valid, reason = self.is_valid(give_reason=True, shuffle=True)
        print("bad count", count)
        self.bound = old_bound
        self.trans_rules = old_rules
        return False

    def update_specs(self, trans_rules=None, rules_only=False):
        "Update specs, bigdomain and score to match the current or given transition rules."
        if trans_rules is None:
            trans_rules = self.trans_rules
        domain_nvecs = dict()
        max_card = 0
        #print("old specs", self.specs)
        for (node, rules) in trans_rules.items():
            domain_nvecs[node] = dict()
            for (fpat, nvecs) in rules.items():
                fset = frozenset(fpat)
                max_card = max(max_card, len(fset))
                if fset not in domain_nvecs:
                    domain_nvecs[node][fset] = set()
                domain_nvecs[node][fset] |= set(nvecs)
        self.specs = {node : [(v, list(d))
                              for (d,vs) in nvecs.items()
                              for v in vs]
                      for (node, nvecs) in domain_nvecs.items()
                      if nvecs}
        if self.score is None:
            self.score = [0]*max_card
        else:
            self.score = [0]*len(self.score)
        for (node, rules) in trans_rules.items():
            for (fpat, nvecs) in rules.items():
                self.score[-len(fpat)] += len(nvecs)
        #print("score", self.score)
        if rules_only or None in self.bigpats.values():
            return
        #print("new specs", self.specs)
        bigdomain = dict()
        for node in self.sym_nodes:
            bigdomain[node] = self.bigdomain_from_spec(node)
        #print("new bigdomain", bigdomain)
        if bigdomain != self.bigdomain:
            #print("changing")
            self.bigdomain = bigdomain
            self.bigpats = {node : set(fd.frozendict({nvec : bigpat[nvec]
                                                      for nvec in bigdomain[node]})
                                       for bigpat in pats)
                            for (node, pats) in self.bigpats.items()}

    def minimize_rule_count(self, solver_str, verbose=False, print_freq=5000, max_rounds=None, ordered_split=False, save_rules=None, sort_rules=False):
        "Iteratively remove rules until each is essential, starting from the largest."
        rule_triples = [(source, fpat, nvec)
                        for (source, rules) in self.trans_rules.items()
                        for (fpat, nvecs) in rules.items()
                        if max_rounds is None or len(fpat) > 1
                        for nvec in nvecs]
        random.shuffle(rule_triples)
        if sort_rules:
            rule_triples.sort(key=lambda p: -len(p[1]))
        #valid, reason = self.is_valid(give_reason=True)
        #if not valid:
        #    print("Invalid")
        #    print(reason)
        #    1/0
        #old_rules = {fpat : vecs.copy() for (fpat, vecs) in  self.trans_rules.items()}
        if verbose:
            print("Minimizing rule count")
        num_removed = max(1, len(rule_triples)//10)
        i = 0
        while rule_triples and (max_rounds in [None, "until_fail"] or i < max_rounds):
            i += 1
            # pick rules, remove them and check whether we can reach the same bound as before
            removed = rule_triples[:num_removed]
            old_rules = {source : {fpat : vecs.copy()
                                  for (fpat, vecs) in rules.items()}
                         for (source, rules) in self.trans_rules.items()}
            for (source, fpat, vec) in removed:
                del self.trans_rules[source][fpat][vec]
                if not self.trans_rules[source][fpat]:
                    del self.trans_rules[source][fpat]
            if verbose:
                print("Round {}: from {} to {} rules, {} left to check".format(i, sum(len(nvecs) for rules in old_rules.values() for nvecs in rules.values()), sum(len(nvecs) for rules in self.trans_rules.values() for nvecs in rules.values()), len(rule_triples)))
            same_bound = self.compute_bound(solver_str, verbose=verbose, print_freq=print_freq, ordered_split=ordered_split)
            #print("Changed:", same_bound)
            if same_bound:
                # rule was not needed
                rule_triples = [(source, fpat, nvec)
                                for (source, fpat, nvec) in rule_pairs[num_removed:]
                                if fpat in self.trans_rules[source]
                                if nvec in self.trans_rules[source][fpat]]
                if save_rules is not None:
                    if verbose:
                        print("Saving intermediate rules...", end='')
                    self.save_transfer_rules(save_rules)
                    if verbose:
                        print(" done")
            else:
                # rule was needed -> put it back
                self.trans_rules = old_rules
                self.update_specs(rules_only=True)
                if num_removed == 1:
                    if max_rounds == "until_fail":
                        break
                    rule_triples.pop(0)
                else:
                    num_removed = max(1, num_removed//2)
                    random.shuffle(rule_triples)
                    rule_triples.sort(key=lambda p: -len(p[0]))
            #if valid:
            #    #self.try_rationalize()
            #    still_valid, reason = self.is_valid(give_reason=True)
            #    if not still_valid:
            #        print("From valid to invalid")
            #        print(reason)
            #        bigpat = reason[0]
            #        print(self.trans_rules == old_rules)
            #        print(self.is_valid(bigpat=bigpat, give_reason=True))
            #        1/0
                

    def compute_bound(self, solver_str, verbose=False, print_freq=5000, save_constr=None, load_constr=None, split=False, max_split=None, num_split=None, ordered_split=False):
        "Compute the best lower bound for the specs and the associated charge transfer rules."
        # this is how large density can be made, i.e. what we want to compute
        density = pulp.LpVariable("epsilon",
                                  min(self.weights.values()),
                                  max(self.weights.values()))
        density.setInitialValue(max(self.weights.values()))

        # we simply try to maximize this density in our problem
        prob = pulp.LpProblem("discharge", pulp.LpMaximize)
        prob += density

        total_vars = 1
        total_constr = 0
        send = {}

        if load_constr is not None:
            # load bigpats from a file
            print("loading")
            with open(load_constr + '.output', 'r') as f:
                bigdomain = dict()
                bigpats = dict()
                while True:
                    line = f.readline()
                    if line.strip() == "#bigdomain":
                        continue
                    elif line.strip() == "#bigpats":
                        break
                    else:
                        node, domain = eval(line)
                        bigdomain[node] = domain
                while True:
                    line = f.readline()
                    if line.strip() == "#end":
                        break
                    elif line.strip() == "#node":
                        node = eval(f.readline())
                        bigpats[node] = []
                    else:
                        bigpats[node].append(eval(line))
            print("done")

        if verbose:
            print("Computing pattern variables")
        i = 0
        if self.trans_rules is None:
            for (node, node_specs) in self.specs.items():
                for (tr_nvec, domain) in node_specs:
                    for pat in self.sft.all_patterns(domain, extra_rad=self.radius, mod_symmetries=[aut for aut in self.sym_nodes[node] if aut(tr_nvec) == tr_nvec]):
                        fr_pat = fd.frozendict(pat)
                        send[node, fr_pat, tr_nvec] = pulp.LpVariable("patvec{}".format(i))
                        send[node, fr_pat, tr_nvec].setInitialValue(0)
                        i += 1
                        total_vars += 1
                        if verbose and total_vars%print_freq == 0:
                            print("{} found so far".format(total_vars))
        else:
            i = 0
            splits = 0
            triples = [(source, fr_pat, nvecs)
                       for (source, rules) in self.trans_rules.items()
                       for (fr_pat, nvecs) in rules.items()]
            random.shuffle(triples)
            triples.sort(key=lambda p: -len(p[1]))
            for (source, fr_pat, nvecs) in triples:
                for tr_nvec in nvecs:
                    if split and len(fr_pat) > 1 and (max_split is None or splits < max_split):
                        # replace pattern with smaller subpatterns
                        splits += 1
                        if num_split is None:
                            split_nvecs = fr_pat
                        elif ordered_split:
                            split_nvecs = list(sorted(fr_pat))[:num_split]
                        else:
                            split_nvecs = random.sample(sorted(fr_pat), min(num_split, len(fr_pat)))
                        for nvec in split_nvecs:
                            new_fpat = fr_pat.delete(nvec)
                            if (source, new_fpat, tr_nvec) not in send:
                                send[source, new_fpat, tr_nvec] = pulp.LpVariable("patvec{}".format(i)) #, 0, 1)
                                send[source, new_fpat, tr_nvec].setInitialValue(0)
                                i += 1
                                total_vars += 1
                                if verbose and total_vars%print_freq == 0:
                                    print("{} found so far".format(total_vars))
                    elif (not split) or all(any(fr_pat.get(nvec, None) != sym
                                                for (nvec, sym) in fr_pat2.items())
                                            for (source2, fr_pat2, tr_nvec2) in send
                                            if source2 == source and tr_nvec2 == tr_nvec):
                        # keep original pattern
                        send[source, fr_pat, tr_nvec] = pulp.LpVariable("patvec{}".format(i)) #, 0, 1)
                        send[source, fr_pat, tr_nvec].setInitialValue(0)
                        i += 1
                        total_vars += 1
                        if verbose and total_vars%print_freq == 0:
                            print("{} found so far".format(total_vars))

        # TODO: update this
        #specs = dict()
        #for (fpat, vec) in send:
        #    if fpat not in specs:
        #        specs[fpat] = []
        #    specs[fpat].append(vec)
        #self.update_specs(specs, rules_only=True)

        if verbose:
            print("Done with {} variables, now adding constraints".format(total_vars))
            #for ((s, p, d), v) in send.items():
            #    print("when", p)
            #    print("can send to", d)
            #    print("var", v)

        constr_tim = time.time()
        # list all legal combinations of patterns around origin
        # only handle one node from each symmetry orbit
        i = 0
        for node in self.sym_nodes:
            for (orig_val, surr) in self.surroundings(node, rules=None if self.bound is None else list(send), verbose=verbose):
                # for each legal combo, sum the contributions from each -v
                summa = 0
                for (source, pat, nvec, away) in surr:
                    try:
                        if away:
                            summa -= send[source, pat, nvec]
                        else:
                            summa += send[source, pat, nvec]
                    except KeyError:
                        continue
                if node in self.relevant_nodes:
                    summa += self.weights[orig_val]
                    prob += summa >= density
                    #print("adding", summa >= density)
                else:
                    prob += summa >= 0
                i += 1
                if verbose and i%print_freq == 0:
                    print("{} found so far".format(i))

        if save_constr is not None:
            # save bigpats to file
            with open(save_constr + '.output', 'w') as f:
                f.write("#bigdomain\n")
                for p in self.bigdomain.items():
                    f.write(str(p)+"\n")
                f.write("#bigpats\n")
                for (node, pats) in self.bigpats.items():
                    f.write("#node\n")
                    f.write(str(node)+"\n")
                    for pat in pats:
                        f.write(str(dict(pat))+"\n")
                f.write("#end")

        if verbose:
            print("Done with {} constraints in {} seconds, now solving".format(i, time.time()-constr_tim))
        #print("prob", prob)
        tim = time.time()
        solver, solver_opts = SOLVER_DICTS[solver_str][0]
        solver(**solver_opts).solve(prob)
        #pulp.HiGHS(msg=False,
        #           solver="ipx"
        #           ).solve(prob)
        #pulp.PULP_CBC_CMD(msg=False, warmStart=True, keepFiles=True).solve(prob)
        #pulp.GLPK_CMD(msg=False, options=SOLVER_OPTS_INITIAL).solve(prob)
        if verbose:
            print("Solved in {} seconds, bound {}".format(time.time()-tim, density.varValue))

        

        if self.bound is not None and density.varValue + TOLERANCE < self.bound:
            self.update_specs(rules_only=True)
            return False

        self.trans_rules = {node : dict() for node in self.sft.nodes}
        for ((source, fr_pat, nvec), var) in send.items():
            if var.varValue:
                if fr_pat not in self.trans_rules[source]:
                    self.trans_rules[source][fr_pat] = dict()
                self.trans_rules[source][fr_pat][nvec] = var.varValue

        if self.bound is None:
            self.bound = density.varValue
        self.update_specs()
        #print("trans_rules", self.trans_rules)
        return True

    
    def recompute_with_holes(self, solver_str, verbose=False, print_freq=5000, max_larges=None, num_split=None, ordered_split=False, minimize_all=False, sort_pats=True):
        "Recompute the argument using patterns with one node removed, minimizing contributions of large patterns."
        # an upper bound on the total share send by large patterns, which we minimize
        if self.bound is None:
            raise GriddyRuntimeError("Cannot recompute discharging argument with no initial bound.")
        
        total_vars = 0
        total_constr = 0
        rule_triples = [(node, fpat, nvec)
                        for (node, rules) in self.trans_rules.items()
                        for (fpat, nvecs) in rules.items()
                        for nvec in nvecs]
        random.shuffle(rule_triples)
        if sort_pats:
            rule_triples.sort(key=lambda p: -len(p[1]))
        #print("num split", num_split)

        if verbose:
            print("Computing pattern variables")
        i = 0
        num_larges = 0
        processed_triples = dict() # True for to-be minimized rules, False for others
        for triple in rule_triples:
            node, fpat, tr_nvec = triple
            if triple not in processed_triples:
                i += 1
                if verbose and i%print_freq == 0:
                    print("{} found so far".format(i))
            if len(fpat) > 1 and (max_larges is None or num_larges < max_larges):
                #print("n")
                processed_triples[triple] = True
                num_larges += 1
                if num_split is None:
                    split_nvecs = fpat
                elif ordered_split:
                    split_nvecs = list(sorted(fpat))[:num_split]
                else:
                    split_nvecs = random.sample(sorted(fpat), min(num_split, len(fpat)))
                #print(split_nvecs)
                for sp_nvec in split_nvecs:
                    #print("k")
                    new_fpat = fpat.delete(sp_nvec)
                    if (node, new_fpat, tr_nvec) not in processed_triples:
                        processed_triples[node, new_fpat, tr_nvec] = minimize_all
                        i += 1
                        if verbose and i%print_freq == 0:
                            print("{} found so far".format(i))
            elif triple not in processed_triples:
                processed_triples[triple] = minimize_all

        #for (fpat, vecs) in self.trans_rules.items():
        #    if fpat not in all_pats:
        #        print("not in all_pats")
        #        1/0
        #    patvecs = all_pats[fpat][0]
        #    for vec in vecs:
        #        if vec not in patvecs:
        #            print("not in patvecs", fpat, vecs, vec, patvecs)
        #            1/0

        #assert all(fpat in all_pats
        #           and all(vec in all_pats[fpat][0] for vec in vecs)
        #           for (fpat, vecs) in self.trans_rules.items())

        rules = dict()
        for (node, fpat, nvec) in processed_triples:
            if node not in rules:
                rules[node] = dict()
            if fpat not in rules[node]:
                rules[node][fpat] = []
            rules[node][fpat].append(nvec)
        self.update_specs(trans_rules=rules, rules_only=True)

        send = dict()
        sum_large = 0

        i = 0
        i_large = 0
        i_small = 0
        for ((node, fr_pat, tr_nvec), large) in processed_triples.items():
            # create variables for how much is discharged in each direction from each pattern
            # for large patterns we split into positive and negative parts
            if large:
                for sign in [True, False]:
                    send[node, fr_pat, tr_nvec, sign] = pulp.LpVariable("patvec{}".format(i), lowBound=0)
                    if tr_nvec in self.trans_rules[node].get(fr_pat, []):
                        send[node, fr_pat, tr_nvec, sign].setInitialValue(max(0, (-1)**(1-sign)*self.trans_rules[node][fr_pat][tr_nvec]))
                    else:
                        send[node, fr_pat, tr_nvec, sign].setInitialValue(0)
                    sum_large += (len(fr_pat) + 1) * send[node, fr_pat, tr_nvec, sign]
                    i += 1
                i_large += 1
            else:
                send[node, fr_pat, tr_nvec, None] = pulp.LpVariable("patvec{}".format(i))
                if fr_pat in self.trans_rules[node] and tr_nvec in self.trans_rules[node][fr_pat]:
                    send[node, fr_pat, tr_nvec, None].setInitialValue(self.trans_rules[node][fr_pat][tr_nvec])
                else:
                    send[node, fr_pat, tr_nvec, None].setInitialValue(0)
                i += 1
                i_small += 1

        if verbose:
            print("Done with {} variables (2*{} to be minimized, {} free), now adding constraints".format(i, i_large, i_small))
        constr_tim = time.time()

        # we minimize the sum of the absolute values of the charges sent by large patterns
        prob = pulp.LpProblem("discharge_opt", pulp.LpMinimize)
        prob += sum_large
            
        # list all legal combinations of patterns around origin
        i = 0
        for node in self.sym_nodes:
            for (orig_val, surr) in self.surroundings(node, rules=[p[:3] for p in send if p[3] != False]):
                # for each legal combo, sum the contributions from each -v
                summa = 0
                for (source, pat, nvec, away) in surr:
                    if (source, pat, nvec) not in processed_triples:
                        continue
                    if processed_triples[source, pat, nvec]:
                        # large pattern -> has sign
                        if away:
                            summa -= send[source, pat, nvec, True]
                            summa += send[source, pat, nvec, False]
                        else:
                            summa += send[source, pat, nvec, True]
                            summa -= send[source, pat, nvec, False]
                    else:
                        # small pattern -> does not have sign
                        if away:
                            summa -= send[source, pat, nvec, None]
                        else:
                            summa += send[source, pat, nvec, None]

                # the resulting charge must be at least the known bound
                if node in self.relevant_nodes:
                    summa += self.weights[orig_val]
                    constr = summa >= self.bound
                else:
                    constr = summa >= 0
                #print("constr", constr)
                #if constr == False:
                #    raise GriddyRuntimeError("Unable to optimize invalid discharging argument")
                prob += constr
                i += 1
                if verbose and i%print_freq == 0:
                    print("{} found so far".format(i))

        if verbose:
            print("Done with {} constraints in {} seconds, now solving".format(i, time.time()-constr_tim))
        
        #print("status before", prob.status)
        tim = time.time()
        solver, solver_opts = SOLVER_DICTS[solver_str][0]
        solver(**solver_opts).solve(prob)
        #pulp.HiGHS(msg=False, solver="ipx").solve(prob)
        #pulp.GLPK_CMD(msg=False, options=SOLVER_OPTS_RECOMPUTE).solve(prob)
        #pulp.PULP_CBC_CMD(msg=False, warmStart=True).solve(prob)
        if prob.status != 1:
            backup = SOLVER_DICTS[solver_str][1]
            if backup is not None:
                solver(**solver_opts).solve(prob)
                if prob.status != 1:
                    raise NoSolutionError("Unsolvable linear problem")
            else:
                raise NoSolutionError("Unsolvable linear problem")
        if verbose:
            print("Solved in {} seconds".format(time.time()-tim))
        #print("status after", prob.status)

        # collect results
        self.trans_rules = dict()
        for ((node, fr_pat, nvec, sign), var) in send.items():
            if var.varValue:
                if node not in self.trans_rules:
                    self.trans_rules[node] = dict()
                if fr_pat not in self.trans_rules[node]:
                    self.trans_rules[node][fr_pat] = dict()
                if nvec not in self.trans_rules[node][fr_pat]:
                    self.trans_rules[node][fr_pat][nvec] = 0
                if (sign is None) or sign:
                    self.trans_rules[node][fr_pat][nvec] += var.varValue
                else:
                    self.trans_rules[node][fr_pat][nvec] -= var.varValue
        self.update_specs()
            



if __name__ == "__main__":
    t = time.time()
    nodes = [0]
    alph = [0,1]
    forbs = [{(-1,0,0):0, (0,0,0):0, (1,0,0):0,(0,1,0):0}]
    sft = SFT(2, nodes, alph, forbs=forbs)
    domain = [(0,0,0),(-1,0,0),(0,-1,0),(0,1,0),(1,0,0)]
    #patterns = list(sft.all_patterns([(a,b,0) for (a,b) in domain+[(0,0)]]))
    #patterns = pats(set((a,b,0) for (a,b) in domain+[(0,0)]), alph)
    #patterns = [pat for pat in patterns if sft.deduce(pat, set(pat))]
    #print("patterns", len(patterns))
    vecs = [(0,1),(1,0),(-1,0)]
    dens = optimal_density(sft, [(vecs, domain)], 1, verbose=True)
    print("density", dens)
    print("took", time.time() - t, "seconds")
