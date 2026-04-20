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
import random

TOLERANCE = 1e-6

SOLVER_DICTS = {
    "CBC" : (pulp.apis.PULP_CBC_CMD,
             {"msg" : False,
              "warmStart" : True,
              "keepFiles" : True
              }),
    "GLPK" : (pulp.apis.GLPK_CMD,
              {"msg" : False,
               "options" : ["--primal", "--cbg",  "--xcheck"]
               }),
    "HiGHS_hipo" : (pulp.apis.HiGHS,
                    {"msg" : False,
                     "solver" : "hipo"
                     }),
    "HiGHS_ipx" : (pulp.apis.HiGHS,
                   {"msg" : False,
                    "solver" : "ipx"
                    }),
    "HiGHS_simplex" : (pulp.apis.HiGHS,
                       {"msg" : False,
                        "solver" : "simplex",
                        "simplex_strategy" : "primal"
                        })
}

def rules_to_tree(alph, bigdomain, rule_pairs):
    "Transform charge transfer rules into a decision tree, which can be used to extract constraints from bigpats."
    # quads will store tuples (pat, vec, away, tr_pat) where:
    # pat is the original pattern,
    # vec is the vector along which we transfer charge,
    # away is True if we transfer away from the origin,
    # tr_pat is pat translated by -vec if away is False, and pat otherwise.
    # We will look for tr_pat in the bigpats.
    quads = []
    for (pat, vec) in rule_pairs:
        quads.append((pat, vec, True, pat))
        quads.append((pat, vec, False,
                      fd.frozendict({nvsub(nvec, vec) : sym
                                     for (nvec, sym) in pat.items()})))
    tree, size = quads_to_tree(alph, bigdomain, quads, [])
    assert size == len(quads)
    #print("tree", size, len(tree), [p[:2] for p in tree])
    return tree

def quads_to_tree(alph, bigdomain, quads, tree):
    # tree is a list of triples: tree := [(nvec, sym, [tree]) | (pat, vec, bool)].
    # the idea is that we iterate the list and test whether bigpat[nvec] = sym.
    # at each match, if the third item is a list we recurse,
    # and otherwise we add (pat, vec, away) to the constraint.
    #print("call", quads, tree)
    sumsizes = 0
    while quads:
        #print("lq", len(quads))
        old_len = len(quads)
        if all(q[3] == quads[0][3] for q in quads[1:]):
            #print("eq")
            for quad in quads:
                tree.append(quad)
                sumsizes += 1
            break
        else:
            # greedily choose nvec and sym that split quads the most evenly
            pair = max(((nvec, sym) for nvec in bigdomain for sym in alph[nvec[1]]
                        if any(q[3].get(nvec, None) == sym for q in quads)),
                       key = lambda p: min(n := sum(1 for q in quads
                                                    if q[3].get(p[0], None) == p[1]),
                                           len(quads) - n))
            nvec, sym = pair
            chosen = [(pat, vec, away, tr_pat.delete(nvec))
                      for (pat, vec, away, tr_pat) in quads
                      if tr_pat.get(nvec, None) == sym]
            #print("pair", nvec, sym, old_len, len(chosen))
            #print("lc", len(chosen))
            assert len(chosen) != len(quads)
            subtree, subsize = quads_to_tree(alph, bigdomain, chosen, [])
            sumsizes += subsize
            tree.append((nvec, sym, subtree))
            quads = [q for q in quads if q[3].get(nvec, None) != sym]
            assert old_len == len(quads) + len(chosen)
    #print("ret", tree[::-1])
    return tree[::-1], sumsizes

def print_tree(tree, level=0):
    for nvec, sym, item in reversed(tree):
        print("{}on {} at {}:".format(" "*level, sym, nvec))
        if type(item) == list:
            print_tree(item, level+1)
        else:
            print("{}use {}".format(" "*(level+1), item))

class DischargingArgument:
    "A discharging argument for a lower bound on the minimum density of an SFT."

    def __init__(self, sft, specs, radius, weights=None):
        self.sft = sft
        self.weights = weights
        self.radius = radius
        self.specs = specs
        if weights is None:
            self.weights = {a:int(a) for alph in sft.alph.values() for a in alph}
        else:
            self.weights = weights
        self.bound = None
        # trans_rules will be a dict[frozenpattern : dict[vector : number]]
        self.trans_rules = None
        self.bigpats = None
        self.bigdomain = None
        self.score = None

    def save_transfer_rules(self, filename):
        "Save transfer rules and bound to a file."
        with open(filename+".output", 'w') as f:
            if type(self.bound) == float:
                f.write(str(self.bound)+'\n')
            else:
                # Fraction
                num, den = self.bound.as_integer_ratio()
                f.write(str(num) + '/' + str(den) + '\n')
            for (fpat, vecs) in self.trans_rules.items():
                for ((vec, node), sym) in fpat.items():
                    f.write(" ".join(str(c) for c in vec) + " ." + ".".join(node) + " " + sym + " ")
                f.write(':')
                for (vec, amount) in vecs.items():
                    f.write(" " + " ".join(str(c) for c in vec) + " ")
                    if type(amount) == float:
                        f.write(str(amount))
                    else:
                        # Fraction
                        num, den = amount.as_integer_ratio()
                        f.write(str(num) + '/' + str(den))
                f.write('\n')

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
            for ln in f.readlines():
                if ':' not in ln:
                    continue
                #print("ln", repr(ln))
                patstr, rest = ln.split(':')
                pat = dict()
                items = patstr.split()
                dim = self.sft.dim
                for i in range(len(items)//(dim+2)):
                    vec = tuple(int(c) for c in items[(dim+2)*i : (dim+2)*(i+1)-2])
                    #print("vec", vec)
                    nodestr = items[(dim+2)*(i+1)-2]
                    if nodestr == '.':
                        node = ()
                    else:
                        node = tuple(nodestr[1:].split('.'))
                    #print("node", node)
                    pat[vec, node] = items[(dim+2)*(i+1)-1]
                    #print("sym", pat[vec, node])
                fpat = fd.frozendict(pat)
                if fpat not in self.trans_rules:
                    self.trans_rules[fpat] = dict()
                restitems = rest.split()
                #print("restitems", restitems)
                for i in range(len(restitems)//(dim+1)):
                    vec = tuple(int(c) for c in restitems[(dim+1)*i : (dim+1)*(i+1)-1])
                    #print("vec", vec)
                    numstr = restitems[(dim+1)*(i+1)-1]
                    #print("numstr", numstr)
                    if '/' in numstr:
                        num = Fraction(*(int(x) for x in numstr.split('/')))
                    else:
                        num = float(numstr)
                    self.trans_rules[fpat][vec] = num

    # enumerate combined locally correct patterns that affect origin
    def surroundings(self, bigpat=None, ret_big=False, rule_pairs=None):
        #print("Spec len", len(self.specs))
        # TODO: find a more efficient way to generate these when self.specs is large
        compute_bigpats = False
        if bigpat is not None:
           bigpats = [bigpat] 
        elif self.bigpats is None:
            compute_bigpats = True
            self.bigdomain = set(nvsub(nvec, vec) for (vecs, domain) in self.specs for nvec in domain for vec in vecs+[(0,)*self.sft.dim]) | {((0,)*self.sft.dim, node) for node in self.sft.nodes}
            bigpats = self.sft.all_patterns(self.bigdomain, extra_rad=self.radius)
            self.bigpats = []
        else:
            bigpats = self.bigpats
        if rule_pairs is None or (len(rule_pairs) >= 2**sum(len(x) for (x,_) in self.specs)):
            for bigpat in bigpats:
                surr = []
                orig_nodes = {node : bigpat[((0,)*self.sft.dim, node)] for node in self.sft.nodes}
                for (vecs, domain) in self.specs:
                    orig_pat = fd.frozendict({nvec : bigpat[nvec] for nvec in domain})
                    for vec in vecs:
                        # away from origin
                        surr.append((orig_pat, vec, True))
                        # toward origin
                        surr.append((fd.frozendict({nvec : bigpat[nvsub(nvec, vec)] for nvec in domain}), vec, False))
                if compute_bigpats:
                    self.bigpats.append(bigpat)
                if ret_big:
                    yield (orig_nodes, surr, bigpat)
                else:
                    yield (orig_nodes, surr)
        else:
            tree = rules_to_tree(self.sft.alph, self.bigdomain, rule_pairs)
            for bigpat in bigpats:
                #print("new bigpat", bigpat)
                surr = []
                orig_nodes = {node : bigpat[((0,)*self.sft.dim, node)] for node in self.sft.nodes}
                curr_tree = tree.copy()
                while curr_tree:
                    #print("popping", curr_tree[-1])
                    item = curr_tree.pop()
                    # item is either (nvec, sym, subtree) or (pat, vec, away, tr_pat)
                    if len(item) == 4:
                        if all(bigpat[nvec] == sym for (nvec, sym) in item[3].items()):
                            # a rule that matches
                            surr.append(item[:3])
                    elif bigpat[item[0]] == item[1]:
                        # a subtree that matches
                        curr_tree.extend(item[2])
                #print("surr", surr)
                if compute_bigpats:
                    self.bigpats.append(bigpat)
                if ret_big:
                    yield (orig_nodes, surr, bigpat)
                else:
                    yield (orig_nodes, surr)
    

    def is_valid(self, bigpat=None, give_reason=False):
        "Check that the argument is valid."
        bigpat_given = bigpat is not None
        if self.bound is None:
            if give_reason:
                return True, "uninitialized"
            else:
                return True
        # list all legal combinations of patterns around origin
        i = 0
        rule_pairs = [(fpat, vec) for (fpat, vecs) in self.trans_rules.items() for vec in vecs]
        for (orig_nodes, surr, bigpat) in self.surroundings(ret_big=True, bigpat=bigpat, rule_pairs=rule_pairs):
            # for each legal combo, sum the contributions from each -v
            if isinstance(self.bound, Fraction):
                summa = Fraction(0)
                for node in self.sft.nodes:
                    summa += Fraction(self.weights[orig_nodes[node]]) / Fraction(len(self.sft.nodes))
            else:
                summa = 0
                for node in self.sft.nodes:
                    summa += self.weights[orig_nodes[node]] / len(self.sft.nodes)
            for (pat, vec, away) in surr:
                try:
                    if away:
                        summa -= self.trans_rules[pat][vec]
                    else:
                        summa += self.trans_rules[pat][vec]
                except KeyError:
                    # missing rules are treated as 0
                    pass
            if type(summa) == float:
                # reduce floating point inaccuracies but possibly introduce false positives
                summa += TOLERANCE
            if summa < self.bound:
                if give_reason:
                    return False, (bigpat, orig_nodes,
                                   [(pat, vec, away,
                                     self.trans_rules[pat][vec]
                                     if pat in self.trans_rules and vec in self.trans_rules[pat]
                                     else None)
                                    for (pat, vec, away) in surr],
                                   summa,
                                   self.bound)
                else:
                    return False
        if give_reason:
            if bigpat_given:
                return True, (bigpat, orig_nodes,
                              [(pat, vec, away,
                                self.trans_rules[pat][vec]
                                if pat in self.trans_rules and vec in self.trans_rules[pat]
                                else None)
                               for (pat, vec, away) in surr],
                              summa,
                              self.bound)
            else:
                return True, "valid"
        else:
            return True

    def try_rationalize(self):
        "Attempt to convert into rational numbers. Return whether it was succesful."
        for n in [25, 50, 75, 100, 150, 200, 350, 500, 750, 1000, 2000, 5000, 10000, 20000, 50000, 100000, 200000, 500000, 1000000]:
            rat_ok = self.rationalize(n)
            if rat_ok:
                return True
        return False
    
    def rationalize(self, denom_bound, verbose=False):
        "Attempt to convert into rational numbers using given denominator bound. Return whether it was succesful."
        old_bound = self.bound
        self.bound = Fraction(self.bound).limit_denominator(denom_bound)
        old_rules = self.trans_rules
        self.trans_rules = {fpat : {vec : Fraction(num).limit_denominator(denom_bound)
                                    for (vec, num) in vecs.items()}
                            for (fpat, vecs) in self.trans_rules.items()}
        valid, reason = self.is_valid(give_reason=True)
        if valid:
            return True
        else:
            if verbose:
                print("Could not rationalize with denominator <= {}, reason:".format(denom_bound))
                bigpat, orig_nodes, rules, summa, bound = reason
                old_summa = 0
                for node in self.sft.nodes:
                    old_summa += self.weights[orig_nodes[node]] / len(self.sft.nodes)
                for (pat, vec, away, _) in rules:
                    if pat in old_rules and vec in old_rules[pat]:
                        if away:
                            old_summa -= old_rules[pat][vec]
                        else:
                            old_summa += old_rules[pat][vec]
                print(bigpat,
                      [(pat, vec, away, amount,
                        old_rules[pat][vec]
                        if pat in old_rules and vec in old_rules[pat]
                        else None)
                       for (pat, vec, away, amount) in rules],
                      summa, bound,
                      old_summa, old_bound)
            self.bound = old_bound
            self.trans_rules = old_rules
            return False

    def update_specs(self, trans_rules=None, rules_only=False):
        "Update specs, bigdomain and score to match the current or given transition rules."
        if trans_rules is None:
            trans_rules = self.trans_rules
        domain_vecs = dict()
        for (fpat, vecs) in trans_rules.items():
            fset = frozenset(fpat)
            if fset not in domain_vecs:
                domain_vecs[fset] = set()
            domain_vecs[fset] |= set(vecs)
        self.specs = [(list(v),list(d)) for (d,v) in domain_vecs.items()]
        if self.score is None:
            self.score = [0]*max((len(fpat) for fpat in trans_rules), default=0)
        else:
            self.score = [0]*len(self.score)
        for (fpat, vecs) in trans_rules.items():
            self.score[-len(fpat)] += len(vecs)
        if rules_only or self.bigpats is None:
            return
        #print("new specs", self.specs)
        bigdomain = set(nvsub(nvec, vec)
                        for (vecs, domain) in self.specs
                        for nvec in domain
                        for vec in vecs+[(0,)*self.sft.dim]) \
                            | {((0,)*self.sft.dim, node)
                               for node in self.sft.nodes}
        if bigdomain != self.bigdomain:
            #print("old bigdomain", self.bigdomain, "new", bigdomain)
            self.bigdomain = bigdomain
            self.bigpats = set(fd.frozendict({nvec : bigpat[nvec]
                                              for nvec in bigdomain})
                               for bigpat in self.bigpats)

    def minimize_rule_count(self, solver_str, verbose=False, print_freq=5000, max_rounds=None, ordered_split=False, save_rules=None, sort_rules=False):
        "Iteratively remove rules until each is essential, starting from the largest."
        rule_pairs = [(fpat, vec)
                      for (fpat, vecs) in self.trans_rules.items()
                      if max_rounds is None or len(fpat) > 1
                      for vec in vecs]
        random.shuffle(rule_pairs)
        if sort_rules:
            rule_pairs.sort(key=lambda p: -len(p[0]))
        #valid, reason = self.is_valid(give_reason=True)
        #if not valid:
        #    print("Invalid")
        #    print(reason)
        #    1/0
        #old_rules = {fpat : vecs.copy() for (fpat, vecs) in  self.trans_rules.items()}
        if verbose:
            print("Minimizing rule count")
        num_removed = max(1, len(rule_pairs)//10)
        i = 0
        while rule_pairs and (max_rounds in [None, "until_fail"] or i < max_rounds):
            i += 1
            # pick rules, remove them and check whether we can reach the same bound as before
            removed_pairs = rule_pairs[:num_removed]
            old_rules = {fpat : vecs.copy()
                         for (fpat, vecs) in self.trans_rules.items()}
            for (fpat, vec) in removed_pairs:
                del self.trans_rules[fpat][vec]
                if not self.trans_rules[fpat]:
                    del self.trans_rules[fpat]
            if verbose:
                print("Round {}: from {} to {} rules, {} left to check".format(i, sum(len(vecs) for vecs in old_rules.values()), sum(len(vecs) for vecs in self.trans_rules.values()), len(rule_pairs)))
            same_bound = self.compute_bound(solver_str, verbose=verbose, print_freq=print_freq, ordered_split=ordered_split)
            #print("Changed:", same_bound)
            if same_bound:
                # rule was not needed
                rule_pairs = [(fpat, vec) for (fpat, vec) in rule_pairs[num_removed:]
                              if fpat in self.trans_rules
                              if vec in self.trans_rules[fpat]]
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
                    rule_pairs.pop(0)
                else:
                    num_removed = max(1, num_removed//2)
                    random.shuffle(rule_pairs)
                    rule_pairs.sort(key=lambda p: -len(p[0]))
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
            self.bigdomain = []
            self.bigpats = []
            with open(load_constr + '.output', 'r') as f:
                strs = f.readline().split()
                nvec_len = self.sft.dim+1
                for coords in [strs[i*nvec_len:(i+1)*nvec_len] for i in range(len(strs)//nvec_len)]:
                    #print("got coords", coords, coords[-1].split('.'))
                    self.bigdomain.append((tuple(int(c) for c in coords[:-1]),
                                           tuple(s for s in coords[-1].split('.') if s)))
                #print("bigdomain", self.bigdomain)
                for line in f.readlines():
                    if line:
                        self.bigpats.append({nvec : sym
                                             for (nvec, sym) in zip(self.bigdomain, line.split())})

        if verbose:
            print("Computing pattern variables")
        if self.trans_rules is None:
            for (k, (vectors, domain)) in enumerate(self.specs):
                patterns = set()
                for pat in self.sft.all_patterns(domain, extra_rad=self.radius):
                    patterns.add(fd.frozendict(pat))

                # create variables for how much is discharged in each direction from each pattern
                i = 0
                for vec in vectors:
                    for fr_pat in patterns:
                        # assert p[(0,0)] == 1
                        # send at most everything away
                        send[fr_pat, vec] = pulp.LpVariable("patvec{},{}".format(k,i)) #, 0, 1)
                        send[fr_pat, vec].setInitialValue(0)
                        i += 1
                        total_vars += 1
                        if verbose and total_vars%print_freq == 0:
                            print("{} found so far".format(total_vars))
        else:
            i = 0
            splits = 0
            for (fr_pat, vecs) in sorted(random.sample(list(self.trans_rules.items()),
                                                       k=len(self.trans_rules)),
                                         key=lambda p:-len(p[0])):
                for vec in vecs:
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
                            if (new_fpat, vec) not in send:
                                send[new_fpat, vec] = pulp.LpVariable("patvec{}".format(i)) #, 0, 1)
                                send[new_fpat, vec].setInitialValue(0)
                                i += 1
                                total_vars += 1
                                if verbose and total_vars%print_freq == 0:
                                    print("{} found so far".format(total_vars))
                    elif (not split) or all(any(fr_pat.get(nvec, None) != sym
                                                for (nvec, sym) in fr_pat2.items())
                                            for (fr_pat2, vec2) in send
                                            if vec2 == vec):
                        # keep original pattern
                        send[fr_pat, vec] = pulp.LpVariable("patvec{}".format(i)) #, 0, 1)
                        send[fr_pat, vec].setInitialValue(0)
                        i += 1
                        total_vars += 1
                        if verbose and total_vars%print_freq == 0:
                            print("{} found so far".format(total_vars))
                        
        specs = dict()
        for (fpat, vec) in send:
            if fpat not in specs:
                specs[fpat] = []
            specs[fpat].append(vec)
        self.update_specs(specs, rules_only=True)

        if verbose:
            print("Done with {} variables, now adding constraints".format(total_vars))

        constr_tim = time.time()
        # list all legal combinations of patterns around origin
        i = 0
        for (orig_nodes, surr) in self.surroundings(rule_pairs=None if self.bound is None else send):
            # for each legal combo, sum the contributions from each -v
            summa = 0
            #print("orig_pat", orig_pat)
            for node in self.sft.nodes:
                summa += self.weights[orig_nodes[node]] / len(self.sft.nodes)
            for (pat, vec, away) in surr:
                try:
                    if away:
                        summa -= send[pat, vec]
                    else:
                        summa += send[pat, vec]
                except KeyError:
                    pass

            prob += summa >= density
            i += 1
            if verbose and i%print_freq == 0:
                print("{} found so far".format(i))

        if save_constr is not None:
            # save bigpats to file
            with open(save_constr + '.output', 'w') as f:
                bigdomain = list(self.bigdomain)
                bigdomain_line = " ".join(" ".join(str(c) for c in vec) + " ." + ".".join(node)
                                          for (vec, node) in bigdomain)
                f.write(bigdomain_line+"\n")
                for bigpat in self.bigpats:
                    bigpat_line = " ".join(bigpat[nvec] for nvec in bigdomain)
                    f.write(bigpat_line+"\n")

        if verbose:
            print("Done with {} constraints in {} seconds, now solving".format(i, time.time()-constr_tim))
        tim = time.time()
        solver, solver_opts = SOLVER_DICTS[solver_str]
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

        self.trans_rules = dict()
        for ((fr_pat, vec), var) in send.items():
            if var.varValue:
                if fr_pat not in self.trans_rules:
                    self.trans_rules[fr_pat] = dict()
                self.trans_rules[fr_pat][vec] = var.varValue

        if self.bound is None:
            self.bound = density.varValue
        self.update_specs()
        return True

    
    def recompute_with_holes(self, solver_str, verbose=False, print_freq=5000, max_larges=None, num_split=None, ordered_split=False, minimize_all=False, sort_pats=True):
        "Recompute the argument using patterns with one node removed, minimizing contributions of large patterns."
        # an upper bound on the total share send by large patterns, which we minimize
        if self.bound is None:
            raise GriddyRuntimeError("Cannot recompute discharging argument with no initial bound.")
        
        total_vars = 0
        total_constr = 0
        all_pairs = dict() # (fpat, vec) : True for large patterns, False for small
        #print("num split", num_split)

        if verbose:
            print("Computing pattern variables")
        i = 0
        num_larges = 0
        for (fpat, vecs) in sorted(random.sample(list(self.trans_rules.items()),
                                                 k=len(self.trans_rules)),
                                   key=(lambda p:-len(p[0])) if sort_pats else (lambda _: 0)):
            for vec in vecs:
                #fpat = fd.frozendict(pat)
                if (fpat, vec) not in all_pairs:
                    i += 1
                    if verbose and i%print_freq == 0:
                        print("{} found so far".format(i))
                if len(fpat) > 1 and (max_larges is None or num_larges < max_larges):
                    #print("n")
                    all_pairs[fpat, vec] = True
                    num_larges += 1
                    if num_split is None:
                        split_nvecs = fpat
                    elif ordered_split:
                        split_nvecs = list(sorted(fpat))[:num_split]
                    else:
                        split_nvecs = random.sample(sorted(fpat), min(num_split, len(fpat)))
                    #print(split_nvecs)
                    for nvec in split_nvecs:
                        #print("k")
                        new_fpat = fpat.delete(nvec)
                        if (new_fpat, vec) not in all_pairs:
                            all_pairs[new_fpat, vec] = minimize_all
                            i += 1
                            if verbose and i%print_freq == 0:
                                print("{} found so far".format(i))
                elif (fpat, vec) not in all_pairs:
                    all_pairs[fpat, vec] = minimize_all

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

        specs = dict()
        for (fpat, vec) in all_pairs:
            if fpat not in specs:
                specs[fpat] = []
            specs[fpat].append(vec)
        self.update_specs(specs, rules_only=True)

        send = dict()
        sum_large = 0

        i = 0
        i_large = 0
        i_small = 0
        for ((fr_pat, vec), large) in all_pairs.items():
            # create variables for how much is discharged in each direction from each pattern
            # for large patterns we split into positive and negative parts
            if large:
                for sign in [True, False]:
                    send[fr_pat, vec, sign] = pulp.LpVariable("patvec{},{},{}".format(i,sign,large), lowBound=0)
                    if vec in self.trans_rules.get(fr_pat, []):
                        send[fr_pat, vec, sign].setInitialValue(max(0, (-1)**(1-sign)*self.trans_rules[fr_pat][vec]))
                    else:
                        send[fr_pat, vec, sign].setInitialValue(0)
                    sum_large += (len(fr_pat) + 1) * send[fr_pat, vec, sign]
                    i += 1
                    i_large += 1
            else:
                send[fr_pat, vec, None] = pulp.LpVariable("patvec{},{},{}".format(i,None,large))
                if fr_pat in self.trans_rules and vec in self.trans_rules[fr_pat]:
                    send[fr_pat, vec, None].setInitialValue(self.trans_rules[fr_pat][vec])
                else:
                    send[fr_pat, vec, None].setInitialValue(0)
                i += 1
                i_small += 1

        if verbose:
            print("Done with {} variables ({} to be minimized, {} free), now adding constraints".format(i, i_large, i_small))
        constr_tim = time.time()

        # we minimize the sum of the absolute values of the charges sent by large patterns
        prob = pulp.LpProblem("discharge_opt", pulp.LpMinimize)
        prob += sum_large
            
        # list all legal combinations of patterns around origin
        i = 0
        for (orig_nodes, surr) in self.surroundings(rule_pairs=[p[:2] for p in send]):
            # for each legal combo, sum the contributions from each -v
            summa = 0
            #print("orig_pat", orig_pat)
            for node in self.sft.nodes:
                summa += self.weights[orig_nodes[node]] / len(self.sft.nodes)
            for (pat, vec, away) in surr:
                if (pat, vec) not in all_pairs:
                    continue
                #print("summing", pat, vec, away)
                if all_pairs[pat, vec]:
                    # large pattern -> has sign
                    if away:
                        summa -= send[pat, vec, True]
                        summa += send[pat, vec, False]
                    else:
                        summa += send[pat, vec, True]
                        summa -= send[pat, vec, False]
                else:
                    # small pattern -> does not have sign
                    if away:
                        summa -= send[pat, vec, None]
                    else:
                        summa += send[pat, vec, None]

            # the resulting charge must be at least the known bound
            constr = summa >= self.bound
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
        solver, solver_opts = SOLVER_DICTS[solver_str]
        solver(**solver_opts).solve(prob)
        #pulp.HiGHS(msg=False, solver="ipx").solve(prob)
        #pulp.GLPK_CMD(msg=False, options=SOLVER_OPTS_RECOMPUTE).solve(prob)
        #pulp.PULP_CBC_CMD(msg=False, warmStart=True).solve(prob)
        if prob.status != 1:
            raise NoSolutionError("Unsolvable linear problem")
        if verbose:
            print("Solved in {} seconds".format(time.time()-tim))
        #print("status after", prob.status)

        # collect results
        self.trans_rules = dict()
        for ((fr_pat, vec, sign), var) in send.items():
            if var.varValue:
                if fr_pat not in self.trans_rules:
                    self.trans_rules[fr_pat] = dict()
                if vec not in self.trans_rules[fr_pat]:
                    self.trans_rules[fr_pat][vec] = 0
                if (sign is None) or sign:
                    self.trans_rules[fr_pat][vec] += var.varValue
                else:
                    self.trans_rules[fr_pat][vec] -= var.varValue
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
