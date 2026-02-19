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

SOLVER_OPTS_INITIAL = ["--primal", "--xcheck"]
SOLVER_OPTS_RECOMPUTE = ["--dual", "--xcheck"]

# TODO: re-allow saving and loading bigpats

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

    # enumerate combined locally correct patterns that affect origin
    def surroundings(self, bigpat=None, ret_big=False):
        #print(specs, "speculature")
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
        for (orig_nodes, surr, bigpat) in self.surroundings(ret_big=True, bigpat=bigpat):
            # for each legal combo, sum the contributions from each -v
            if isinstance(self.bound, Fraction):
                summa = Fraction(0)
                for node in self.sft.nodes:
                    summa += Fraction(self.weights[orig_nodes[node]], len(self.sft.nodes))
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
                summa += 0.00001
            if summa < self.bound:
                if give_reason:
                    return False, (bigpat,
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
                return True, (bigpat,
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

    def rationalize(self, denom_bound):
        "Attempt to convert into rational numbers. Return whether it was succesful."
        old_bound = self.bound
        self.bound = Fraction(self.bound).limit_denominator(denom_bound)
        old_rules = self.trans_rules
        self.trans_rules = {fpat : {vec : Fraction(num).limit_denominator(denom_bound)
                                    for (vec, num) in vecs.items()}
                            for (fpat, vecs) in self.trans_rules.items()}
        if self.is_valid():
            return True
        else:
            self.bound = old_bound
            self.trans_rules = old_rules
            return False

    def update_specs(self, trans_rules=None):
        "Update specs to match the current or given transition rules."
        if trans_rules is None:
            trans_rules = self.trans_rules
        domain_vecs = dict()
        for (fpat, vecs) in trans_rules.items():
            fset = frozenset(fpat)
            if fset not in domain_vecs:
                domain_vecs[fset] = set()
            domain_vecs[fset] |= set(vecs)
        self.specs = [(list(v),list(d)) for (d,v) in domain_vecs.items()]
        bigdomain = set(nvsub(nvec, vec) for (vecs, domain) in self.specs for nvec in domain for vec in vecs+[(0,)*self.sft.dim]) | {((0,)*self.sft.dim, node) for node in self.sft.nodes}
        if bigdomain != self.bigdomain:
            self.bigdomain = bigdomain
            self.bigpats = set(fd.frozendict({nvec : bigpat[nvec]
                                              for nvec in bigdomain})
                               for bigpat in self.bigpats)

    def compute_bound(self, verbose=False, print_freq=5000, save_constr=None, load_constr=None):
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
        all_pats = set()
        send = {}

        if load_constr is not None:
            # load bigpats from a file
            bigdomain = []
            bigpats = []
            with open(load_constr + '.output', 'r') as f:
                strs = f.readline().split()
                nvec_len = self.sft.dim+1
                for coords in [strs[i*nvec_len:(i+1)*nvec_len] for i in range(len(strs)//nvec_len)]:
                    #print("got coords", coords, coords[-1][1:].split('.'))
                    bigdomain.append((tuple(int(c) for c in coords[:-1]),
                                      tuple(coords[-1][1:].split('.')[1:])))
                #print("bigdomain", bigdomain)
                for line in f.readlines():
                    if line:
                        bigpats.append({nvec : sym for (nvec, sym) in zip(bigdomain, line.split())})
            self.bigdomain = bigdomain
            self.bigpats = bigpats
                    

        for (k, (vectors, domain)) in enumerate(self.specs):
            if verbose:
                print("Computing pattern variables in spec {}/{}".format(k+1, len(self.specs)))
            patterns = set()
            for pat in self.sft.all_patterns(domain):
                patterns.add(fd.frozendict(pat))
                all_pats |= patterns

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
                    

        if verbose:
            print("Done with {} variables, now adding constraints".format(total_vars))

        # list all legal combinations of patterns around origin
        i = 0
        for (orig_nodes, surr) in self.surroundings():
            # for each legal combo, sum the contributions from each -v
            summa = 0
            #print("orig_pat", orig_pat)
            for node in self.sft.nodes:
                summa += self.weights[orig_nodes[node]] / len(self.sft.nodes)
            for (pat, vec, away) in surr:
                if away:
                    summa -= send[pat, vec]
                else:
                    summa += send[pat, vec]

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
            print("Done with {} constraints, now solving".format(i))
        tim = time.time()
        pulp.GLPK_CMD(msg=False, options=SOLVER_OPTS_INITIAL).solve(prob)
        if verbose:
            print("Solved in {} seconds".format(time.time()-tim))

        self.trans_rules = {fr_pat : dict() for fr_pat in all_pats}
        for ((fr_pat, vec), var) in send.items():
            if var.varValue:
                self.trans_rules[fr_pat][vec] = var.varValue

        self.bound = density.varValue
        self.update_specs()

    
    def recompute_with_holes(self, verbose=False, print_freq=5000, max_larges=None, num_split=None):
        "Recompute the argument using patterns with one node removed, minimizing contributions of large patterns."
        # an upper bound on the total share send by large patterns, which we minimize
        if self.bound is None:
            raise GriddyRuntimeError("Cannot recompute discharging argument with no initial bound.")
        
        total_vars = 0
        total_constr = 0
        all_pats = dict() # vecs plus True for large patterns, False for small

        if verbose:
            print("Computing pattern variables")
        i = 0
        num_larges = 0
        for (fpat, vecs) in sorted(self.trans_rules.items(), key=lambda p:-len(p[0])):
            #fpat = fd.frozendict(pat)
            if fpat not in all_pats:
                i += 1
                if verbose and i%print_freq == 0:
                    print("{} found so far".format(i))
            if (max_larges is None) or (num_larges < max_larges):
                if fpat in all_pats:
                    all_pats[fpat] = (set(vecs) | set(all_pats[fpat][0]), True)
                else:
                    all_pats[fpat] = (vecs, True)
                num_larges += 1
                if num_split is None:
                    split_nvecs = fpat
                else:
                    split_nvecs = random.sample(sorted(fpat), min(num_split, len(fpat)))
                for nvec in split_nvecs:
                    new_fpat = fpat.delete(nvec)
                    if new_fpat in all_pats:
                        all_pats[fpat] = (set(vecs) | set(all_pats[fpat][0]), all_pats[fpat][1])
                    else:
                        all_pats[new_fpat] = (vecs, False)
                        i += 1
                        if verbose and i%print_freq == 0:
                            print("{} found so far".format(i))
            elif fpat in all_pats:
                all_pats[fpat] = (set(vecs) | set(all_pats[fpat][0]), all_pats[fpat][1])
            else:
                all_pats[fpat] = (vecs, False)

        for (fpat, vecs) in self.trans_rules.items():
            if fpat not in all_pats:
                print("not in all_pats")
                1/0
            patvecs = all_pats[fpat][0]
            for vec in vecs:
                if vec not in patvecs:
                    print("not in patvecs", fpat, vecs, vec, patvecs)
                    1/0

        assert all(fpat in all_pats
                   and all(vec in all_pats[fpat][0] for vec in vecs)
                   for (fpat, vecs) in self.trans_rules.items())

        self.update_specs({fpat : vecs for (fpat, (vecs, _)) in all_pats.items()})

        send = dict()
        sum_large = 0

        i = 0
        i_large = 0
        i_small = 0
        for (fr_pat, (vecs, large)) in all_pats.items():
            # create variables for how much is discharged in each direction from each pattern
            # for large patterns we split into positive and negative parts
            for vec in vecs:
                if large:
                    for sign in [True, False]:
                        send[fr_pat, vec, sign] = pulp.LpVariable("patvec{},{},{}".format(i,sign,large), lowBound=0)
                        sum_large += send[fr_pat, vec, sign]
                        i += 1
                        i_large += 1
                else:
                    send[fr_pat, vec, None] = pulp.LpVariable("patvec{},{},{}".format(i,sign,large))
                    i += 1
                    i_small += 1

        if verbose:
            print("Done with {} variables ({} to be minimized, {} free), now adding constraints".format(i, i_large, i_small))

        # we minimize the sum of the absolute values of the charges sent by large patterns
        prob = pulp.LpProblem("discharge_opt", pulp.LpMinimize)
        prob += sum_large
            
        # list all legal combinations of patterns around origin
        i = 0
        for (orig_nodes, surr) in self.surroundings():
            # for each legal combo, sum the contributions from each -v
            summa = 0
            #print("orig_pat", orig_pat)
            for node in self.sft.nodes:
                summa += self.weights[orig_nodes[node]] / len(self.sft.nodes)
            for (pat, vec, away) in surr:
                if pat not in all_pats or vec not in all_pats[pat][0]:
                    continue
                #print("summing", pat, vec, away)
                if all_pats[pat][1]:
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
            print("Done with {} constraints, now solving".format(i))
        
        #print("status before", prob.status)
        tim = time.time()
        pulp.GLPK_CMD(msg=False, options=SOLVER_OPTS_RECOMPUTE).solve(prob)
        if prob.status != 1:
            raise GriddyRuntimeError("Unsolvable linear problem")
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
