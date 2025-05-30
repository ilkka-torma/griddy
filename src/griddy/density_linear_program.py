"""
Functions for computing lower bounds for density by a discharging argument encoded as a linear program. Uses the Pulp library.
"""

import circuit
from sft import SFT, centered_hypercube
from general import *
import pulp
import frozendict as fd
import time


# given sft, vectors and patterns, enumerate combined locally correct patterns that affect origin
# yield values are dicts : nvec -> pat
# they are shared, i.e. should not be modified by the consumer
def surroundings(the_sft, specs, radius):
    bigdomain = set(nvsub(nvec, vec) for (vecs, domain) in specs for nvec in domain for vec in vecs+[(0,)*the_sft.dim])
    for bigpat in the_sft.all_patterns(bigdomain, extra_rad=radius):
        surr = []
        orig_nodes = {node : bigpat[(0,)*the_sft.dim + (node,)] for node in the_sft.nodes}
        for (vecs, domain) in specs:
            orig_pat = fd.frozendict({nvec : bigpat[nvec] for nvec in domain})
            for vec in vecs:
                # away from origin
                surr.append((orig_pat, vec, True))
                # toward origin
                surr.append((fd.frozendict({nvec : bigpat[nvsub(nvec, vec)] for nvec in domain}), vec, False))
        yield (orig_nodes, surr)

# given sft, vectors along which to share charge, and patterns that guide the sharing, find best provable lower bound
# specs is a list of pairs (vectors, domain)
# vectors is a list of Z^d-vectors that should not contain origin
# domain is a set of nvectors that should contain origin cell
# nodes' weights are averaged together for the purposes of charge sharing
def optimal_density(the_sft, specs, radius, weights=None, ret_shares=False, verbose=False, print_freq=5000):
    if weights is None:
        weights = {a:a for alph in the_sft.alph.values() for a in alph}
    if verbose:
        print("Lower-bounding density using specs {}".format(specs))
    # this is how large density can be made, i.e. what we want to compute
    density = pulp.LpVariable("epsilon",
                              min(weights.values()),
                              max(weights.values()))
    density.setInitialValue(max(weights.values()))

    # we simply try to maximize this density in our problem
    prob = pulp.LpProblem("discharge", pulp.LpMaximize)
    prob += density

    total_vars = 1
    total_constr = 0
    all_pats = set()
    send = {}
    
    for (k, (vectors, domain)) in enumerate(specs):
        if verbose:
            print("Computing pattern variables in spec {}/{}".format(k+1, len(specs)))
        patterns = set()
        i = 0
        for pat in the_sft.all_patterns(domain):
            patterns.add(fd.frozendict(pat))
            i += 1
            if verbose and i%print_freq == 0:
                print("{} found so far".format(i))
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
        total_vars += i
    
    if verbose:
        print("Done with {} variables, now adding constraints".format(total_vars))
    
    # list all legal combinations of patterns around origin
    i = 0
    for (orig_nodes, surr) in surroundings(the_sft, specs, radius):

        # for each legal combo, sum the contributions from each -v
        summa = 0
        #print("orig_pat", orig_pat)
        for node in the_sft.nodes:
            summa += weights[orig_nodes[node]] / len(the_sft.nodes)
        for (pat, vec, away) in surr:
            if away:
                summa -= send[pat, vec]
            else:
                summa += send[pat, vec]

        prob += summa >= density
        i += 1
        if verbose and i%print_freq == 0:
            print("{} found so far".format(i))

    if verbose:
        print("Done with {} constraints, now solving".format(i))
    pulp.PULP_CBC_CMD(msg=False, warmStart=True).solve(prob)

    if ret_shares:
        pat_rules = {fr_pat : dict() for fr_pat in all_pats}
        for ((fr_pat, vec), var) in send.items():
            if var.varValue:
                pat_rules[fr_pat][vec] = var.varValue
        return density.varValue, pat_rules
    else:
        return density.varValue

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
