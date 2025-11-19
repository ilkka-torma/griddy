import sofic1d
import blockmap
import griddy

import circuit
from general import *

# start from initial states and function
# final states
def automaton_from_function(initials, alphabet, transition_rule, final_state_rule = None):
    transitions = {}
    seen = set(initials)
    frontier = list(initials)
    if final_state_rule:
        final_states = set([i for i in initials if final_state_rule(i)])
    else:
        final_states = None
    while frontier:
        #print(frontier)
        newfrontier = []
        for f in frontier:
            for a in alphabet:
                #print("try", f, a)
                for t in transition_rule(f, a):
                    #print("trans", t)
                    if (f, a) not in transitions:
                        transitions[(f, a)] = set()
                    transitions[(f, a)].add(t)
                    if t in seen:
                        continue
                    if final_state_rule:
                        final_states.add(t)
                    newfrontier.append(t)
                    seen.add(t)
        frontier = newfrontier

    if final_state_rule:
        return seen, transitions, alphabet, final_states
    else:
        return seen, transitions, alphabet

"""
Given the local rule of a block map, and its radius on the right,
(so nbhd is the interval [0, radius])
and a representation of sofic shift as edge-labeled graph,
compute such representation for image.

Sofic shift is a tuple (nodes, edges, alphabet),
and edges is a dict (a, l) -> [b] where a, b are nodes,
and l is a label from alphabet.

Our states will remember a word of length at most r,
(a suffix of the word which has been read so far),
and the current node after reading said word.

Actually, this allows initially writing whatever, and we should
only take the limit set.
"""
def compute_image(local_rule, sofic):
    #print(local_rule)
    #print(sofic)
    radius, image_alphabet, local_rule = local_rule
    nodes, edges, alphabet = sofic
    initials = set([((), n) for n in nodes])
    def transition_rule(node, sym):
        # node is word read so far, and the state of original sofic
        word, fromnode = node
        for presym in alphabet:
            wordd = word[:]
            wordd += (presym,)
            if len(wordd) == radius + 1:
                if local_rule(wordd) != sym:
                    continue    
            if (fromnode, presym) not in edges:
                continue
            if len(wordd) > radius:
                wordd = wordd[1:]
            for tonode in edges[(fromnode, presym)]:
                yield (wordd, tonode)
    return automaton_from_function(initials, image_alphabet, transition_rule)

# only take edges involving given nodes
def edge_restrict(edges, nodes):
    ret_edges = {}
    for e in edges:
        if e[0] not in nodes:
            continue
        val = set()
        for c in edges[e]:
            if c in nodes:
                val.add(c)
        ret_edges[e] = val
    return ret_edges

# remove unreachable states and co-unreachable states
# dumb n^2 algorithm
def essentify(sofic):
    return right_essentify(left_essentify(sofic))

def left_essentify(sofic):
    return flip(right_essentify(flip(sofic)))

# Duplication of this in many places.
def flip(sofic):
    nodes, edges, alphabet = sofic
    redges = {}
    for e in edges:
        node, sym = e
        for n in edges[e]:
            if (n, sym) not in redges:
                redges[n, sym] = set()
            redges[n, sym].add(node)
    return nodes, redges, alphabet

def right_essentify(sofic):
    nodes, edges, alphabet = sofic
    #print(nodes)
    while True:
        next_nodes = []
        for c in nodes:
            for a in alphabet:
                if (c, a) in edges:
                    break
            else: # no edge from c
                continue
            next_nodes.append(c)
        if len(next_nodes) == len(nodes):
            break
        nodes = next_nodes
    return nodes, edge_restrict(edges, nodes), alphabet
            
def XOR(l): return (l[0] + l[1]) % 2

# given block map and sofic, give another sofic
def sofic_from_BM_and_sofic(BM, sofic):
    assert BM.from_topology == sofic.topology
    assert BM.from_nodes == sofic.nodes
    assert BM.from_alphabet == sofic.alph
    assert BM.dimension == 1

    #print("BM", sofic.trans) 
    # sofic is a Sofic1D object, convert to (nodes, edges, alphabet)
    states = [n for n in sofic.states]
    # print(nodes, "blump")
    # we optimize transition table in Sofic1D when right-resolving
    # and have to undo that here
    edges = sofic.trans
    if sofic.right_resolving:
        for statesym in sofic.trans:
            sofic.trans[statesym] = set([sofic.trans[statesym]])
    #print(edges, "gilly")
    alphabet = list(sofic.trans_alph)
    tuple_sofic = states, edges, alphabet
    #print("esme", tuple_sofic)

    # then from 1D block map we need (radius, image_alphabet, local rule)
    # get neighborhood as vectors \subset \Z^d
    nbhd = BM.get_neighborhood(only_cells = True)
    #print(nbhd, "flaka")
    # of course actually d = 1, so we get length-1 vectors
    nbhd = [n[0] for n in nbhd]
    nbhd_min, nbhd_max = min(nbhd), max(nbhd)
    #print(nbhd_min, nbhd_max)
    radius = nbhd_max - nbhd_min # list(range(, +1)) # make contiguous
    # alphabet is just the image alphabet, use a product
    image_alphabet = list(iter_prod(*(iter(BM.to_alphabet[node])
                                  for node in BM.to_nodes)))

    # given a word of length radius + 1, evaluate the BlockMap circuit(s)
    def local_rule(w):
        #print("evaling", w)
        # convert to pattern (= truth values for variables)
        pattern = {}
        for v in nbhd:
            for n_idx, n in enumerate(BM.from_nodes):
                #print("an node", n_idx, n)
                for s in BM.from_alphabet[n]:
                    # note that n is a number, not a vector of len 1
                    if w[v + nbhd_min][n_idx] == s:
                        pattern[(v,), n, s] = True
                    else:
                        pattern[(v,), n, s] = False
        #print(pattern)
        # now evaluate circuits
        result = []
        for n in BM.to_nodes:
            for a in BM.to_alphabet[n]:
                circ = BM.circuits[n, a].copy()
                if circuit.evaluate(circ, pattern):
                    result.append(a)
                    break
            else:
                raise Exception("Bug: BlockMap circuits do not cover all cases!")
        #print(result)
        return tuple(result)

    # compute the image as (seen_nodes, transitions, image_alphabet)
    # note that even in the one-sided case, our sofics are always surjective!
    image = compute_image((radius, image_alphabet, local_rule),
                          tuple_sofic)
    image = essentify(image)

    s = sofic1d.Sofic1D(BM.to_nodes, BM.to_alphabet,
                        BM.to_topology, image[1],
                        right_resolving=False,
                        onesided=sofic.onesided,
                        debug=False)
    #print("result of is ", s.trans)
    return s









