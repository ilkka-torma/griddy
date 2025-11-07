# Learn an automatic configuration from a process that tries to build it locally

from general import *
from angluin import DFALearner
from automatic_conf import AutomaticStructure, AutomaticConf
from sft import Nodes, SFT
from finite_automata import NFA

def sum_then_lex(dim, nodes, nvec):
    if nvec is None:
        return (0,)*dim + (list(nodes)[0],)
    if nvec[-1] != list(nodes)[-1]:
        return nvec[:-1] + (list(nodes)[list(nodes).index(nvec[-1])+1],)
    the_sum = sum(nvec[:-1])
    if nvec[0] == the_sum:
        # Max vec of given sum -> min vec of next sum
        return (0,)*(len(nvec)-2) + (the_sum+1, list(nodes)[0])
    else:
        vec = list(nvec[:-1])
        i,c = max((i,c) for (i,c) in enumerate(vec) if c != 0)
        vec[-1] += c-1
        vec[i-1] += 1
        vec[i] -= c
        return tuple(vec) + (list(nodes)[0],)

def max_then_lex(dim, nodes, nvec):
    if nvec is None:
        return (0,)*dim + (list(nodes)[0],)
    nlist = list(nodes)
    if nvec[-1] != nlist[-1]:
        return nvec[:-1] + (nlist[nlist.index(nvec[-1])+1],)
    the_max = max(nvec[:-1])
    if all(n == the_max for n in nvec[:-1]):
        # increase max
        return (0,)*(len(nvec)-2) + (the_max+1, nlist[0])
    vec = list(nvec[:-1])
    while True:
        i = len(vec)-1
        while True:
            vec[i] += 1
            if vec[i] > the_max:
                vec[i] = 0
                i -= 1
            else:
                break
        if the_max in vec:
            break
    return tuple(vec) + (nlist[0],)
        

# Let's quickly implement an N^d lex min learner
# Default order of N^d is by sum then lex
def learn_lex_min(struct, sft, order_succ=None, reset_freq=1):
    if order_succ is None:
        # Use sum then lex
        order_succ2 = lambda nvec: sum_then_lex(struct.dim, struct.nodes, nvec)
    else:
        order_succ2 = lambda nvec: order_succ(struct.dim, struct.nodes, nvec)

    dim = sft.dim
    pat_alph = sft.alph
    #print("got alph", pat_alph, "from", sft.alph)
    nvecs = [None]
    pattern = dict()

    # Extend pattern by one symbol, or backtrack if impossible
    # Return whether it was succesful and list of removed coordinates if not
    def extend():
        new_nvec = order_succ2(nvecs[-1])
        for new_sym in pat_alph[new_nvec[-1]]:
            pattern[new_nvec] = new_sym
            for forb in sft.forbs:
                for f_vec0 in set(nvec[:-1] for nvec in forb):
                    if all(pattern.get(nvadd(f_nvec, vsub(new_nvec[:-1], f_vec0)), None) == sym
                           for (f_nvec, sym) in forb.items()):
                        # Forbidden pattern found, break
                        break
                else:
                    # No forb found, continue
                    continue
                # Forb found, break
                break
            else:
                # No forb found, nice
                nvecs.append(new_nvec)
                return True, None
        # If we are here, no symbol was good -> backtrack
        del pattern[new_nvec]
        changed = []
        while pattern[nvecs[-1]] == pat_alph[nvecs[-1][-1]][-1]:
            changed.append(nvecs[-1])
            del pattern[nvecs[-1]]
            del nvecs[-1]
        changed.append(nvecs[-1])
        #print(pattern)
        #print(nvecs)
        #print(pat_alph)
        sym_list = pat_alph[nvecs[-1][-1]]
        pattern[nvecs[-1]] = sym_list[sym_list.index(pattern[nvecs[-1]])+1]
        return False, changed

    learner = DFALearner(struct.alph + list(struct.nodes))
    handle = learner.learn()
    (msg, data) = next(handle)
    sent = set()

    # Learning process loop
    n = 0
    i = 0
    extended = False
    print("Entering learning loop")
    while True:
        i += 1
        if False and i%1 == 0:
            print("Pattern size", len(pattern))
            print("Got message", msg, data)
        if msg == "eq":
            #print(data.info_string(verbose=True))
            # If learner gives a configuration of the SFT, we are done
            conf = AutomaticConf(struct, data)
            # Check if we are consistent with the struct language
            lang_dfa = data.map_outputs(lambda c: c is not None)
            struct_dfa = struct.word_dfa.extend_alph(struct.nodes).concat(NFA.one_of(struct.alph + list(struct.nodes), list(struct.nodes))).determinize()
            eq, witness = lang_dfa.equals(struct_dfa, ret_diff=True)
            if not eq:
                #print("found in word dfa")
                (msg, data) = handle.send(("no", tuple(witness), None))
                continue
            if conf.is_contained(sft):
                print("Success, pattern size", len(pattern))
                return conf
            if extended:
                n += 1
                if False and n >= reset_freq:
                    #print("too many failed queries, reset search")
                    n = 0
                    extended = False
                    learner = DFALearner(struct.alph + list(struct.nodes))
                    handle = learner.learn()
                    (msg, data) = next(handle)
                    sent = set()
                    continue
            # Otherwise we have to give a counterexample
            #print("Looking for counterexample")
            # Look for one in the pattern
            for (nvec, sym) in sorted(pattern.items(), key=lambda p: max(p[0][:-1])):
                if conf[nvec] != sym:
                    #print("Found", vec, "in pattern")
                    (msg, data) = handle.send(("no", struct.vec_to_word(nvec[:-1]) + (nvec[-1],), None))
                    break
            else:
                # Now we have to extend the pattern
                #print("not found, extending")
                while True:
                    success, removed = extend()
                    extended = True
                    if success:
                        #print("extended at", nvecs[-1], "now size", len(pattern))
                        if conf[nvecs[-1]] != pattern[nvecs[-1]]:
                            nvec = nvecs[-1]
                            (msg, data) = handle.send(("no", struct.vec_to_word(nvec[:-1]) + (nvec[-1],), None))
                            break
                    else:
                        # Backtracked
                        if any(w in sent for w in removed):
                            (msg, data) = handle.send(("backtrack",
                                                       [struct.vec_to_word(nvec[:-1])+(nvec[-1],) for nvec in removed],
                                                       None))
                            for nvec in removed:
                                sent.discard(nvec)
                            break
        if msg == "eval":
            if not (data and data[-1] in struct.nodes and\
                    all(c not in struct.nodes for c in data[:-1]) and\
                    struct.word_dfa.accepts(data[:-1])):
                (msg, data) = handle.send(("val", None, data))
                continue
            nvec = struct.word_to_vec(data[:-1]) + (data[-1],)
            #print("finding", nvec, "in pattern")
            # Look for the value in the pattern first
            if nvec in pattern:
                #print("found")
                sent.add(nvec)
                (msg, data) = handle.send(("val", pattern[nvec], nvec))
            else:
                # Now we have to extend the pattern
                j = 0
                while True:
                    j += 1
                    #print("not found, extending")
                    success, removed = extend()
                    extended = True
                    if success:
                        #if j%10000 == 0:
                        #    print("extended at", vecs[-1], "to size", len(pattern))
                        #1/0
                        if nvec == nvecs[-1]:
                            sent.add(nvec)
                            (msg, data) = handle.send(("val", pattern[nvec], nvec))
                            break
                    else:
                        # Backtracked
                        if any(w in sent for w in removed):
                            (msg, data) = handle.send(("backtrack",
                                                       [struct.vec_to_word(nvec[:-1])+(nvec[-1],) for nvec in removed],
                                                       None))
                            for nvec in removed:
                                sent.discard(nvec)
                            break

def test():
    # Test this on an N^2 SFT
    dim = 2
    nodes = Nodes()
    alph = {() : ['0', '1']}
    # Grid topology
    top = [("up", (0,0,()), (0,1,())),
           ("dn", (0,0,()), (0,-1,())),
           ("rt", (0,0,()), (1,0,())),
           ("lt", (0,0,()), (-1,0,()))]
    forbs = [{(0,0,()):'0', (0,1,()):'0', (1,0,()):'0'},
             {(0,0,()):'1', (0,1,()):'0', (1,0,()):'0', (1,1,()):'0'}]
    the_sft = SFT(dim, nodes, alph, top, forbs=forbs, onesided=[0,1])
    struct = AutomaticStructure.n_ary(2, 2, nodes)
    print("Learning configuration...")
    conf = learn_lex_min(struct, the_sft, reset_freq=3)
    print("Learning process finished")
    print(conf.info_string(verbose=True))

if __name__ == "__main__":
    test()
