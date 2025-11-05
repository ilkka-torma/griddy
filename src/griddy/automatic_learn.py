# Learn an automatic configuration from a process that tries to build it locally

from general import *
from angluin import DFALearner
from automatic_conf import AutomaticStructure, AutomaticConf
from sft import Nodes, SFT

def sum_then_lex(nodes, nvec):
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

# Let's quickly implement an N^d lex min learner
# Default order of N^d is by sum then lex
def learn_lex_min(struct, sft, order_succ=None, reset_freq=5):
    if order_succ is None:
        # Use sum then lex
        order_succ = lambda nvec: sum_then_lex(struct.nodes, nvec)

    dim = sft.dim
    pat_alph = list(sft.alph[()])
    #print("got alph", pat_alph, "from", sft.alph)
    nvecs = [(0,)*dim + (list(struct.nodes)[0],)]
    pattern = {nvecs[0] : pat_alph[0]}

    # Extend pattern by one symbol, or backtrack if impossible
    # Return whether it was succesful and list of removed coordinates if not
    def extend():
        new_nvec = order_succ(nvecs[-1])
        for new_sym in pat_alph:
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
        while pattern[nvecs[-1]] == pat_alph[-1]:
            changed.append(nvecs[-1])
            del pattern[nvecs[-1]]
            del nvecs[-1]
        changed.append(nvecs[-1])
        pattern[nvecs[-1]] = pat_alph[pat_alph.index(pattern[nvecs[-1]])+1]
        return False, changed

    learner = DFALearner(struct.alph)
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
        if i%100 == 0:
            print("Pattern size", len(pattern))
            print("Got message", msg, data)
        if msg == "eq":
            #print(data.info_string(verbose=True))
            # If learner gives a configuration of the SFT, we are done
            conf = AutomaticConf(struct, data)
            # Check if we are consistent with the struct language
            lang_dfa = data.map_outputs(lambda c: c is not None)
            eq, witness = lang_dfa.equals(struct.word_dfa, ret_diff=True)
            if not eq:
                #print("found in word dfa")
                (msg, data) = handle.send(("no", tuple(witness)))
                continue
            if conf.is_contained(sft):
                return conf
            if extended:
                n += 1
                if n >= reset_freq:
                    #print("too many failed queries, reset search")
                    n = 0
                    extended = False
                    learner = DFALearner(struct.alph)
                    handle = learner.learn()
                    (msg, data) = next(handle)
                    sent = set()
                    continue
            # Otherwise we have to give a counterexample
            #print("Looking for counterexample")
            # Look for one in the pattern
            for (nvec, sym) in pattern.items():
                if conf[nvec] != sym:
                    #print("Found", vec, "in pattern")
                    (msg, data) = handle.send(("no", struct.vec_to_word(nvec)))
                    break
            else:
                # Now we have to extend the pattern
                #print("not found, extending")
                while True:
                    success, removed = extend()
                    extended = True
                    if success:
                        #print("extended at", vecs[-1], "now size", len(pattern))
                        if conf[nvecs[-1]] != pattern[nvecs[-1]]:
                            (msg, data) = handle.send(("no", struct.vec_to_word(nvecs[-1])))
                            break
                    else:
                        # Backtracked
                        if any(w in sent for w in removed):
                            (msg, data) = handle.send(("backtrack",
                                                       [struct.vec_to_word(nvec) for nvec in removed]))
                            for nvec in removed:
                                sent.discard(nvec)
                            break
        if msg == "eval":
            if not struct.word_dfa.accepts(data):
                #print("word", data, "not in struct language")
                (msg, data) = handle.send(("val", None))
                continue
            nvec = struct.word_to_vec(data)
            #print("finding", vec, "in pattern")
            # Look for the value in the pattern first
            if nvec in pattern:
                #print("found")
                sent.add(nvec)
                (msg, data) = handle.send(("val", pattern[nvec]))
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
                            (msg, data) = handle.send(("val", pattern[nvec]))
                            break
                    else:
                        # Backtracked
                        if any(w in sent for w in removed):
                            (msg, data) = handle.send(("backtrack",
                                                       [struct.vec_to_word(nvec) for nvec in removed]))
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
