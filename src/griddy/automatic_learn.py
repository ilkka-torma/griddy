# Learn an automatic configuration from a process that tries to build it locally

from general import *
from angluin import DFALearner
from automatic_conf import AutomaticStructure, AutomaticConf
from sft import Nodes, SFT

def sum_then_lex(vec):
    the_sum = sum(vec)
    if vec[0] == the_sum:
        # Max vec of given sum -> min vec of next sum
        return (0,)*(len(vec)-1) + (the_sum+1,)
    else:
        vec = list(vec)
        i,c = max((i,c) for (i,c) in enumerate(vec) if c != 0)
        vec[-1] += c-1
        vec[i-1] += 1
        vec[i] -= c
        return tuple(vec)

# Let's quickly implement an N^d lex min learner
# Default order of N^d is by sum then lex
def learn_lex_min(struct, sft, order_succ=None, reset_freq=1000):
    if order_succ is None:
        # Use sum then lex
        order_succ = sum_then_lex

    dim = sft.dim
    pat_alph = list(sft.alph[()])
    print("got alph", pat_alph, "from", sft.alph)
    vecs = [(0,)*dim]
    pattern = {(0,)*dim : pat_alph[0]}

    # Extend pattern by one symbol, or backtrack if impossible
    # Return whether it was succesful and list of removed coordinates if not
    def extend():
        new_vec = order_succ(vecs[-1])
        for new_sym in pat_alph:
            pattern[new_vec] = new_sym
            for forb in sft.forbs:
                for f_vec0 in forb:
                    if all(pattern.get(vadd(vsub(new_vec, f_vec0), f_vec), None) == sym
                           for (f_vec, sym) in forb.items()):
                        # Forbidden pattern found, break
                        break
                else:
                    # No forb found, continue
                    continue
                # Forb found, break
                break
            else:
                # No forb found, nice
                vecs.append(new_vec)
                return True, None
        # If we are here, no symbol was good -> backtrack
        del pattern[new_vec]
        changed = []
        while pattern[vecs[-1]] == pat_alph[-1]:
            changed.append(vecs[-1])
            del pattern[vecs[-1]]
            del vecs[-1]
        changed.append(vecs[-1])
        pattern[vecs[-1]] = pat_alph[pat_alph.index(pattern[vecs[-1]])+1]
        return False, changed

    learner = DFALearner(struct.alph)
    handle = learner.learn()
    (msg, data) = next(handle)
    sent = set()

    # Learning process loop
    n = 0
    i = 0
    extended = False
    while True:
        i += 1
        if i%100 == 0:
            print("Pattern size", len(pattern))
            print("Got message", msg, data)
        if msg == "eq":
            print(data.info_string(verbose=True))
            # If learner gives a configuration of the SFT, we are done
            conf = AutomaticConf(struct, data)
            if conf.is_contained(sft):
                return conf
            n += 1
            if extended and n >= reset_freq:
                print("too many failed queries, reset search")
                n = 0
                extended = False
                learner = DFALearner(struct.alph)
                handle = learner.learn()
                (msg, data) = next(handle)
                sent = set()
                continue
            # Otherwise we have to give a counterexample
            print("Looking for counterexample")
            # Look for one outside the struct language
            lang_dfa = data.map_outputs(lambda c: c is not None)
            eq, witness = lang_dfa.equals(struct.word_dfa, ret_diff=True)
            if not eq:
                print("found in word dfa")
                (msg, data) = handle.send(("no", tuple(witness)))
                continue
            # Look for one in the pattern
            for (vec, sym) in pattern.items():
                if conf[vec] != sym:
                    print("Found", vec, "in pattern")
                    (msg, data) = handle.send(("no", struct.vec_to_word(vec)))
                    break
            else:
                # Now we have to extend the pattern
                print("not found, extending")
                while True:
                    success, removed = extend()
                    extended = True
                    if success:
                        #print("extended at", vecs[-1], "now size", len(pattern))
                        if conf[vecs[-1]] != pattern[vecs[-1]]:
                            (msg, data) = handle.send(("no", struct.vec_to_word(vecs[-1])))
                            break
                    else:
                        # Backtracked
                        if any(w in sent for w in removed):
                            (msg, data) = handle.send(("backtrack",
                                                       [struct.vec_to_word(vec) for vec in removed]))
                            for vec in removed:
                                sent.discard(vec)
                            break
        if msg == "eval":
            if not struct.word_dfa.accepts(data):
                print("word", data, "not in struct language")
                (msg, data) = handle.send(("val", None))
                continue
            vec = struct.word_to_vec(data)
            #print("finding", vec, "in pattern")
            # Look for the value in the pattern first
            if vec in pattern:
                #print("found")
                sent.add(vec)
                (msg, data) = handle.send(("val", pattern[vec]))
            else:
                # Now we have to extend the pattern
                j = 0
                while True:
                    j += 1
                    #print("not found, extending")
                    success, removed = extend()
                    extended = True
                    if success:
                        if j%10000 == 0:
                            print("extended at", vecs[-1], "to size", len(pattern))
                        #1/0
                        if vec == vecs[-1]:
                            sent.add(vec)
                            (msg, data) = handle.send(("val", pattern[vec]))
                            break
                    else:
                        # Backtracked
                        if any(w in sent for w in removed):
                            (msg, data) = handle.send(("backtrack",
                                                       [struct.vec_to_word(vec) for vec in removed]))
                            for vec in removed:
                                sent.discard(vec)
                            break

def test():
    # Test this on an N^2 SFT
    dim = 2
    alph = {() : ['0', '1']}
    # Grid topology
    top = [("up", (0,0,()), (0,1,())),
           ("dn", (0,0,()), (0,-1,())),
           ("rt", (0,0,()), (1,0,())),
           ("lt", (0,0,()), (-1,0,()))]
    forbs = [{(0,0,()):'1', (0,1,()):'1', (1,0,()):'1'},
             {(0,0,()):'1', (0,1,()):'0', (1,0,()):'0', (1,1,()):'0'},
             {(0,0,()):'0', (0,1,()):'0', (1,0,()):'0', (1,1,()):'0'}]
    the_sft = SFT(dim, Nodes(), alph, top, forbs=forbs, onesided=[0,1])
    struct = AutomaticStructure.n_ary(2, 2)
    conf = learn_lex_min(struct, the_sft, reset_freq=3)
    print("learning process finished")
    print(conf.info_string(verbose=True))

if __name__ == "__main__":
    test()
