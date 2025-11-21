# Learn an automatic configuration from a process that tries to build it locally

from general import *
from angluin import DFALearner, infer_dfa
from automatic_conf import AutomaticStructure, AutomaticConf
from sft import Nodes, SFT, add_uniqueness_constraints
from finite_automata import DFA, NFA
from circuit import AND, solver_process, transform
from frozendict import frozendict

class PatternBuilder:
    "Abstract pattern builder class"

    def __init__(self, sft):
        self.sft = sft

class LexMinBuilder(PatternBuilder):
    "Build a lexicographically minimal pattern"

    def __init__(self, sft, extra_rad=0):
        super().__init__(sft)

        self.pattern = dict()
        self.nvecs = [None]
        
        # Construct SAT instance
        circuits = []
        nvecs = set()
        #print("radii", self.sft.radii(twosided=True))
        for vec in hyperrect([(-b,-a+extra_rad) for (a,b) in self.sft.radii(twosided=True)]):
            circ = sft.circuit.copy()
            transform(circ, lambda var: nvadd(var[:-1], vec) + var[-1:])
            circuits.append(circ)
            for var in circ.get_variables():
                nvecs.add(var[:-1])
        add_uniqueness_constraints(self.sft.alph, circuits, nvecs)
        #print("circuits", circuits)
        self.circuit = AND(*circuits)
        self.circuit_nvecs = list(set(var[:-1] for var in self.circuit.get_variables()))
        self.circuit_vecs = list(set(nvec[:-1] for nvec in self.circuit_nvecs))
        self.circuit_radii = [(min(vec[i] for vec in self.circuit_vecs),
                               max(vec[i] for vec in self.circuit_vecs))
                              for i in range(sft.dim)]
        self.solver = solver_process(self.circuit, ret_assignment=False)
        _ = next(self.solver)

    def extend(self):
        "Extend by a single node vector, or backtrack"
        #print("extend", self.nvecs, self.pattern)
        last_nvec = self.nvecs[-1]
        assert (last_nvec is None) or (last_nvec in self.pattern)
        next_nvec = max_then_lex(self.sft.dim, self.sft.nodes, last_nvec)
        #print("next_nvec", next_nvec)
        assert next_nvec not in self.pattern
        success = self._try_extend(next_nvec, self.sft.alph[next_nvec[-1]])
        if success:
            assert next_nvec in self.pattern
            return (True, next_nvec)
        else:
            # Backtrack
            changed = []
            del self.nvecs[-1]
            while last_nvec is not None:
                #print("backtrack", last_nvec, self.pattern)
                changed.append(last_nvec)
                sym = self.pattern[last_nvec]
                del self.pattern[last_nvec]
                syms = self.sft.alph[last_nvec[-1]]
                greater_syms = syms[syms.index(sym)+1:]
                success = self._try_extend(last_nvec, greater_syms)
                if success:
                    break
                else:
                    last_nvec = self.nvecs.pop(-1)
            return (False, changed)

    def _try_extend(self, nvec, syms):
        #if len(self.pattern) < 6:
        #print("trying to extend", self.pattern, "at", nvec, "using", syms)
        # Return True if succeeded, False if failed
        if syms:
            # Bisecting search for the value
            left, right = syms[:len(syms)//2], syms[len(syms)//2:]
            #print("bisecting", left, right)
            sym = right[0]
            
            tr_vec = [max(nvec[i], -self.circuit_radii[i][0])
                      for i in range(self.sft.dim)]
            #if len(self.pattern) < 6:
            #print("tr_vec", tr_vec)
            solver_values = {}
            for circ_nvec in self.circuit_nvecs:
                node = circ_nvec[-1]
                pat_nvec = nvadd(circ_nvec, tr_vec)
                #print("circ_nvec", circ_nvec, "pat_nvec", pat_nvec)
                if pat_nvec in self.pattern:
                    pat_sym = self.pattern[pat_nvec]
                    #print("in pattern", pat_sym)
                    for the_sym in self.sft.alph[node][1:]:
                        solver_values[circ_nvec + (the_sym,)] = pat_sym == the_sym
                elif pat_nvec == nvec:
                    #print("is nvec", sym)
                    for the_sym in self.sft.alph[node][1:]:
                        solver_values[circ_nvec + (the_sym,)] = sym == the_sym

            #if len(self.pattern) < 6:
            #print("sent values", {a[:-1] : a[-1] for (a,b) in solver_values.items() if b})
            is_sat = self.solver.send(solver_values)
            #print("is_sat", is_sat)
            if is_sat:
                # See if we can find a smaller symbol
                if not self._try_extend(nvec, left):
                    # Actually extend
                    self.nvecs.append(nvec)
                    self.pattern[nvec] = sym
                return True
            elif self._try_extend(nvec, left):
                return True
            else:
                return self._try_extend(nvec, right[1:])
        # If we are here, then there are no extensions
        return False
        

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
    # first maximum, then lex
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
    # now we have some position not max
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

def learn_lex_min_gold(struct, sft, builder, buffer_rad=0, verbose=False, print_freq=1000):

    alph = struct.alph + list(struct.nodes)
    words_list = []
    nvecs_list = []
    #struct_dfa = struct.word_dfa.extend_alph(struct.nodes).concat(NFA.one_of(alph, list(struct.nodes))).determinize().minimize()
    old_pattern = dict()
    
    while True:
        n = len(words_list)
        new_words = list(words(n, struct.alph))
        words_list.append(new_words)
        new_nvecs = set(vadd(struct.word_to_vec(word), vec) + (node,)
                        for word in new_words
                        for vec in hyperrect([(0,buffer_rad+1)]*struct.dim)
                        for node in struct.nodes)
        nvecs_list.append(new_nvecs)
        #print("words_list", words_list)

        if verbose:
            print("Extending to cover words of length", n)
        i = 0
        while any(nvec not in builder.pattern for nvec in new_nvecs):
            builder.extend()
            i += 1
            if verbose and i%print_freq == 0:
                print("  Round {}: Extended to size {}".format(i, len(builder.pattern)))

        if verbose:
            print("Extended to size {}, now building DFAs".format(len(builder.pattern)))

        min_changed = len(nvecs_list)
        for (k, nvecs) in list(enumerate(nvecs_list[:-1]))[::-1]:
            if any(old_pattern[nvec] != builder.pattern[nvec]
                   for nvec in nvecs):
                min_changed = k
        #print("min_changed", min_changed)

        old_pattern = builder.pattern.copy()
            
        for k in range(min_changed, len(words_list)+1):
            word_outputs = {word :
                            frozendict({node : builder.pattern[struct.word_to_vec(word) + (node,)]
                                        for node in struct.nodes})
                            for words in words_list[:k]
                            for word in words}

            dfa = infer_dfa(struct.alph, word_outputs)
            #trans = dict()
            #outputs = {None : None}
            #for st in tuple_dfa.states:
            #    outputs[st, None] = None
            #    for sym in struct.alph:
            #        # simulate tuple dfa
            #        trans[(st, None), sym] = (tuple_dfa(st, sym), None)
            #        for node in struct.nodes:
            #            # go to sink
            #            trans[(st, node), sym] = None
            #        trans[None, sym] = None
            #    for node in struct.nodes:
            #        # go to node state
            #        trans[(st, None), node] = (st, node)
            #        for node2 in struct.nodes:
            #            trans[(st, node2), node] = None
            #        trans[None, node] = None
            #        outputs[st, node] = tuple_dfa.outputs[st][node]
            #dfa = DFA(alph, trans, (tuple_dfa.init, None), outputs=outputs).minimize()
            if verbose:
                print("Built DFA with", len(dfa.states), "states")
            #lang_dfa = dfa.map_outputs(lambda c: c is not None)
            #if not lang_dfa.equals(struct_dfa):
            #    continue
            conf = AutomaticConf(struct, dfa)
            if sft.__contains__(conf, verbose=verbose):
                print("Done, needed pattern of size", len(builder.pattern))
                return conf
        

# Let's quickly implement an N^d lex min learner
# Default order of N^d is by sum then lex
def learn_lex_min_angluin(struct, sft, builder, verbose=False, print_freq=1000):

    dim = sft.dim
    pat_alph = sft.alph

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
        if verbose and i%print_freq == 0:
            print("Learning round", i)
            print("  Pattern size:", len(builder.pattern))
            print("  Queries: {} eval ({} in main branch), {} eq ({} in main branch)".\
                  format(learner.total_eval_count, learner.eval_count, learner.total_eq_count, learner.eq_count))
            print("  Last query:", msg, data)
        if msg == "eq":
            #print(data.info_string(verbose=True))
            # Check if we are consistent with the struct language
            lang_dfa = data.map_outputs(lambda c: c is not None)
            eq, witness = lang_dfa.equals(struct.word_dfa, ret_diff=True)
            if not eq:
                #print(lang_dfa.info_string(verbose=True))
                #print(struct.word_dfa.info_string(verbose=True))
                #print("found in word dfa", witness)
                (msg, data) = handle.send(("no", tuple(witness), None))
                continue
            # If learner gives a configuration of the SFT, we are done
            conf = AutomaticConf(struct, data)
            if sft.__contains__(conf, verbose=verbose):
                if verbose:
                    print("Success on round", i)
                    print("  Pattern size:", len(builder.pattern))
                    print("  Queries: {} eval ({} in main branch), {} eq ({} in main branch)".\
                          format(learner.total_eval_count, learner.eval_count, learner.total_eq_count, learner.eq_count))
                return conf
            # Otherwise we have to give a counterexample
            #print("Looking for counterexample")
            # Look for one in the pattern
            for (nvec, sym) in sorted(builder.pattern.items(), key=lambda p: max(p[0][:-1])):
                if conf[nvec] != sym:
                    #print("Found", nvec, sym, "in pattern", conf[nvec], "in conf")
                    #print("Word", struct.vec_to_word(nvec[:-1]) + (nvec[-1],))
                    (msg, data) = handle.send(("no", struct.vec_to_word(nvec[:-1]), None))
                    break
            else:
                # Now we have to extend the pattern
                #print("not found, extending")
                j=0
                while True:
                    success, changed = builder.extend()
                    j+=1
                    if success:
                        if j%print_freq == 0:
                            print("  Extended at", builder.nvecs[-1], "to size", len(builder.pattern), "to find counterexample")
                        #if len(builder.pattern)%100 == 0:
                        #    print("extended at", changed, "now size", len(builder.pattern))
                        if conf[changed] != builder.pattern[changed]:
                            (msg, data) = handle.send(("no", struct.vec_to_word(changed[:-1]), None))
                            break
                    else:
                        # Backtracked
                        if any(w[:-1] in sent for w in changed):
                            (msg, data) = handle.send(("backtrack",
                                                       [struct.vec_to_word(nvec[:-1]) for nvec in changed],
                                                       None))
                            for nvec in changed:
                                sent.discard(nvec[:-1])
                            break
        if msg == "eval":
            if not struct.word_dfa.accepts(data):
                (msg, data) = handle.send(("val", None, data))
                continue
            vec = struct.word_to_vec(data)
            #print("finding", nvec, "in pattern")
            # Look for the value in the pattern first
            if all(vec + (node,) in builder.pattern for node in struct.nodes):
                #print("found")
                sent.add(vec)
                (msg, data) = handle.send(("val", frozendict({node: builder.pattern[vec + (node,)]
                                                              for node in struct.nodes}), vec))
            else:
                # Now we have to extend the pattern
                j = 0
                while True:
                    j += 1
                    #print("not found, extending")
                    success, changed = builder.extend()
                    if success:
                        if j%print_freq == 0:
                            print("  Extended at", builder.nvecs[-1], "to size", len(builder.pattern), "to find", vec)
                        #1/0
                        if all(vec + (node,) in builder.pattern for node in struct.nodes):
                            sent.add(vec)
                            (msg, data) = handle.send(("val", frozendict({node: builder.pattern[vec + (node,)]
                                                              for node in struct.nodes}), vec))
                            break
                    else:
                        # Backtracked
                        if any(w[:-1] in sent for w in changed):
                            (msg, data) = handle.send(("backtrack",
                                                       [struct.vec_to_word(nvec[:-1]) for nvec in changed],
                                                       None))
                            for nvec in changed:
                                sent.discard(nvec[:-1])
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
    forbs = [{(0,0,()):'0', (0,1,()):'0', (1,0,()):'0'}]
    the_sft = SFT(dim, nodes, alph, top, forbs=forbs, onesided=[0,1])
    struct = AutomaticStructure.n_ary(2, 2, nodes)
    print("Learning configuration...")
    conf = learn_lex_min(struct, the_sft, LexMinBuilder(the_sft))
    print("Learning process finished")
    print(conf.info_string(verbose=True))

if __name__ == "__main__":
    test()
