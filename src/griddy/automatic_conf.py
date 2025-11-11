
from general import *
from configuration import Conf
from finite_automata import DFA, NFA, NTrans

class AutomaticStructure:
    """
    An automatic structure on N^d (two-sided dimensions to be added later).
    """

    def __init__(self, dim, nodes, alph, word_dfa, word_to_vec, vec_to_word, addition_transducer, name=None):
        """
        To define an automatic structure, one needs:
        1) A dimension.
        2) An input alphabet A.
        3) A DFA M for valid vector words over A (which can be converted to vectors).
        4) A function f that takes a word in L(M) and returns a vector in N^d.
           It should be a bijection between N^d and L(M)
        5) The inverse function f^{-1} of the above.
        6) The addition transducer function T.
           It takes a nonnegative vector v and gives a nondeterministic transducer T_v.
           The transducer takes a word x in L(M) and outputs a word T_v(x) in L(M)
           such that f(T_v(x)) = f(x) + v.
        """
        self.dim = dim
        self.nodes = nodes
        self.alph = alph
        self.word_dfa = word_dfa
        self.word_to_vec = word_to_vec
        self.vec_to_word = vec_to_word
        self.addition_transducer = addition_transducer
        if name is None:
            name = "no name"
        self.name = name

    def valid_for(self, vecs):
        for vec in vecs:
            word = self.vec_to_word(vec)
            if not self.word_dfa.output(word):
                return False
            if vec != self.word_to_vec(word):
                return False
        for vec in vecs:
            # Check that given a valid word, the tranducer will not produce invalid words
            adder = self.addition_transducer(vec)
            init = (adder.init, self.word_dfa.init, self.word_dfa.init)
            seen = {init}
            frontier = {init}
            trans = dict()
            while frontier:
                new_frontier = set()
                for triple in frontier:
                    (a_st, d1_st, d2_st) = triple
                    for sym in self.alph:
                        new_d1_st = self.word_dfa.trans[d1_st, sym]
                        trans[triple, sym] = []
                        pairs = adder.trans[a_st, sym]
                        for (new_a_st, outs) in pairs:
                            new_d2_st = self.word_dfa.read_word(d2_st, outs)
                            new_triple = (new_a_st, new_d1_st, new_d2_st)
                            trans[triple, sym].append(new_triple)
                            if new_triple not in seen:
                                seen.add(new_triple)
                                new_frontier.add(new_triple)
                frontier = new_frontier

            finals = {(a_st, d1_st, d2_st)
                      for (a_st, d1_st, d2_st) in seen
                      if a_st in adder.finals
                      if self.word_dfa.outputs[d1_st]}
            if any(not self.word_dfa.outputs[d2_st] for (_, _, d2_st) in finals):
                print("not accept", vec)
                return False

            # Check that the transducer will accept every valid word
            nfa_trans = {(st, sym) : list(set(st2 for (st2, _) in adder.trans[st, sym]))
                         for st in adder.states
                         for sym in self.alph}
            nfa = NFA(self.alph, nfa_trans, {adder.init}, adder.finals)
            res, word = nfa.contains(self.word_dfa.extend_alph([None]).concat(NFA.singleton(self.alph+[None], None)), track=True)
            if not res:
                print("not every word accepted:", word, vec)
                print(adder.init, adder.finals, nfa_trans)
                return False

            # Check that the transducer gives correct outputs
            for vec2 in vecs:
                word = self.vec_to_word(vec2)
                out_word = []
                st = adder.init
                for sym in word + (None,):
                    (st, out) = adder.trans[st, sym][0]
                    out_word.extend(out)
                vec3 = self.word_to_vec(out_word)
                if vec3 != vadd(vec, vec2):
                    print("incorrect output:", vec, vec2, vec3, word, out_word)
                    return False
            
        return True

    def patches(self, domain, dfa):
        """
        Take a list D of node vectors in N^d and a DFA M, representing a configuration.
        The DFA reads a word in L(M), then a node, and outputs a symbol.
        Return an iterator for patches w+S occurring in the configuration,
        encoded as length-|D| tuples of symbols.
        """
        # We construct the states of a nondeterministic automaton for the configuration
        # over the patches and extract its possible outputs.
        # The states of the automaton are tuples (q, ((p1,q1), ..., (pk,qk)) where
        # k is the number of distinct vectors on D,
        # q is a state of the word DFA, pi is a state of the addition transducer,
        # and qi is a state of the configuration DFA.
        # The transducers read the input and feed their outputs to their respective DFAs.
        # We reject if the word DFA or some addition tranducer rejects.

        #print("Finding patches")

        vecs = list(set(nvec[:-1] for nvec in domain))
        #vec_domain = dict()
        #for nvec in domain:
        #    vec = nvec[:-1]
        #    node = nvec[-1]
        #    if vec in vec_domain:
        #        vec_domain[vec].append(node)
        #    else:
        #        vec_domain[vec] = [node]
        adders = [self.addition_transducer(vec) for vec in vecs]
        
        the_init = (self.word_dfa.init,
                    tuple((adder.init, dfa.init) for adder in adders))
        frontier = {the_init}
        seen = {the_init}
        while frontier:
            #print("Frontier size", len(frontier))
            new_frontier = set()
            for state in frontier:
                (w_st, add_d_pairs) = state
                for sym in self.alph + [None]:
                    if sym is None:
                        new_w_st = w_st
                    else:
                        new_w_st = self.word_dfa(w_st, sym)
                    results_list = []
                    for (adder, (add_st, d_st)) in zip(adders, add_d_pairs):
                        # We put all the new states in the list and take the product
                        results_list.append(iter([(new_add_st, dfa.read_word(d_st, add_out))
                                                  for (new_add_st, add_out) in adder(add_st, sym)]))
                    new_add_d_states = iter_prod(*results_list)
                    for new_add_d_pairs in new_add_d_states:
                        new_state = (new_w_st, tuple(new_add_d_pairs))
                        if new_state not in seen:
                            seen.add(new_state)
                            new_frontier.add(new_state)
            frontier = new_frontier

        #print("Found", len(seen), "states")

        seen_patches = set()
        for (w_st, add_d_pairs) in seen:
            if self.word_dfa.outputs[w_st] and\
               all(add_st in adder.finals
                   for (adder, (add_st, _)) in zip(adders, add_d_pairs)):
                # Feed nodes to DFAs
                d_sts = {vec : d_st for (vec, (_, d_st)) in zip(vecs, add_d_pairs)}
                patch = []
                for nvec in domain:
                    #print("okoko", dfa(d_sts[nvec[:-1]], nvec[-1]))
                    patch.append(dfa.outputs[dfa(d_sts[nvec[:-1]], nvec[-1])])
                if None in patch:
                    raise Exception("Invalid patch {}".format(patch))
                patch = tuple(patch)
                if patch not in seen_patches:
                    #print("Found patch", patch)
                    seen_patches.add(patch)
                    yield patch

    @classmethod
    def n_ary(self, dim, arity, nodes):
        "The mixed n-ary encoding of N^d with given nodes"
        if type(arity) == int:
            arity = [arity]*dim
        alph = list(iter_prod(*(iter(range(a)) for a in arity)))

        word_dfa =\
            DFA.universal(alph).concat(NFA.singleton(alph, (0,)*dim)).\
            determinize().negate().minimize()
                    
        #print("word dfa")
        #print(word_dfa.info_string(verbose=True))
        #1/0
        
        def w2v(w):
            vec = [0]*dim
            for (i, digits) in enumerate(w):
                for (j, d) in enumerate(digits):
                    vec[j] += d*arity[j]**i
            return tuple(vec)

        def v2w(vec):
            if any(i<0 for i in vec):
                return None
            word = []
            while any(vec):
                word.append(tuple(d%arity[j] for (j,d) in enumerate(vec)))
                vec = tuple(d//arity[j] for (j,d) in enumerate(vec))
            return tuple(word)

        def add_trans(vec):
            #print("add_trans", vec)
            init = vec
            finals = {"acc"}
            frontier = {vec, "acc"}
            seen = {vec}
            trans = dict()
            while frontier:
                #print("frontier", frontier)
                new_frontier = set()
                for the_vec in frontier:
                    if the_vec == "acc":
                        for sym in alph + [None]:
                            trans[the_vec, sym] = []
                        continue
                    #print("the_vec", the_vec)
                    trans[the_vec, None] = [("acc", list(v2w(the_vec)))]
                    for sym in alph:
                        pairs = [(vi//ai + int(di+(vi%ai) >= ai), (di+vi)%ai)
                                 for (vi, di, ai) in zip(the_vec, sym, arity)]
                        new_vec, out = zip(*pairs)
                        if new_vec not in seen:
                            seen.add(new_vec)
                            new_frontier.add(new_vec)
                        trans[the_vec, sym] = [(new_vec, [out])]
                frontier = new_frontier
            return NTrans(alph, trans, init, finals)

        ret = self(dim, nodes, alph, word_dfa, w2v, v2w, add_trans, name="{}-ary".format(arity))
        #assert ret.valid_for(list(onesided_hypercube(dim, 10)))
        return ret

class AutomaticConf(Conf):

    def __init__(self, struct, dfa, dim=None):
        if dim is None:
            dim = struct.dim
        super().__init__(onesided = list(range(dim)))

        self.struct = struct
        self.dfa = dfa
        self.dim = dim

    def __getitem__(self, nvec):
        word = self.struct.vec_to_word(nvec[:-1])
        if word is None:
            return None
        return self.dfa.output(word + (nvec[-1],))

    def info_string(self, verbose=False):
        s = "Automatic configuration on {} structure".format(self.struct.name)
        if verbose:
            s += " defined by\n" + self.dfa.info_string(verbose=True)
        return s

    def is_contained(self, sft):
        "Is this configuration in the given SFT?"
        #print("testing containment for SFT and automatic conf")
        forbs = sft.forbs
        #print("forbs", forbs)
        domain = list(set(nvec for forb in forbs for nvec in forb))
        #print("domain", domain)
        for patch in self.struct.patches(domain, self.dfa):
            #print("checking patch", patch)
            for forb in forbs:
                #print("checking forb", forb)
                for (nvec, c) in forb.items():
                    ix = domain.index(nvec)
                    #print("checking coord", vec, "at index", ix, "for sym", c)
                    if patch[ix] != c:
                        break
                else:
                    #print("Found forb", forb)
                    return False
        return True
        

