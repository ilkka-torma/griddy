
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
        3) A DFA for valid words over A (which can be converted to node vectors).
        4) A function that takes a word over A and returns a node vector in N^d.
           It should be a bijection between the language of the word DFA and N^d.
        5) The inverse function of the above.
        6) The addition transducer function.
           It takes a nonnegative vector v_0 and gives a nondeterministic transducer T,
           which outputs words that are then concatenated into a consistent output.
           T transforms a given word w representing v into w' representing v + v_0.
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

    def patches(self, domain, dfa):
        """
        Take a list D of node vectors in N^d and a DFA M, representing a configuration.
        Return an iterator for patches w+S occurring in the configuration,
        encoded as length-|D| tuples of symbols.
        """
        # We construct the states of a nondeterministic automaton for the configuration
        # over the patches and extract its possible outputs.
        # The states of the automaton are tuples (q, ((p1,q1), ..., (pk,qk))) where k = |D|,
        # q is a state of the word DFA, pi is a state of the addition transducer,
        # and qi is a state of the configuration DFA.
        # The transducers read the input and feed their outputs to their respective DFAs.
        # We reject if the word DFA or some addition tranducer rejects.
        adders = [self.addition_transducer(vec) for vec in domain]
        
        the_init = (self.word_dfa.init, tuple((adder.init, dfa.init) for adder in adders))
        frontier = {the_init}
        seen = {the_init}
        while frontier:
            new_frontier = set()
            for state in frontier:
                (w_st, states) = state
                for sym in self.alph:
                    new_w_st = self.word_dfa(w_st, sym)
                    new_add_pair_list = []
                    for (adder, (add_st, _)) in zip(adders, states):
                        # We put all the adder results in the list
                        # and take the product later
                        new_add_pair_list.append(iter(adder(add_st, sym)))
                    new_add_list = iter_prod(*new_add_pair_list)
                    for add_pairs in new_add_list:
                        new_states = []
                        for ((new_add_st, add_outs), (_, dfa_st)) in zip(add_pairs, states):
                            new_dfa_st = dfa.read_word(dfa_st, add_outs)
                            new_states.append((new_add_st, new_dfa_st))
                        new_state = (new_w_st, tuple(new_states))
                        if new_state not in seen:
                            seen.add(new_state)
                            new_frontier.add(new_state)
            frontier = new_frontier

        seen_patches = set()
        for (w_st, states) in seen:
            if self.word_dfa.outputs[w_st] and\
               all(add_st in adder.finals
                   for (adder, (add_st, _)) in zip(adders, states)):
                patch = tuple(dfa.outputs[dfa_st] for (_, dfa_st) in states)
                if patch not in seen_patches:
                    seen_patches.add(patch)
                    yield patch

    @classmethod
    def n_ary(self, dim, arity, nodes):
        "The mixed n-ary encoding of N^d with given nodes"
        if type(arity) == int:
            arity = [arity]*dim
        digits = list(iter_prod(*(iter(range(a)) for a in arity)))
        alph = digits + list(nodes)

        word_dfa =\
            NFA.one_of(alph, list(nodes)).\
            concat(NFA.one_of(alph, digits).star().\
                   intersect(DFA.universal(alph).\
                             concat(NFA.singleton(alph, (0,)*dim)).\
                             determinize().negate())).\
            determinize().minimize()
                    
        #print("word dfa")
        #print(word_dfa.info_string(verbose=True))
        #1/0
        
        def w2v(w):
            node = w[0]
            w = w[1:]
            vec = [0]*dim
            for (i, digits) in enumerate(w):
                for (j, d) in enumerate(digits):
                    vec[j] += d*arity[j]**i
            return tuple(vec) + (node,)

        def v2w(nvec):
            node = nvec[-1]
            vec = nvec[:-1]
            word = []
            while any(vec):
                word.append(tuple(d%arity[j] for (j,d) in enumerate(vec)))
                vec = tuple(d//arity[j] for (j,d) in enumerate(vec))
            return (node,) + tuple(word)

        def add_trans(vec):
            init = vec
            finals = {"acc"}
            frontier = {vec}
            seen = {vec}
            trans = dict()
            while frontier:
                new_frontier = set()
                for the_vec in frontier:
                    for sym in alph:
                        if the_vec in ["acc", "rej"]:
                            trans[the_vec, sym] = [("rej", [])]
                            new_sts = ["rej"]
                        elif sym in nodes:
                            trans[the_vec, sym] = [(the_vec, [sym])]
                            new_sts = []
                        else:
                            pairs = [(vi//ai + int(di+vi >= ai), (di+vi)%ai)
                                     for (vi, di, ai) in zip(the_vec, sym, arity)]
                            new_vec, out = zip(*pairs)
                            trans[the_vec, sym] = [(new_vec, [out])]
                            new_sts = [new_vec]
                            if all(d < a for (d,a) in zip(new_vec, arity)):
                                trans[the_vec, sym].append(("acc", [out, new_vec]))
                                new_sts.append("acc")
                        for new_st in new_sts:
                            if new_st not in seen:
                                seen.add(new_st)
                                new_frontier.add(new_st)
                frontier = new_frontier
            return NTrans(alph, trans, init, finals)

        return self(dim, nodes, alph, word_dfa, w2v, v2w, add_trans, name="{}-ary".format(arity))

class AutomaticConf(Conf):

    def __init__(self, struct, dfa, dim=None):
        if dim is None:
            dim = struct.dim
        super().__init__(onesided = list(range(dim)))

        self.struct = struct
        self.dfa = dfa

    def __getitem__(self, nvec):
        return self.dfa.output(self.struct.vec_to_word(nvec))

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
                    return False
        return True
        

