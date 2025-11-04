
from general import *
from configuration import Conf
from finite_automata import DFA, NFA

class AutomaticStructure:
    """
    An automatic structure on N^d (two-sided dimensions to be added later).
    """

    def __init__(self, dim, alph, word_dfa, strict_word_dfa, word_to_vec, vec_to_word, addition_transducer, name=None):
        """
        To define an automatic structure, one needs:
        1) A dimension.
        2) An input alphabet A.
        3) A DFA for valid words over A (which can be converted to vectors).
        4) A DFA for strictly valid words over A (which give a valid transducer result).
        5) A function that takes a word over A and returns a vector in N^d.
        6) The reverse function of the above.
        7) The addition transducer function.
           It takes a nonnegative vector v_0 and gives a transducer T (as a pair init, trans).
           T transforms word w representing v into w' representing v + v_0.
        """
        self.dim = dim
        self.alph = alph
        self.word_dfa = word_dfa
        self.strict_word_dfa = strict_word_dfa
        self.word_to_vec = word_to_vec
        self.vec_to_word = vec_to_word
        self.addition_transducer = addition_transducer
        if name is None:
            name = "no name"
        self.name = name

    def patch_automaton(self, domain, dfa, minimize=False):
        """
        Take a list D of vectors in N^d and a DFA M, representing a configuration.
        Return a DFA N that takes a word w and returns the patch w+S of the configuration,
        encoded as a length-|D| list of symbols.
        The word is rejected (resulting in None) if the strict word DFA rejects it.
        """
        adders = [self.addition_transducer(vec) for vec in domain]
        adder_trans = [adder[1] for adder in adders]
        
        the_init = (self.strict_word_dfa.init, tuple((adder[0], dfa.init) for adder in adders))
        frontier = {the_init}
        seen = {the_init}
        trans = dict()
        while frontier:
            new_frontier = set()
            for state in frontier:
                (w_st, states) = state
                for sym in self.alph:
                    new_states = []
                    for (adder, (add_st, dfa_st)) in zip(adder_trans, states):
                        new_add_st, add_sym = adder[add_st, sym]
                        new_dfa_st = dfa(dfa_st, add_sym)
                        new_states.append((new_add_st, new_dfa_st))
                    new_w_st = self.strict_word_dfa(w_st, sym)
                    new_state = (new_w_st, tuple(new_states))
                    trans[state, sym] = new_state
                    if new_state not in seen:
                        seen.add(new_state)
                        new_frontier.add(new_state)
            frontier = new_frontier

        outputs = { (w_st, states) :
                    tuple(dfa.outputs[dfa_st]
                          for (_, dfa_st) in states)
                    if self.strict_word_dfa.outputs[w_st]
                    else None
                    for (w_st, states) in seen }
        ret = DFA(self.alph, trans, the_init, outputs=outputs)
        ret.rename()
        if minimize:
            ret = ret.minimize()
        return ret

    @classmethod
    def n_ary(self, dim, arity):
        "The mixed n-ary encoding of N^d"
        if type(arity) == int:
            arity = [arity]*dim
        alph = list(iter_prod(*(iter(range(a)) for a in arity)))

        strict_word_dfa = DFA.universal(alph).concat(NFA.singleton(alph,(0,)*dim)).determinize().minimize()
        word_dfa = DFA.universal(alph)
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
            word = []
            while any(vec):
                word.append(tuple(d%arity[j] for (j,d) in enumerate(vec)))
                vec = tuple(d//arity[j] for (j,d) in enumerate(vec))
            return tuple(word)

        def add_trans(vec):
            init = vec
            frontier = {vec}
            seen = {vec}
            trans = dict()
            while frontier:
                new_frontier = set()
                for the_vec in frontier:
                    for digits in alph:
                        pair = [(vi//ai + int(di+vi >= ai), (di+vi)%ai)
                                for (vi, di, ai) in zip(the_vec, digits, arity)]
                        new_vec, out = zip(*pair)
                        trans[the_vec, digits] = (new_vec, out)
                        if new_vec not in seen:
                            seen.add(new_vec)
                            new_frontier.add(new_vec)
                frontier = new_frontier
            return init, trans

        return self(dim, alph, word_dfa, strict_word_dfa, w2v, v2w, add_trans, name="{}-ary".format(arity))

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
        domain = list(set(nvec[:-1] for forb in forbs for nvec in forb))
        #print("domain", domain)
        patch_aut = self.struct.patch_automaton(domain, self.dfa, minimize=True)
        #print("patch aut")
        #print(patch_aut.info_string(verbose=True))
        for patch in set(patch_aut.outputs.values()):
            if patch is None:
                continue
            #print("checking patch", patch)
            for forb in forbs:
                #print("checking forb", forb)
                for (nvec, c) in forb.items():
                    vec = nvec[:-1]
                    ix = domain.index(vec)
                    #print("checking coord", vec, "at index", ix, "for sym", c)
                    if patch[ix] != c:
                        break
                else:
                    return False
        return True
        

