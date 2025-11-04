
from general import *
from configuration import Conf
from finite_automata import DFA

class AutomaticStructure:
    """
    A little endian automatic structure on N^d (two-sided dimensions to be added later).
    """

    def __init__(self, dim, alph, word_to_vec, vec_to_word, addition_transducer):
        """
        To define an automatic structure, one needs:
        1) A dimension.
        2) An input alphabet A.
        3) A function that takes a word over (A + None)^d and returns a vector in N^d.
           Short components are padded with Nones on the right (we use little endian).
        4) The reverse function of the above.
        5) The addition transducer function.
           It takes a nonnegative vector v_0 and gives a transducer T (as a pair init, trans).
           T transforms word w representing v into w' representing v + v_0.
        """
        self.dim = dim
        self.alph = alph
        self.word_to_vec = word_to_vec
        self.vec_to_word = vec_to_word
        self.addition_transducer = addition_transducer

    def patch_automaton(self, domain, dfa):
        """
        Take a list D of vectors in N^d and a DFA M, representing a configuration.
        Return a DFA N that takes a word w and returns the patch w+S of the configuration,
        encoded as a length-|D| list of symbols.
        """
        adders = [self.addition_transducer(vec) for vec in domain]
        adder_trans = [adder[1] for adder in adders]
        
        the_init = tuple((adder[0], dfa.init) for adder in adders)
        frontier = {the_init}
        seen = {the_init}
        trans = dict()
        while frontier:
            new_frontier = set()
            for states in frontier:
                for sym in self.alph:
                    new_states = []
                    for (adder, (add_st, dfa_st)) in zip(adders, states):
                        new_add_st, add_sym = adder[add_st, sym]
                        new_dfa_st = dfa(dfa_st, add_sym)
                        new_states.append((new_add_st, new_dfa_st))
                    new_states = tuple(new_states)
                    trans[states, sym] = new_states
                    if new_states not in seen:
                        seen.add(new_states)
                        new_frontier.add(new_states)
            frontier = new_frontier

        outputs = { states : [dfa.outputs[dfa_st]
                              for (_, dfa_st) in states]
                    for states in seen }
        ret = DFA(self.alph, trans, the_init, outputs=outputs)
        ret.rename()
        return ret

    @classmethod
    def n_ary(self, dim, arity):
        "The mixed n-ary encoding of N^d"
        if type(arity) == int:
            arity = [arity]*dim
        alph = list(iter_prod(*(range(a) for a in arity)))
        
        def w2v(w):
            vec = [0]*dim
            for (i, digits) in enumerate(w):
                for (j, d) in enumerate(digits):
                    vec[j] += arity[j]**d
            return tuple(vec)

        def v2w(vec):
            word = []
            while any(vec):
                word.append(tuple(d%arity[j] for (j,d) in enumerate(vec)))
                vec = tuple(d//arity[j] for (j,d) in enumerate(vec))
            return word

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

        return self(dim, alph, w2v, v2w, add_trans)

class AutomaticConf(Conf):

    def __init__(self, struct, dfa, dim=None):
        if dim is None:
            dim = struct.dim
        super().__init__(onesided = list(range(dim)))

        self.struct = struct
        self.dfa = dfa

    def __getitem__(self, nvec):
        return self.dfa.output(self.struct.vec_to_word(nvec))

    def is_contained(self, sft):
        "Is this configuration in the given SFT?"
        forbs = sft.forbs
        domain = list(set(nvec for forb in forbs for nvec in forb))
        patch_aut = self.struct.patch_automaton(domain, self.dfa)
        for patch in patch_aut.outputs.values():
            for forb in forbs:
                if all(patch[domain.index(nvec)] == c for (nvec, c) in forb.items()):
                    return False
        return True
        
