
from general import *
from configuration import Conf

class AutomaticStructure:
    """
    A little endian automatic structure on N^d (two-sided dimensions to be added later).
    """

    def __init__(self, dim, alph, word_to_vec, vec_to_word, set_automaton):
        """
        To define an automatic structure, one needs:
        1) A dimension.
        2) An input alphabet A.
        3) A function that takes a word over (A + None)^d and returns a vector in N^d.
           Short components are padded with Nones on the right (we use little endian).
        4) The reverse function of the above.
        5) The "patch function".
           It takes a list S of vectors of N^d (the "patch") and a DFA M (the "configuration") with outputs in B.
           It returns a DFA that reads a word w over (A + None)^d and outputs an |S|-tuple of Bs.
           This represents the contents of the configuration at v + S, where v is the vector corresponding to w.
        """
        self.dim = dim
        self.alph = alph
        self.word_to_vec = word_to_vec
        self.vec_to_word = vec_to_word
        self.patch_automaton = patch_automaton

    @classmethod
    def n_ary(self, dim, arity):
        "The n-ary encoding of N^d"
        alph = words(dim, list(range(arity)))

        def w2v(w):
            vec = [0]*dim
            for (i, digits) in enumerate(w):
                for (j, d) in enumerate(digits):
                    vec[j] += arity**d
            return tuple(vec)

        def v2w(vec):
            word = []
            while any(vec):
                word.append(tuple(d%arity for d in vec))
                vec = tuple(d//arity for d in vec)
            return word

        def patch_aut(vecs, dfa):
            pass

        return self(dim, alph, w2v, v2w, patch_aut)

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
        
