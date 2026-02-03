import math
from circuit import Circuit, AND, OR, NOT, T, F, IFF, V

# Does this string represent a number?
def is_nat(string):
    if not string:
        return False
    if string == '0':
        return True
    if string[0] != '0' and all(c in "0123456789" for c in string):
        return True
    return False

def node_constraints(alphabets):
    "Give all node constaints for a circuit or list of circuits."
    def func(circuits):
        if type(circuits) == Circuit:
            circuits = [circuits]
        nodes = set(var[:-1] for circuit in circuits for var in circuit.get_variables())
        anded = []
        for node in nodes:
            alph = alphabets[node[1]]
            nvars = [V(node+(l,)) for l in alph.node_vars]
            anded.append(alph.node_constraint(nvars))
        return AND(*anded)
    return func

class Alphabet:
    "A finite alphabet plus a method of encoding it into circuits."

    def __init__(self, symbols, node_vars, model_to_sym, node_constraint, node_eq_sym, node_eq_node, sym_to_num, encoding = None):
        """
        A finite alphabet.
        * symbols is a list of its elements (they have a default order).
        * node_vars is a list of labels that together encode the symbol at a given node:
          (cell, node) is encoded by V((cell, node, label)) for label in node_vars.
        * node_constraint is a function that takes a list of circuits representing node variables and
          returns a circuit, a constraint that must hold for the encoding to be valid.
        * model_to_sym takes a truth assignment of the variables (list of booleans) and returns
          the corresponding symbol.
        * node_eq_sym is a function that takes a list of circuits representing node variables and
          a symbol of the alphabet, and returns a circuit constraining them to represent the symbol.
        * node_eq_node is a function that takes two lists of circuits and returns a circuit
          constraining them to represent the same variable.
        * sym_to_num takes a symbol and returns a number or None
        """
        self.symbols = symbols
        self.node_vars = node_vars
        self.model_to_sym = model_to_sym
        self.node_constraint = node_constraint
        self.node_eq_sym = node_eq_sym
        self.node_eq_node = node_eq_node
        self.sym_to_num = sym_to_num
        self.encoding = encoding

    def __repr__(self):
        return "Alphabet({}, encoding={})".format(self.symbols, self.encoding)

    def __iter__(self):
        return iter(self.symbols)

    def __getitem__(self, ix):
        return self.symbols[ix]

    def __len__(self):
        return len(self.symbols)

    def __contains__(self, val):
        return val in self.symbols

    def __eq__(self, other):
        if not isinstance(other, Alphabet):
            return False
        return self.encoding == other.encoding and self.symbols == other.symbols

    @classmethod
    def test_alph(self, syms):
        "An alphabet encoded in unary: one variable per symbol, exactly one is true. Used for testing."

        labels = [(sym, "TEST!") for sym in syms]

        def m_to_s(bools):
            return syms[bools.index(True)]
        
        def exactly_one(circs):
            seen = circs[0]
            two = F
            for circ in circs[1:]:
                two = OR(two, AND(seen, circ))
                seen = OR(seen, circ)
            return AND(seen, NOT(two))

        def n_eq_s(circs, sym):
            return circs[syms.index(sym)]

        def n_eq_n(circs1, circs2):
            return AND(*(IFF(circ1, circ2) for (circ1, circ2) in zip(circs1, circs2)))

        def s_to_num(sym):
            if is_nat(sym):
                return int(sym)
            else:
                return None
                          
        return self(syms, labels, m_to_s, exactly_one, n_eq_s, n_eq_n, s_to_num, encoding="test")

    @classmethod
    def unary(self, syms):
        "An alphabet encoded in unary: one variable per symbol, exactly one is true."

        def m_to_s(bools):
            return syms[bools.index(True)]
        
        def exactly_one(circs):
            seen = circs[0]
            two = F
            for circ in circs[1:]:
                two = OR(two, AND(seen, circ))
                seen = OR(seen, circ)
            return AND(seen, NOT(two))

        def n_eq_s(circs, sym):
            return circs[syms.index(sym)]

        def n_eq_n(circs1, circs2):
            return AND(*(IFF(circ1, circ2) for (circ1, circ2) in zip(circs1, circs2)))

        def s_to_num(sym):
            if is_nat(sym):
                return int(sym)
            else:
                return None
                          
        return self(syms, syms, m_to_s, exactly_one, n_eq_s, n_eq_n, s_to_num, encoding="unary")

    @classmethod
    def unary_minus_one(self, syms):
        "An alphabet encoded in unary minus one: one variable per symbol except the first one, at most one is true."

        def m_to_s(bools):
            try:
                ix = bools.index(True)+1
            except ValueError:
                ix = 0
            return syms[ix]
        
        def at_most_one(circs):
            seen = circs[0]
            two = F
            for circ in circs[1:]:
                two = OR(two, AND(seen, circ))
                seen = OR(seen, circ)
            return NOT(two)

        def n_eq_s(circs, sym):
            ix = syms.index(sym)
            if ix:
                return circs[ix-1]
            else:
                return NOT(OR(*circs))

        def n_eq_n(circs1, circs2):
            return AND(*(IFF(circ1, circ2) for (circ1, circ2) in zip(circs1, circs2)))

        def s_to_num(sym):
            if is_nat(sym):
                return int(sym)
            else:
                return None
                          
        return self(syms, syms[1:], m_to_s, at_most_one, n_eq_s, n_eq_n, s_to_num, encoding="unary_minus_one")

    @classmethod
    def binary(self, syms):
        """
        An alphabet encoded in binary: ceil(log_2(n)) bits used for n variables.
        First variable is coded 000, then 001, etc..
        """

        vrs = list(range(math.ceil(math.log2(len(syms)))))

        def m_to_s(bools):
            "Return symbol coded by bits in bools list."
            v = 0
            for b in bools:
                v *= 2
                v += int(b)
            if v >= len(syms):
                raise Exception("Internal error, non-letter seen.")
            return syms[v]

        def codes_something(circs):
            "circuit value can't be more more than len(sym)-1"
            symc = list(int(a) for a in bin(len(syms) - 1)[2:])
            assert len(symc) == len(vrs)
            # we've seen a larger digit in alphabet already
            ok_already = F
            checks = []
            for ib, b in enumerate(symc):
                # if the current bit is 0
                if not b:
                    checks.append(OR(ok_already, NOT(circs[ib])))
                if b:
                    ok_already = OR(ok_already, NOT(circs[ib]))
            return AND(*checks)

        def n_eq_s(circs, sym):
            ix = syms.index(sym)
            symc = list(int(a) for a in bin(ix)[2:])
            symc = [0] * (len(vrs)- len(symc)) + symc
            checks = []
            for i in range(len(vrs)):
                if symc[i]:
                    checks.append(circs[i])
                else:
                    checks.append(NOT(circs[i]))
            return AND(*checks)

        def n_eq_n(circs1, circs2):
            return AND(*(IFF(circ1, circ2) for (circ1, circ2) in zip(circs1, circs2)))

        def s_to_num(sym):
            if is_nat(sym):
                return int(sym)
            else:
                return None
                          
        return self(syms, vrs, m_to_s, codes_something, n_eq_s, n_eq_n, s_to_num, encoding="binary")




