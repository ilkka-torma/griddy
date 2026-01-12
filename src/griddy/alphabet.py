
from circuit import AND, OR

class Alphabet:
    "A finite alphabet plus a method of encoding it into circuits."

    def __init__(self, symbols, node_vars, node_constraint, node_eq_sym, node_eq_node):
        """
        A finite alphabet.
        symbols is a list of its elements (they have a default order).
        node_vars is a list of labels that together encode the symbol at a given node:
        (cell, node) is encoded by (cell, node, label) for label in node_vars.
        node_constraint is a function that takes a list of circuits representing node variables and
        returns a circuit, a constraint that must hold for the encoding to be valid.
        node_eq_sym is a function that takes a list of circuits representing node variables
        and a symbol of the alphabet, and returns a circuit constraining them to represent the symbol.
        node_eq_node is a function that takes two lists of circuits and returns a circuit
        constraining them to represent the same variable.
        """
        self.symbols = symbols
        self.node_vars = node_vars
        self.node_constraint = node_constraint
        self.node_eq_sym = node_eq_sym
        self.node_eq_node = node_eq_node

    def __repr__(self):
        return "Alphabet({})".format(self.symbols)

    def __iter__(self):
        return iter(self.symbols)

    def __getitem__(self, ix):
        return self.symbols[ix]

    def __len__(self):
        return len(self.symbols)

    @classmethod
    def unary(self, syms):
        "An alphabet encoded in unary: one variable per symbol, exactly one is true."
        
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
            return AND(*(EQ(circ1, circ2) for (circ1, circ2) in zip(circs1, circs2)))
                          
        return self(syms, syms, exactly_one, n_eq_s, n_eq_n)

    @classmethod
    def unary_minus_one(self, syms):
        "An alphabet encoded in unary minus one: one variable per symbol except the first one, at most one is true."
        
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
            return AND(*(EQ(circ1, circ2) for (circ1, circ2) in zip(circs1, circs2)))
                          
        return self(syms, syms[1:], at_most_one, n_eq_s, n_eq_n)
