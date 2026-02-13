import circuit as cc
#from circuit import *
from frozendict import frozendict as fd

# circuits is dict : index -> Circuit,
# and we interpret that when dict[a] is satisfied,
# the ath output bit is on
class MOCircuit:
    def __init__(self, circuits):
        self.circuits = circuits
    def equivalent(self, other):
        for a in self.circuits:
            m = cc.equivalent(self.circuits[a], other.circuits[a], True)
            if m != True:
                return (a, m)
        return True
    def __getitem__(self, index):
        return self.circuits[index]
    def __repr__(self):
        return "MOCircuit({})".format(self.circuits)

class MOCircuitSet:
    def __init__(self, indices):
        # we assume all MOCircuits use the same output bit names
        self.bits = indices
        # from unique hashes to (MOCircuit, int) pairs
        self.circuits = dict()
        # (output bit, pattern) that separate MOCircuits,
        # i.e. there is a pattern and info about which bit to eval on
        self.patterns = list()
        # running index
        self.count = 0
    def add(self, new, really_add = True):
        #print("adding", new, really_add)
        hashy = {}
        # p is a dict : bit name -> pattern
        for (a, p) in self.patterns:
            hashy[(a, p)] = cc.evaluate(new.circuits[a], p, default_false=True)
        hashy = fd(hashy)
        #print(hashy, "he")
        if hashy in self.circuits:
            #print("hash was there")
            (prev, ix) = self.circuits[hashy]
            #m = new, prev, True)
            m = new.equivalent(prev)
            #print("oho", m)
            if m == True:
                #self.existing = m
                return prev #False
            if really_add:
                self.add_pattern((m[0], fd(m[1])))
                # now the hash has to be unique, so recursion is safe
                return self.add(new)
            else:
                return True
        else:
            #print("adding hash", fd(hashy))
            if really_add:
                
                self.circuits[hashy] = (new, self.count)
                #print("mallu", self.circuits)
                self.count += 1
                return new
            return True
    def add_pattern(self, sep):
        #print("adding", sep)
        a, p = sep
        self.patterns.append((a, p))
        newcircuits = {}
        for h in self.circuits:
            (circ, ix) = self.circuits[h]
            v = cc.evaluate(circ.circuits[a], p, default_false=True)
            hcopy = dict(h)
            hcopy[sep] = v
            #print(hcopy, "gimA")
            newcircuits[fd(hcopy)] = (circ, ix)
        self.circuits = newcircuits
    def index(self, circ):
        # assumes circ is in the set
        hashy = {}
        for a,p in self.patterns:
            hashy[a,p] = cc.evaluate(circ.circuits[a], p, default_false=True)
        return self.circuits[fd(hashy)][1]
    def __contains__(self, item):
        #print("kiliman")
        return not (self.add(item, False) == True)
    def __str__(self):
        return "CircuitSet container with %s circuits." % len(self.circuits)
    def __len__(self):
        return self.count
    def __iter__(self):
        return iter(c for (c,_) in self.circuits.values())

class MOCircuitDict:
    def __init__(self, indices):
        self.set = MOCircuitSet(indices)
        self.dict = {}
    def __getitem__(self, circ):
        if not circ in self.set:
            #print("nonne")
            return None
        idx = self.set.index(circ)
        return self.dict[idx]
    def __setitem__(self, circ, val):
        self.set.add(circ)
        #print("does have?", circ in self.set)
        #print("index", self.set.index(circ))
        #print(self.set.index(circ), "mas")
        self.dict[self.set.index(circ)] = val
    def __contains__(self, circ):
        return circ in self.set
    def __iter__(self):
        yield from self.set
    def __len__(self):
        return len(self.dict)

"""
c1 = MOCircuit({"0":cc.AND(cc.V(0), cc.V(1)), "1":cc.AND(cc.V(0), cc.NOT(cc.V(1))), "2":cc.NOT(cc.V(0))})
c2 = MOCircuit({"0":cc.NOT(cc.OR(cc.NOT(cc.V(0)), cc.NOT(cc.V(1)))), "1":cc.AND(cc.V(0), cc.NOT(cc.V(1))), "2":cc.NOT(cc.V(0))})
cs = MOCircuitDict(["0", "1", "2"])
cs[c1] = 3
print(cs[c2])
"""

 
