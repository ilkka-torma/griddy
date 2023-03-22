
from circuit import *

def vadd(vec1, vec2):
    return tuple(a+b for (a,b) in zip(vec1, vec2))

def vsub(vec1, vec2):
    return tuple(a-b for (a,b) in zip(vec1, vec2))

def vmod(m, v):
    return v[0]%m, v[1]%m

def Z2square(rad):
    for x in range(-rad, rad+1):
        for y in range(-rad, rad+1):
            yield (x, y)

def centered_hypercube(dim, rad):
    if dim == 0:
        yield ()
        return
    for v in centered_hypercube(dim-1, rad):
        for a in range(-rad, rad+1):
            yield v + (a,)

def Z2onesidedsquare(rad):
    for x in range(0, rad):
        for y in range(0, rad):
            yield (x, y)

def onesided_hypercube(dim, rad):
    if dim == 0:
        yield ()
        return
    for v in centered_hypercube(dim-1, rad):
        for a in range(0, rad):
            yield v + (a,)

# check that circuit is forced to be true when variable set
def forced_by(circuit, vals_as_list):
    andeds = []
    for (var, val) in vals_as_list:
        if val:
            andeds.append(V(var))
        else:
            andeds.append(NOT(V(var)))
    return models(andeds, circuit)

# we have a circuit and some values
# minimize the dict of values so that stays tautology
def minimize_solution(circuit, vals, necessary_vals = None):
    
    if necessary_vals == None:
        assert evaluate(circuit, vals)
        necessary_vals = []

    assert type(vals) == dict
    vals = list(vals.items())
    mini = minimize_solution_(circuit, vals, necessary_vals)
    as_dict = {}
    for (var, val) in mini:
        as_dict[var] = val
    return as_dict
        

def minimize_solution_(circuit, vals, necessary_vals):
    #print("juli", vals, necessary_vals)
    if len(vals) == 0:
        return necessary_vals

    first, rest = vals[0], vals[1:]
    if forced_by(circuit, rest + necessary_vals):
        return minimize_solution_(circuit, rest, necessary_vals)

    return minimize_solution_(circuit, rest, necessary_vals + [first])
    
def add_uniqueness_constraints(nodes, alphabet, circuits, all_positions):
    for p in all_positions:
        for n in nodes:
            pnvars = []
            for a in alphabet:
                #print(alphabet)
                pnvars.append(V(p + (n, a, 0)))
            #print(list(map(str, pnvars)))
            #print(ATMOSTONE(*pnvars))
            circuits[p + (n, "alldiff")] = AND(ATMOSTONE(*pnvars), OR(*pnvars))

class SFT:
    "dim-dimensional SFT on a gridlike graph"

    def __init__(self, dim, nodes, alph, forbs=None, circuit=None, formula=None):
        self.dim = dim
        self.nodes = nodes
        self.alph = alph
        self.forbs = forbs
        self.circuit = circuit
        self.formula = formula # just for display, not actually used in computations
        if self.circuit is None:
            self.deduce_circuit()

    def __str__(self):
        return "SFT(dim={}, nodes={}, alph={})".format(self.dim, self.nodes, self.alph)

    # find periodic configuration in c1 which is not in c2
    def exists_periodic_not_in(self, other, r):
        #print("exper", r)
        if len(self.alph) > 2:
            return self.exists_periodic_not_in_big_alphabet(other, r)

        c1 = self.circuit.copy()
        c2 = other.circuit.copy()
        #print(c1)
        #print(c2)
        circuits = {}

        for v in onesided_hypercube(self.dim, r): #Z2onesidedsquare(r):
            #print(v, "vee")
            circuits[v] = c1.copy()

            for var in c1.get_variables():
                #print(var, "to", vmod(r, vadd(v, var[:-1])) + (var[-1], 0) )
                rel_pos = vmod(r, vadd(v, var[:-1])) + (var[-1], 0)
                #print(var, rel_pos)
                substitute(circuits[v], var, V(rel_pos))
                #print(circuits[v])

        circuits[None] = NOT(c2)
        #print("init", circuits[None])
        for var in c2.get_variables():
            #print("c2", var, "to", V(vmod(r, var[:-1]) + (var[-1], 0)))
            #print("cee", var, vmod(r, var[:-1]) + (var[-1], 0))
            substitute(circuits[None], var, V(vmod(r, var[:-1]) + (var[-1], 0)))
            #print(circuits[None])

        #for k in circuits:
        #    print(k, circuits[k])
        #print("no22")
        m = SAT(AND(*(list(circuits.values()))), True)
        #print(AND(*(list(circuits.values()))))
        if m == False:
            return False
        print(m)
        return True
        
    # find periodic configuration in c1 which is not in c2
    def exists_periodic_not_in_big_alphabet(self, other, r):

        c1 = self.circuit.copy()
        c2 = other.circuit.copy()
        #print(c1)
        #print(c2)
        all_positions = set()
        circuits = {}
        
        for v in onesided_hypercube(self.dim, r):
            #print(v, "vee")
            circuits[v] = c1.copy()
            
            for var in c1.get_variables():

                #print(var, "to", vmod(r, vadd(v, var[:-1])) + (var[-1], 0) )
                rel_pos = vmod(r, vadd(v, var[:-2])) + (var[-2:]) + (0,)
                #print(var, rel_pos)
                substitute(circuits[v], var, V(rel_pos))
                all_positions.add(rel_pos[:-3])
                #print(circuits[v])

        circuits[None] = NOT(c2)
        #print("init", circuits[None])
        for var in c2.get_variables():
            #print("c2", var, "to", V(vmod(r, var[:-1]) + (var[-1], 0)))
            #print("cee", var, vmod(r, var[:-1]) + (var[-1], 0))
            substitute(circuits[None], var, V(vmod(r, var[:-2]) + var[-2:] + (0,)))
            #print(circuits[None])
            all_positions.add(rel_pos[:-2])
        #print(circuits)
        add_uniqueness_constraints(self.nodes, self.alph, circuits, all_positions)
        #print(circuits)
        #a = bbb

        #for k in circuits:
        #    print(k, circuits[k])
        #print("no22")
        m = SAT(AND(*(list(circuits.values()))), True)
        #print(AND(*(list(circuits.values()))))
        if m == False:
            return False
        #for t in sorted(m):
        #    print (t, m[t])
        return True

    def ball_forces_allowed(self, other, r):
        if len(self.alph) > 2:
            return self.ball_forces_allowed_big_alphabet(other, r)

        circuits = {}

        for v in centered_hypercube(self.dim, r):
            circuits[v] = self.circuit.copy()
            for var in self.circuit.get_variables():
                rel_pos = vadd(v, var[:-1]) + (var[-1], 0)
                substitute(circuits[v], var, V(rel_pos))
                #print(rel_pos)

        circuits[None] = NOT(other.circuit.copy())
        for var in other.circuit.get_variables():
            substitute(circuits[None], var, V(var + (0,)))

        #print("no22")
        m = SAT(AND(*(list(circuits.values()))))
        if m == False:
            return True
        return False
        
    def ball_forces_allowed_big_alphabet(self, other, r):
        all_positions = set()
        circuits = {}
        
        for v in onesided_hypercube(self.dim, r):
            circuits[v] = self.circuit.copy()
            for var in self.circuit.get_variables():
                rel_pos = vadd(v, var[:-2]) + var[-2:] + (0,)
                all_positions.add(rel_pos[:-3]) # drop node, letter and the zero
                substitute(circuits[v], var, V(rel_pos))
                #print(rel_pos)

        circuits[None] = NOT(other.circuit.copy())
        for var in other.circuit.get_variables():
            all_positions.add(var[:-2])
            substitute(circuits[None], var, V(var + (0,)))

        add_uniqueness_constraints(self.nodes, self.alph, circuits, all_positions)
            
        #print("no22")
        m = SAT(AND(*(list(circuits.values()))))
        if m == False:
            return True
        return False

    def deduce(self, known_values, domain):
        if len(self.alph) != 2:
            raise Exception("Only binary alphabets supported in deduce")
        if not (self.deftype & SFTType.CIRCUIT):
            raise Exception("SFT must have a circuit in deduce")
        
        circuits = {}
    
        for v in domain:
            circuits[v] = circuit.copy()
            for var in circuit.get_variables():
                # translate and add 0 at end so that we don't replace twice
                rel_pos = vadd(v, var[:-1]) + (var[-1], 0) 
                substitute(circuits[v], var, V(rel_pos))
                # print(circuits[v])

        forceds = set()
        for v in known_values:
            if known_values[v] == self.alph[1]:
                forceds.add(V(v + (0,)))
            else:
                forceds.add(NOT(V(v + (0,))))

        #print("no22")
        m = SAT(AND(*(list(circuits.values()) + list(forceds))), True)
        if m == False:
            return None
        #print(m)
        mm = {}
        for v in domain:
            for n in nodes:
                if v + (n, 0) in m:
                    mm[v + (n,)] = m[v + (n, 0,)]
                else:
                    mm[v + (n,)] = None # was not actually discussed by rules
        return mm

    def deduce_circuit(self):
        if self.circuit is None:
            if len(self.alph) == 2:
                anded = []
                for forb in self.forbs:
                    anded.append(OR(*((NOT(V(nvec)) if c else V(nvec))
                                      for (nvec, c) in forb.items())))
                self.circuit = AND(*anded)
            else:
                anded = []
                for forb in self.forbs:
                    anded.append(OR(*(NOT(V(nvec + (c,)))
                                      for (nvec, c) in forb.items())))
                self.circuit = AND(*anded)

    def deduce_forbs(self, domain=None):
        self.forbs = []
        self.deduce_forbs_(domain)
        # deduce forbs gives the forbs with true/false variables,
        # we want to simplify them into an alphabet size independent form
        self.clean_forbs()

    def clean_forbs(self):
        new_forbs = []
        for f in self.forbs:
            new_forb = {}
            for q in f:
                if len(self.alph) == 2:
                    if f[q]:
                        new_forb[q] = self.alph[1]
                    else:
                        new_forb[q] = self.alph[0]
                else:
                    if f[q]:
                        new_forb[q[:-1]] = q[-1]
            new_forbs.append(new_forb)
        self.forbs = new_forbs

    def deduce_forbs_(self, domain=None):
        verbose_deb = True
        if type(domain) == int:
            if len(self.alph) == 2:
                domain = [vec + (node,) for vec in centered_hypercube(self.dim, domain)
                          for node in self.nodes]
            else:
                domain = [vec + (node, a) for vec in centered_hypercube(self.dim, domain)
                          for node in self.nodes for a in self.alph]
        if domain is None:
            domain = list(self.circuit.get_variables())
        #assert len(self.alph) == 2
        if len(self.alph) == 2:
            for v in self.circuit.get_variables():
                #print(v, domain, self.dim)
                pass
            assert all(v in domain for v in self.circuit.get_variables())

        # we want to tile domain so that it has no existing forbos, but
        # the circuit fails at the origin
        complemented = NOT(self.circuit.copy())
        forbiddens = []
        for f in self.forbs:
            # anchor is just some position in domain of forbo (without node info)
            # which we will position in various places
            anchor = list(f)[0][:-1]
            for v in domain:
                for t in f:
                    if vadd(vsub(t[:-1], anchor), v) not in domain:
                        continue
                # we go here if the entire forbidden pattern translate fits in domain
                else:
                    # we make a circuit that says that we differ from the pattern somewhere
                    oreds = []
                    for t in f:
                        u = vadd(v, vsub(t[:-1], anchor)) + (t[-1],)
                        value = f[t]
                        if len(self.alph) == 2:
                            if value == self.alph[1]:
                                oreds.append(NOT(V(u)))
                            else:
                                oreds.append(V(u))
                        else:
                            oreds.append(NOT(V(u + (value,))))
                    forbiddens.append(OR(*oreds))

        if len(self.alph) != 2:
            add_uniqueness_constraints(self.nodes, self.alph, forbiddens, domain)

        m = SAT(AND(complemented, *forbiddens), True)
        if m == False:
            return None

        # we now know that m is a forbidden thingy
        # we then try to minimize it...
        minimal = {}
        for v in complemented.get_variables():
            minimal[v] = m[v]
        #print("minimizing", minimal)
        minimal = minimize_solution(complemented, minimal)
        #a = bbb

        print("new minimal", minimal)
        if verbose_deb and False: # todo
            assert len(self.alph) == 2
            forb_str = ""
            for t in sorted(minimal):
                 print(t, minimal[t])    
            

        self.forbs.append(minimal)
        
        self.deduce_forbs_(domain)

    def contains(self, other, limit = None, return_radius = False):
        r = 1
        while limit is None or r <= limit:
            if other.ball_forces_allowed(self, r):
                if return_radius:
                    return True, r
                return True
            if other.exists_periodic_not_in(self, r):
                if return_radius:
                    return False, r
                return False
            r += 1
        return None

    def equals(self, other, limit = None, return_radius = False):
        c12, rad = self.contains(other, limit, return_radius = True)
        if c12 == None:
            return None, limit
        elif c12 == False:
            return False, rad
        c21, rad2 = other.contains(self, limit, return_radius = True)
        if c21 == None:
            return None, limit
        return c21, max(rad, rad2)
