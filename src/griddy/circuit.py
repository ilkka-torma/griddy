"""
A Circuit is a trivial container for circuits with ONE output.
The initial inputs can be any Python objects or other Circuits.
You can use substitute to in-place set the value of an input.
In-place so that subexpressions can be handled efficiently.

You should only perform substitutions on a "top-level circuit"
and not share subexpressions between distinct top-level Circuits,
as you may not want their variables to mean the same.

Probably not parallelizable.
"""

#import ctypes

#def val_by_id(i):
#    return ctypes.cast(i, ctypes.py_object).value

from pysat.solvers import Glucose4
import time
#from circuitset import CircuitSet
import circuitset
import itertools as it
from general import *

def circuit(op, *inputs):
    c = Circuit(op, *inputs)
    if not hasattr(Circuit, "global_simplify"):
        Circuit.global_simplify = False
    #if Circuit.global_simplify:
    #    assert hasattr(Circuit, "global_simplify_threshold_min")
    if Circuit.global_simplify and Circuit.global_simplify_threshold_min <= c.complexity <= Circuit.global_simplify_threshold_max:
        #print("a")
        if Circuit.global_set == None:
            Circuit.global_set = circuitset.CircuitSet()
        added = Circuit.global_set.add(c)
        """
        if added != c:
            print(len(Circuit.global_set))
        else:
            print("new")
        """
        return added
    else:
        #if not Circuit.global_simplify:
        #    print("WHAT")
        #print("a")
        return c

class Circuit:
    smart_simplify = False
    #global_simplify = False
    #global_simplify_threshold_min = 10
    #global_simplify_threshold_max = 60
    global_set = None
    #internal_sweep_int = 1
    verbose = False
    def __init__(self, op, *inputs):
        self.op = op
        self.inputs = inputs
        #self.isi = 0
        self.complexity = 1
        for i in inputs:
            if type(i) == Circuit:
                self.complexity += i.complexity
        self.SAT = None
        self.TAUTO = None
        if Circuit.smart_simplify:
            self.simplify()
            
    def simplify(self):
        if self.op in "FT":
            return
        #print("a")
        
        if TAUTO(self):
            self.op = "T"
            self.inputs = []
            return
        #print("a")
        
        if UNSAT(self):
            self.op = "F"
            self.inputs = []
            return
        #print("a")
        if self.op == "&":
            #print("here")
            remove = []
            for i in range(len(self.inputs)):
                if self.inputs[i].SAT == None:
                    self.inputs[i].SAT = SAT(self.inputs[i])
                if self.inputs[i].SAT == False:
                    self.op = "F"
                    self.inputs = []
                    return
                #print("check tauto", self.inputs[i])
                if self.inputs[i].TAUTO == None:
                    self.inputs[i].TAUTO = TAUTO(self.inputs[i])
                #print("taauto", self.inputs[i].TAUTO)
                if self.inputs[i].TAUTO == True:
                    remove.append(i)
            #print(remove)
            for i in reversed(remove):
                self.inputs = self.inputs[:i] + self.inputs[i+1:]
            if len(self.inputs) == 0:
                self.op = "T"
                self.inputs = []
            #elif len(self.inputs) == 1: actually a bad idea!
            #    self.op = self.inputs[0].op
            #    self.inputs = self.inputs[0].inputs
        elif self.op == "|":
            #print("here")
            remove = []
            for i in range(len(self.inputs)):
                if self.inputs[i].TAUTO == None:
                    self.inputs[i].TAUTO = TAUTO(self.inputs[i])
                if self.inputs[i].TAUTO == True:
                    self.op = "T"
                    self.inputs = []
                    return
                if self.inputs[i].SAT == None:
                    self.inputs[i].SAT = SAT(self.inputs[i])
                if self.inputs[i].SAT == False:
                    remove.append(i)
                    
            for i in reversed(remove):
                self.inputs = self.inputs[:i] + self.inputs[i+1:]
            if len(self.inputs) == 0:
                self.op = "F"
                self.inputs = []

        elif self.op == "!":
            #print(str(self), "a")
            if self.inputs[0].SAT == None:
                self.inputs[0].SAT = SAT(self.inputs[0])
            if self.inputs[0].SAT == False:
                self.op = "T"
                self.inputs = []
                self.TAUTO = True
            if self.inputs[0].TAUTO == None:
                self.inputs[0].TAUTO = TAUTO(self.inputs[0])
            if self.inputs[0].TAUTO == True:
                self.op = "F"
                self.inputs = []
                self.SAT = False

    def __repr__(self):
        return str(self)
    def __str__(self):
        return "C" + tostr(self)
    def basic_str(self): # iirc for debug
        if self.op == "V":
            return str(self.inputs[0])
        if self.op == "!":
            return "!" + self.inputs[0].basic_str()
        return self.op + "(" + ", ".join(map(lambda a:a.basic_str(), self.inputs)) + ")"
        #return "circuit with inputs %s" % list(sorted(self.collect_inputs()))
    def collect_inputs(self, sofar = None):
        if sofar == None:
            sofar = set()
        for q in self.inputs:
            if isinstance(q, Circuit):
                q.collect_inputs(sofar)
            else:
                print(q)
                sofar.add(q)
        return sofar
    def copy(self, copies = None):
        if copies == None:
            copies = {}
        if id(self) in copies:
            return copies[id(self)]
        if self.op == "V":
            return V(*self.inputs)
        else:
            inputcopies = []
            for q in self.inputs:
                inputcopies.append(q.copy(copies))
            ret = Circuit(self.op, *inputcopies)
            copies[id(self)] = ret
            return ret
    def get_variables(self):
        return get_vars(self)
    def internal_nodes(self, vars_too=False):
        return int_nodes(self, vars_too)
        
    def get_id(self):
        if self.op == "V":
            return self.inputs[0]
        else:
            return id(self)
    #def __eq__(self, other):
    #    return models(self, other) and models(other, self)
    #def __hash__(self):
    #    return 0

    def nice_str(self, tab = 4, depth = 0, suppress_first = False, values = None):
        value = ""
        if values:
            # assume values is in the stupid format where V is suppressed in vars, and others are by their id...
            if self.op == "V":
                ss = self.inputs[0]
            else:
                ss = id(self)
            v = "T" if values[ss] else "F"
            value = v+"="
        if self.op == "V":
            ret = value + str(self) + "\n"
        elif self.op == "!":
            ret = value+"!" + self.inputs[0].nice_str(tab, depth+1, True, values)
        else:
            ret = value+self.op + " "*(tab-len(self.op)-len(value))
            for i, inp in enumerate(self.inputs):
                ret += inp.nice_str(tab, depth+tab, i == 0, values)
        if suppress_first:
            return ret
        else:
            return " "*depth + ret

#print(Circuit.global_simplify_threshold_min, Circuit.global_simplify_threshold_max)

def tostr(c):
    appearances = get_appearances(c)
    #print(appearances)
    appears_multiply = set()
    for d in appearances:
        if appearances[d] > 1:
            appears_multiply.add(d)
    #print(appears_multiply)
    #print(val_by_id(list(appears_multiply)[0]))
    return tostr_(c, appears_multiply)

def get_appearances(c, appearances = None):
    #print(type(c))
    if appearances == None:
        appearances = {}
    if c.op == "V":
        return appearances
    else:
        if id(c) not in appearances:
            appearances[id(c)] = 0
        appearances[id(c)] += 1
        #print("added app for %s = %s" % (c.basic_str(), id(c)))
        if appearances[id(c)] > 1:
            return appearances
        for q in c.inputs:
            get_appearances(q, appearances)
        return appearances
    
def tostr_(c, appears_multiply, alreadys = None, running = None):
    if alreadys == None:
        alreadys = {}
        running = [0]
    if c.op == "V":
        return "V" + str(c.inputs[0])
    if id(c) in alreadys:
        return "[" + alreadys[id(c)] + "]"
    if c.op != "!":
        s = c.op + "("
        first = True
        for i in c.inputs:
            if not first:
                s += ", "
            first = False
            s += tostr_(i, appears_multiply, alreadys, running)
        s += ")"
    else:
        s = c.op + tostr_(c.inputs[0], appears_multiply, alreadys, running)

    if id(c) in appears_multiply:    
        s = str(running[0]) + "=" + s
        alreadys[id(c)] = str(running[0])
        running[0] += 1
        return s
    
    return s

#kiliman = False

def evaluate(c, values):
    eve = c
    values = dict(values)
    c = Circuit.copy(c)
    for v in c.get_variables():
        if v not in values:
            values[v] = F
    values[None] = None
    for a in values:
        val = values[a]
        if val == False:
            val = F
        elif val == True:
            val = T
        substitute(c, a, val)
    if c.op == "T":
        return True
    elif c.op == "F":
        return False
    raise Exception("problem")

    

# substitute b for a in c, in place
def substitute(c, a, b):
    #print("sube")
    if type(a) == Circuit:
        assert a.op == "V"
        substitute(c, a.inputs[0], b)
        return
    #print(c, a, b)
    dealts = set()
    ##isi = Circuit.internal_sweep_int
    #Circuit.internal_sweep_int += 1
    substitute_(c, a, b, dealts)
    #print(c)

def substitute_(c, a, b, dealts):

    #print("subbin' %s for %s in %s" % (b, a, c))

    if c.op == "V":
        #print("circuit is V(", c.inputs, ")")
        if c.inputs[0] == a:
            #print("subbing", a)
            c.op = b.op
            c.inputs = b.inputs
        #else:
        #    print("not subbing", a)
        return
  
    elif c.op in "TF":
        return

    elif c in dealts:# .isi == isi: # already substituted
        return
    dealts.add(c)
    #c.isi = isi

    if c.op == "&":
        newinputs = []
        for q in c.inputs:
            substitute_(q, a, b, dealts)
            if type(q) != Circuit:
                newinputs.append(q)
            elif q.op == "T":
                pass
            elif q.op == "F":
                c.op = "F"
                c.inputs = []
                return
            else:
                newinputs.append(q)
        c.inputs = newinputs
        if len(c.inputs) == 0:
            c.op = "T"
            c.inputs = []
        #elif len(c.inputs) == 1: bad idea!
        #    c.op = c[0].op
        #    c.inputs = c[1].inputs
    elif c.op == "|":
        newinputs = []
        for q in c.inputs:
            substitute_(q, a, b, dealts)
            if type(q) != Circuit:
                newinputs.append(q)
            elif q.op == "F":
                pass
            elif q.op == "T":
                c.op = "T"
                c.inputs = []
                return
            else:
                newinputs.append(q)
        c.inputs = newinputs
        if len(c.inputs) == 0:
            c.op = "F"
            c.inputs = []
        #elif len(c.inputs) == 1: bad idea!
        #    c.op = c.inputs[0].op
        #    c.inputs = c.inputs[0].inputs
    elif c.op == "!":
        #print("here")
        assert len(c.inputs) == 1
        substitute_(c.inputs[0], a, b, dealts)
        if type(c.inputs[0]) != Circuit:
            newinputs.append(c.inputs[0])
        elif c.inputs[0].op == "T":
            c.op = "F"
            c.inputs = []
        elif c.inputs[0].op == "F":
            c.op = "T"
            c.inputs = []
        else:
            if type(c.inputs[0]) == Circuit and c.inputs[0].op == "!":
                c.op = c.inputs[0].inputs[0].op
                c.inputs = c.inputs[0].inputs[0].inputs
    else:
        raise NotImplementedError("Operator %s not implemented." % c.op)



# apply transformation to all variables of c, in place
def transform(c, f):
    #print("transforming", c)
    dealts = set()
    ##isi = Circuit.internal_sweep_int
    #Circuit.internal_sweep_int += 1
    transform_(c, f, dealts)
    #print(c)

def transform_(c, f, dealts):

    #print("subbin' %s for %s in %s" % (b, a, c))

    if c.op == "V":
        inputs = [f(a) for a in c.inputs]
        assert len(inputs) == 1
        # precisely the type of copying I wanted to avoid, but whatever
        if type(inputs[0]) == Circuit:
            c.op = inputs[0].op
            c.inputs = inputs[0].inputs
        else:
            c.inputs = inputs
        return
  
    elif c.op in "TF":
        return

    elif c in dealts:# .isi == isi: # already substituted
        return
    dealts.add(c)
    #c.isi = isi

    if c.op == "&":
        newinputs = []
        for q in c.inputs:
            transform_(q, f, dealts)
            if type(q) != Circuit:
                newinputs.append(q)
            elif q.op == "T":
                pass
            elif q.op == "F":
                c.op = "F"
                c.inputs = []
                return
            else:
                newinputs.append(q)
        c.inputs = newinputs
        if len(c.inputs) == 0:
            c.op = "T"
            c.inputs = []
        #elif len(c.inputs) == 1: bad idea!
        #    c.op = c[0].op
        #    c.inputs = c[1].inputs
    elif c.op == "|":
        newinputs = []
        for q in c.inputs:
            transform_(q, f, dealts)
            if type(q) != Circuit:
                newinputs.append(q)
            elif q.op == "F":
                pass
            elif q.op == "T":
                c.op = "T"
                c.inputs = []
                return
            else:
                newinputs.append(q)
        c.inputs = newinputs
        if len(c.inputs) == 0:
            c.op = "F"
            c.inputs = []
        #elif len(c.inputs) == 1: bad idea!
        #    c.op = c.inputs[0].op
        #    c.inputs = c.inputs[0].inputs
    elif c.op == "!":
        assert len(c.inputs) == 1
        transform_(c.inputs[0], f, dealts)
        if type(c.inputs[0]) != Circuit:
            newinputs.append(c.inputs[0])
        elif c.inputs[0].op == "T":
            c.op = "F"
            c.inputs = []
        elif c.inputs[0].op == "F":
            c.op = "T"
            c.inputs = []
        else:
            if type(c.inputs[0]) == Circuit and c.inputs[0].op == "!":
                c.op = c.inputs[0].inputs[0].op
                c.inputs = c.inputs[0].inputs[0].inputs
    else:
        raise NotImplementedError("Operator %s not implemented." % c.op)

def get_vars(c):
    #print("Kemme", type(c), c.op, c.inputs)
    #isi = Circuit.internal_sweep_int
    #Circuit.internal_sweep_int += 1
    dealts = set()
    return get_vars_(c, dealts)

def get_vars_(c, dealts):
    if c in dealts: #.isi == isi:
        return set()
    #c.isi = isi
    dealts.add(c)
    
    if c.op == "V":
        return set([c.inputs[0]])
    else:
        s = set()
        for t in c.inputs:
            #print(t)
            s.update(get_vars_(t, dealts))
        return s

def int_nodes(c, vars_too=False):
    #isi = Circuit.internal_sweep_int
    #Circuit.internal_sweep_int += 1
    dealts = set()
    return int_nodes_(c, dealts, vars_too)

def int_nodes_(c, dealts, vars_too):
    #if c.isi == isi:
    #    return list()
    if c not in dealts:
        dealts.add(c)
        #c.isi = isi
    
        if c.op != "V":
            for t in c.inputs:
                for node in int_nodes_(t, dealts, vars_too):
                    yield node
            yield c
        elif vars_too:
            yield c

def LDAC(n):
    if type(n) != int:
        n = len(n)
    return lambda a: last_diff_and_count(a, (lambda m:m)(n))

# given a circuit whose variables are tuples,
# construct a circuit that states that last values
# are different, and if we reach count, then one should
# be true
# of course very specific to our coding of 
def last_diff_and_count(circs, count):
    #print(count, list(map(str, circs)))
    lasts = {}
    for c in circs:
        for v in c.get_variables():
            #print(v)
            if v[:-1] not in lasts:
                lasts[v[:-1]] = set()
            lasts[v[:-1]].add(v)
    newlasts = {} # change to variables
    for l in lasts:
        newlasts[l] = list(map(lambda a : V(a), lasts[l]))
    lasts = newlasts
    andeds = []
    for l in lasts:
        #print("lasts", l, lasts[l])
        if len(lasts[l]) > 1:
            #print(l, "yers")
            if len(lasts[l]) == count:
                andeds.append(AND(ATMOSTONE(*lasts[l]), OR(*lasts[l])))
            else:
                andeds.append(ATMOSTONE(*lasts[l]))
    #for a in andeds:
    #    print(str(a))
    return AND(*andeds)

# same sa LDAC, but the alphabet size (or set) is a function
# that gives alphabets or their cardinalities
def LDAC2(alphabet_func):
    #print("LDAC2 called with", alphabet_func)
    def leng(a):
        if type(a) == int:
            return a
        return len(a)
    af = lambda a:leng(alphabet_func(a))
    return lambda a: last_diff_and_count2(a, af)

# given a circuit whose variables are tuples,
# construct a circuit that states that last values
# are different, and if we reach count, then one should
# be true
# of course very specific to our coding of 
def last_diff_and_count2(circs, count):
    #print("ldac2 called with count", count)
    #print(count, list(map(str, circs)))
    # lasts is a dict of nvec -> set(var)
    lasts = {}
    for c in circs:
        #print(type(c))
        #print(c.op)
        #print(type(c.inputs[0]))
        #print(c.inputs[0].inputs[0].op)
        for v in c.get_variables():
            #print(v)
            if v[:-1] not in lasts:
                lasts[v[:-1]] = set()
            lasts[v[:-1]].add(v)
    #print("ijrjf")
    #print(lasts)
    newlasts = {} # change to variables
    for l in lasts:
        newlasts[l] = list(map(lambda a : V(a), lasts[l]))
    # lasts is now a dict of nvec -> set(V(var))
    lasts = newlasts
    andeds = []
    for l in lasts:
        if len(lasts[l]) > 1:
            if len(lasts[l]) == count(l):
                andeds.append(AND(ATMOSTONE(*lasts[l]), OR(*lasts[l])))
            else:
                andeds.append(ATMOSTONE(*lasts[l]))
    return AND(*andeds)


# copied from models
# TODO: rewrite
def circuit_to_sat_instance_good(circ, var_to_name, next_name=None):
    sm = Circuit.smart_simplify
    Circuit.smart_simplify = False
    if next_name is None:
        next_name = 1
    else:
        # next_name could be returned from a call to this,
        # and thus be the negation of something, in which case
        # I wouldn't trust it was incremented correctly
        assert next_name > 0

    variables = circ.get_variables()
    
    for v in variables:
        if v not in var_to_name:
            var_to_name[v] = next_name
        next_name += 1
    if circ.op == "V":
        if id(circ) not in var_to_name:
            var_to_name[id(circ)] = var_to_name[circ.inputs[0]]

    clauses = []
    # NB. it's a children-before-parents ordering
    for q in circ.internal_nodes():
        assert q.op != "V"
        if id(q) in var_to_name: continue
        # we usually use a new name, although ! will cancel
        var_to_name[id(q)] = next_name
        inps = []
        for i in q.inputs:
            if i.op == "V":
                inps.append(var_to_name[i.inputs[0]])
            else:
                inps.append(var_to_name[id(i)])
        #print(q.op, len(inps))
        if q.op == "!":
            #nam = inps[0]
            #clauses.append([nam, next_name])
            #clauses.append([-nam, -next_name])
            # trivial optimization, we just use the negation directly
            var_to_name[id(q)] = -inps[0]
            next_name -= 1
        elif q.op == "&":
            for inp in inps:
                clauses.append([inp, -next_name])
            clauses.append(list([-inp for inp in inps]) + [next_name])
        elif q.op == "|":
            for inp in inps:
                clauses.append([-inp, next_name])
            clauses.append(inps + [-next_name])
        elif q.op == "T":
            clauses.append([var_to_name[id(q)]])
        elif q.op == "F":
            clauses.append([-var_to_name[id(q)]])
        else:
            raise Exception("nope")
        next_name += 1
    
    Circuit.smart_simplify = sm
    # return the clauses, and the name of the last clause, which corresponds to the actual circuit value
    # this can be negated (minus), 
    top_name = next_name - 1
    # double nots are impossible, so not at top level means that top is negation of variable in input
    if circ.op == "!": top_name = -top_name
    return clauses, top_name

def circuit_to_sat_instance(circ, var_to_name, next_name=None):
    sm = Circuit.smart_simplify
    Circuit.smart_simplify = False
    if next_name is None:
        next_name = 1

    variables = circ.get_variables()
    
    for v in variables:
        if v not in var_to_name:
            var_to_name[v] = next_name
            next_name += 1
    if circ.op == "V":
        if id(circ) not in var_to_name:
            var_to_name[id(circ)] = var_to_name[circ.inputs[0]]

    clauses = []
    for q in circ.internal_nodes(): 
        assert q.op != "V"
        # it seems we are calling this many times, and encountering the same subcircuit;
        # then we have a variable for this already
        if id(q) in var_to_name: continue
        var_to_name[id(q)] = next_name
        inps = []
        for i in q.inputs:
            if i.op == "V":
                inps.append(var_to_name[i.inputs[0]])
            else:
                inps.append(var_to_name[id(i)])
        #print(q.op, len(inps))
        if q.op == "!":
            nam = inps[0]
            clauses.append([nam, next_name])
            clauses.append([-nam, -next_name])
        elif q.op == "&":
            for inp in inps:
                clauses.append([inp, -next_name])
            clauses.append(list([-inp for inp in inps]) + [next_name])
        elif q.op == "|":
            for inp in inps:
                clauses.append([-inp, next_name])
            clauses.append(inps + [-next_name])
        # these should be optimized away anyway except at root, so no worries that they are inefficient
        elif q.op == "T": 
            clauses.append([var_to_name[id(q)]])
        elif q.op == "F":
            clauses.append([-var_to_name[id(q)]])
        else:
            raise Exception("nope")
        next_name += 1
    
    Circuit.smart_simplify = sm
    return clauses, next_name-1

def solver_process(circ, ret_assignment=False):
    "A generator for repeatedly checking satisfiability with different initial assignments"
    var_to_name = dict()
    clauses, next_name = circuit_to_sat_instance(circ, var_to_name)
    clauses.append([next_name])
    # Get a first batch of values (dict of varname : bool)
    values = yield None
    with Glucose4(bootstrap_with=clauses) as solver:
        while True:
            #print("solver got", values, "has var_to_name",
            #      {v : n for (v,n) in var_to_name.items() if type(v) != int})
            assum = [(-1)**(1-val) * var_to_name[var]
                     for (var, val) in values.items()
                     if var in var_to_name]
            res = solver.solve(assumptions=assum)
            if res:
                if ret_assignment:
                    model = solver.get_model()
                    out_values = {name : m[abs(var_to_name[var])-1] > 0
                                  for (var, name) in var_to_name.items()}
                    values = yield out_values
                else:
                    values = yield True
            else:
                if ret_assignment:
                    values = yield None
                else:
                    values = yield False

def projections(circ, the_vars):
    "All possible satisfiable values of the given variables"
    #print(circ)
    var_to_name = dict()
    clauses, next_name = circuit_to_sat_instance(circ, var_to_name)
    clauses.append([next_name])
    circ_vars = circ.get_variables()
    used = [var for var in the_vars if var in circ_vars]
    unused = [var for var in the_vars if var not in circ_vars]
    #print("names", var_to_name)
    #print("names", [(x,y) for (x,y) in var_to_name.items() if type(x) == tuple])
    #print("clauses", clauses)
    with Glucose4(bootstrap_with=clauses) as s:
        while s.solve():
            m = s.get_model()
            #print(m)
            base = {var : (m[abs(var_to_name[var])-1] > 0)
                    for var in used}
            for boolvec in iter_prod(*(iter([False,True]) for _ in range(len(unused)))):
                for (var, val) in zip(unused, boolvec):
                    base[var] = val
                yield base
            #print("adding clause", [-m[abs(var_to_name[var])-1] for var in the_vars])
            s.add_clause([-m[abs(var_to_name[var])-1] for var in used])

"""
models_under tells whether C1 being true implies C2 is true,
assuming the constraints given by under hold.
Here, under is a function that gives constraints given a bunch of circuits.
Note that
a -> (b -> c)
<==>
!a | (!b | c)
<==>
(!a | !b) | c
<==>
!(a & b) | c
<==>
a & b -> c
"""
def models_under(C1, C2, under, return_sep = False):
    sm = Circuit.smart_simplify
    Circuit.smart_simplify = False
    if type(C1) != Circuit:
        C1 = AND(*C1)
    if type(C2) != Circuit:
        C2 = AND(*C2)
    Circuit.smart_simplify = sm

    C1 = AND(C1, under([C1, C2]))

    return models(C1, C2, return_sep)

"""
C1 and C2 are lists of circuits
we want to know if it is possible to
satisfy C1 so that C2 is not satisfied...
in other words, we want to know whether C1 \models C2.

We should find all variables in C1 and C2, and
they will be variables 1 through n.
Then for each internal node in Ci, we add a
variable, and depending on the .op, we force its
value.

Finally, we force that the variables corresponding
to top levels of C1 circuits have value 1, but
some C2 value has 0...
"""
def models(C1, C2, return_sep = False):
    sm = Circuit.smart_simplify
    Circuit.smart_simplify = False
    if type(C1) != Circuit:
        C1 = AND(*C1)
    if type(C2) != Circuit:
        C2 = AND(*C2)
        
    Circuit.smart_simplify = sm
    variables = set(C1.get_variables())
    variables.update(set(C2.get_variables()))
    """
    next_name = 1
    var_to_name = {}
    clauses = []
    for v in variables:
        var_to_name[v] = next_name
        next_name += 1
    if C1.op == "V":
        var_to_name[id(C1)] = var_to_name[C1.inputs[0]]
    if C2.op == "V":
        var_to_name[id(C2)] = var_to_name[C2.inputs[0]]
    seen = set()
    for q in it.chain(C1.internal_nodes(), C2.internal_nodes()):
        if q in seen:
            continue
        seen.add(q)
        assert q.op != "V"
        var_to_name[id(q)] = next_name
        inps = []
        for i in q.inputs:
            if i.op == "V":
                inps.append(var_to_name[i.inputs[0]])
            else:
                inps.append(var_to_name[id(i)])
        if q.op == "!":
            nam = inps[0]
            clauses.append([nam, next_name])
            clauses.append([-nam, -next_name])
        elif q.op == "&":
            for inp in inps:
                clauses.append([inp, -next_name])
            clauses.append(list([-inp for inp in inps]) + [next_name])
        elif q.op == "|":
            for inp in inps:
                clauses.append([-inp, next_name])
            clauses.append(inps + [-next_name])
        elif q.op == "T":
            clauses.append([var_to_name[id(q)]])
        elif q.op == "F":
            clauses.append([-var_to_name[id(q)]])
        else:
            raise Exception("nope")
        next_name += 1
    clauses.append([var_to_name[id(C1)]])
    clauses.append([-var_to_name[id(C2)]])
    Circuit.smart_simplify = sm
    """

    var_to_name = {}
    clauses, next_name = circuit_to_sat_instance_good(C1, var_to_name)
    clauses.append([var_to_name[id(C1)]])
    clauses2, _ = circuit_to_sat_instance_good(C2, var_to_name, abs(next_name) + 1)
    clauses.extend(clauses2)
    clauses.append([-var_to_name[id(C2)]])
    
    with Glucose4(bootstrap_with=clauses) as s:
        if s.solve():
            if return_sep:
                m = s.get_model()
                #print(m)
                varvals = {}
                for v in variables:
                    if m[var_to_name[v] - 1] > 0:
                        varvals[v] = True
                    else:
                        varvals[v] = False
                return varvals
            return False
        return True

# can both change c and return something different...
# use only on top level
def tech_simp(c, dones = None):
    if type(c) != Circuit:
        return c
    if dones == None:
        dones = set()
    if c in dones:
        return c
    if c.op in "&|" and len(c.inputs) == 1:
        return tech_simp(c.inputs[0])
    else:
        newinputs = []
        for i in c.inputs:
            newinputs.append(tech_simp(i))
        c.inputs = newinputs
    dones.add(c)
    return c

def UNSAT_under(C, under, return_sep = False):
    m = models_under(C, F, under, return_sep)
    if not return_sep:
        return m
    else:
        if m == True:
            return True
        else:
            return m

def UNSAT(C, return_sep = False):
    m = models(C, F, return_sep)
    if not return_sep:
        return m
    else:
        if m == True:
            return True
        else:
            return m

def SAT_under(C, under, return_model = False):
    if not return_model:
        return not UNSAT_under(C, under)
    else:
        m = UNSAT_under(C, under, True)
        if m == True:
            return False
        return m
        
def SAT(C, return_model = False):
    if not return_model:
        return not UNSAT(C)
    else:
        m = UNSAT(C, True)
        if m == True:
            return False
        return m


    
        
        
def TAUTO(C):
    #print(C)
    """sm = Circuit.smart_simplify
    Circuit.smart_simplify = False
    C = NOT(C)
    Circuit.smart_simplify = sm
    """
    return models(T, C)

def equivalent_under(C1, C2, under, return_sep = False):
    m = models_under(C1, C2, under, return_sep)
    #print(C1, C2, m)
    if m != True:
        return m
    return models_under(C2, C1, under, return_sep)

def equivalent(C1, C2, return_sep = False):
    m = models(C1, C2, return_sep)
    #print(C1, C2, m)
    if m != True:
        return m
    return models(C2, C1, return_sep)

def V(inputs):
    return Circuit("V", inputs)
def AND(*inputs):
    #print("ahem", inputs)
    if len(inputs) == 1:
        #print(type(inputs[0]))
        assert type(inputs[0]) == Circuit
        return inputs[0]
    if len(inputs) == 0:
        return T
    if F in inputs:
        return F
    if all(x==T for x in inputs):
        return T
    if None in inputs:
        return None
    #print(Circuit.smart_simplify)
    #print("making ADN", list(map(str, inputs)))
    #print("res", Circuit("&", *inputs))
    andeds = []
    for inp in inputs:
        if inp == T:
            continue
        if inp == F:
            return F
        if inp.op == "&":
            andeds.extend(inp.inputs)
        elif inp not in andeds:
            andeds.append(inp)
    if len(andeds) == 1:
        return andeds[0]
    return circuit("&", *andeds)

def OR(*inputs):
    if len(inputs) == 1:
        assert type(inputs[0]) == Circuit
        return inputs[0]
    if len(inputs) == 0:
        return F
    if T in inputs:
        return T
    if all(x==F for x in inputs):
        return F
    if None in inputs:
        return None
    oreds = []
    for inp in inputs:
        if inp == T:
            return T
        if inp == F:
            continue
        if inp.op == "|":
            oreds.extend(inp.inputs)
        elif inp not in oreds:
            oreds.append(inp)
    if len(oreds) == 1:
        return oreds[0]
    return circuit("|", *inputs)
def NOT(*inputs):
    #print(inputs)
    assert len(inputs) == 1
    if inputs[0] == None:
        return None
    if inputs[0] == T:
        return F
    if inputs[0] == F:
        return T
    if inputs[0].op == "!":
        return inputs[0].inputs[0]
    return circuit("!", *inputs)
T = circuit("T")
F = circuit("F")
def IMP(*inputs):
    assert len(inputs) == 2
    # while
    #print(inputs)
    if inputs[0] == None:
        return None
    if inputs[0] == F:
        return T
    if inputs[1] == None:
        return None
    return OR(NOT(inputs[0]), inputs[1])
    #return Circuit("->", *inputs)
def IFF(*inputs):
    assert len(inputs) == 2
    return OR(AND(inputs[0], inputs[1]), AND(NOT(inputs[0]), NOT(inputs[1])))
    #return AND(IMP(inputs[0], inputs[1]), IMP(inputs[1], inputs[0]))
def XOR(*inputs):
    if len(inputs) == 1:
        assert type(inputs[0]) == Circuit
        return inputs[0]
    if len(inputs) == 0:
        return F
    #assert len(inputs) == 2 # I just didn't bother to implement in general
    if len(inputs) > 2:
        left = inputs[:len(inputs)//2]
        right = inputs[len(inputs)//2:]
        return XOR(XOR(*left), XOR(*right))
    return AND(OR(*inputs), NOT(AND(*inputs)))
    #return Circuit("<->", *inputs)
# this is just used for small sets when we have larger than binary alphabets;
# note that for very large alphabets one should instead use
# smth like binary configurations written in N
def ATMOSTONE(*inputs):
    inps = []
    for a in range(len(inputs)):
        for b in range(a+1, len(inputs)):
            inps.append(OR(NOT(inputs[a]), NOT(inputs[b])))
    return AND(*inps)


#c = OR(AND(V("b"), V("a")), NOT(V("b")), NOT(V("b")))
#print(evaluate(c, {"a": True, "b": True}))


#print(evaluate(V("a"), {}))
#a = bbb

#equivalent(F, T)

#print(TAUTO(NOT(T)))

#a = V("a")
#print(SAT(a))
#print(SAT(V("a"), True))


#c = OR(T)

#3AND(Circuit("T"), Circuit("T"))
#print(models(T, Circuit("T")))
    
"""
c = OR(OR(V("a"), V("b")), V("a"))
cc = AND(c, c, c, c, c, c, c, c, c)
qq = cc.copy()
print(cc)
substitute(cc, "a", T)
print(cc)
print(qq)
substitute(qq, "a", T)
print(qq)
"""

"""
t = time.time()
a = OR(V("a"), V("b"), V("c"))
b = AND(OR(V("b"), V("a")), V("c"))
print(models([a], [b]))
print (time.time() - t)
"""

