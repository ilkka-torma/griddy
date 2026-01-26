from general import *

"""
a Graph has 
 * origin()
 * should implement iterator for getting all cells, to use as default
 * generators -- always positive generators,
   we use (gen, 1), (gen, -1) for pos and neg
 * move(node, generator)
can have
 * move_rel that takes cell c and an offset cell c'. If c' = o.m,
 this is supposed to return c.m. This makes sense for Cayley graphs of monoids.
 * moves_to that takes cell c and gives moves from origin to c
"""
class Graph:
    #def origin(self): raise NotImplemented("origin not implemented.")
    #def __iter__(self): raise NotImplemented("__iter__ not implemented.")
    #def moves(self): raise NotImplemented("generators not implemented.")
    #def move(self, cell, generator): raise NotImplemented("move not implemented.")
    #def has_cell(self, cell):
    # by default just check if it's one of the moves in general
    def has_move(self, cell, generator): return generator in self.moves()
    def ball(self, rad):
        b = set([self.origin()])
        frontier = set(b)
        for i in range(rad):
            newfrontier = set()
            for f in frontier:
                for g in self.moves():
                    for candidate in [self.move(f, (g, 1)), self.move(f, (g, -1))]:
                        if candidate not in b:
                            newfrontier.add(candidate)
                            b.add(candidate)
            frontier = newfrontier
        return b

class TrivialGroup(Graph):
    def __init__(self, generators):
        self.generators = generators
    def origin(self):
        return ""
    def move(self, cell, generator):
        return cell
        
def sign(i):
    if i == 0:
        return 0
    elif i < 0:
        return -1
    else:
        return 1

class AbelianGroup(Graph):
    def __init__(self, generators):
        self.generators = list(generators)
        self.dim = len(generators)
    def origin(self):
        return (0,)*self.dim
    def from_vector(self, v):
        assert len(v) == self.dim
        return tuple(v)
    def has_cell(self, cell):
        return type(cell) == tuple and all(map(lambda a:type(a) == int, cell)) and len(cell) == self.dim
    def move(self, cell, generator):
        gen, power = generator
        idx = self.generators.index(gen)
        return cell[:idx] + (cell[idx]+power,) + cell[idx+1:]
    def moves(self):
        return self.generators
    # move to cell that is at offset relative to the input cell
    def move_rel(self, cell, offset):
        return vadd(cell, offset)
    def move_relative(self, cell):
        gen, power = generator
        idx = self.generators.index(gen)
        return cell[:idx] + (cell[idx]+power,) + cell[idx+1:]
    def moves_to(self, cell):
        ret = []
        for d,i in enumerate(cell):
            for j in range(abs(i)):
                ret.append((generators[d], sign(i)))
        return ret
    # note that generators can also return True here, currently very fragile
    def is_cell(self, cell):
        return isinstance(cell, tuple) and len(cell) == self.dim
    def __repr__(self):
        return "Abelian group with generators {}".format(self.generators)
    def __eq__(self, other):
        if not isinstance(other, AbelianGroup):
            return False
        return self.generators == other.generators
    #def __iter__(self):
    
# turn a Griddy topology into a graph
"""
def TopologyGraph(Graph):
    def __init__(self, dim, nodes, topology):
        self.generators = list(t[0] for t in topology)
    def origin(self):
        return (0,)*dim + self.first
    def 
      
    
 * origin()
 * should implement iterator for getting all cells, to use as default
 * generators -- always positive generators,
   we use (gen, 1), (gen, -1) for pos and neg
 * move(node, generator)
    CR4d8e2_nodes = sft.Nodes(["big", "small"])
    CR4d8e2_topology = [('N', (0, 0, 'big'), (0, 1, 'small')),
                    ('NE', (0, 0, 'big'), (1, 1, 'big')),
                    ('E', (0, 0, 'big'), (0, 0, 'small')),
                    ('SE', (0, 0, 'big'), (0, -1, 'big')),
                    ('S', (0, 0, 'big'), (-1, -1, 'small')),]
 """

# reduce from the right as much as you can; could just be once since we apply it each time
def free_simplify(word):
    if len(word) < 2:
        return word
    word = free_simplify(word[:-1]) + word[-1]
    if len(word) > 1 and inverses(word[-1], word[-2]):
        word = word[:-2]
    return word

# reduce from the right as much as you can; could just be once since we apply it each time
def free_simplify2(word, involutions):
    if len(word) < 2:
        return word
    word = free_simplify2(word[:-1], involutions) + word[-1]
    if len(word) > 1 and inverses2(word[-1], word[-2], involutions):
        word = word[:-2]
    return word

def inverses(a, b):
    return a.islower() != b.islower() and a.lower() == b.lower()

def inverses2(a, b, involutions):
    if a in involutions:
        return a.lower() == b.lower()
    return a.islower() != b.islower() and a.lower() == b.lower()

def inverse(a):
    if a.islower():
        return a.upper()
    return a.lower()

def inverse2(a, involutions):
    if a.lower() in involutions:
        return a.lower()
    if a.islower():
        return a.upper()
    return a.lower()

# generators in one case
def reduced_words(generators, l):
    if l == 0:
        yield ""
        return
    if l == 1:
        for g in generators:
            yield g
            yield inverse(g)
        return
    for r in reduced_words(generators, l-1):
        for g in [h for h in generators] + [inverse(h) for h in generators]:
            if not inverses(g, r[-1]):
                yield r + g
                
    

"""
Cells are (H, V) where H is a word over horizontal generators
and V is a word over vertical generators. We assume lower and upper case are
inverses. To multiply by horizontal generator, just join to horizontal
on the right. To multiply by vertical, use tiles to commute.
"""
class SquareComplex(Graph):
    # tiles are ENWS-quadruples, which should be
    # 4-way deterministic complete Wang tile set
    def __init__(self, tiles):
        E_colors = set([t[0].lower() for t in tiles])
        N_colors = set([t[1].lower() for t in tiles])
        W_colors = set([t[2].lower() for t in tiles])
        S_colors = set([t[3].lower() for t in tiles])
        assert E_colors == W_colors
        assert N_colors == S_colors
        assert E_colors.intersection(N_colors) == set()
        # note that E-sided edge is indeed vertical in the square
        self.V_colors = E_colors
        self.H_colors = N_colors
        self.tiles = tiles
    def origin(self):
        return ("", "")
    # we accept also upper case as move.
    def has_move(self, cell, m):
        return m.lower() in self.moves() or m.upper() in self.moves()
    def has_cell(self, cell):
        return type(cell) == tuple and len(cell) == 2 and \
               all(a in self.V_colors for a in cell[0]) and all(a in self.H_colors for a in cell[1])
    def is_cell(self, cell):
        return isinstance(cell, tuple) and len(cell) == 2 and isinstance(cell[0], str) and isinstance(cell[1], str)
    def moves(self):
        return set(self.V_colors) | set(self.H_colors)
    def move(self, cell, generator):
        generator, power = generator
        if power == -1:
            generator = inverse(generator)
        if generator.lower() in self.H_colors:
            return cell[0], free_simplify(cell[1] + generator)
        newh = ""
        for c in reversed(cell[1]): # go over horizontals of cell
            for t in self.tiles: # should be look-up, but this shouldn't be time-critical
                # if a tile actually has these as SE, take corresponding WN
                if t[3] == c and t[0] == generator:
                    newh = t[1] + newh
                    generator = t[2]
                    break
                if t[1] == c and inverses(t[0], generator):
                    newh = t[3] + newh
                    generator = inverse(t[2])
                    break
                if inverses(t[3], c) and t[2] == generator:
                    newh = inverse(t[1]) + newh
                    generator = t[0]
                    break
                if inverses(t[1], c) and inverses(t[2], generator):
                    newh = inverse(t[3]) + newh
                    generator = inverse(t[0])
                    break
            else:
                raise Exception("Move by %s failed in square complex at %s." % (generator, cell))
        return free_simplify(cell[0] + generator), newh
    def move_rel(self, cell, offset):
        #print("move_rel", cell, offset)
        for s in offset[0] + offset[1]:
            cell = self.move(cell, (s, 1))
        return cell


"""
Like SquareComplex, but allows involutions.
"""
class SquareComplex2(Graph):
    # tiles are ENWS-quadruples, which should be
    # 4-way deterministic complete Wang tile set
    def __init__(self, tiles, involutions):
        E_colors = set([t[0].lower() for t in tiles])
        N_colors = set([t[1].lower() for t in tiles])
        W_colors = set([t[2].lower() for t in tiles])
        S_colors = set([t[3].lower() for t in tiles])
        print(E_colors, W_colors)
        assert E_colors == W_colors
        assert N_colors == S_colors
        assert E_colors.intersection(N_colors) == set()
        self.involutions = involutions
        # note that E-sided edge is indeed vertical in the square
        self.V_colors = E_colors
        self.H_colors = N_colors
        self.tiles = tiles
    def origin(self):
        return ("", "")
    # we accept also upper case as move.
    def has_move(self, cell, m):
        return m.lower() in self.moves() or m.upper() in self.moves()
    def has_cell(self, cell):
        return type(cell) == tuple and len(cell) == 2 and \
               all(a in self.V_colors for a in cell[0]) and all(a in self.H_colors for a in cell[1])
    # seems this is just the type check
    def is_cell(self, cell):
        return isinstance(cell, tuple) and len(cell) == 2 and \
            isinstance(cell[0], str) and isinstance(cell[1], str)
    def moves(self):
        return set(self.V_colors) | set(self.H_colors)
    def move(self, cell, generator):
        print("cell", cell, generator)
        generator, power = generator
        if power == -1:
            generator = inverse2(generator, self.involutions)
        if generator.lower() in self.H_colors:
            return cell[0], free_simplify2(cell[1] + generator, self.involutions)
        print("here", generator)
        newh = ""
        for c in reversed(cell[1]): # go over horizontals of cell
            nextgenerator = None
            for t in self.tiles: # should be look-up, but this shouldn't be time-critical
                #print(cell, generator, t)
                # if a tile actually has these as SE, take corresponding WN
                if t[3] == c and t[0] == generator:
                    newh = t[1] + newh
                    assert nextgenerator == None
                    nextgenerator = t[2]
                    #break
                elif t[1] == c and inverses2(t[0], generator, self.involutions):
                    newh = t[3] + newh
                    assert nextgenerator == None
                    nextgenerator = inverse2(t[2], self.involutions)
                    #break
                elif inverses(t[3], c) and t[2] == generator:
                    newh = inverse2(t[1], self.involutions) + newh
                    assert nextgenerator == None
                    nextgenerator = t[0]
                    #break
                elif inverses(t[1], c) and inverses(t[2], generator, self.involutions):
                    newh = inverse2(t[3], self.involutions) + newh
                    assert nextgenerator == None
                    nextgenerator = inverse2(t[0], self.involutions)
                    #break
                #print(newh, nextgenerator
            if nextgenerator == None:
                print("derp")
            #else:
            #    raise Exception("Move by %s failed in square complex at %s." % (generator, cell))
            generator = nextgenerator
        print("mm")
        return free_simplify2(cell[0] + generator, self.involutions), newh
    def move_rel(self, cell, offset):
        #print("move_rel", cell, offset)
        for s in offset[0] + offset[1]:
            print("from",cell, s)
            cell = self.move(cell, (s, 1))
            print("to", cell)
        return cell

# IMPLEMENTATION IS BROKEN SINCE NEGATIVES GO FORWARD,
# THESE ARE GOING TO BE REMOVED LATER, HOWEVER, SO WE DON'T CARE
class Subgroup:
    def __init__(self, group, generators):
        self.supergroup = group
        self.generators = dict(generators)
    def origin(self):
        return self.supergroup.origin()
    # we accept also upper case as move.
    def has_move(self, cell, m):
        return m in self.generators
    def is_cell(self, cell):
        #print(cell, "test")
        return self.supergroup.is_cell(cell) # best we can do, correct type check at least
        #raise Exception("Membership in subgroup cannot be checked.")
    #def is_cell(self, cell):
        #return True
        #raise Exception("Membership in subgroup cannot be checked.")
    def moves(self):
        return set([g for g in self.generators])
    # we only do moves forward... we're planning to disallow inverses anyway!!
    def move(self, cell, generator):
        #if generator[1] == -1:
        # return None
        try:
            ret = self.supergroup.move_rel(cell, self.generators[generator[0]])
        except:
            #print(cell, self.generators[generator[0]])
            print(cell, self.generators[generator[0]])
            a = Bbb
        if ret == None:
            
            print(ret)
        return ret
    def move_rel(self, cell, offset):
        print(cell, offset,"moverel")
        return self.supergroup.move_rel(cell, offset)
        

# taken from Laurent's paper;
# byay are the list in ENWS order of the colors, oriented northeast!
# so actually the horizontals (every second) are inverted...
# I think it's the same as saying by = ya though by flipping y and Y
# so it's really that byAY relation translated to byay... we should just
# list relations of course, but for now it is what it is...
Aleshin = SquareComplex(["byay", "axby", "cxcy", "bxax", "cybx", "aycx"])

# from paper of Radu, a_1a_2a_3 = abc, b_1b_2b_3 = xyz
SC_F661 = SquareComplex([# the ones same for all
                         "axbX", "ayBy", "aYbx", "aXbY",
                         # specific to 661
                         "azAZ", "aZAz", "bzBZ", "bZCz", 
                         "cxcx", "cyCZ", "cYCy"])

invs = ["a","b","c","d","x","y","z","p","q"]
# no flips, since everything here is involution
SC_G451 = SquareComplex2(["axax", "ayay", "azbz", "bxbx", "bycy", "cxcz",
                          "apap", "aqaq", "bpbq", "cpcp", "cqdq", "dxdy", "dzdp"],
                         involutions = invs)



print(SC_G451.move_rel(('', 'zy'), ('ac', '')))

# the simple subgroup
newgens = []
for a in "abcd":
    for b in "abcd":
        if a != b:
            newgens.append((a+b, (a+b, "")))
for x in "xyzpq":
    for y in "xyzpq":
        if x != y:
            newgens.append((x+y, ("", x+y)))
#print(len(newgens))
SC_G451_smp = Subgroup(SC_G451, newgens)

o = SC_G451_smp.origin()
#('', 'zy') ('ac', 1) ('ac', '')
o = SC_G451_smp.move(o, ("zy", 1))
o = SC_G451_smp.move(o, ("ac", 1))
print(o)


"""
elem = SC_G451_smp.origin()
print(elem)
elem = SC_G451_smp.move(elem, ("ab", 1))
print(elem)
elem = SC_G451_smp.move(elem, ("yx", 1))
print(elem)
elem = SC_G451_smp.move(elem, ("ab", 1))
print(elem)
elem = SC_G451_smp.move(elem, ("ba", 1))
print(elem)
"""


"""
o = Aleshin.origin()
print(o)
for q in "abaxXybaBx":
    o = Aleshin.move(o, (q, 1))
    print("move", q, "now", o)
"""

"""
# this tests correct count in Aleshin
rr = 7
c = 0
for b in Aleshin.ball(rr):
    c += 1
print(c)
c = 0
for a in range(rr + 1):
    for b in range(rr + 1):
        if a + b <= rr:
            for u in reduced_words("abc", a):
                for v in reduced_words("xy", b):
                    c += 1
print(c)
"""
    
