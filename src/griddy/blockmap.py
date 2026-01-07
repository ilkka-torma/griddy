from circuit import *
from general import *
from sft import *
import mocircuits
import time


"""
circuits is a dict of circuits : (node, symbol) -> circuit
for each node exactly one should say yes or this is nondeterministic
variables in circuits are (vector, node, symbol) encodeed
overlaps should be "ignore", "check" or "remove"
"""
class BlockMap:
    def __init__(self, from_alphabet, to_alphabet, from_nodes, to_nodes, dimension, circuits, from_topology,
                 to_topology, graph, overlaps="remove", verbose=False):

        ##print(circuits)
                     
        #print(from_alphabet, to_alphabet, from_nodes, to_nodes, dimension, circuits, from_topology, to_topology, overlaps, graph)
        
        self.from_alphabet = from_alphabet
        self.to_alphabet = to_alphabet
        self.from_nodes = from_nodes
        self.to_nodes = to_nodes
        self.dimension = dimension
        self.graph = graph
        self.from_topology = from_topology
        self.to_topology = to_topology
        self.graph = graph

        self.partial = False

        #assert type(circuits) == dict
        if verbose:
            print("constructing CA of dim", dimension, "from nodes", from_nodes, "and alphabet", from_alphabet, "to", to_nodes, to_alphabet)
            

        #  dict is only used internally, assume disjointness and full specification
        if type(circuits) == dict:
            self.circuits = circuits #[(n,a,circuits[(n,a)]) for (n,a) in circuits]

        # inputs can be messier, and we remove intersections and add defaults
        # default is first missing symbol, if one is missing.
        # but if all appear, we use the first letter of the alphabet.
        if type(circuits) == list:
            
            self.circuits = self.circuits_from_list(circuits, overlaps)

            # check that there are no additional circuits, just to catch bugs
            for (n, a) in self.circuits:
                if n not in to_nodes:
                    raise Exception(n, "is not a node in range of CA")
                if a not in to_alphabet[n]:
                    raise Exception(a, "is not in alphabet of node", n, "in range of CA")
            
            ##print("here", self.circuits)

            for n in to_nodes:
                circs = {}
                for a in to_alphabet[n]:
                    if (n, a) in self.circuits:
                        circs[a] = self.circuits[(n, a)]
                # check if we should add default case because one is explicitly missing
                if len(circs) < len(to_alphabet[n]):
                    default_found = False
                    for a in to_alphabet[n]:
                        if a not in circs:
                            if not default_found:
                                if verbose:
                                    print("Using {} as default symbol for node {} in block map".format(a, n))
                                self.circuits[(n, a)] = AND(*(NOT(b) for b in circs.values()))
                            else:
                                self.circuits[(n, a)] = F
                # all formulas are there, but we should possibly still add a default case
                # if it's possible that no formula triggers; default is first letter then
                else:
                    ldac = LDAC2(lambda a:self.from_alphabet[a[1]])
                    first_sym = from_alphabet[n][0]
                    if SAT_under(AND(*(NOT(b) for b in circs.values())), ldac):
                        if verbose:
                            print("Using {} as default symbol for node {} in block map".format(first_sym, n))
                        self.circuits[(n, first_sym)] = AND(*(NOT(circs[b]) for b in circs if b != first_sym))
                        
        if verbose:
            for n in to_nodes:
                for a in to_alphabet[n]:
                    print("Circuit for out node", n, "letter", a, "is", self.circuits[(n, a)])

        """
        # check dimensions...
        for n in to_nodes:
            for a in to_alphabet[n]:
                
                print("check", n, a)
                for q in self.circuits[(n, a)].get_variables():
                    assert len(q[0]) == self.dimension
                print((n,a), "ok")
        """
                    
            
                        
    def info_string(self, name, verbose=False):
        partial = ""
        if self.partial: partial = "partial "
        s = ["{}-dimensional {}block map {}".format(self.dimension, partial, name)]
        s.append("Domain nodes: {}".format(list(self.from_nodes)))
        s.append("Domain alphabet: {}".format(self.from_alphabet))
        if verbose:
            s.append("Domain topology: {}".format(self.from_topology))
        s.append("Range nodes: {}".format(list(self.to_nodes)))
        s.append("Range alphabet: {}".format(self.to_alphabet))
        
        if verbose:
            s.append("Range topology: {}".format(self.to_topology))
            #s.append("Circuits (of sizes {}): {}".format([circ.complexity for circ in self.circuits.values()], self.circuits))
            for (n, a) in self.circuits:
                s.append("Circuit for node %s letter %s: %s" % (n, a, self.circuits[n, a]))
        return "\n".join(s)

    # we get a list of (node, sym, formula)
    # if overlaps is "remove", we should refine to disjoints:
    # if (n, a, C) appears, and (n, b) already has formula,
    # then, remove simultaneous solutions from C
    # if overlaps is "check", we should raise an exception if the rules are not disjoint
    # if overlaps if "ignore", assume the rules are disjoint
    def circuits_from_list(self, circuits, overlaps):
        if overlaps == "ignore":
            disjoints = circuits
        else:
            disjoints = []
            for (node, sym, formula) in circuits:
                form = formula
                # go over all previous
                for (node_, sym_, formula_) in disjoints:
                    if node_ != node:
                        continue
                    if sym_ != sym:
                        #print("from_alphabet", self.from_alphabet)
                        ldac = LDAC2(lambda nvec: self.from_alphabet[nvec[-1]])
                        if SAT_under(AND(form, formula_), ldac):
                            if overlaps == "check":
                                raise Exception("Overlapping rules for node {}, symbols {} and {}".format(node_, sym_, sym))
                            form = AND(form, NOT(formula_))
                disjoints.append((node, sym, form))
        ret_circuits = {}
        for (node, sym, formula) in disjoints:
            if (node, sym) not in ret_circuits:
                ret_circuits[(node, sym)] = formula
            else:
                ret_circuits[(node, sym)] = OR(ret_circuits[(node, sym)], formula)
        return ret_circuits

    def tomocircuit(self):
        return mocircuits.MOCircuit(self.circuits)

    # compose with other; other is done after
    def then(self, other, verbose = False):
        if verbose:
            print("composing block map")
            print(self)
            print("with")
            print(other)
        assert self.graph == other.graph
        assert self.to_alphabet == other.from_alphabet
        assert self.to_nodes == other.from_nodes
        assert self.dimension == other.dimension

        # calculate all cells that will be used
        other_cells = set()
        for c in other.circuits:
            for s in other.circuits[c].get_variables():
                #print(s)
                other_cells.add(s[0]) # just need to know the cells
                
        # Make shifted copies of our circuits, one for each cell used by other.
        # Note that the circuits that do not get used are actually killed by
        # Python's GC, because they are literally not going to be involved in
        # the final circuit.
        circuits = {}
        for s in other_cells: 
            for ns in self.circuits:
                circuit_copy = self.circuits[ns].copy()
                def shift(v):
                    #print("shifting", v, "by", s)
                    return (vadd(v[0], s),) + v[1:] # TODO replace with graph.move_rel
                #print("transforming")
                #print(circuit_copy, s)
                transform(circuit_copy, shift)
                #print(circuit_copy)
                #print((s,) + ns, " is where")
                circuits[(s,) + ns] = circuit_copy

        # now the circuits dict has for each relevant position-symbol combo a circuit
        # we just combine them with the other circuit by literally replacing

        ret_circuits = {}
        for ns in other.circuits: # ns = node, symbol
            # we should construct the circuit for a particular node and symbol
            # make a copy of the relevant circuit
            ret_circuit = other.circuits[ns].copy()
            # ns = node, symbol
            transform(ret_circuit, lambda a:circuits[a])
            ret_circuits[ns] = ret_circuit

        ret = BlockMap(self.from_alphabet, other.to_alphabet, self.from_nodes, other.to_nodes, self.dimension, ret_circuits, self.from_topology, other.to_topology, self.graph)
        return ret

    def after(self, other, verbose = False):
        return other.then(self, verbose)

    def __eq__(self, other):
        if self.from_alphabet != other.from_alphabet:
            return False
        if self.to_alphabet != other.to_alphabet:
            return False
        if self.dimension != other.dimension:
            return False
        if self.from_nodes != other.from_nodes:
            return False
        if self.to_nodes != other.to_nodes:
            return False
        # TODO: remove this or fix
        for ns in self.circuits:
            ldac = LDAC2(self.from_alphabet) #lambda a: last_diff_and_count(a, len(self.to_alphabet))
            if not equivalent_under(self.circuits[ns], other.circuits[ns], ldac):
                return False
        return True

    def separating(self, other):
        "Return a witness for inequality, or None if one does not exist"
        for ns in self.circuits:
            #print(ns)
            #ldac = LDAC2(self.from_alphabet) #lambda a: last_diff_and_count(a, len(self.to_alphabet))
            ldac = LDAC2(lambda nvec: self.from_alphabet[nvec[-1]])
            diff = equivalent_under(self.circuits[ns], other.circuits[ns], ldac, return_sep=True)
            if diff != True:
                pat = dict()
                domain = set(var[:-2] for var in diff)
                for vec in domain:
                    for node in self.from_nodes:
                        for sym in self.from_alphabet[node][1:]:
                            if diff.get(vec+(node,sym), False):
                                pat[vec+(node,)] = sym
                                break
                        else:
                            pat[vec+(node,)] = self.from_alphabet[node][0]
                return (ns, pat)
        return None

    # this cannot be up to date because now we can have different alphabet for each node
    """
    def injective_to_ball(self, r):
        if self.graph != None:
            return self.injective_to_graph_ball(r)
        # two circuits per position per letter
        # force images same
        # force preimage different
        eq_circuits = []
        for p in centered_hypercube(self.dimension, r):
            for n in self.to_nodes:
                for a in self.to_alphabet:
                    circA = self.circuits[(n, a)].copy()
                    circB = self.circuits[(n, a)].copy()
                    # shift the cell, i.e. not node or letter
                    # and also add x at the end, we make two copies of each
                    def shift(v, x): return vadd(v[:-2], p) + v[-2:] + (x,)
                    transform(circA, lambda y:shift(y, "A"))
                    #circuits[p + (n, a, 0)] = circA
                    transform(circB, lambda y:shift(y, "B"))
                    #circuits[p + (n, a, 1)] = circB
                    eq_circuits.append(IFF(circA, circB))
                    #print(IFF(circA, circB))
                    
        origin = (0,)*self.dimension
        differents = []
        for n in self.from_nodes:
            for a in self.from_alphabet:
                differents.append(XOR(V(origin + (n, a, "A")), V(origin + (n, a, "B"))))
        # all images must be the same, and some central node has diff preimage
        ret = UNSAT_under(AND(AND(*eq_circuits), OR(*differents)), LDAC2(self.from_alphabet))
        return ret
    """

    def injective_to_graph_ball(self, r, verbose):
        # two circuits per position per letter
        # force images same
        # force preimage different at origin

        #print(self.to_alphabet)
        
        # construct circuits saying that two have same image
        eq_circuits = []
        # we allow a partial CA, but injectivity only checked if we actually specify _some_ image everywhere
        some_image = []
        if verbose: t = time.time()
        bb = self.graph.ball(r)
        if verbose: print("Ball is of size", len(bb))
        for p in bb:
            for n in self.to_nodes:
                some_letter = []
                for a in self.to_alphabet[n]:
                    circA = self.circuits[(n, a)].copy()
                    circB = self.circuits[(n, a)].copy()
                    # shift the cell, i.e. not node or letter
                    # and also add x at the end, we make two copies of each
                    # def move_rel(self, cell, offset): = move to cell that is at offset relative to the input cell
                    # x[2] is the VALUE of the cell, so label should be before for ldaccing to work
                    def shift(x, label):
                        return self.graph.move_rel(p, x[0]), x[1], label, x[2] #return vadd(v[:-2], p) + v[-2:] + (x,)
                    transform(circA, lambda y:shift(y, "A"))
                    #circuits[p + (n, a, 0)] = circA
                    #print("circA", circA)
                    transform(circB, lambda y:shift(y, "B"))
                    #print("circB", circB)
                    #circuits[p + (n, a, 1)] = circB
                    eq_circuits.append(IFF(circA, circB))
                    some_letter.append(circA) # one of these should say yes
                    #print(IFF(circA, circB))
                # check that one says yes
                some_image.append(OR(*some_letter)) 
                    
        origin = self.graph.origin()
        differents = []
        for n in self.from_nodes:
            for a in self.from_alphabet[n][1:]:
                differents.append(XOR(V((origin, n, "A", a)), V((origin, n, "B", a))))
        # all images must be the same, and some central node has diff preimage, and all images have to be specified
        def lda(a): return self.from_alphabet[a[1]]
        if verbose:print("Circuit constructed in time {}".format(time.time() - t))
        ret = UNSAT_under(AND(AND(*eq_circuits), OR(*differents), AND(*some_image)), LDAC2(lda))
        if verbose:print("Solved in time {}".format(time.time() - t))
        return ret

    # count "obstructions to injectivity":
    # enumerate triples (A,B) st. A < B differ at origin, can be extended to radius r+r0, and map to equal radius-r balls
    # only allow total CA for now
    def obstructions_to_graph_ball_injectivity(self, rad, preim_set, verbose=False):
        #print("OTGBI", preim_set)
        eq_circuits = []
        if verbose:
            print("Enumerating obstructions to injectivity")
            t = time.time()
        r_ball = self.graph.ball(rad)

        im_circs = dict()
        
        for cell in r_ball:
            def shift(x, label):
                return self.graph.move_rel(cell, x[0]), x[1], label, x[2]
                    
            for node in self.to_nodes:
                for sym in self.to_alphabet[node]:
                    circA = self.circuits[node, sym].copy()
                    circB = self.circuits[node, sym].copy()
                    transform(circA, lambda y: shift(y, "A"))
                    transform(circB, lambda y: shift(y, "B"))
                    im_circs[cell, node, sym] = (circA, circB)
                    eq_circuits.append(IFF(circA, circB))

        origin = self.graph.origin()
        differents = []
        circ_A = T
        for node in self.to_nodes:
            for sym in self.from_alphabet[node][1:]:
                circ_A = AND(circ_A, NOT(V((origin, node, "A", sym))))
                differents.append(AND(circ_A, V((origin, node, "B", sym))))

        lda =  LDAC2(lambda a: self.from_alphabet[a[1]])
        circ = AND(OR(*differents), *eq_circuits)
        circ = AND(circ, lda([circ]))
        if verbose: print("Circuit constructed in time {}".format(time.time() - t))

        proj_vars = []
        for (moves, node) in preim_set:
            cell = origin
            for move in moves:
                cell = self.graph.move(cell, (move,1))
            for sym in self.from_alphabet[node][1:]:
                for label in ["A","B"]:
                    proj_vars.append((cell, node, label, sym))

        #print(circ)
        #print(proj_vars)
        circ_vars = list(circ.get_variables())
        for var in proj_vars:
            if var not in circ_vars:
                print(var)
                1/0

        first = True
        for vals in projections(circ, proj_vars):
            if verbose and first:
                print("First one found in time {}".format(time.time() - t))
                first = False
            yield vals
            
        if verbose: print("Enumerated in time {}".format(time.time() - t))

    # construct a circuit that states preimage and image, and that image is in clopen
    def image_intersects(self, clopen, verbose):
        positions = set([v[0] for v in clopen.circuit.get_variables()])
        pre_cells = set()
        image_correct = []
        for p in positions:
            for n in self.to_nodes:
                # at each node, check that image has correct symbol.
                for a in self.to_alphabet[n]:
                    """
                    Check that image has letter, i.e. (p,n,img,a) is true,
                    iff circA moved to (p,n,pre,a) evaluates to true.
                    """
                    circ = self.circuits[(n, a)].copy()
                    def shift(x, label):
                        m = self.graph.move_rel(p, x[0])
                        pre_cells.add(m)
                        return m, x[1], label, x[2] #return vadd(v[:-2], p) + v[-2:] + (x,)
                    transform(circ, lambda y:shift(y, "pre"))
                    image = V((p, n, "img", a))
                    image_correct.append(IFF(circ, image))
                    #print("image circ", IFF(circ, image))
        image_circuit = AND(*image_correct)
        circuits = [image_circuit]
        #print("image circ", image_circuit)

        # on preimage side, we should do the annoying coding, check that at most one is true
        for p in pre_cells:
            for n in self.from_nodes:
                circuits.append(ATMOSTONE(*(V((p, n, "pre", sym)) for sym in self.from_alphabet[n][1:])))
                #print("ATMO", circuits[-1])
                
        # We check that on image side, we actually have an image everywhere. This is because block map could be partial,
        # so we should not just assume to_alphabet[0] circuit gives True when others give False. This is also why
        # above we have the circuit check also for a = to_alphabet[0].
        for p in positions:
            for n in self.to_nodes:
                circuits.append(ATMOSTONE(*(V((p, n, "img", sym)) for sym in self.to_alphabet[n])))
                circuits.append(OR(*(V((p, n, "img", sym)) for sym in self.to_alphabet[n])))
                #print("ATMOi", circuits[-2])
                #print("yesi", circuits[-1])

        # on the image side, we finally have to check that we are in clopen
        ccirc = clopen.circuit.copy()
        transform(ccirc, lambda x:(x[0],x[1],"img",x[2]))
        circuits.append(ccirc)
        #print("imgcor ", circuits[-1])

        test = AND(*circuits)

        return SAT(test)
                
        
        
        
    def __repr__(self):
        return repr(self.circuits)

    """
    A CA is injective on its full shift if there exists
    a radius r such that there do not exist a pair of
    r-sized patterns P, Q with distinct central symbols which have
    distinct images.

    On the other hand, it is not injective if we can find two periodic
    points with the same image.
    """
    def injective(self):
        r = 1
        while True:
            if self.injective_to_ball(r):
                return True
            if not self.injective_on_periodics(r):
                return False
            r += 1

    # assume the environments match
    def preimage(self, the_sft):
        sft_circ = the_sft.circuit.copy()
        for var in sft_circ.get_variables():
            substitute(sft_circ, var, V(var+(None,))) # prevent accidental repeated substitutions
        for var in sft_circ.get_variables():
            #print("mummeli", var)
            vec, node, sym = var[:3]
            bm_circ = self.circuits[node, sym].copy()
            #print(bm_circ.get_variables())
            transform(bm_circ, lambda var2: (vadd(vec, var2[0]),) + var2[1:])
            substitute(sft_circ, var, bm_circ)
        return SFT(self.dimension, self.from_nodes, self.from_alphabet, self.from_topology, self.graph, circuit=sft_circ)

    def relation(self, tracks=None):
        "The relation defining this block map (as an SFT), i.e. its graph"
        if tracks is None:
            tracks = (0,1)
        dom_alph = self.from_alphabet
        dom_nodes = self.from_nodes
        cod_alph = self.to_alphabet
        cod_nodes = self.to_nodes
        dim = self.dimension
        nodes = Nodes({tr:nodes for (tr, nodes) in zip(tracks, (dom_nodes, cod_nodes))})
        alph = {(tr,)+node : alph[node]
                for (tr, nodes, alph) in zip(tracks, (dom_nodes, cod_nodes), (dom_alph, cod_alph))
                for node in nodes}
        anded = []
        for ((node, sym), circ) in self.circuits.items():
            new_circ = circ.copy()
            transform(new_circ, lambda var: (var[0], ((tracks[0],) + var[1])) + var[-1:])
            if sym != cod_alph[node][0]:
                anded.append(IFF(V(((0,)*dim, (tracks[1],) + node, sym)), new_circ))
            else:
                not_others = AND(*(NOT(V(((0,)*dim, (tracks[1],) + node, sym2)))
                                   for sym2 in cod_alph[node][1:]))
                anded.append(IFF(not_others, new_circ))
                
        #for sft in sfts:
        #    print(sft)
        #    print("topo", sft.topology)
        #    print()
        topology = []
        for tr in tracks:
            if tr == tracks[0]:
                topo = self.from_topology
            else:
                topo = self.to_topology
            for t in topo:
                # t[:1] is the name of an edge. We make a copy with track added.
                topology.append(t[:2] + tuple(((tr,) + n) for n in t[2:]))
        #print(topology)
        
        return SFT(dim, nodes, alph, topology, self.graph, circuit=AND(*anded))

    def is_CA(self):
        return self.to_alphabet == self.from_alphabet and self.to_nodes == self.from_nodes # and self.to_topology == self.from_topology

    def fixed_points(self):
        "The SFT of fixed points of this CA"
        assert self.is_CA()
        alph = self.from_alphabet
        nodes = self.from_nodes
        dim = self.dimension
        anded = []
        for ((node, sym), circ) in self.circuits.items():
            new_circ = circ.copy()
            if sym != alph[node][0]:
                anded.append(IMP(V(((0,)*dim, node, sym)), new_circ))
            else:
                not_others = AND(*(NOT(V(((0,)*dim, node, sym2))) for sym2 in alph[node][1:]))
                anded.append(IMP(not_others, new_circ))
        return SFT(dim, nodes, alph, self.from_topology, self.graph, circuit=AND(*anded))

    def spacetime_diagram(self, onesided=True, time_axis=None):
        "The SFT of spacetime diagrams of this CA"
        assert self.is_CA()
        alph = self.from_alphabet
        nodes = self.from_nodes
        dim = self.dimension
        
        if time_axis is None:
            time_axis = self.dimension

        anded = []
        for ((node, sym), circ) in self.circuits.items():
            #print("circ info", node, sym, circ)
            new_circ = circ.copy()
            transform(new_circ, lambda var: (var[0][:time_axis] + (0,) + var[0][time_axis:], var[1], var[2]))
            val_vec = ((0,)*time_axis + (1,) + (0,)*(dim-time_axis), node)
            local_alph = alph[node]
            if sym == local_alph[0]:
                is_val = AND(*(NOT(V(val_vec + (sym2,))) for sym2 in local_alph[1:]))
            else:
                is_val = V(val_vec + (sym,))
            anded.append(IFF(new_circ, is_val))

        #print(self.from_topology)

        topology = []
        for t in self.from_topology: 
            # append the new dimension in the edges, t[:1] is the (label,)
            #topology.append(t[:1] + tuple(tt[:time_axis] + (0,) + tt[time_axis:] for tt in t[1:])) <- old format
            topology.append(t[:1] + (t[1][:time_axis] + (0,) + t[1][time_axis:], t[2], t[3]))
            # add the time direction, default name is "fut"/"past"
        for n in nodes:
            topology.append(("fut", (0,)*time_axis + (1,) + (0,)*(dim-time_axis) + (n, n)))
            topology.append(("past", (0,)*time_axis + (-1,) + (0,)*(dim-time_axis) + (n, n)))
            
        return SFT(dim+1, nodes, alph, topology, self.graph, circuit=AND(*anded), onesided=[time_axis] if onesided else [])

    def get_neighborhood(self, only_cells):
        if not only_cells:
            raise Exception("Neighborhood in terms of nodes not implemented.")
        circs = self.circuits
        neighborhood = set()
        for n in self.to_nodes:
            for s in self.to_alphabet[n]:
                for q in circs[n, s].get_variables():
                    vec = q[0]
                    neighborhood.add(vec) # drop node and symbol
                    
        # to prevent bugs and maybe remove special cases
        # always give a nonempty nbhd (it's not guaranteed minimal anyway)
        if len(neighborhood) == 0:
            neighborhood.add((0,)*self.dimension)
            
        return neighborhood       

    """
    def explicit_local_rule(self, contiguous = False):
        if contiguous:
            if self.dimension != 1:
                raise Exception("Contiguous local rule can only be requested in one dimension.")
            
        from_nodes = self.from_nodes
        from_alph = self.from_alphabet # this is a dict from nodes to alphabets
        # circuits are a dictionary from node and symbol to circuit telling us when it is accepting
        circs = self.circuits

        # first, calculate the neighborhood
        neighborhood = []
        for n in nodes:
            for s in from_alph[n]:
                for q in circs[n, s].get_variables():
                    vec, n, s = q[:-2], q[-2], q[-1]
                    neighborhood.append(vec)
                    
        if contiguous:
            # dimension is 1, note that we have singleton tuples but they compare the same
            m, M = min(neighborhood), max(neighborhood)
            neighborhood = [(s,) for s in range(m[0], M[0]+1)]
            
        #if open_singleton_tuple:
        #    neighborhood = [s[0] for s in neighborhood]
            
        # next, the main part: calculate the rule as an explicit local rule
        # for each node, we should enumerate all possible patterns in the neighborhood
        nodepats = list()
        for n in nodes:
            nodepats.append(pats(neighborhood, from_alph[n]))
        
        rule = {}
        for c in iter_prod(*nodepats):
            # transpose the product so that it's from vectors to product alphabet
            ptrn = {}
            for v in neighborhood:
                ptrn[v] = [cc[v] for cc in c]
            result = self.evaluate_on(ptrn)
    """

    #def local rule(self):

# given a list of cellular automata, compute relations
# among them up to radius rad as semigroup
def find_relations(CAs, rad):
    i = 0
    firstCA = CAs[0]
    alphabet = firstCA.to_alphabet
    nodes = firstCA.to_nodes
    dimension = firstCA.dimension
    indices = []
    for n in nodes:
        for a in alphabet[n]:
            indices.append((n, a))
    mod = mocircuits.MOCircuitDict(indices)
    identityrule = {}
    for n in nodes:
        for a in alphabet[n][1:]:
            identityrule[(n, a)] = V(((0,)*dimension, n, a))
    # topology None because it really does not matter
    idca = BlockMap(alphabet, alphabet, nodes, nodes, dimension, identityrule, None, None, CAs[0].graph)
    #assert idca.then(idca) == idca
    mod[idca.tomocircuit()] = (idca, ())
    #print("idcirc", idca.circuits)
    #print("cacirc", CAs[0].circuits)
    

    #print(CAs[0])

    #assert CAs[0].tomocircuit() in mod
    
    #a = bbb
    frontier = [(idca, ())]

    
    #assert idca.tomocircuit() in mod
    """
    for i in range(len(CAs)):
        if CAs[i].tomocircuit() not in mod:
            mod[CAs[i].tomocircuit()] = (CAs[i], (i,))
            frontier.append((CAs[i], (i,)))
            yield
    """

    relations = []
    for r in range(rad):
        print("Frontier size %s at depth %s; total number of CA %s." % (len(frontier), r, len(mod)))
        #for ca, w in frontier:
        #    print(w)
        newfrontier = []
        for ca, w in frontier:
            for k in range(len(CAs)):
                newca = ca.after(CAs[k])
                newcamo = newca.tomocircuit()
                if newcamo in mod:
                    yield ("rel", mod[newcamo][1], w + (k,))
                    relations.append((mod[newcamo][1], w + (k,)))
                    continue
                yield ("CA", newca, w + (k,))
                mod[newcamo] = (newca, w + (k,))
                newfrontier.append((newca, w + (k,)))
        frontier = newfrontier

    ret = {}
    for k in mod:
        img = mod[k]
        ret[img[1]] = img[0]

    return ret, relations
        
        





#def that_action(CA):
    


#def CA()

r"""
Given a cellular automaton, which is a tuple
(alphabet, radius rule)
return a new CA
(alphabet^2 \cup \{>, <\}, new radius, new rule)
which realizes the action from my paper.
"""

# basic testing, id, not, xors

"""
alphabet = {0 : [0, 1]}
nodes = [0]
dimension = 1
id_CA_circuits = {(0,0) : NOT(V((0,0,0,1))), (0,1) : V((0,0,0,1))}
a = BlockMap(alphabet, alphabet, nodes, nodes, dimension, id_CA_circuits, None, None)
print(a.explicit_local_rule(contiguous = True))
"""

"""

not_CA_circuits = {(0,1) : V((0,0,0,0))}
b = CA(alphabet, nodes, dimension, not_CA_circuits)

print(a.then(b) == b, True) # true
print(b.then(b) == a, True) # true
print(b.then(a.then(b)) == b.then(a).then(a), False) # false
print(a.then(b) == b.then(b).then(b), True)


xor_CA_circuits = {(0,1) : XOR(V((0,0,0,1)), V((1,0,0,1)))}
x = CA(alphabet, nodes, dimension, xor_CA_circuits)

xor2_CA_circuits = {(0,1) : XOR(V((0,0,0,1)), V((2,0,0,1)))}
x2 = CA(alphabet, nodes, dimension, xor2_CA_circuits)

print(x.then(x.then(x2).then(a)) == x2.then(x).then(x), True)
print(x.then(x.then(x2)) == x2.then(a).then(x).then(x2), False)
"""



"""
# more interesting testing: lamplighter group; 
alphabet = [0,1]
nodes = ["up", "dn"]
dimension = 1

can = {}
partial_right_shift_CA_circuits = {("dn", 0) : V((0,0,"dn",0)),
                             ("up", 0) : V((-1,0,"up",0))}
can["R"] = CA(alphabet, nodes, dimension, partial_right_shift_CA_circuits)
partial_left_shift_CA_circuits = {("dn", 0) : V((0,0,"dn",0)),
                             ("up", 0) : V((1,0,"up",0))}
can["L"] = CA(alphabet, nodes, dimension, partial_left_shift_CA_circuits)
sum_down_CA_circuits = {("up", 0) : V((0,0,"up",0)),
                        ("dn", 1) : XOR(V((0,0,"up",1)), V((0,0,"dn",1)))}
can["s"] = CA(alphabet, nodes, dimension, sum_down_CA_circuits)
id_CA_circuits = {("dn", 0) : V((0,0,"dn",0)),
                  ("up", 0) : V((0,0,"up",0))}
can["e"] = CA(alphabet, nodes, dimension, id_CA_circuits)

def evalstr(s):
    #print(s)
    ret = can["e"]
    for i in s:
        #print(can[i].circuits)
        ret = ret.then(can[i])
    #print(ret, "RETURN")
    return ret

""
print(evalstr("ss") == evalstr("e"), True)
print(evalstr("LR") == evalstr("RL"), True)
print(evalstr("LR") == evalstr("R"), False)
print(evalstr("RRRsLLLsRRRsLLLs") == evalstr("e"), True)
print(evalstr("RRRsLLLsRRRLLLs") == evalstr("e"), False)
""

#CAs, rels = find_relations([can["L"], can["R"], can["s"]], 10)

"""


"""
SO_XOR_circuits = {("up",1) : V((0,"dn",1)),
                   ("dn",1) : XOR(V((0,"dn",1)), V((0,"up",1)), V((1,"up",1)))}
SO_XOR = CA(alphabet, nodes, dimension, SO_XOR_circuits)
#xor_CA_circuits = {(0,"up") : XOR(V((0,0,0,1)), V((1,0,0,1)))}
#x = CA(alphabet, nodes, dimension, xor_CA_circuits)

print(evalstr("RRRsLLLsRRRsLLLs").then(SO_XOR).injective_to_ball(0))
"""

"""

def addat(n):
    if n > 0:
        return "R"*n + "s" + "L"*n
    n = -n
    return "L"*n + "s" + "R"*n

def addats(ns):
    r = ""
    for n in ns:
        r += addat(n)
    return r

t = time.time()
A = evalstr(addats([0, 6, 3, 2, 3]))
B = evalstr(addats([6, 2, 2, 3, 2, 3, 0]))
C = evalstr(addats([6, 5, 4, 3, 2, 1, 0, -1, 5, 4, 3, 1, -1]))
D = evalstr(addats([0, 6, 4, 2, 3]))
print(A == B)
print(B == C)
print(C == D)
#print(evalstr("RRRsLLLsRRRsLLLsL") == evalstr("L"), True)

print(time.time() - t)                        
"""
                        



"""
alphabet = [0,1]
nodes = [0,1]
dimension = 1

#shift_CA_circuits = {(0,1) : XOR(V((0,0,0)), V((1,0,0)))}

# second order xor
#SO_XOR_circuits = {(0,1) : V((0,1,1)),
#                   (1,1) : XOR(V((0,1,1)), V((0,0,1)), V((1,0,1)))}
#a = CA(alphabet, nodes, dimension, SO_XOR_circuits)
#print(a.injective_to_ball(0))
#print(a.injective_to_ball(1))
"""



"""
alphabet = [0,1]
nodes = [0]
dimension = 1

c = {(0,1) : XOR(V((0,0,1)), V((1,0,1)))}
x1 = CA(alphabet, nodes, dimension, c)
c = {(0,1) : XOR(V((0,0,1)), V((1,0,1)), V((2,0,1)))}
x2 = CA(alphabet, nodes, dimension, c)
CAs, rels = find_relations([x1, x2], 7)
"""











