from circuit import *
from mocircuits import *
from general import *
from sft import *
from alphabet import node_constraints
import time


"""
circuits is a dict : (node, label) -> circuit
the labels come from to_alphabet[node].node_vars
together the circuits associated to a single node form the circuit for the output symbol
for each node exactly one output symbol should be produced or this is nondeterministic
variables in circuits are (vector, node, label) encoded on the preimage side
overlaps should be "ignore", "check" or "remove"
"""
class BlockMap:
    def __init__(self, from_alphabet, to_alphabet, from_nodes, to_nodes, dimension, circuits, from_topology,
                 to_topology, graph, overlaps="remove", verbose=False, partial=False):

        #print("BlockMap circuits", circuits)
                     
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

        self.partial = partial

        #assert type(circuits) == dict
        if verbose:
            print("constructing CA of dim", dimension, "from nodes", from_nodes, "and alphabet", from_alphabet, "to", to_nodes, to_alphabet)
            

        # (node, label) : circ dict is only used internally, assume disjointness and full specification
        if any(type(x) == Circuit for x in circuits.values()):
            self.circuits = circuits #[(n,a,circuits[(n,a)]) for (n,a) in circuits]

        # node : [(circ, val)] dict
        else:
            new_circuits, partial_circuits = self.circuits_from_rules(circuits)
            self.partial = partial_circuits is not None
            self.circuits = new_circuits
            self.partial_circuits = partial_circuits
        
        if verbose:
            for node in to_nodes:
                for l in to_alphabet[node].node_vars:
                    print("Circuit for out node", node, "label", l, "is", self.circuits[node, l])
                if self.partial:
                    print("Partial circuit for out node", node, "is", self.partial_circuits[node])

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

    # we get a dict of node : [(circ, sym or pos)], the circs in each list are disjoint
    # we return a dict of (node, sym) : circuit and possibly a partiality dict node : circuit
    def circuits_from_rules(self, rules):

        partial = False
        ret_circuits = dict()
        partial_circuits = dict()
        for node in self.to_nodes:
            if node in rules:
                local_alph = self.to_alphabet[node]
                oreds = {label : [] for label in local_alph.node_vars}
                pairs = rules[node]
                has_img_oreds = []
                for (circ, val) in pairs:
                    if val in local_alph:
                        # a symbol -> make a model and enforce it
                        has_img_oreds.append(circ)
                        nvars = [V(l) for l in local_alph.node_vars]
                        model = SAT(AND(local_alph.node_eq_sym(nvars, val),
                                        local_alph.node_constraint(nvars)),
                                    return_model=True)
                        for label in local_alph.node_vars:
                            if model[label]:
                                oreds[label].append(circ)
                    else:
                        # we have a position
                        cell, dom_node = val
                        dom_alph = self.from_alphabet[dom_node]
                        if dom_alph == local_alph:
                            # alphabets agree -> copy
                            has_img_oreds.append(circ)
                            for label in local_alph.node_vars:
                                oreds[label].append(AND(circ, V((cell, dom_node, label))))
                        else:
                            # alphabets disagree -> make models and enforce them
                            for sym in dom_alph:
                                if sym in local_alph:
                                    dom_vars = [V((cell, dom_node, l)) for l in dom_alph.node_vars]
                                    nvars = [V(l) for l in local_alph.node_vars]
                                    model = SAT(AND(local_alph.node_eq_sym(nvars, sym),
                                                    local_alph.node_constraint(nvars)),
                                                return_model=True)
                                    for label in local_alph.node_vars:
                                        if model[label]:
                                            oreds[label].append(AND(circ, dom_alph.node_eq_sym(dom_vars, sym)))
                                    has_img_oreds.append(AND(circ, dom_alph.node_eq_sym(dom_vars, sym)))
                                            
                for label in local_alph.node_vars:
                    ret_circuits[node, label] = OR(*oreds[label])

                # check partiality
                #print("has img oreds", has_img_oreds)
                if SAT_under(NOT(OR(*has_img_oreds)), node_constraints(self.from_alphabet)):
                    partial = True
                    partial_circuits[node] = NOT(OR(*has_img_oreds))
            else:
                for label in self.alphabet[node].val_label:
                    ret_circuits[node, label] = F
                partial = True
                partial_circuits[node] = T
        if partial:
            for node in self.to_nodes:
                if node not in partial_circuits:
                    partial_circuits[node] = F
            return ret_circuits, partial_circuits
        else:
            return ret_circuits, None

    def tomocircuit(self):
        return MOCircuit(self.circuits)

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
        for circ in other.circuits.values():
            for var in circ.get_variables():
                #print(s)
                other_cells.add(var[0]) # just need to know the cells
                
        # Make shifted copies of our circuits, one for each cell used by other.
        # Note that the circuits that do not get used are actually killed by
        # Python's GC, because they are literally not going to be involved in
        # the final circuit.
        circuits = {}
        for cell in other_cells:
            for ((node, var), circ) in self.circuits.items():
                circuit_copy = circ.copy()
                def shift(v):
                    #print("shifting", v, "by", s)
                    return (vadd(v[0], cell),) + v[1:] # TODO replace with graph.move_rel
                #print("transforming")
                #print(circuit_copy, s)
                transform(circuit_copy, shift)
                #print(circuit_copy)
                #print((s,) + ns, " is where")
                circuits[cell, node, var] = circuit_copy

        # now the circuits dict has for each relevant position-symbol combo a circuit
        # we just combine them with the other circuit by literally replacing

        ret_circuits = {}
        for ((node, var), circ) in other.circuits.items():
            # we should construct the circuit for a particular node and var
            # make a copy of the relevant circuit
            ret_circuit = circ.copy()
            # ns = node, symbol
            transform(ret_circuit, lambda cnv: circuits[cnv])
            ret_circuits[node, var] = ret_circuit

        # TODO: add partial circuits
        if self.partial or other.partial:
            raise Exception("Composition not yet supported for partial block maps")

        ret = BlockMap(self.from_alphabet, other.to_alphabet, self.from_nodes, other.to_nodes, self.dimension, ret_circuits, self.from_topology, other.to_topology, self.graph, partial=self.partial or other.partial)
        return ret

    def after(self, other, verbose = False):
        return other.then(self, verbose)

    def __eq__(self, other):
        if self.partial or other.partial:
            raise Exception("Equality check not yet supported for partial block maps")
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
        if self.partial != other.partial:
            return False
        # TODO: remove this or fix
        for ns in self.circuits:
            #lambda a: last_diff_and_count(a, len(self.to_alphabet))
            if not equivalent_under(self.circuits[ns], other.circuits[ns], node_constraints(self.from_alphabet)):
                return False
        return True

    def separating(self, other):
        "Return a witness for inequality, or None if one does not exist"
        if self.partial or other.partial:
            raise Exception("Separation check not yet supported for partial block maps")
        for ((node, var), circ) in self.circuits.items():
            circ2 = other.circuits[node, var]
            diff = equivalent_under(circ, circ2, node_constraints(self.from_alphabet), return_sep=True)
            if diff != True:
                pat = dict()
                domain = set(var[:2] for var in diff)
                for nvec in domain:
                    local_alph = self.from_alphabet[nvec[1]]
                    vals = [diff[nvec + (var,)] for var in local_alph.node_vars]
                    pat[nvec] = local_alph.model_to_sym(vals)
                return ((node, var), pat)
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

        #print("self.circuits")
        #for ((node, var), circ) in self.circuits.items():
        #    print("{} {} : {}".format(node, var, circ))
        #print(self.to_alphabet)
        
        # construct circuits saying that two have same image
        eq_circuits = []
        # we allow a partial CA, but injectivity only checked if we actually specify _some_ image everywhere
        some_image = []
        if verbose: t = time.time()
        ball = self.graph.ball(r)
        if verbose: print("Ball is of size", len(ball))
        for cell in ball:
            def shift(x, tag):
                # here x = (cell, node var)
                return (self.graph.move_rel(cell, x[0]), x[1], tag, x[2])
            for node in self.to_nodes:
                local_alph = self.to_alphabet[node]
                some_letter = []
                circsA = []
                circsB = []
                for label in local_alph.node_vars:
                    circA = self.circuits[node, label].copy()
                    circB = circA.copy()
                    transform(circA, lambda y:shift(y, "A"))
                    transform(circB, lambda y:shift(y, "B"))
                    circsA.append(circA)
                    circsB.append(circB)
                eq_circuits.append(local_alph.node_eq_node(circsA, circsB))
                if self.partial:
                    p_circA = self.partial_circuits[node].copy()
                    transform(p_circA, lambda y:shift(y, "A"))
                    some_image.append(NOT(p_circA))

        # debug
        #print("eq circuits")
        #for s in eq_circuits:
        #    print(s)

        # debug
        #print("some image")
        #for s in some_image:
        #    print(s)
        
        origin = self.graph.origin()
        differents = []
        for node in self.from_nodes:
            local_alph = self.from_alphabet[node]
            varsA = [V((origin, node, "A", l)) for l in local_alph.node_vars]
            varsB = [V((origin, node, "B", l)) for l in local_alph.node_vars]
            differents.append(NOT(local_alph.node_eq_node(varsA, varsB)))

        # debug
        #print("differents")
        #for s in differents:
        #    print(s)
                
        # all images must be the same, and some central node has diff preimage, and all images have to be specified
        #def lda(a): return self.from_alphabet[a[1]]
        circ = AND(AND(*eq_circuits), OR(*differents), AND(*some_image))
        #varses = circ.get_variables()
        if verbose:print("Circuit constructed in time {}".format(time.time() - t))
        ret = UNSAT_under(circ, node_constraints(self.from_alphabet))
        #ret = UNSAT_under(AND(AND(*eq_circuits), OR(*differents)), node_constraints(self.from_alphabet))
        if verbose:print("Solved in time {}".format(time.time() - t))

        # just for a quick debug, you can print the solution; should really return a pattern object for Griddy exploration I guess
        """
        if ret == False:
            #model = SAT_under(AND(AND(*eq_circuits), OR(*differents), AND(*some_image)), node_constraints(self.from_alphabet), True)
            model = SAT_under(AND(AND(*eq_circuits), OR(*differents)), node_constraints(self.from_alphabet), True)
            for m in model:
                print(m, model[m])
        """
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
                local_alph = self.to_alphabet[node]
                circsA = []
                circsB = []
                for label in local_alph.node_vars:
                    circA = self.circuits[node, label].copy()
                    circB = circA.copy()
                    transform(circA, lambda y:shift(y, "A"))
                    transform(circB, lambda y:shift(y, "B"))
                    circsA.append(circA)
                    circsB.append(circB)
                eq_circuits.append(local_alph.node_eq_node(circsA, circsB))

        origin = self.graph.origin()
        differents = []
        circ_A = T
        for node in self.from_nodes:
            local_alph = self.from_alphabet[node]
            nvars_A = [V((origin, node, "A", l)) for l in local_alph.node_vars]
            nvars_B = [V((origin, node, "B", l)) for l in local_alph.node_vars]
            for sym in self.from_alphabet[node]:
                circ_A = AND(circ_A, NOT(local_alph.node_eq_sym(nvars_A, sym)))
                differents.append(AND(circ_A, local_alph.node_eq_sym(nvars_B, sym)))

        #lda =  LDAC2(lambda a: self.from_alphabet[a[1]])
        circ = AND(OR(*differents), *eq_circuits)
        circ = AND(circ, node_constraints(self.from_alphabet)(circ))
        if verbose: print("Circuit constructed in time {}".format(time.time() - t))

        proj_vars = []
        for (moves, node) in preim_set:
            cell = origin
            for move in moves:
                cell = self.graph.move(cell, (move,1))
            for label in self.from_alphabet[node].node_vars:
                for tag in ["A","B"]:
                    proj_vars.append((cell, node, tag, label))

        #print(circ)
        #print(proj_vars)
        #circ_vars = list(circ.get_variables())
        #for var in proj_vars:
        #    if var not in circ_vars:
        #        print(var)
        #        1/0

        first = True
        for vals in projections(circ, proj_vars):
            if verbose and first:
                print("First one found in time {}".format(time.time() - t))
                first = False
            yield vals
            
        if verbose: print("Enumerated in time {}".format(time.time() - t))

    def image_intersects(self, clopen, verbose=False):
        clopen_cells = set([var[0] for var in clopen.circuit.get_variables()])
        img_exists = []
        bm_circuits = dict()
        for cell in clopen_cells:
            def shift(var):
                new_cell = self.graph.move_rel(cell, var[0])
                return new_cell, var[1], var[2]
            for node in self.to_nodes:
                local_alph = self.to_alphabet[node]
                node_circs = []
                for label in local_alph.node_vars:
                    bm_circ = self.circuits[node, label].copy()
                    transform(bm_circ, shift)
                    node_circs.append(bm_circ)
                    bm_circuits[cell, node, label] = bm_circ
                if self.partial:
                    p_circ = self.partial_circuits[node].copy()
                    transform(p_circ, shift)
                    img_exists.append(NOT(p_circ))
        clopen_circ = clopen.circuit.copy()
        transform(clopen_circ, lambda var: bm_circuits[var])
        return SAT_under(AND(clopen_circ, *img_exists), node_constraints(self.from_alphabet))
        #return SAT_under(AND(clopen_circ, *image_constr), node_constraints(self.from_alphabet))
            
    """
    # construct a circuit that states preimage and image, and that image is in clopen
    def image_intersects(self, clopen, verbose):
        positions = set([v[0] for v in clopen.circuit.get_variables()])
        pre_cells = set()
        image_correct = []
        for p in positions:
            for n in self.to_nodes:
                # at each node, check that image has correct symbol.
                for a in self.to_alphabet[n]:
                    
                    # Check that image has letter, i.e. (p,n,img,a) is true,
                    # iff circA moved to (p,n,pre,a) evaluates to true.
                    
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
    """
        
        
        
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
            tracks = ('0', '1')
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
        if self.partial:
            raise Exception("Fixed points not supported for partial CA")
        assert self.is_CA()
        alph = self.from_alphabet
        nodes = self.from_nodes
        dim = self.dimension
        anded = []
        for node in nodes:
            in_vars = [V(((0,)*dim, node, l)) for l in alph[node].node_vars]
            out_vars = [self.circuits[node, l].copy() for l in alph[node].node_vars]
            anded.append(alph[node].node_eq_node(in_vars, out_vars))
        return SFT(dim, nodes, alph, self.from_topology, self.graph, circuit=AND(*anded))

    def spacetime_diagram(self, onesided=True, time_axis=None):
        "The SFT of spacetime diagrams of this CA"
        if self.partial:
            raise Exception("Spacetime diagram not supported for partial CA")
        assert self.is_CA()
        alph = self.from_alphabet
        nodes = self.from_nodes
        dim = self.dimension
        
        if time_axis is None:
            time_axis = self.dimension

        anded = []
        for ((node, label), circ) in self.circuits.items():
            #print("circ info", node, label, circ)
            new_circ = circ.copy()
            transform(new_circ, lambda var: (var[0][:time_axis] + (0,) + var[0][time_axis:], var[1], var[2]))
            val_vec = ((0,)*time_axis + (1,) + (0,)*(dim-time_axis), node)
            anded.append(IFF(new_circ, V(val_vec + (label,))))

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
        neighborhood = set(var[0] for circ in self.circuits.values() for var in circ.get_variables())
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
def find_relations(CAs, rad, verbose=False):
    i = 0
    firstCA = CAs[0]
    alphabet = firstCA.to_alphabet
    nodes = firstCA.to_nodes
    dimension = firstCA.dimension
    indices = []
    for node in nodes:
        for label in alphabet[node].node_vars:
            indices.append((node, label))
    mod = MOCircuitDict(indices)
    identityrule = {}
    for node in nodes:
        for label in alphabet[node].node_vars:
            identityrule[node, label] = V(((0,)*dimension, node, label))
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
        if verbose:
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











