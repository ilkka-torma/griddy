from general import *
from circuit import *
from configuration import *
from itertools import chain
import automatic_conf


class Nodes:
    "A hierarchical set of nodes"

    # nodes can be either a single label, a flat list of labels,
    # a recursive dict from labels, or None
    # in symbols: nodes = label | list(label) | dict(label : nodes) | None
    # labels must be strings or integers
    # internally, a Nodes stores a dict with Nones for flat labels
    def __init__(self, nodes=None):
        if nodes is None or nodes == [] or nodes == dict():
            self.nodes = None
        elif type(nodes) == Nodes:
            self.nodes = nodes.nodes
        elif type(nodes) == list:
            for x in nodes:
                if type(x) not in [int, str]:
                    raise Exception("Node label must be integer or string, not {}".format(x))
            self.nodes = {x : None for x in nodes}
        elif type(nodes) == dict:
            self.nodes = {label : Nodes(track) or None
                          for (label, track) in nodes.items()}
        elif type(nodes) in [int, str]:
            self.nodes = {nodes : none}
        else:
            raise Exception("Bad node specification: {}".format(nodes))
            
    @classmethod
    def from_list(cls, node_list):
        #print("from list", node_list)
        nodes = dict()
        for (i, node) in enumerate(node_list):
            if not node:
                raise Exception("Bad node list: {}".format(node_list))
            head = node[0]
            if head in nodes:
                if nodes[head] is None or len(node) == 1:
                    raise Exception("Bad node list: {} (offender is {} at position {})".format(node_list, node, i))
                nodes[head].append(node[1:])
            elif len(node) == 1:
                nodes[head] = None
            else:
                nodes[head] = [node[1:]]
        #print("computed", nodes)
        return cls({label : rest if rest is None else Nodes.from_list(rest)
                    for (label, rest) in nodes.items()})
            
    def __bool__(self):
        return self.nodes is not None

    def __iter__(self):
        if self:
            def the_iter():
                for (label, track) in self.nodes.items():
                    if track is None:
                        yield (label,)
                    else:
                        for node in track:
                            yield (label,) + node
            return the_iter()
        else:
            return iter([()])

    def __len__(self):
        #print("len", self, self.nodes)
        if self:
            return sum(1 if track is None else len(track) for track in self.nodes.values())
        else:
            return 1
            
    def __in__(self, item):
        if type(item) != tuple:
            return False
        if self:
            if item == ():
                return False
            track = self.nodes[item[0]]
            if track is None:
                return len(item) == 1
            return item[1:] in track
        else:
            return item == ()

    def track(self, label):
        if self.flat:
            raise KeyError("A flat node list has no tracks")
        else:
            return self.nodes[label]
        
    def compatible(self, items):
        #print("compatible", self, items)
        if not items:
            return True
        if not self:
            return False
        if items[0] not in self.nodes:
            return False
        if self.nodes[items[0]] is None:
            return len(items) == 1
        return self.nodes[items[0]].compatible(items[1:])
        
    def subtrack(self, items):
        if not items:
            return self
        if len(items) == 1:
            if items in self:
                return [()]
            else:
                return False
        return self.track(items[0]).subtrack(items[1:])

    def __str__(self):
        return "Nodes[" + ", ".join(self.str_nodes()) + "]"

    def str_nodes(self):
        for node in self:
            yield '.'.join(str(part) for part in node)

    def __eq__(self, other):
        if type(other) != Nodes:
            return False
        return self.nodes == other.nodes
    
    def first_node(self):
        for n in self:
            return n

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
def minimize_solution(circuit, vals, necessary_vals = None, sort_by_dist=False):

    #print("minimizing")
    #print(circuit)
    #print(vals)
    #print(necessary_vals)
    #print(sort_by_dist)
    
    if necessary_vals == None:
        assert evaluate(circuit, vals)
        necessary_vals = []

    assert type(vals) == dict
    if sort_by_dist:
        vals = list(sorted(vals.items(), key=lambda v: -sum(abs(i) for i in v[0][0])))
    else:
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

# vecs is a list of vectors
def add_uniqueness_constraints(alphabet, circuits, nvecs):
    #print(nvecs, alphabet)
    for nvec in nvecs:
        #print("mekga", alphabet)
        #print(nvec)
        local_alph = alphabet[nvec[-1]]
        if len(local_alph) > 2:
            circuits.append(ATMOSTONE(*(V(nvec + (sym,)) for sym in local_alph[1:])))

def nonnegative_patterns(dim, tr_dims, patterns):
    "Translate the pattern to have nonnegative coordinates along the specified dimensions"
    #print("nonneg öat", patterns)
    tr_vec = []
    for i in range(dim):
        if i in tr_dims:
            tr_vec.append(-min(vec[0][i] for pat in patterns for vec in pat))
        else:
            tr_vec.append(0)
    return [{nvadd(nvec, tr_vec) : val for (nvec, val) in pat.items()} for pat in patterns]

# tr_dims are the dimensions translated to nonnegative (usually one-sided directions)
def nonnegative_circuit(dim, tr_dims, circ):
    circ = circ.copy()
    variables = circ.get_variables()
    #print(variables," kikkoman")
    tr_vec = []
    for i in range(dim):
        if i in tr_dims:
            tr_vec.append(-min(var[0][i] for var in variables))
        else:
            tr_vec.append(0)
    #print("just to see", circ)
    transform(circ, lambda var: (vadd(var[0], tr_vec),) + var[1:])
    
    return circ
    
# From dict(nvec : [symbol]), produce patterns
def product_patterns(prod_pat):
    if not prod_pat:
        yield dict()
    else:
        nvec = min(prod_pat)
        partial = dict(p for p in prod_pat.items() if p[0] != nvec)
        syms = prod_pat[nvec]
        for pat in product_patterns(partial):
            for sym in syms:
                new_pat = pat.copy()
                new_pat[nvec] = sym
                yield new_pat

class SFT:
    "dim-dimensional SFT on a gridlike graph"

    # Onesided is a list of dimensions
    # In a onesided SFT, the set of forbidden patterns and the circuit are translated so that the onesided coordinates are nonnegative and start at 0
    def __init__(self, dim, nodes, alph, topology, graph, forbs=None, circuit=None, formula=None, onesided=None):
        self.dim = dim
        self.nodes = nodes
        self.alph = alph
        self.topology = topology
        self.graph = graph
        if onesided is None:
            onesided = []
        self.onesided = onesided

        if forbs is None:
            self.forbs = None
        else:
            self.forbs = nonnegative_patterns(self.dim, self.onesided, forbs)
        self.formula = formula # just for display, not actually used in computations
        if circuit is None:
            self.circuit = None
            self.deduce_circuit()
        else:
            self.circuit = nonnegative_circuit(self.dim, self.onesided, circuit)
        #print(self.circuit.complexity)

    def __str__(self):
        return "SFT(dim={}, nodes={}, alph={}{})".format(self.dim, self.nodes, self.alph, (", onesided="+str(self.onesided)) if self.onesided else "")
        
    def info_string(self, name, verbose=False):
        s = ["{}-dimensional SFT {}".format(self.dim, name)]
        s.append("Nodes: {}".format(list(self.nodes)))
        s.append("Alphabet: {}".format(self.alph))
        if verbose:
            s.append("Topology: {}".format(self.topology))
        s.append("Onesided along axes {}".format(self.onesided))
        if self.forbs is None:
            s.append("Forbidden patterns not computed")
        elif verbose:
            s.append("Forbidden patterns: {}".format(self.forbs))
        else:
            s.append("{} forbidden patterns".format(len(self.forbs)))
        if verbose:
            s.append("Circuit (of size {}): {}".format(self.circuit.complexity, self.circuit))
        return "\n".join(s)

    def __contains__(self, conf, verbose=False, incomplete=False, print_freq=1):
        if not isinstance(conf, Conf):
            raise TypeError("Expected Conf, not {}".format(type(conf)))
        elif isinstance(conf, RecognizableConf):
            #print("testing containment of", conf.display_str())
            if conf.dim != self.dim or conf.onesided != self.onesided:
                return False
            conf_vecs = set(hyperrect([(a, d) for (a, b, c, d) in conf.markers]))
            my_vecs = set(var[0] for var in self.circuit.get_variables())
            if not my_vecs:
                my_vecs.add((0,)*self.dim)
            tr_bounds = []
            for (i, (a, b, c, d)) in enumerate(conf.markers):
                if i in self.onesided:
                    min_bound = 0
                else:
                    min_bound = a - max(vec[i] for vec in my_vecs)
                max_bound = d - min(vec[i] for vec in my_vecs)
                tr_bounds.append((min_bound, max_bound))
            #print(var_vecs, all_vecs)
            for vec in hyperrect(tr_bounds):
                circ = self.circuit.copy()
                #print(circ)
                def tr(var):
                    #print(var, "vir")
                    #print(vec)
                    #print(nvadd(var[:-1], vec), "kik")
                    #print(conf)
                    #print(conf[nvadd(var[:-1], vec)])
                    #print("trans", var, "glem", conf[nvadd(var[:-1], vec)])
                    if var[-1] == conf[nvadd(var[:-1], vec)]:
                        return T
                    else:
                        return F
                transform(circ, tr)
                if not SAT(circ):
                    return False
            return True
        elif isinstance(conf, automatic_conf.AutomaticConf):
            #print("forbs", self.forbs)
            domain = list(set(var[:-1] for var in self.circuit.get_variables()))
            patch_solver = solver_process(self.circuit)
            _ = next(patch_solver)
            
            for patch in conf.struct.patches(domain, conf.dfa, verbose=verbose, incomplete=incomplete, print_freq=print_freq):
                #print("patch", patch)
                solver_values = dict()
                for (nvec, patch_sym) in zip(domain, patch):
                    for sym in self.alph[nvec[1]][1:]:
                        solver_values[nvec + (sym,)] = patch_sym == sym
                if not patch_solver.send(solver_values):
                    return False
            return True
        else:
            raise Exception("Unknown configuration type")
    
    def radii(self, twosided=False):
        vecs = set(var[0] for var in self.circuit.get_variables())
        if twosided:
            return [(min(vec[i] for vec in vecs), max(vec[i] for vec in vecs))
                    for i in range(self.dim)]
        else:
            return [max(vec[i] for vec in vecs) - min(vec[i] for vec in vecs) + 1
                    for i in range(self.dim)]

    # Find recognizable configuration (i.e. uniformly eventually periodic in each orthogonal direction) in self which is not in other
    # The semilinear structure is a periodic rectangular tiling, and the contents of a rectangle depend on which axes its lowest corner lies in
    # We could also have the sizes of the rectangles depend on this, but this is simpler for now
    # Some directions can be declared fully periodic instead of eventually periodic
    # For a onesided non-periodic direction, only consider translates of the formula whose variables are on the nonnegative part of the axis
    def exists_recognizable_not_in(self, other, radii, periodics=None, return_conf=False):
        #print("radii", radii, "periodics", periodics)

        if periodics is None:
            periodics = []
        
        my_vecs = set(var[0] for var in self.circuit.get_variables())
        if not my_vecs:
            my_vecs.add((0,)*self.dim)
        other_vecs = set(var[0] for var in other.circuit.get_variables())
        if not other_vecs:
            other_vecs.add((0,)*self.dim)
        #print("my_vecs", my_vecs, "other_vecs", other_vecs)
        conf_bounds = [(0 if i in self.onesided+periodics else -rad,
                        rad if i in periodics else 2*rad)
                       for (i, rad) in enumerate(radii)]
        all_vecs = set(hyperrect(conf_bounds))
        #print("all_vecs", all_vecs)
        tr_bounds = []
        for (i, rad) in enumerate(radii):
            if i in self.onesided+periodics:
                min_bound = 0
            else:
                min_bound = -rad - max(vec[i] for vec in chain(my_vecs, other_vecs))
            if i in periodics:
                max_bound = rad
            else:
                max_bound = 2*rad - min(vec[i] for vec in chain(my_vecs, other_vecs))
            tr_bounds.append((min_bound, max_bound))
        #print("radii", radii)
        #print("conf_bounds", conf_bounds)
        #print("tr_bounds", tr_bounds)

        def wrap(var):
            #print("var", var)
            ret = []
            for (i, (r,x)) in enumerate(zip(radii, var[0])):
                if i in periodics:
                    ret.append(x%r)
                elif x < 0:
                    ret.append(x%r - r)
                elif x < r:
                    ret.append(x)
                else:
                    ret.append(x%r + r)
            ret = (tuple(ret),) + var[-2:]
            #print("ret", ret)
            return ret

        circuits = []
        others = []
        for vec in hyperrect(tr_bounds):
            #if any(vadd(vec, my_vec) in all_vecs for my_vec in my_vecs) and\
            if all(vec[i]+my_vec[i] >= 0 for my_vec in my_vecs for i in self.onesided):
                #print("adding my circ")
                circ = self.circuit.copy()
                transform(circ, lambda var: wrap(nvadd(var[:-1], vec) + var[-1:]))
                circuits.append(circ)
            if any(vadd(vec, other_vec) in all_vecs for other_vec in other_vecs) and\
               all(vec[i]+other_vec[i] >= 0 for other_vec in other_vecs for i in self.onesided) and\
               all(vec[i] == 0 or i not in periodics for i in range(self.dim)):
                #print("adding other circ")
                not_other = NOT(other.circuit.copy())
                transform(not_other, lambda var: wrap(nvadd(var[:-1], vec) + var[-1:]))
                others.append(not_other)
        circuits.append(OR(*others))

        #print(circuits)
        add_uniqueness_constraints(self.alph, circuits, [vec + (node,) for vec in all_vecs for node in self.nodes])

        m = SAT(AND(*circuits), True)
        
        if m == False:
            if return_conf:
                return False, None
            else:
                return False
        #print("model", m)
        if return_conf:
            pat = dict()
            for vec in hyperrect(conf_bounds):
                for node in self.nodes:
                    for sym in self.alph[node][1:]:
                        var = (vec, node, sym)
                        if m.get(var, False):
                            pat[(vec, node)] = sym
                            break
                    else:
                        pat[(vec, node)] = self.alph[node][0]
            #print("making separating conf from", pat, radii, periodics, self.onesided)
            markers = []
            for (i,r) in enumerate(radii):
                if i in periodics:
                    markers.append((0,0, r,r))
                else:
                    markers.append((-r,0,r,2*r))
            conf = RecognizableConf(markers, pat, self.nodes, onesided=self.onesided)
            return True, conf
        return True

    def ball_forces_allowed(self, other, r):
        all_positions = set()
        circuits = []

        bounds = [(0 if i in self.onesided else -r, r) for i in range(self.dim)]
        
        for vec in hyperrect(bounds):
            circ = self.circuit.copy()
            transform(circ, lambda var: nvadd(var[:-1], vec) + (var[-1],))
            for var in circ.get_variables():
                all_positions.add(var[:-1]) # drop letter
                #print(rel_pos)
            circuits.append(circ)

        #print (other.circuit.copy().get_variables())

        not_other = NOT(other.circuit.copy())
        for var in not_other.get_variables():
            all_positions.add(var[:-1])
        circuits.append(not_other)

        #print("megalodontix")
        #for c in circuits:
            #print(c)
            #print(c.get_variables())
            #print()
        add_uniqueness_constraints(self.alph, circuits, all_positions)
        #print("no22")
        m = SAT(AND(*circuits))
        if m == False:
            return True
        return False
        
    def deduce_global(self, conf, periodics=None, fixed_axes=None, bound=None):
        # Deduce a configuration with variable structure.
        
        # conf is a recognizable configuration
        # periodics is a list of directions we want to be periodic
        # fixed_axes is a list of directions where we have fixed the markers
        
        if periodics is None:
            periodics = []
        if fixed_axes is None:
            fixed_axes = []
        
        #print("deducing with", periodics, fixed_axes)
        
        markers = conf.minimized_markers(fixed_axes = fixed_axes)
        #print("markers minimized to", markers)
        
        marker_gens = []
        for (i, marker) in enumerate(markers):
            if i in fixed_axes:
                marker_gens.append(iter([marker]))
            else:
                marker_gens.append(gen_markers_from_minimal(marker, periodic=i in periodics))
                
        #print("marker gens", marker_gens)
        
        for (i, new_markers) in enumerate(iter_prod(*marker_gens)):
            print("deducing", i, "with markers", new_markers)
            if i == bound:
                print("bound reached")
                break
            
            # try to find a configuration with given structure
            ret_conf = self.deduce(conf.remark(list(new_markers)))
            if ret_conf is not None:
                #print("found", ret_conf.display_str())
                return ret_conf
            
            # try to find a finite patch
            filled = dict()
            for vec in hyperrect([(-i,i+1) for _ in range(self.dim)]):
                for node in self.nodes:
                    nvec = vec + (node,)
                    filled[nvec] = conf[nvec]
            finite_conf = RecognizableConf(None, filled, self.nodes)
            #print("finite_conf", finite_conf.display_str())
            if self.deduce(finite_conf) is None:
                print("failed")
                break
                
        return None

    def deduce(self, conf):
        # Deduce a recognizable configuration with a fixed marker structure.
        
        #print("deduce(", conf.display_str(), ")")
                
        diff_vecs = set(var[:-2] for var in self.circuit.get_variables())
        vec_domain = set(vsub(nvec[:-1], dvec)
                         for nvec in conf.pat
                         for dvec in diff_vecs)
                         
        #print("diff_vecs", list(sorted(diff_vecs)))
        #print("vec_domain", list(sorted(vec_domain)))
        #print("deducing from", conf.display_str())
        unknowns = set(nvec for (nvec, sym) in conf.pat.items())
        
        #print("vec_domain", vec_domain)
        #print("unknowns", unknowns)
        
        # circuits will only contain the circuits that refer only to nodes in the domain
        circuits = {}
        #vecs = set(nvec[:-1] for nvec in conf.pat)
    
        for vec in vec_domain:
            circ = self.circuit.copy()
            transform(circ, lambda var: nvwraps(conf.markers, nvadd(var[:-1], vec)) + var[-1:])
            if all(conf[var[:-1]] is not None for var in circ.get_variables()):
                circuits[vec] = circ
                
        #print("circuits", list(sorted(circuits.keys())))
        
        forceds = set()
        for (nvec, syms) in conf.pat.items():
            node = nvec[-1]
            if syms is None or (type(syms) == list and set(syms) == set(self.alph[node])):
                continue
            if type(syms) != list:
                syms = [syms]
            ored = []
            for sym in syms:
                if sym == self.alph[node][0]:
                    ored.append(AND(*(NOT(V(nvec + (a,))) for a in self.alph[node][1:])))
                else:
                    ored.append(V(nvec + (sym,)))
            forceds.add(OR(*ored))

        circuits = list(circuits.values())
        add_uniqueness_constraints(self.alph, circuits, unknowns)

        # Make SAT instance, solve and extract model
        instance = AND(*(list(circuits) + list(forceds)))
        #print("forceds", forceds)
        model = SAT(instance, True)
        if model == False:
            return None

        # Produce pattern from model
        #print("model", model)
        pat = {}
        for nvec in conf.pat:
            node = nvec[-1]
            if conf[nvec] is None:
                pat[nvec] = None
            else:
                for sym in self.alph[node][1:]:
                    if nvec + (sym,) in model and model[nvec + (sym,)]:
                        pat[nvec] = sym
                        break
                else:
                    pat[nvec] = self.alph[node][0]
        #print("final pat", pat)
        return RecognizableConf(conf.markers, pat, self.nodes, onesided=conf.onesided)

    def all_periodics(self, periods, existing=None):
        if existing is None:
            existing = dict()

        
        all_positions = set(hyperrect([(0,p) for p in periods]))
        nvecs = set(vec + (node,)
                    for vec in all_positions
                    for node in self.nodes)
        
        circuits = []
        for vec in all_positions:
            circ = self.circuit.copy()
            transform(circ, lambda var: nvmods(periods, nvadd(var[:-1], vec)) + var[-1:])
            circuits.append(circ)

        for (nvec, sym) in existing.items():
            if sym == self.alph[nvec[-1]][0]:
                circuits.extend(NOT(V(nvec+(a,))) for a in self.alph[nvec[-1]][1:])
            else:
                circuits.append(V(nvec+(sym,)))

        add_uniqueness_constraints(self.alph, circuits, nvecs)

        for model in projections(AND(*circuits), [nvec+(sym,) for nvec in nvecs for sym in self.alph[nvec[-1]][1:]]):
            pat = dict()
            for nvec in nvecs:
                for sym in self.alph[nvec[-1]][1:]:
                    if model[nvec+(sym,)]:
                        pat[nvec] = sym
                        break
                else:
                    pat[nvec] = self.alph[nvec[-1]][0]
            yield pat
        
    # generate all patterns over the given hyperrectangle where the SFT rule holds locally
    # dimensions is a list of integer pairs
    # period_structure consists of Nones (meaning fully periodic directions) and pairs (a,b),
    # where each of a and b is either None (no period) or an integer p (eventual period p)
    def all_hyperrect_patterns(self, dimensions, period_structure=None, project_to=None, extra_rad=0):
    
        if period_structure is None:
            period_structure = [(None, None)]*self.dim
            
        rads = self.radii(twosided=True)

        #print("args", dimensions, period_structure, rads)
            
        tr_bounds = []
        for (bound, spec, (rmin, rmax)) in zip(dimensions, period_structure, rads):
            if spec is None:
                # periodic direction: use exactly the hyperrect bounds
                tr_bounds.append(bound)
            else:
                a, b = spec
                if a is None:
                    # free border: ensure the ciruit fits inside
                    min_bound = bound[0]-rmin-extra_rad
                else:
                    # eventually periodic border: entire neighborhood must be in loop
                    min_bound = bound[0]+a-rmax
                if b is None:
                    max_bound = bound[1]-rmax+extra_rad
                else:
                    max_bound = bound[1]-b+rmin
                tr_bounds.append((min_bound, max_bound))
                
        #print("tr_bounds", tr_bounds)
        def wrap(vec):
            vec = list(vec)
            for (i, ((b1, b2), spec)) in enumerate(zip(dimensions, period_structure)):
                if spec is None:
                    vec[i] = (vec[i]-b1)%(b2-b1)+b1
                else:
                    a, b = spec
                    while a is not None and vec[i] < b1+a:
                        vec[i] += a
                    while b is not None and vec[i] > b2-b:
                        vec[i] -= b
            return tuple(vec)
        
        circuits = []
        for tr_vec in hyperrect(tr_bounds):
            circ = self.circuit.copy()
            transform(circ, lambda var: (wrap(vadd(tr_vec, var[0])),) + var[1:])
            circuits.append(circ)
            
        nvecs = set((vec, node,) for vec in hyperrect(dimensions) for node in self.nodes)
        if project_to is None:
            project_to = set(nvecs)
            
        for circ in circuits:
            for var in circ.get_variables():
                nvecs.add(var[:-1])
        #print("circs", circuits)
        #print("nvecs", nvecs)
        #assert all(var[:-1] in nvecs for circ in circuits for var in circ.get_variables())
        
        add_uniqueness_constraints(self.alph, circuits, nvecs)

        
        
        for model in projections(AND(*circuits), [nvec+(sym,) for nvec in project_to for sym in self.alph[nvec[-1]][1:]]):
            pat = dict()
            for nvec in project_to:
                for sym in self.alph[nvec[-1]][1:]:
                    if model[nvec+(sym,)]:
                        pat[nvec] = sym
                        break
                else:
                    pat[nvec] = self.alph[nvec[-1]][0]
            #print("yielding", pat)
            yield pat
    
    # domain is a collection of nodevectors
    def all_patterns(self, domain, existing=None, extra_rad=0):

        if existing is None:
            existing = dict()
        
        vecs = set(vadd(nvec[0], tr)
                    for nvec in domain
                    for tr in centered_hypercube(self.dim, extra_rad))

        circuits = []
        all_positions = set()
        for vec in vecs:
            #print("mippa", vec)
            circ = self.circuit.copy()
            #print(circ.get_variables())
            transform(circ, lambda var: nvadd(var[:2], vec) + var[2:])
            #print(circ.get_variables())
            for var in circ.get_variables():
                all_positions.add(var[:2])
            circuits.append(circ)
            
        for (nvec, sym) in existing.items():
            if sym == self.alph[nvec[1]][0]:
                circuits.extend(NOT(V(nvec+(a,))) for a in self.alph[nvec[1]][1:]) # TODO
            else:
                circuits.append(V(nvec+(sym,)))

        #print("kapa")
        #for c in circuits:
        #    print (c.get_variables())

        add_uniqueness_constraints(self.alph, circuits, all_positions)

        for model in projections(AND(*circuits), [nvec+(sym,) for nvec in domain for sym in self.alph[nvec[-1]][1:]]):
            pat = dict()
            for nvec in domain:
                for sym in self.alph[nvec[1]][1:]:
                    if model[nvec+(sym,)]:
                        pat[nvec] = sym
                        break
                else:
                    pat[nvec] = self.alph[nvec[1]][0]
            yield pat

    # for one-dimensional sfts, the language can be requested as strings
    # TODO: replace extra_rad with exact calculation
    def language_as_words(self, n):
        assert self.dim == 1
        for p in self.all_patterns(list(range(n)), extra_rad = 10):
            s = []
            for q in sorted(p):
                s.append(p[q])
            yield tuple(s)

    def deduce_circuit(self):
        if self.circuit is None:
            anded = []
            for forb in self.forbs:
                ored = []
                for (nvec, c) in forb.items():
                    if c == self.alph[nvec[-1]][0]:
                        ored.extend(V(nvec+(d,)) for d in self.alph[nvec[-1]][1:])
                    else:
                        ored.append(NOT(V(nvec+(c,))))
                anded.append(OR(*ored))
            self.circuit = AND(*anded)

    def deduce_forbs(self, domain=None):
        self.forbs = []
        self.deduce_forbs_(domain)
        # deduce forbs gives the forbs with true/false variables,
        # we want to simplify them into an alphabet size independent form
        # self.clean_forbs()

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

    # domain_or_rad is a collection of vectors OR an integer
    def deduce_forbs_(self, domain_or_rad=None):
        #print("alph", self.alph)
        verbose_deb = True
        var_nvecs = [var[:-1] for var in self.circuit.get_variables()]
        #print("var_nvecs", var_nvecs)
        if domain_or_rad is None:
            domain_or_rad = 0
        if type(domain_or_rad) == int:
            bounds = [(0 if i in self.onesided else -domain_or_rad, domain_or_rad+1) for i in range(self.dim)]
            vec_domain = list(hyperrect(bounds))
        else:
            vec_domain = domain_or_rad
        all_positions = set(nvadd(nvec, vec)
                            for nvec in var_nvecs
                            for vec in vec_domain)
        #vec_domain = set(var[:-2] for var in domain)
        #print("nvec_domain", vec_domain)
        #print("var_nvecs", var_nvecs)
        #print("all pos", all_positions)
        #assert len(self.alph) == 2
        assert all(nvec in all_positions for nvec in var_nvecs)

        # we want to tile domain so that it has no existing forbos, but
        # the circuit fails at the origin
        complemented = NOT(self.circuit.copy())
        #print("complemented", complemented)
        forb_circuits = [complemented]
        forb_here_circuits = [complemented]
        # note: every forb is forbidden by the untranslated circuit, so it's safe to place anywhere
        for vec in vec_domain:
            #print("implementing forb", forb)
            for forb in self.forbs:
                oreds = []
                for (forb_nvec, value) in forb.items():
                    local_vec = nvadd(forb_nvec, vec)
                    if value == self.alph[local_vec[-1]][0]:
                        oreds.extend(V(local_vec+(sym,)) for sym in self.alph[local_vec[-1]][1:])
                    else:
                        oreds.append(NOT(V(local_vec+(value,))))
                #print("oreds", oreds)
                forb_circuits.append(OR(*oreds))
                if all(c == 0 for c in vec):
                    forb_here_circuits.append(OR(*oreds))
                
        add_uniqueness_constraints(self.alph, forb_circuits, all_positions)
        add_uniqueness_constraints(self.alph, forb_here_circuits, all_positions)

        final_circ = AND(*forb_circuits)
        #print("final circ", final_circ)
        m = SAT(final_circ, True)
        if m == False:
            return None

        # we now know that m is a forbidden thingy
        # we then try to minimize it
        minimal = {}
        for nvec in var_nvecs:
            for sym in self.alph[nvec[-1]][1:]:
                minimal[nvec+(sym,)] = m[nvec+(sym,)]
        #print("minimizing", minimal)
        comp = [complemented]
        add_uniqueness_constraints(self.alph, comp, var_nvecs)
        minimal = minimize_solution(complemented, minimal, sort_by_dist=True)
        #a = bbb
        #print("got", minimal)
        
        support = set((nvec_sym[:-1]) for nvec_sym in minimal)
        new_forbs = dict() # a dict of symbol lists
        for nvec in support:
            node = nvec[-1]
            new_forbs[nvec] = []
            falses = []
            for sym in self.alph[node][1:]:
                try:
                    if minimal[nvec + (sym,)]:
                        new_forbs[nvec].append(sym)
                        break
                    else:
                        falses.append(sym)
                except KeyError:
                    pass
            else:
                new_forbs[nvec].append(self.alph[node][0])
                for sym in self.alph[node][1:]:
                    if sym not in falses:
                        new_forbs[nvec].append(sym)
                        
        #print("prod", new_forbs)
        for new_forb in product_patterns(new_forbs):
            #print("new forb", new_forb)
            if all(forb != new_forb for forb in self.forbs):
                self.forbs.append(new_forb)
        
        self.deduce_forbs_(vec_domain)

    def inconsistent_with(self, other, verbose=False):
        if verbose:
            if self.dim != other.dim:
                print("The compared SFTs have different dimensions.")
            elif self.onesided != other.onesided:
                print("The compared SFTs have different sidedness.")
            elif self.nodes != other.nodes:
                print("The compared SFTs have different nodes.")
            elif self.alph != other.alph:
                print("The compared SFTs have different alphabets.")
        return self.dim != other.dim or self.onesided != other.onesided or self.nodes != other.nodes or self.alph != other.alph

    def contains(self, other, limit = None, return_radius_and_sep = False, method="periodic", verbose=False):
        "Test containment using forced allowed patterns or special configurations"
        #print("containment method", method)
        test = self.inconsistent_with(other, verbose=verbose)
        if test:
            if return_radius_and_sep:
                return False, 0, Conf()
            else:
                return False
            
        r = 1
        while limit is None or r <= limit:
            if verbose:
                print("Trying radius", r)
            if other.ball_forces_allowed(self, r):
                if return_radius_and_sep:
                    return True, r, None
                return True
            if method == "recognizable":
                res, sep = other.exists_recognizable_not_in(self, [r]*self.dim, return_conf=return_radius_and_sep)
            elif method == "periodic":
                res, sep = other.exists_recognizable_not_in(self, [r]*self.dim,
                                                            periodics = [i for i in range(self.dim) if i not in self.onesided],
                                                            return_conf=return_radius_and_sep)
            else:
                raise Exception("Unknown method: {}".format(method))
            if res:
                if return_radius_and_sep:
                    return False, r, sep
                return False
            r += 1
        return None

    def equals(self, other, limit = None, return_radius = False, method=None, verbose=False):
        test = self.inconsistent_with(other, verbose=verbose)
        if test:
            if return_radius:
                return False, 0
            else:
                return False
        if verbose:
            print("Testing containment 1")
        c12, rad, _ = self.contains(other, limit, return_radius_and_sep = True, method=method, verbose=verbose)
        if c12 == None:
            return None, limit
        elif c12 == False:
            return False, rad
        if verbose:
            print("Testing containment 2")
        c21, rad2, _ = other.contains(self, limit, return_radius_and_sep = True, method=method, verbose=verbose)
        if c21 == None:
            return None, limit
        return c21, max(rad, rad2)

    def all_patterns_splitting(self, domain, known_values=None, extra_rad=0, rec=0):
        "Compute the number of patterns on given domain"
        if known_values is None:
            known_values = dict()

        variables = set(self.circuit.get_variables())
        var_dims = []
        dom_dims = []
        for i in range(self.dim):
            vdmin, vdmax = min(var[i] for var in variables), max(var[i] for var in variables)
            if vdmin == vdmax:
                vdmax += 1
            var_dims.append((vdmin, vdmax))
            dom_dims.append((min(nvec[i] for nvec in domain), max(nvec[i] for nvec in domain)))

        diff, splitdim = max((max_dd-min_dd-max_vd+min_vd-1, i) for (i, ((min_vd, max_vd), (min_dd, max_dd))) in enumerate(zip(var_dims, dom_dims)))
        if diff >= 3:
            # recurse
            min_vd, max_vd = var_dims[splitdim]
            min_dd, max_dd = dom_dims[splitdim]
            mid_pos = (min_dd+max_dd+min_vd-max_vd+1)//2
            #mid_vec = (0,)*splitdim + ((mid_pos,) + (0,)*(self.dim-splitdim-1)
            mid_domain = set(nvec for nvec in domain if mid_pos <= nvec[splitdim] < mid_pos+max_vd-min_vd)
            left_domain = set(nvec for nvec in domain if nvec[splitdim] < mid_pos+max_vd-min_vd)
            right_domain = set(nvec for nvec in domain if mid_pos <= nvec[splitdim])
            for mid_pat in self.all_patterns_splitting(mid_domain, known_values=known_values, extra_rad=extra_rad, rec=rec+1):
                mid_pat.update(known_values)
                rpats = list(self.all_patterns_splitting(right_domain, known_values=mid_pat, extra_rad=extra_rad, rec=rec+1))
                for lpat in self.all_patterns_splitting(left_domain, known_values=mid_pat, extra_rad=extra_rad, rec=rec+1):
                    for rpat in rpats:
                        newpat = rpat.copy()
                        rpat.update(lpat)
                        yield newpat
        else:
            # compute by brute force
            for pat in self.all_patterns(domain, existing=known_values, extra_rad=extra_rad):
                yield pat
                   
    def count_patterns_splitting(self, domain, known_values=None, extra_rad=0, rec=0):
        "Compute the number of patterns on given domain"
        if known_values is None:
            known_values = dict()

        variables = set(self.circuit.get_variables())
        var_dims = []
        dom_dims = []
        for i in range(self.dim):
            vdmin, vdmax = min(var[i] for var in variables), max(var[i] for var in variables)
            if vdmin == vdmax:
                vdmax += 1
            var_dims.append((vdmin, vdmax))
            dom_dims.append((min(nvec[i] for nvec in domain), max(nvec[i] for nvec in domain)))

        diff, splitdim = max((max_dd-min_dd-max_vd+min_vd-1, i) for (i, ((min_vd, max_vd), (min_dd, max_dd))) in enumerate(zip(var_dims, dom_dims)))
        if diff >= 3:
            # recurse
            min_vd, max_vd = var_dims[splitdim]
            min_dd, max_dd = dom_dims[splitdim]
            mid_pos = (min_dd+max_dd+min_vd-max_vd+1)//2
            #mid_vec = (0,)*splitdim + ((mid_pos,) + (0,)*(self.dim-splitdim-1)
            mid_domain = set(nvec for nvec in domain if mid_pos <= nvec[splitdim] < mid_pos+max_vd-min_vd)
            left_domain = set(nvec for nvec in domain if nvec[splitdim] < mid_pos+max_vd-min_vd)
            right_domain = set(nvec for nvec in domain if mid_pos <= nvec[splitdim])
            summa = 0
            for mid_pat in self.all_patterns_splitting(mid_domain, known_values=known_values, extra_rad=extra_rad, rec=rec+1):
                mid_pat.update(known_values)
                lefts = self.count_patterns_splitting(left_domain, known_values=mid_pat, extra_rad=extra_rad, rec=rec+1)
                rights = self.count_patterns_splitting(right_domain, known_values=mid_pat, extra_rad=extra_rad, rec=rec+1)
                summa += lefts*rights
            return summa
        else:
            # compute by brute force
            return sum(1 for _ in self.all_patterns(domain, existing=known_values, extra_rad=extra_rad))

    # A simple method that checks tilability of larger and larger boxes.
    def keep_tiling(self):
        r = 1
        while True:
            print(r)

            m = self.tile_box(r)
            assert m
            
            r += 1
        return None

    def tile_box(self, r, verbose=False):
        all_positions = set()
        circuits = []
        
        tim = time.time()
        for vec in centered_hypercube(self.dim, r):
            circ = self.circuit.copy()
            transform(circ, lambda var: nvadd(var[:-1], vec) + var[-1:])
            for var in circ.get_variables():
                all_positions.add(var[:-1]) # drop letter
            circuits.append(circ)

        add_uniqueness_constraints(self.alph, circuits, all_positions)
        if verbose:
            print("Constructed instance in {} seconds".format(time.time() - tim))

        tim = time.time()
        m = SAT(AND(*circuits))
        if verbose:
            print("Solved instance in {} seconds".format(time.time() - tim))
        return not (m == False)

def intersection(*sfts):
    assert all(node in sfts[0].nodes for other in sfts[1:] for node in other.nodes)
    circuit = AND(*(sft.circuit.copy() for sft in sfts))
    return SFT(sfts[0].dim, sfts[0].nodes, sfts[0].alph, sfts[0].topology, sfts[0].graph, circuit=circuit, onesided=sfts[0].onesided)

def product(*sfts, track_names=None):
    if track_names is None:
        track_names = list(str(n) for n in range(len(sfts)))
    nodes = Nodes({tr:sft.nodes for (tr, sft) in zip(track_names, sfts)})
    alph = {(tr,) + node : sft.alph[node]
            for (tr, sft) in zip(track_names, sfts)
            for node in sft.nodes}
    anded = []
    for (tr, sft) in zip(track_names, sfts):
        circ = sft.circuit.copy()
        transform(circ, lambda var: (var[0], (tr,) + var[1],) + var[-1:])
        anded.append(circ)
    #for sft in sfts:
    #    print(sft)
    #    print("topo", sft.topology)
    #    print()
    topology = []
    for (tr, sft) in zip(track_names, sfts):
        for t in sft.topology:
            # make new topology with track added
            #print(t)
            topology.append(t[:2] + tuple(((tr,) + n) for n in t[2:]))
    #print(topology)
    return SFT(sfts[0].dim, nodes, alph, topology, sfts[0].graph, circuit=AND(*anded), onesided=sfts[0].onesided)



