#import debug_print_hook

try:
    import dparser
    import parsy
    import gparser
except ImportError as error:
    print("Perhaps you have not installed the prerequisite modules for Griddy.")
    print("The file pip_installs.bat contains a list of pip installs you should perform.")
    import os
    if os.name == 'nt':
        print("You seem to be running Windows, so you can simply run pip_installs.bat directly.")
    print("\n\n")
        
import sys

from general import *

import compiler2 as compiler
import regexp_compiler
import sft
import sofic1d
import sofic_from_aut
import finite_automata
import configuration
import circuit
import abstract_SAT_simplify

import period_automaton
import density_linear_program
import automatic_conf
import automatic_learn
import time

import argparse
import fractions
import math

import blockmap
import tfg

import compute_sofic_image

import graphs

from basic_things import *

class Griddy:
    def __init__(self):
        self.SFTs = {}
        self.blockmaps = {}
        self.TFGs = {}
        self.clopens = {}
        self.confs = {}
        self.automata = {}
        self.environments = {}
        self.nodes = sft.Nodes()
        self.alphabet = {() : ['0', '1'] for node in self.nodes}
        self.dim = 2
        self.topology = grid
        self.graph = graphs.AbelianGroup([0,1]) #None
        #self.tiler_skew = 1 # actually skew is completely useless
        self.tiler_gridmoves = [(1,0), (0,1)]
        self.tiler_nodeoffsets = {() : (0,0)}
        self.formulae = []
        self.weights = None
        self.externals = {}
        
    def has_nodes(self):
        return self.nodes != sft.Nodes()
        
    """
    if we have no nodes, cells should double as nodes, and
    thus we pretend to always be in the ()-node of a cell
    """
    def process_nvec(self, nvec):
        #print(nvec)
        #if not self.has_nodes() and len(nvec) == self.dim:
        #    return (nvec, ())
        #print((nvec[:self.dim], nvec[-1]))
        #return (nvec[:self.dim], nvec[-1])
        if type(nvec[-1]) == tuple:
            return nvec
        else:
            return (nvec, ())

    def run_file(self, filename):
        with open(fix_filename(filename), 'r') as f:
            code = f.read()
        self.run(code)

    def run(self, code, mode="report", print_parsed=False):
        #print("mode", mode)
        # some commands accumulate results to this list, returned at the end
        results = []
        try:
            parsed = gparser.parse_griddy(code)
            if print_parsed:
                print(parsed)
        except parsy.ParseError as e:
            if mode != "silent": print("Parse error: {}".format(e))
            linenum, lineindex = parsy.line_info_at(e.stream, e.index)
            the_line = e.stream.splitlines()[linenum]
            if mode != "silent": print(the_line)
            if mode != "silent": print(" "*lineindex + "^")
            if mode == "assert" or mode == "silent":
                raise Exception("Parse error")
            return None
        #print (parsed)
        #a = bbb
        for parsed_line in parsed:
            cmd, args, kwds, flags = parsed_line
            #print("cmd", cmd, args, kwds, flags)
            print("parsed line", parsed_line)
            #if "ver_golden_mean_shift" in self.sfts:
                #print(self.sfts["ver_golden_mean_shift"].circs)
            #print(self.topology)
            
            
            if cmd == "nodes":
                #print("nodes", args[0])
                if type(args[0]) == list:
                    self.nodes = sft.Nodes.from_list(args[0])
                elif type(args[0]) == dict:
                    def clean(arg):
                        if type(arg) == dict:
                            return {key[0] if type(key) == tuple else key : clean(val) for (key, val) in arg.items()}
                        elif type(arg) == list:
                            return [val[0] if type(val) == tuple else val for val in arg]
                    self.nodes = sft.Nodes(clean(args[0]))
                alph0 = list(self.alphabet.values())[0]
                if all(alph == alph0 for alph in self.alphabet.values()):
                    self.alphabet = {node : alph0 for node in self.nodes}
                self.tiler_gridmoves = [(1,0), (0,1)] # why is this here? TODO
                #self.tiler_skew = 1
                self.tiler_nodeoffsets = {node : (2*j/(3*len(self.nodes)), 2*j/(3*len(self.nodes))) for (j,node) in enumerate(self.nodes)}
                
            elif cmd == "dim":
                dim = args[0]
                self.dim = dim
                self.tiler_gridmoves = [char_vector(self.dim, j) for j in range(self.dim)]
                self.tiler_nodeoffsets = {0 : zero_vector(self.dim)}

                # let's have this set a basic topology with ell_1
                self.topology = []
                for d in range(dim):
                    for dr in [-1, 1]:
                        if dr == -1: s = "M"
                        else: s = "P"
                        self.topology.append(("Z"*d+s+"Z"*(dim-d-1), (0,)*(dim+1), (0,)*d + (dr,) + (0,)*(dim-d-1) + (0,)))
                self.topology = modernize_topology(self.topology, self.dim)
                
            elif cmd == "alphabet":
                alph = args[0]
                default = kwds.get("default", None)
                if type(alph) == list and default is None:
                    default = alph
                self.alphabet = {node:default for node in self.nodes}
                if type(alph) == dict:
                    for (labels, local_alph) in alph.items():
                        subtr = self.nodes.subtrack(labels)
                        if subtr == False:
                            raise Exception("Invalid subtrack for {}: {}".format(self.nodes, labels))
                        for subnode in subtr:
                            node = labels + subnode
                            self.alphabet[node] = local_alph
                if None in self.alphabet.values():
                    raise Exception("Incomplete alphabet definition")

            elif cmd == "graph":
                grph = args[0]
                if grph == "none":
                    self.graph = None # this is outdated, now we should always have a graph!
                else:
                    self.topology = []
                    if grph == "Aleshin":
                        self.graph = graphs.Aleshin
                    if grph == "SC_F661":
                        self.graph = graphs.SC_F661
                    
            elif cmd == "topology":
                top = args[0]
                if top in ["line"]:
                    self.dim = 1
                    self.topology = line
                    self.nodes = sft.Nodes()
                    # only the first will be used
                    self.tiler_gridmoves = [(1, 0), (0, 1)]
                    #self.tiler_skew = 1
                    self.tiler_nodeoffsets = {() : (0,0)}
                elif top in ["square", "grid", "squaregrid"]:
                    self.dim = 2
                    self.topology = grid
                    self.nodes = sft.Nodes()
                    self.tiler_gridmoves = [(1,0), (0,1)]
                    #self.tiler_skew = 1
                    self.tiler_nodeoffsets = {() : (0,0)}
                elif top in ["hex", "hexgrid"]:
                    self.dim = 2
                    self.topology = hexgrid
                    # hex grid is currently implemented with nodes, instead of directly as a graph, so we cannot use nodes with it
                    self.nodes = sft.Nodes(['0','1']) 
                    self.tiler_gridmoves = [(1,0), (-0.5,0.8)]
                    #self.tiler_skew = 1
                    self.tiler_nodeoffsets = {('0',) : (0,0.15), ('1',) : (0.5,-0.15)}
                elif top in ["king", "kinggrid"]:
                    self.dim = 2
                    self.topology = kinggrid
                    self.nodes = sft.Nodes()
                    self.tiler_gridmoves = [(1,0), (0,1)]
                    #self.tiler_skew = 1
                    self.tiler_nodeoffsets = {() : (0,0)}
                elif top[:4] in ["king"]:
                    dim = int(top[4:])
                    self.dim = dim                    
                    self.topology = []
                    for w in words(dim, "MZP"):
                        if w != "Z"*dim:
                            v = ()
                            for i in w:
                                if i == "M": v += (-1,)
                                if i == "Z": v += (0,)
                                if i == "P": v += (1,)
                            self.topology.append((w, (0,)*dim + ((),), v+((),)))
                    self.nodes = sft.Nodes()
                    self.tiler_gridmoves = [(1,0), (0,1)]
                    #self.tiler_skew = 1
                    self.tiler_nodeoffsets = {() : (0,0)}
                elif top in ["triangle", "trianglegrid"]:
                    self.dim = 2
                    self.topology = trianglegrid
                    self.nodes = sft.Nodes()
                    self.tiler_gridmoves = [(1,0), (-0.5,0.6)]
                    #self.tiler_skew = 1
                    self.tiler_nodeoffsets = {() : (0,0)}
                elif top in ["CR"]:
                    self.dim = 2
                    self.topology = CR4d8e2_topology
                    self.nodes = CR4d8e2_nodes
                    self.tiler_gridmoves = [(1,0), (-0.5,0.5)]
                    #self.tiler_skew = 1
                    self.tiler_nodeoffsets = {"big" : (0,0), "small" : (0.5,0)}
                else:
                    self.topology = []
                    legacy = None
                    for edge in top:
                        if legacy == None:
                            legacy = (len(edge) == 3)
                            #print("legacy topology? " + str(legacy))
                        else:
                            assert legacy == (len(edge) == 3)
                        if legacy:
                            if edge:
                                if len(edge) > 3:
                                    raise Exception("Bad topology edge: {}; maybe you forgot a semicolon?".format(edge))
                                if len(edge) < 3:
                                    raise Exception("Bad topology edge: {}".format(edge))
                                self.topology.append((edge[0],) + tuple(self.process_nvec(nvec) for nvec in edge[1:]))
                        else:
                            if len(edge) == 4:
                                self.topology.append(edge)
                            else:
                                self.topology.append(edge + ((), ()))
                    if legacy:
                        self.topology = modernize_topology(self.topology, self.dim)
                if type(top) == str:
                    alph0 = list(self.alphabet.values())[0]
                    if all(alph == alph0 for alph in self.alphabet.values()):
                        self.alphabet = {node : alph0 for node in self.nodes}
                """
                We construct a graph from the topology and nodes, so that commands that use graphs will work.
                We do not enter full "graph mode", however, where nodes would be on top of the graph.
                """
                self.graph = graphs.AbelianGroup(range(self.dim))
                #print("ki", self.topology)
                

            elif cmd == "save_environment":
                name = args[0]
                self.environments[name] = (self.dim, self.nodes, self.topology, self.alphabet, self.graph)

            elif cmd == "load_environment":
                name = args[0]
                if name in self.environments:
                    self.dim, self.nodes, self.topology, self.alphabet, self.graph = self.environments[name]
                    
                elif name in self.SFTs:
                    the_sft = self.SFTs[name]
                    self.dim = the_sft.dim
                    self.nodes = the_sft.nodes
                    self.topology = the_sft.topology
                    self.alphabet = the_sft.alph
                    self.graph = the_sft.graph
                    
            elif cmd == "sft" or cmd == "clopen":
                name = args[0]
                defn = args[1]
                onesided = kwds.get("onesided", [])
                if cmd == "sft":
                    constructor = sft.SFT
                else:
                    constructor = sft.Clopen
                if "verbose" in flags:
                    if cmd == "sft":
                        if mode != "silent": print("Defining SFT named", name)
                    else:
                        if mode != "silent": print("Defining clopen set named", name)
                # Definition is either a list of forbidden patterns or a formula
                if type(defn) == list:
                    forbs = [{self.process_nvec(nvec) : sym for (nvec, sym) in forb.items()} for forb in defn]
                    #print("defn", defn, "forbs", forbs)
                    self.SFTs[name] = constructor(self.dim, self.nodes, self.alphabet, self.topology, self.graph, forbs=forbs, onesided=onesided)
                elif type(defn) == tuple:
                    #print("defn", defn)
                    #circ = compiler.formula_to_circuit(self.nodes, self.dim, self.topology, self.alphabet,
                    #                                   defn, self.externals, simplify="simplify" in flags)
                    
                    #graph, topology, nodes, alphabet, formula, externals, simplify
                    #print(self.topology, "filippo")
                    circ = compiler.formula_to_circuit2(self.graph, self.topology, self.nodes, self.alphabet, defn, self.externals, simplify="simplify" in flags)
                    #vardict = dict()
                    #inst = circuit.circuit_to_sat_instance(circ, vardict)
                    #import abstract_SAT_simplify
                    if "simplify" in flags:
                        _, simp = abstract_SAT_simplify.simplify_circ_eqrel(circ)
                        simp.simplify()
                        #print (inst[0])
                        #s = set(abs(v) for c in inst[0] for v in c)
                        s1 = sum(1 for _ in circ.internal_nodes(vars_too=True))
                        s2 = sum(1 for _ in simp.internal_nodes(vars_too=True))
                        if "verbose" in flags:
                            if mode != "silent": print ("Circuit size", s1, "reduced to", s2)
                        circ = simp
                    
                    self.SFTs[name] = constructor(self.dim, self.nodes, self.alphabet, self.topology, self.graph, circuit=circ, formula=defn, onesided=onesided)
                else:
                    raise Exception("Unknown SFT definition: {}".format(defn))
                #print("CIRCUIT", circ)
                #print("CIRCUIT", self.SFTs[name].circuit)
                
            elif cmd == "sofic1D":
                sofic_name = args[0]
                name = args[1]
                verbose = "verbose" in flags
                if name in self.SFTs:
                    self.SFTs[sofic_name] = sofic1d.Sofic1D.from_SFT(self.SFTs[name], verbose=verbose)
                elif name in self.automata:
                    if "forbs" in flags:
                        self.SFTs[sofic_name] = sofic_from_aut.sofic_from_forbs(self.nodes, self.alphabet, self.topology, self.automata[name], onesided="onesided" in flags, verbose=verbose)
                    else:
                        self.SFTs[sofic_name] = sofic_from_aut.sofic_as_limit(self.nodes, self.alphabet, self.topology, self.automata[name], onesided="onesided" in flags, verbose=verbose)

            elif cmd == "regexp":
                name = args[0]
                regexp = args[1]
                verbose = "verbose" in flags
                aut = regexp_compiler.compile_regexp(self.nodes, self.alphabet, regexp, verbose=verbose)
                if "minimize" in flags:
                    aut = aut.determinize().minimize()
                if verbose:
                    if mode != "silent": print("Produced {}-state {}.".format(len(aut.states), "DFA" if isinstance(aut, finite_automata.DFA) else "NFA"))
                self.automata[name] = aut
                
            elif cmd == "determinize":
                name = args[0]
                verbose = "verbose" in flags
                if name in self.SFTs:
                    self.SFTs[name].determinize(verbose=verbose)
                elif name in self.automata:
                    self.automata[name] = self.automata[name].determinize(verbose=verbose)
                
            elif cmd == "minimize":
                name = args[0]
                verbose = "verbose" in flags
                if name in self.SFTs:
                    self.SFTs[name].minimize(verbose=verbose)
                elif name in self.automata:
                    self.automata[name] = self.automata[name].minimize(verbose=verbose)

            elif cmd == "intersection":
                isect_name = args[0]
                names = args[1]
                if not names:
                    raise Exception("Empty intersection")
                sfts = []
                for name in names:
                    try:
                        sfts.append(self.SFTs[name])
                    except KeyError:
                        raise Exception("{} is not an SFT".format(name))
                first = sfts[0]
                for other in sfts[1:]:
                    if first.dim != other.dim:
                        raise Exception("Incompatible dimensions: {} and {}".format(first.dim, other.dim))
                    if first.nodes != other.nodes:
                        raise Exception("Incompatible node sets: {} and {}".format(first.nodes, other.nodes))
                    if first.alph != other.alph:
                        raise Exception("Incompatible alphabets: {} and {}".format(first.alph, other.alph))
                    if first.onesided != other.onesided:
                        raise Exception("Cannot intersect onesided and twosided SFT")
                if isinstance(first, sft.SFT) or isinstance(first, sft.Clopen) or isinstance(first, sft.CSIntersection):
                    self.SFTs[isect_name] = sft.intersection(*sfts)
                else:
                    self.SFTs[isect_name] = sofic1d.intersection(*sfts)
                
            elif cmd == "union":
                isect_name = args[0]
                names = args[1]
                if not names:
                    raise Exception("Empty intersection")
                sofics = []
                for name in names:
                    try:
                        sofics.append(self.SFTs[name])
                    except KeyError:
                        raise Exception("{} is not an SFT".format(name))
                    if not isinstance(self.SFTs[name], sofic1d.Sofic1D):
                        raise Exception("Can only compute unions of 1D sofic shifts")
                first = sofics[0]
                for other in sofics[1:]:
                    if first.dim != other.dim:
                        raise Exception("Incompatible dimensions: {} and {}".format(first.dim, other.dim))
                    if first.nodes != other.nodes:
                        raise Exception("Incompatible node sets: {} and {}".format(first.nodes, other.nodes))
                    if first.alph != other.alph:
                        raise Exception("Incompatible alphabets: {} and {}".format(first.alph, other.alph))
                    if first.onesided != other.onesided:
                        raise Exception("Cannot intersect onesided and twosided SFT")
                self.SFTs[isect_name] = sofic1d.union(*sofics)

            elif cmd == "product":
                prod_name = args[0]
                names = args[1]
                if not names:
                    raise Exception("Empty product")
                sfts = []
                for name in names:
                    try:
                        sfts.append(self.SFTs[name])
                    except KeyError:
                        raise Exception("{} is not an SFT or sofic shift".format(name))
                if any((sft.dim, sft.onesided, type(sft)) != (sfts[0].dim, sfts[0].onesided, type(sfts[0])) for sft in sfts[1:]):
                    raise Exception("Incompatible SFTs or sofic shifts")
                track_names = kwds.get("tracks", None)
                # where do we put the environment of the product
                env = kwds.get("env", None)
                if isinstance(sfts[0], sft.SFT):
                    prod = sft.product(*sfts, track_names=track_names)
                else:
                    prod = sofic1d.product(*sfts, track_names=track_names)
                self.SFTs[prod_name] = prod
                if env != None:
                    env_dim = prod.dim
                    env_nodes = prod.nodes
                    env_alphabet = prod.alph
                    env_topology = prod.topology
                    if env != "env":
                        self.environments[env] = (env_dim, env_nodes, env_topology, env_alphabet)
                    else:
                        self.dim = env_dim
                        self.nodes = env_nodes
                        self.topology = env_topology
                        self.alphabet = env_alphabet

            elif cmd == "language":
                lang_name = args[0]
                sofic_name = args[1]
                try:
                    the_sofic = self.SFTs[sofic_name]
                except KeyError:
                    raise Exception("{} is not a 1D sofic shift".format(sofic_name))
                if not isinstance(the_sofic, sofic1d.Sofic1D):
                    raise Exception("{} is not a 1D sofic shift".format(sofic_name))
                self.automata[lang_name] = the_sofic.language()
                        
            elif cmd == "trace":
                trace_name = args[0]
                sft_name = args[1]
                try:
                    the_sft = self.SFTs[sft_name]
                except KeyError:
                    raise Exception("{} is not an SFT".format(sft_name))
                trace_size = args[2]
                trace_spec = args[3]
                verbose = "verbose" in flags
                extra_rad = kwds.get("extra_rad", 0)
                if verbose:
                    if mode != "silent": print("Extracting trace of size {} and spec {} from SFT {}".format(trace_size, trace_spec, sft_name))
                the_trace = sofic1d.Sofic1D.trace(the_sft, trace_size, trace_spec, verbose=verbose, extra_rad=extra_rad)
                self.SFTs[trace_name] = the_trace

            elif cmd == "clopen":
                raise NotImplementedError("Clopen sets not implemented")
                #compiled = compiler.formula_to_circuit(self.nodes, self.dim, self.topology, self.alphabet, i[2])
                #self.clopens[i[1]] = i[2]

            elif cmd == "relation":
                sft_name = args[0]
                blockmap_name = args[1]
                try:
                    block_map = self.blockmaps[blockmap_name]
                except KeyError:
                    raise Exception("{} is not a block map".format(blockmap_name))
                tracks = kwds.get("tracks", None)
                self.SFTs[sft_name] = block_map.relation(tracks=tracks)

            elif cmd == "spacetime_diagram":
                sft_name = args[0]
                ca_name = args[1]
                try:
                    the_ca = self.blockmaps[ca_name]
                except KeyError:
                    raise Exception("{} is not a CA".format(ca_name))
                if not the_ca.is_CA():
                    raise Exception("{} is not a CA".format(ca_name))
                time_axis = kwds.get("time_axis", None)
                twosided = "twosided" in flags
                #print("Computing the spacetime diagram of {} into {}".format(ca_name, sft_name))
                self.SFTs[sft_name] = the_ca.spacetime_diagram(onesided=not twosided, time_axis=time_axis)
                #print(self.SFTs[sft_name].nodes, self.SFTs[sft_name].topology)

            elif cmd == "preimage":
                preim_name = args[0]
                blockmap_name = args[1]
                try:
                    block_map = self.blockmaps[blockmap_name]
                except KeyError:
                    raise Exception("No block map named {}".format(blockmap_name))
                sft_name = args[2]
                try:
                    the_sft = self.SFTs[sft_name]
                except KeyError:
                    raise Exception("No SFT named {}".format(sft_name))
                if (the_sft.dim, the_sft.nodes, the_sft.alph) != (block_map.dimension, block_map.to_nodes, block_map.to_alphabet):
                    raise Exception("SFT {} is incompatible with codomain of {}".format(sft_name, blockmap_name))
                self.SFTs[preim_name] = block_map.preimage(the_sft)

            elif cmd == "fixed_points":
                sft_name = args[0]
                ca_name = args[1]
                try:
                    the_ca = self.blockmaps[ca_name]
                except KeyError:
                    raise Exception("{} is not a CA".format(ca_name))
                if not the_ca.is_CA():
                    raise Exception("{} is not a CA".format(ca_name))
                self.SFTs[sft_name] = the_ca.fixed_points()

            elif cmd == "sofic_image":
                sofic_image_name = args[0]
                ca_name = args[1]
                sofic_preimage_name = args[2]
                try:
                    the_ca = self.blockmaps[ca_name]
                except KeyError:
                    raise Exception("{} is not a CA".format(ca_name))
                if not the_ca.is_CA():
                    raise Exception("{} is not a CA".format(ca_name))
                try:
                    the_sofic = self.SFTs[sofic_preimage_name]
                except KeyError:
                    raise Exception("{} is not a sofic shift".format(sofic_preimage_name))
                if not isinstance(the_sofic, sofic1d.Sofic1D):
                    raise Exception("{} is not a sofic shift".format(sofic_preimage_name))
                self.SFTs[sofic_image_name] = compute_sofic_image.sofic_from_BM_and_sofic(the_ca, the_sofic)
                
            elif cmd == "minimum_density":
                verbose_here = False
                sft_name = args[0]
                if sft_name not in self.SFTs:
                    raise Exception("{} is not an SFT".format(sft_name))
                tim = time.time()
                the_sft = self.SFTs[sft_name]
                if the_sft.forbs is None:
                    raise Exception("{} has no forbidden patterns".format(sft_name))
                periods = args[1]
                threads = kwds.get("threads", 1)
                conf_name = kwds.get("conf_name", None)
                comp_mode = kwds.get("mode", 'S')
                if comp_mode not in ['Q','S','L']:
                    raise Exception("Unknown mode for minimum density: {}".format(comp_mode))
                if comp_mode == 'L' and conf_name is not None:
                    raise Exception("No configuration is available with mode L")
                chunk_size = kwds.get("chunk_size", 200)
                sym_bound = kwds.get("symmetry", None)
                if sym_bound is not None and any(n%2 for n in periods[0]):
                    if mode != "silent": print("First period vector must be even for symmetry breaking")
                    break
                print_freq_pop = kwds.get("print_freq_pop", 5000) and (mode != "silent")
                print_freq_cyc = kwds.get("print_freq_cyc", 1000) and (mode != "silent")
                verb = "verbose" in flags
                rot = "rotate" in flags
                if rot and (the_sft.dim != 2 or periods[0][0] != 0):
                    raise Exception("Rotation only available in 2D and with periods (N,0)")
                if mode != "silent": print("Computing minimum density for %s restricted to period(s) %s"%(sft_name, periods) + (" using weights {}".format(self.weights) if self.weights is not None else ""))
                nfa = period_automaton.PeriodAutomaton(the_sft, periods, weights=self.weights, verbose=verb, rotate=rot, sym_bound=sym_bound)
                border_size = len(the_sft.nodes)*len(nfa.frontier)
                pmat = nfa.pmat
                if mode != "silent" and verbose_here: print("const")
                nfa.populate(verbose=verb, num_threads=threads, chunk_size=chunk_size, report=print_freq_pop)
                if mode != "silent" and verbose_here: print("popula")
                nfa.minimize(verbose=verb)
                if mode != "silent" and verbose_here: print("minim")
                comps = list(nfa.strong_components())
                if not comps:
                    if mode != "silent": print("No configurations exist with given period(s)")
                    continue
                if mode != "silent" and verbose_here: print("strng com")
                del nfa
                min_data = (math.inf,)
                min_aut = None
                for (ic, comp) in enumerate(comps):
                    if verb:
                        if mode != "silent": print("Component {}/{} ({} states)".format(ic+1, len(comps), len(comp.trans)))
                    if comp_mode == 'Q':
                        data = comp.square_min_density_cycle(verbose=verb, num_threads=threads, report=print_freq_cyc)
                    elif comp_mode == 'S':
                        data = comp.linsqrt_min_density_cycle(verbose=verb, num_threads=threads, report=print_freq_cyc)
                    elif comp_mode == 'L':
                        data = comp.linear_min_density_cycle(verbose=verb, num_threads=threads, report=print_freq_cyc)
                    if data[:1] < min_data[:1]:
                        min_data = data
                        min_aut = comp
                if mode != "silent" and verbose_here: print("kikek")
                if comp_mode in 'QS':
                    dens, minlen, stcyc, cyc = min_data
                    true_dens = fractions.Fraction(sum(self.weights[b] if self.weights is not None else int(b) for fr in cyc for b in fr.values()),
                                                        len(cyc)*border_size)
                    if mode != "silent": print("Density", true_dens, "~", dens/(border_size*min_aut.weight_denominator), "realized by cycle of length", len(cyc))
                    if conf_name is None:
                        if mode != "silent": print([(nvadd(nvec,(tr,)+(0,)*(the_sft.dim-1)),c) for (tr,pat) in enumerate(cyc) for (nvec,c) in sorted(pat.items())])
                    else:
                        # TODO: this should be in period_automaton
                        cycpat = dict()
                        for (tr, subpat) in enumerate(cyc):
                            for (nvec, sym) in subpat.items():
                                nvec = (((nvec[0][0]+tr)%len(cyc),) + nvec[0][1:], nvec[1])
                                cycpat[nvec] = sym
                        conf_periods = []
                        for i in reversed(range(1, the_sft.dim)):
                            running_lcm = math.lcm(len(cyc), pmat[i-1][i])
                            for (j, per) in enumerate(conf_periods, start=1):
                                running_lcm = math.lcm(running_lcm, per, pmat[i-1][the_sft.dim-j])
                            conf_periods.append(running_lcm)
                        conf_periods = [len(cyc)] + conf_periods[::-1]
                        pat = dict()
                        for vec in hyperrect([(0,per) for per in conf_periods]):
                            patvec = vec
                            for i in range(1, the_sft.dim):
                                nper = vec[i]//pmat[i-1][i]
                                vec = tuple(a-nper*c for (a,c) in zip(vec, pmat[i-1]))
                            #print(vec[0])
                            vec = (vec[0]%len(cyc),) + vec[1:]
                            #print("patvec", patvec, "into vec", vec)
                            for node in the_sft.nodes:
                                pat[(patvec, node)] = cycpat[(vec, node)]
                        self.confs[conf_name] = configuration.RecognizableConf(conf_periods, pat, the_sft.nodes)
                else:
                    dens, minlen, _ = min_data
                    if mode != "silent": print("Density", dens/(border_size*min_aut.weight_denominator), "realized by cycle of length", minlen, "in minimized automaton")
                expect = kwds.get("expect", None)
                if expect is not None and mode == "assert":
                    if mode != "silent": print(true_dens, "=", expect)
                    assert true_dens == expect
                if mode != "silent": print("Calculation took", time.time() - tim, "seconds.")

            elif cmd == "density_lower_bound":
                sft_name = args[0]
                if sft_name not in self.SFTs:
                    raise Exception("{} is not an SFT".format(sft_name))
                tim = time.time()
                the_sft = self.SFTs[sft_name]
                rad = kwds.get("radius", 0)
                save_constr = kwds.get("save_constr", None)
                load_constr = kwds.get("load_constr", None)
                specs = args[1]
                if not specs:
                    raise Exception("@density_lower_bound requires nonempty specs")
                if type(specs[0][0]) == tuple:
                    # single spec
                    specs = [specs]
                specs = [(dirs, [self.process_nvec(nvec) for nvec in nhood])
                         for [dirs, nhood] in specs]
                print_freq = kwds.get("print_freq", 5000)
                verb = "verbose" in flags
                show_rules = "show_rules" in flags
                print("Computing lower bound for density in {} using specs {} and additional radius {}".format(sft_name, specs, rad))
                # TODO: display nhoods properly
                #patterns = list(the_sft.all_patterns(nhood))
                data = density_linear_program.optimal_density(the_sft, specs, rad, weights=self.weights, verbose=verb, print_freq=print_freq, ret_shares=show_rules, load_constr=load_constr, save_constr=save_constr)
                if show_rules:
                    dens, rules = data
                    if mode != "silent": print("Discharging rules")
                    for (fr_pat, amounts) in sorted(rules.items(), key=lambda p: tuple(sorted(p[0].items()))):
                        if amounts:
                            if mode != "silent": print("on {}:".format(dict(fr_pat)))
                            for (vec, amount) in sorted(amounts.items()):
                                if mode != "silent": print("send {} to {}".format(amount, vec))
                else:
                    dens = data
                if mode != "silent": print("Lower bound", dens)
                expect = kwds.get("expect", None)
                if expect is not None and mode == "assert":
                    if mode != "silent": print(dens, "=", expect)
                    assert dens == expect
                if mode != "silent": print("Calculation took", time.time() - tim, "seconds.")

            elif cmd == "find_automatic_conf":
                conf_name = args[0]
                sft_name = args[1]
                arity = kwds.get("arity", 2)
                extra_rad = kwds.get("extra_rad", 0)
                buffer_rad = kwds.get("buffer_rad", 0)
                print_freq = kwds.get("print_freq", 1000)
                infer_print_freq = kwds.get("infer_print_freq", 1000)
                search_mode = kwds.get("mode", "gold")
                backtrack_depth = kwds.get("backtrack_depth", 0)
                max_lookahead = kwds.get("max_lookahead", None)
                verb = "verbose" in flags
                try:
                    the_sft = self.SFTs[sft_name]
                except KeyError:
                    raise Exception("No SFT named {}".format(sft_name))
                struct = automatic_conf.AutomaticStructure.n_ary(the_sft.dim, arity, the_sft.nodes) # for now
                builder = automatic_learn.LexMinBuilder(the_sft, extra_rad=extra_rad, max_lookahead=max_lookahead)
                if mode != "silent": print("Finding automatic configuration in SFT", sft_name)
                tim = time.time()
                if search_mode == "angluin":
                    conf = automatic_learn.learn_lex_min_angluin(struct, the_sft, builder, verbose=verb, print_freq=print_freq)
                elif search_mode == "gold":
                    conf = automatic_learn.learn_lex_min_gold(struct, the_sft, builder, verbose=verb, print_freq=print_freq, infer_print_freq=infer_print_freq, buffer_rad=buffer_rad, backtrack_depth=backtrack_depth)
                self.confs[conf_name] = conf
                if mode != "silent": print("Calculation took", time.time()-tim, "seconds")

            elif cmd == "show_formula" and mode == "report":
                name = args[0]
                if name in self.SFTs:
                    formula = self.SFTs[name].circuit
                elif name in self.clopens:
                    formula = self.clopens[name][2]
                elif name in self.blockmaps:
                    formula = self.blockmaps[name].circuits
                else:
                    raise Exception("No set named %s" % name)
                if mode != "silent": print("Showing compiled formula(s) for %s." % name)
                if mode != "silent": print(formula)
                if mode != "silent": print()
                
            elif cmd == "show_parsed" and mode == "report":
                name = args[0]
                if name in self.SFTs:
                    formula = self.SFTs[name].formula
                elif name in self.clopens:
                    formula = self.clopens[name][2]
                else:
                    raise Exception("No set named %s" % name)
                if mode != "silent": print("Showing parsed formula for %s." % name)
                if mode != "silent": print(formula)
                if mode != "silent": print()

            elif cmd == "show_graph" and mode == "report":
                name = args[0]
                if name in self.SFTs and isinstance(self.SFTs[name], sofic1d.Sofic1D):
                    trans = self.SFTs[name].trans
                else:
                    raise Exception("No sofic shift named %s" % name)
                if mode != "silent": print("Showing transition graph of %s." % name)
                if mode != "silent": print(trans)
                if mode != "silent": print()

            elif cmd == "show_environment":
                name = kwds.get("sft", None)
                if name == None:
                    if mode != "silent": print (self.dim, self.nodes, self.topology, self.alphabet)
                else:
                    if mode != "silent": print (self.SFTs[name].dim, self.SFTs[name].nodes, self.SFTs[name].topology, self.SFTs[name].alph)
                    
            elif cmd == "info":
                names = args[0]
                verbose = "verbose" in flags
                if names:
                    for name in names:
                        if mode != "silent": print()
                        found = False
                        if name in self.confs:
                            if mode != "silent": print(self.confs[name].info_string(name, verbose=verbose))
                            found = True
                        if name in self.SFTs:
                            if mode != "silent": print(self.SFTs[name].info_string(name, verbose=verbose))
                            found = True
                        if name in self.blockmaps:
                            if mode != "silent": print(self.blockmaps[name].info_string(name, verbose=verbose))
                            found = True
                        if name in self.automata:
                            if mode != "silent": print(self.automata[name].info_string(name, verbose=verbose))
                            found = True
                        if not found:
                            raise Exception("Unknown object: {}".format(name))
                else:
                    if mode != "silent": print("Current environment")
                    if mode != "silent": print("Dimension: {}".format(self.dim))
                    if mode != "silent": print("Nodes: {}".format("[" + ", ".join(self.nodes.str_nodes()) + "]"))
                    if mode != "silent": print("Topology: {}".format(self.topology))
                    if mode != "silent": print("Alphabet: {}".format(self.alphabet))
                    if mode != "silent": print("Symbol weights: {}".format(self.weights))
                    if verbose:
                        if mode != "silent": print("Named subshifts: {}".format(list(self.SFTs)))
                        if mode != "silent": print("Named block maps: {}".format(list(self.blockmaps)))
                        if mode != "silent": print("Named configurations: {}".format(list(self.confs)))
                        if mode != "silent": print("Named environments: {}".format(list(self.environments)))
                        if mode != "silent": print("Tiler vectors: {}".format(self.tiler_gridmoves))
                        if mode != "silent": print("Tiler offsets: {}".format(self.tiler_nodeoffsets))

            elif cmd == "run":
                filename = args[0]
                self.run_file(filename)

            elif cmd == "show_conf" and mode == "report":
                name = args[0]
                hide_contents = "hide_contents" in flags
                if name in self.confs:
                    conf = self.confs[name]
                else:
                    raise Exception("No configuration named %s" % name)
                if mode != "silent": print(conf.display_str(hide_contents=hide_contents))
                if mode != "silent": print()
                
            elif cmd == "empty":
                name = args[0]
                expect = kwds.get("expect", None)
                conf_name = kwds.get("conf_name", None)
                verb = "verbose" in flags
                if name in self.SFTs:
                    the_sft = self.SFTs[name]
                    conf = report_SFT_empty((name,the_sft), verbose=verb, truth=expect, mode=mode)
                    if conf_name is not None and conf is not None:
                        self.confs[conf_name] = conf
                else:
                    raise Exception("No SFT or sofic shift named {}".format(name))

            elif cmd == "equal":
                name1 = args[0]
                name2 = args[1]
                expect = kwds.get("expect", None)
                method = kwds.get("method", "periodic")
                verb = "verbose" in flags
                if name1 in self.SFTs and name2 in self.SFTs:
                    SFT1 = self.SFTs[name1]
                    SFT2 = self.SFTs[name2]
                    report_SFT_equal((name1, SFT1), (name2, SFT2), mode=mode, truth=expect, method=method, verbose=verb)

                elif name1 in self.blockmaps and name2 in self.blockmaps:
                    CA1 = self.blockmaps[name1]
                    CA2 = self.blockmaps[name2]
                    report_blockmap_equal((name1, CA1), (name2, CA2), mode=mode, truth=expect, verbose=verb)

                elif name1 in self.automata and name2 in self.automata:
                    aut1 = self.automata[name1]
                    aut2 = self.automata[name2]
                    report_aut_equal((name1, aut1), (name2, aut2), truth=expect, verbose=verb)
                
                else:
                    raise Exception("%s and %s are not comparable." % (name1, name2))
                
                    #if i[1] not in clopens or i[2] not in clopens:
                    #    raise Exception("%s not a clopen set"i[1] )                
                    #clopen1 = clopens[i[1]]
                    #clopen2 = clopens[i[2]]
                    #raise Exception("Comparison of clopen sets not implemented.")
                    
            elif cmd == "contains":
                item1 = args[0]
                item2 = args[1]
                expect = kwds.get("expect", None)
                method = kwds.get("method", "periodic")
                conf_name = kwds.get("conf_name", None)
                verb = "verbose" in flags
                if item1 in self.SFTs:
                    SFT1 = self.SFTs[item1]
                    if item2 in self.SFTs:
                        SFT2 = self.SFTs[item2]
                        conf = report_SFT_contains((item1, SFT1), (item2, SFT2), mode=mode, truth=expect, method=method, verbose=verb)
                        if conf_name is not None and conf is not None:
                            self.confs[conf_name] = conf
                    elif item2 in self.confs:
                        conf = self.confs[item2]
                        report_SFT_in((item1, SFT1), (item2, conf), mode=mode, truth=expect)
                    else:
                        raise Exception("No SFT, sofic or configuration named {}".format(item2))
                elif item1 in self.automata:
                    aut1 = self.automata[item1]
                    if item2 in self.automata:
                        aut2 = self.automata[item2]
                        report_aut_contains((item1, aut1), (item2, aut2), truth=expect, verbose=verb)
                    else:
                        raise Exception("No automaton named {}".format(item2))
                else:
                    clopen1 = self.clopens[item1]
                    clopen2 = self.clopens[item2]
                    raise Exception("Comparison of clopen sets not implemented.")

            elif cmd == "compare_sft_pairs" and mode == "report":
                method = kwds.get("method", "periodic")
                for a in self.SFTs:
                    for b in self.SFTs:
                        if a == b:
                            continue
                        report_SFT_contains((a, self.SFTs[a]), (b, self.SFTs[b]), method=method)

            elif cmd == "compare_SFT_pairs_equality" and mode == "report":
                method = kwds.get("method", "periodic")
                #print(SFTs_as_list)
                for (i, (aname, a)) in enumerate(self.SFTs.items()):# SFTs_as_list):
                    for (bname, b) in list(self.SFTs.items())[i+1:]: #SFTs_as_list[i+1:]:
                        report_SFT_equal((aname, a), (bname, b), method=method)

            elif cmd == "show_forbidden_patterns":
                name = args[0]
                the_sft = self.SFTs[name]
                if mode != "silent": print("Showing forbidden patterns for %s." % name)
                if the_sft.forbs is None:
                    if mode != "silent": print("Forbidden patterns not yet computed.")
                else:
                    for forb in the_sft.forbs:
                        if mode != "silent": print(forb)
                print()

            elif cmd == "compute_forbidden_patterns":
                name = args[0]
                the_sft = self.SFTs[name]
                rad = kwds.get("radius", 0)
                filename = kwds.get("filename", None)
                save_msg = " into {}.output".format(filename) if filename is not None else ""
                if mode == "report":
                    if rad is None:
                        if mode != "silent": print("Computing forbidden patterns for {}{}.".format(name, save_msg))
                    else:
                        if mode != "silent": print("Computing forbidden patterns for {}{} using radius {}.".format(name, save_msg, rad))
                    if the_sft.forbs is not None:
                        if mode != "silent": print("It already had forbidden patterns; overwriting them.")
                the_sft.deduce_forbs(rad)
                if mode != "silent": print("Found {} patterns.".format(len(the_sft.forbs)))
                if "verbose" in flags:
                    for f in the_sft.forbs:
                        if mode != "silent": print(f)
                
                if filename is not None:
                    with open(filename+".output", 'w') as f:
                        f.write(str(the_sft.forbs))
                        
            elif cmd == "load_forbidden_patterns":
                sft_name = args[0]
                the_sft = self.SFTs[sft_name]
                filename = args[1]
                if mode == "report":
                    if mode != "silent": print("Loading forbidden patterns of {} from {}.output.".format(sft_name, filename))
                with open(filename+".output", 'r') as f:
                    contents = f.read()
                forbs = eval(contents)
                the_sft.forbs = forbs

            elif cmd == "set_weights":
                self.weights = {arg[0] : w for (arg, w) in args[0].items()}
                if mode != "silent": print("Weights set to", self.weights)

            elif cmd == "wang":
                name = args[0]
                tiles = args[1]
                custom_topology = False

                #print(flags)
                
                # a flag can be used to make this use the current topology
                if "topology" in flags or "use_topology" in flags or "custom_topology" in flags:
                    custom_topology = True
                    raise Exception("Work in progress...")
                    colors, formula = general_Wang(tiles, nodes, topology, kwargs.get("inverses", []))
                # ad hoc code for 2d Wang tiles
                else:
                    colors, formula = basic_2d_Wang(tiles)
                    
                circ = compiler.formula_to_circuit(Wang_nodes, 2, Wang_topology, colors, formula, self.externals)
                self.SFTs[name] = sft.SFT(2, Wang_nodes, self.alphabet, circuit=circ, formula=formula)

            # caching is global, is that dangerous?
            # in principle we could have a circuitset here in griddy,
            # and (through compiler) tell Circuit that we are using one,
            elif cmd == "start_cache":
                compiler.start_cache(args[0], args[1])
            elif cmd == "end_cache":
                compiler.end_cache()

            elif cmd == "block_map":
                name = args[0]
                rules = args[1]
                domain_name = kwds.get("domain", None)
                check = "check_overlaps" in flags
                ignore = "ignore_overlaps" in flags
                verbose = "verbose" in flags
                if check and ignore:
                    raise Exception("Conflicting options: @check_overlaps and @ignore_overlaps")
                if check:
                    overlaps = "check"
                elif ignore:
                    if mode != "silent": print("Warning: if a block map definition has overlapping rules, ignoring them can lead to undefined behavior")
                    overlaps = "ignore"
                else:
                    overlaps = "remove"
                if domain_name is None:
                    dom_dim, dom_nodes, dom_top, dom_alph, dom_graph = self.dim, self.nodes, self.topology, self.alphabet, self.graph
                else:
                    dom_dim, dom_nodes, dom_top, dom_alph, dom_graph = self.environments[domain_name]
                codomain_name = kwds.get("codomain", None)
                if codomain_name is None:
                    cod_dim, cod_nodes, cod_top, cod_alph, cod_graph = self.dim, self.nodes, self.topology, self.alphabet, self.graph
                else:
                    cod_dim, cod_nodes, cod_top, cod_alph, cod_graph = self.environments[codomain_name]
                if dom_dim != cod_dim:
                    raise Exception("Dimension mismatch: {} is not {}".format(dom_dim, cod_dim))
                if dom_graph != cod_graph:
                    raise Exception("Graph mismatch: {} is not {}".format(dom_graph, cod_graph))
                circuits = [] #dict()
                for rule in rules:
                    if rule:
                        if self.has_nodes() and len(rule) != 3:
                            if len(rule) > 3:
                                raise Exception("Bad block map rule: {}\nMaybe you forgot a semicolon?".format(rule))
                            else:
                                raise Exception("Bad block map rule: {}".format(rule))
                        elif not self.has_nodes() and len(rule) != 2:
                            if len(rule) > 2:
                                raise Exception("Bad block map rule: {}\nMaybe you forgot a semicolon?".format(rule))
                            else:
                                raise Exception("Bad block map rule: {}".format(rule))
                        if self.has_nodes():
                            node, sym, formula = rule
                        else:
                            sym, formula = rule
                            node = ()
                        #print("CA rule", node, sym, formula)
                        circ = compiler.formula_to_circuit(dom_nodes, dom_dim, dom_top, dom_alph, formula,
                                                           self.externals, simplify="simplify" in flags, graph=self.graph)
                        #print(circ)
                        #graph, topology, nodes, alphabet, formula, externals, simplify=True
                        #circ = compiler.formula_to_circuit2(self.graph, dom_top, dom_nodes, dom_alph, formula, self.externals, simplify="simplify" in flags)
                        circuits.append((node, sym, circ))
                #print(circuits)
                """
                the problem is we should see "up", (0, 1), (), () in compiler, but
                we see "up", (0,0,()) (0,1,())
                """
                self.blockmaps[name] = blockmap.BlockMap(dom_alph, cod_alph, dom_nodes, cod_nodes,
                                                         dom_dim, circuits, dom_top, cod_top, dom_graph,
                                                         overlaps=overlaps, verbose=verbose)

            elif cmd == "TFG":
                name = args[0]
                rules = args[1]
                circuits = {}
                
                for r in rules:
                    if rule:
                        if len(rule) != 4:
                            if mode != "silent": print("Bad TGF rule, ignoring: {}".format(rule))
                            if len(rule) > 4:
                                if mode != "silent": print("Maybe you forgot a semicolon?")
                            continue
                        circ = compiler.formula_to_circuit(self.nodes, self.dim, self.topology, self.alphabet, r[3], self.externals)
                        circuits[(r[0], r[1], r[2])] = circ # node node offset circuit
                self.TFGs[name] = tfg.TFG(self.alphabet, self.nodes, self.dim, circuits)

            elif cmd == "TFG_loops":
                raise Exception("Loop calculation is work in progress.")
                #TFG_name = args[0]
                #SFT_name = args[1]
                #actual_sft = self.SFTs[SFT_name]
                #print (self.TFGs[TFG_name].loops(actual_sft))

            elif cmd == "compose":
                name = args[0]
                composands = args[1]
                if mode != "silent": print("Composing block maps %s." % composands)#, self.CAs)
                """
                result_CA = self.CAs[composands[1]]
                for name in composands[2:]:
                    result_CA = result_CA.then(self.CAs[name])
                """
                #composands = composands[1:]
                result = self.blockmaps[composands[-1]]
                for comp_name in reversed(composands[:-1]):
                    result = self.blockmaps[comp_name].then(result, verbose = "verbose" in flags)
                self.blockmaps[name] = result

            elif cmd == "compute_CA_ball":
                t = time.time()
                radius = args[0]
                gen_names = args[1]
                if "filename" in kwds:
                    filename = kwds["filename"] + ".output"
                else:
                    filename = None
                if mode != "silent": print("Computing length-{} relations for CA {}{}.".format(radius, str(gen_names), "" if filename is None else " into file "+filename))
                generators = [self.blockmaps[j] for j in gen_names]
                assert all(gen.is_CA() for gen in generators)
                if filename is not None:
                    with open(filename, "w") as outfile:
                        for output in blockmap.find_relations(generators, radius):
                            def zz(l):
                                return " ".join(map(lambda a:gen_names[a], l))
                            if output[0] == "rel":
                                outfile.write("New relation: %s = %s" % (zz(output[1]), zz(output[2])) + "\n")
                            else:
                                outfile.write("New CA at %s." % (zz(output[2]),) + "\n")
                            outfile.flush()
                else:
                    for _ in blockmap.find_relations(generators, radius):
                        pass
                if mode != "silent": print("Time to calculate ball: %s seconds." % (time.time() - t))

            elif cmd == "has_post_inverse":
                name = args[0]
                the_bm = self.blockmaps[name]
                verbose = "verbose" in flags
                # by default, we try to find inverse of radius 1 -- could be radius of given tho
                rad = kwds.get("radius", 1) 
                #if mode == "report":
                if mode != "silent": print("Checking existence of post inverse (retraction) with radius %s." % rad)
                result = the_bm.injective_to_graph_ball(int(rad), verbose)
                if result:
                    if the_bm.partial:
                        if mode != "silent": print("A post inverse might exist (the blockmap is partial!)")
                    else:
                        if mode != "silent": print("A post inverse exists.")
                else:
                    if mode != "silent": print("A post inverse of that radius does not exist.")

                expect = kwds.get("expect", None)
                #print(expect)
                if expect is not None and mode == "assert":
                    if mode != "silent": print(result, "=", expect)
                    assert result == (expect == "T")
                results.append(result)

            elif cmd == "image_intersects":
                name = args[0]
                the_bm = self.blockmaps[name]
                clopen = self.SFTs[args[1]]
                verbose = "verbose" in flags
                if not isinstance(clopen, sft.Clopen):
                    raise Exception("{} is not a clopen set.".format(clopen))
                if mode != "silent": print("Checking whether image of block map %s intersects clopen set %s." % (args[0], args[1]))
                result = the_bm.image_intersects(clopen, verbose)
                if result:
                    if mode != "silent": print("Does intersect.")
                else:
                    if mode != "silent": print("Does not intersect.")
                results.append(result)

            # restrict alphabets of codomain
            elif cmd == "restrict_codomain":
                name = args[0]
                codomain_name = args[1]

                cod_dim, cod_nodes, cod_top, cod_alph, cod_graph = self.environments[codomain_name]

                # we just restrict to a partial CA, which will work for injectivity and surj checks
                # since a blockmap has exact circuits for all symbols, now it just doesn't cover all
                self.blockmaps[name].to_alphabet = cod_alph
                self.blockmaps[name].partial = True
                # some basic checks at least
                assert self.blockmaps[name].to_nodes == cod_nodes
                assert self.blockmaps[name].to_topology == cod_top
                
            elif cmd == "tiler":
                import tiler
                name = args[0]
                if mode != "silent": print(kwds)
                x_size = kwds.get("x_size", 10)
                y_size = kwds.get("y_size", 10)
                x_periodic = "x_periodic" in flags
                y_periodic = "y_periodic" in flags
                node_offsets = kwds.get("node_offsets", self.tiler_nodeoffsets)
                node_offsets = {node: tuple(float(a) for a in vec) for (node, vec) in node_offsets.items()}
                pictures = kwds.get("pictures", None)
                if type(pictures) == list:
                    pictures = {node : pictures for node in self.nodes}
                gridmoves = [tuple(map(float, move)) for move in kwds.get("gridmoves", self.tiler_gridmoves)]
                conf_name = kwds.get("initial", None)
                if conf_name is not None:
                    try:
                        conf = self.confs[conf_name]
                    except KeyError:
                        raise Exception("No configuration named {}".format(conf_name))
                else:
                    conf = None
                hidden_nodes = kwds.get("hidden", [])
                if mode != "silent": print(hidden_nodes)
                if mode != "silent": print(gridmoves)
                if mode != "silent": print(self.tiler_gridmoves)
                SFT = self.SFTs[name]
                topo_name = kwds.get("topology", None)
                if topo_name is None:
                    topology = SFT.topology
                else:
                    topology = self.environments[topo_name][2]
                colors = kwds.get("colors", None)
                tiler.run(SFT, topology, gridmoves, node_offsets, x_size, y_size, x_periodic, y_periodic, pictures, colors, initial=conf, hidden_nodes=hidden_nodes)
                #tiler.run(SFT, self.topology, gridmoves, node_offsets, self.tiler_skew, x_size, y_size, x_periodic, y_periodic, pictures)
            
            elif cmd == "entropy_upper_bound":
                name = args[0]
                the_sft = self.SFTs[name]
                dimensions= args[1]
                rad = kwds.get("radius", 0)
                method = kwds.get("method", "deduce")
                
                rect = set([tuple()])
                size = 1
                for h in dimensions:
                    rect = set(vec+(i,) for vec in rect for i in range(h))
                    size *= h
                rect = set(vec+(n,) for vec in rect for n in the_sft.nodes)
                size *= len(the_sft.nodes)
                if mode != "silent": print("Computing upper bound for topological entropy of {} using dimensions {}".format(name, dimensions))
                tim = time.time()
                if method == "deduce":
                    num_pats = sum(1 for _ in the_sft.all_patterns(rect, extra_rad=rad))
                elif method == "recursive":
                    num_pats = the_sft.count_patterns_splitting(rect, extra_rad=rad)
                else:
                    raise Exception("Unknown method: {}".format(method))
                if mode != "silent": print("Entropy is at most log2({})/{} ~ {}".format(num_pats, size, math.log(num_pats, 2)/size))
                if mode != "silent": print("Eta is at most {}^(1/{}) ~ {}".format(num_pats, size, num_pats**(1/size)))
                if mode != "silent": print("Computation took {} seconds".format(time.time() - tim))
                
            elif cmd == "entropy_lower_bound":
                # TODO: split the periodic points as in upper bound
                name = args[0]
                the_sft = self.SFTs[name]
                periods = args[1]
                dims = args[2]
                variables = set(the_sft.circuit.get_variables())
                var_dims = []
                for k in range(the_sft.dim):
                    vdmin, vdmax = min(var[k] for var in variables), max(var[k] for var in variables)
                    var_dims.append(vdmax - vdmin)
                big_periods = [a*b for (a,b) in zip(periods, dims)]
                big_domain = set([tuple()])
                size = 1
                for p in big_periods:
                    big_domain = set(vec + (i,) for vec in big_domain for i in range(p))
                    size *= p
                big_domain = set(vec + (n,) for vec in big_domain for n in the_sft.nodes)
                size *= len(the_sft.nodes)
                if mode != "silent": print("Computing lower bound for topological entropy of {} using {}-periodic points and {}-size blocks".format(name, periods, big_periods))
                num_pats = 0
                tim = time.time()
                for pat in the_sft.all_periodics(periods):
                    border = {nvec : pat[nvmods(periods, nvec)] for nvec in big_domain if any(a <= b for (a,b) in zip(nvec, var_dims))}
                    num_pats = max(num_pats, sum(1 for _ in the_sft.all_periodics(big_periods, existing=border)))
                if mode != "silent": print("Entropy is at least log2({})/{} ~ {}".format(num_pats, size, math.log(num_pats, 2)/size))
                if mode != "silent": print("Eta is at least {}^(1/{}) ~ {}".format(num_pats, size, num_pats**(1/size)))
                if mode != "silent": print("Computation took {} seconds".format(time.time() - tim))
            

            elif cmd == "tile_box":
                name = args[0]
                rad = args[1]
                if mode != "silent": print("Tiling %s-hypercube with SFT %s." % (rad, name))
                succ = self.SFTs[name].tile_box(rad)
                assert succ

            elif cmd == "keep_tiling":
                name = args[0]
                rad = kwds.get("min", 1)
                max_rad = kwds.get("max", None)
                verbose = "verbose" in flags
                while max_rad is None or rad > max_rad:
                    if mode != "silent": print("Tiling %s-hypercube of SFT %s." % (rad, name))
                    self.SFTs[name].tile_box(rad, verbose=verbose)
                    rad += 1
                                        
            elif mode == "report":
                raise Exception("Unknown command %s." % cmd)

        return results

    def add_external(self, name, obj):
        self.externals[name] = obj

             

# for a dict with lists on the right, return all sections
def get_sections(dicto):
    #print(dicto)
    # get an arbitrary key
    if len(dicto) == 0:
        yield {}
        return
    it = next(iter(dicto.items()))
    # remove it
    rest = dict(dicto)
    del rest[it]
    # recursive solution
    for val in dicto[it]:
        for sec in get_sections(rest):
            sect = dict(sec)
            sect[it] = val
            yield sect

# for each node, give the names of edges into it, and out of it, in order...
def get_in_out_edges(topology):
    in_edges = {}
    out_edges = {}
    for t in topology:
        name, a, b = t
        print(a, b)
        if a[-1] not in out_edges:
            out_edges[a[-1]] = []
        out_edges[a[-1]].append(name)
        if b[-1] not in in_edges:
            in_edges[b[-1]] = []
        in_edges[b[-1]].append(name)
    return in_edges, out_edges

# generate Wang tile SFT for the given topology...
# this variant makes an explicit alphabet with a symbol for each Wang tile
def general_Wang(tiles, nodes, topology, inverses):
    raise Exception("I ran out of steam.")
    # variables for symbols
    var_ranges = {}
    # for each node the variables usable there
    node_tiles = {}

    in_edges, out_edges = get_in_out_edges(topology)

    # the inverses list is used as the default order for directions
    directions = []
    for dd in inverses:
        directions.append(dd[0])
        directions.append(dd[1])
        
    # given a tile as a tuple, return tile as dict
    def fix_for_node(node, tile):
        #print(node, tile,out_edges)
        assert len(tile) == len(out_edges[node])

        tile_colors = {}
        remaining_colors = []
        used_directions = set()
        for t in tile:
            if type(t) == tuple and t[0] == "SET":
                tile_colors[t[1]] = t[2]
                used_directions.add(t[1])
            else:
                #raise Exception("non-kw wangs not implemented yet")
                remaining_colors.append(t)
                
        i = 0
        for d in directions:
            if d in out_edges[node]:
                if d not in used_directions:
                    tile_colors[d] = remaining_colors[i]
                    i += 1
        return tile_colors
            
    for t in tiles:
        if t[0] == ["variable"]:
            var_ranges[t[1]] = t[2]
        else:
            if type(t[0]) == list:
                node_list = t[0]
                tile = t[1:]
            else:
                node_list = nodes
                tile = t
            for n in node_list:
                if n not in node_tiles:
                    node_tiles[n] = []
                node_tiles[n].append(fix_for_node(n, tile))
    
    inverses_dict = {}
    all_seen = set()
    for k in inverses:
        inverses_dict[k[0]] = k[1]
        all_seen.add(k[0])
        all_seen.add(k[1])

    # we want that an inverse is specified for all  
    assert all_seen == set([t[0] for t in topology])

    actual_tiles_per_node = {}
    for n in nodes:
        actual_tiles_per_node[n] = []
        for t in node_tiles[n]:
            interesting_ranges = {}
            for c in t:
                if t[c] in var_ranges:
                    interesting_ranges[t[c]] = var_ranges[t[c]]
            for var_vals in get_sections(interesting_ranges):
                actual_tile = {}
                for c in t:
                    if t[c] in var_ranges:
                        val = var_vals[t[c]]
                    else:
                        val = t[c]
                    actual_tile[c] = val
                actual_tiles_per_node[n].append(actual_tile)
                    
    # print(actual_tiles_per_node)

    formula = "Ao \n"
    # for each positive direction, require that ugh...
    for n in nodes:
        nodeformula = "o = o.%s -> (\n" % n
        
        for d in inverses_dict:
            pass
        for t in topology:
            if t[-1] == None:
                pass
            

# given list of tiles, return colors and formula
def basic_2d_Wang(tiles):
    ENWS_colors = set(), set(), set(), set()
    for t in tiles:
        for i in range(4):
            ENWS_colors[i].add(t[i])
    colors = ENWS_colors[0]
    colors = colors.union(ENWS_colors[1])
    colors = colors.union(ENWS_colors[2])
    colors = colors.union(ENWS_colors[3])
    formula = "ACo o.N = o.up.S & o.E = o.rt.W & (\n"
    if len(tiles) == 0:
        raise Exception("Empty list of Wang tiles not implemented.")
    for t in tiles:
        tile_formula = "("
        # (o.E=3 & o.N=1 & o.W=3 & o.S=3) |
        for d,i in zip("ENWS", t):
            # i[1] is already parsed but is rewritten to formula...
            tile_formula += "o.%s=%s & " % (d, str(i))
        formula += tile_formula[:-3] + ") |\n"
    formula = formula[:-3] + ")"
    #print(formula)
    return list(colors), dparser.read_formula(formula)[0]

# given fof (formula or forbos), convert to a (parsed) formula
def forbos_to_formula(fof):
    #print("gille", fof)
    #if fof[0] == "formula":
    #    return fof[1]
    #assert fof[0] == "forbos"
    #fof = fof[1]
    preamble = ("CELLFORALL", "o", None)
    #print (fof)
    andeds = []
    # f goes over 
    for f in fof:
        # print(f, "limas",)
        oreds = []
        for vec in f:
            oreds.append(("NOT", ("HASVAL", ["o", vec], f[vec])))
        andeds.append(("OR",) + tuple(oreds))
    ret = preamble + (("AND",) + tuple(andeds),)
    #print(ret, "MIL")
    return ret
    
def report_SFT_empty(a, mode="report", truth=True, verbose=False):
    name, the_sft = a
    print("Testing whether %s is empty." % name)
    if isinstance(the_sft, sft.SFT) or isinstance(the_sft, sft.Clopen) or isinstance(the_sft, sft.CSIntersection):
        empty = sft.SFT(the_sft.dim, the_sft.nodes, the_sft.alph, the_sft.topology, the_sft.graph, onesided=the_sft.onesided, circuit=circuit.F)
    else:
        empty = sofic1d.Sofic1D(the_sft.nodes, the_sft.alph, the_sft.topology, dict(), onesided=the_sft.onesided)
    tim = time.time()
    res, rad, conf = empty.contains(the_sft, return_radius_and_sep = True, method="periodic", verbose=verbose)
    tim = time.time() - tim
    if res:
        print("%s is EMPTY (radius %s, time %s)" % (name, rad, tim))
    else:
        print("%s is NONEMPTY (radius %s, time %s)" % (name, rad, tim))
        if mode == "report":
            print("Has element: " + conf.display_str())
    if mode == "assert":
        print(res, "=", (truth == "T"))
        assert res == (truth == "T")
    print()
    return conf

def report_SFT_contains(a, b, mode="report", truth=True, method=None, verbose=False):
    aname, aSFT = a
    bname, bSFT = b
    print("Testing whether %s contains %s." % (aname, bname))
    tim = time.time()
    res, rad, conf = aSFT.contains(bSFT, return_radius_and_sep = True, method=method, verbose=verbose)
    tim = time.time() - tim
    if res:
        print("%s CONTAINS %s (radius %s, time %s)" % (aname, bname, rad, tim))
    else:
        print("%s DOES NOT CONTAIN %s (radius %s, time %s)" % (aname, bname, rad, tim))
        if mode == "report":
            print("Separated by: " + conf.display_str())
    if mode == "assert":
        print(res, "=", (truth == "T"))
        assert res == (truth == "T")
    print()
    return conf

def report_SFT_equal(a, b, mode="report", truth=True, method=None, verbose=False):
    aname, aSFT = a
    bname, bSFT = b
    print("Testing whether SFTs %s and %s are equal." % (aname, bname))
    tim = time.time()
    #print("inmediate", aSFT.circuit.copy().get_variables())
    res, rad = aSFT.equals(bSFT, return_radius = True, method=method, verbose=verbose)
    tim = time.time() - tim
    if res: 
        print("They are EQUAL (radius %s, time %s)." % (rad, tim))
    else:
        print("They are DIFFERENT (radius %s, time %s)." % (rad, tim))
    if mode == "assert":
        print(res, "=", (truth == "T"))
        assert res == (truth == "T")
    print()

def report_SFT_in(a, b, mode="report", truth=True):
    aname, aSFT = a
    bname, bconf = b
    print("Testing whether SFT %s contains configuration %s." % (aname, bname))
    tim = time.time()
    res = bconf in aSFT
    tim = time.time() - tim
    if res: 
        print("It DOES (time %s)." % tim)
    else:
        print("It DOES NOT (time %s)." % tim)
    if mode == "assert":
        print(res, "=", (truth == "T"))
        assert res == (truth == "T")
    print()

def report_blockmap_equal(a, b, mode="report", truth=True, verbose=False): # verbose does nothing here
    aname, amap = a
    bname, bmap = b
    print("Testing whether block maps %s and %s are equal." % (aname, bname))
    tim = time.time()
    diff = amap.separating(bmap)
    tim = time.time() - tim
    if diff is None:
        print("They are EQUAL (time %s)." % (tim))
    else:
        print("They are DIFFERENT (time %s)." % (tim))
        (node, value), pattern = diff
        print("Separated by pattern with return value {} on node {}:".format(value, node))
        print(pattern)
    print()
    if mode == "assert":
        print(diff is None, "=", (truth == "T"))
        assert (diff is None) == (truth == "T")

def report_aut_contains(a, b, mode="report", truth=True, method=None, verbose=False):
    aname, aaut = a
    bname, baut = b
    print("Testing whether %s contains %s." % (aname, bname))
    tim = time.time()
    res, word = aaut.contains(baut, verbose=verbose, track=True)
    tim = time.time() - tim
    if res:
        print("%s CONTAINS %s (time %s)" % (aname, bname, tim))
    else:
        print("%s DOES NOT CONTAIN %s (time %s)" % (aname, bname, tim))
        if mode == "report":
            print("Separated by {}".format(word))
    if mode == "assert":
        print(res, "=", (truth == "T"))
        assert res == (truth == "T")
    print()

def report_aut_equal(a, b, mode="report", truth=True, verbose=False): # verbose does nothing here
    aname, aaut = a
    bname, baut = b
    print("Testing whether finite automata %s and %s are equivalent." % (aname, bname))
    tim = time.time()
    res = aaut.equals(baut)
    tim = time.time() - tim
    if res:
        print("They are EQUAL (time %s)." % (tim))
    else:
        print("They are DIFFERENT (time %s)." % (tim))
    print()
    if mode == "assert":
        print(res, "=", (truth == "T"))
        assert res == (truth == "T")

def fix_filename(filename):
    if "." not in filename:
        return filename + ".griddy"
    return filename

# change the topology to modern (graph compatible) format where we just have "command", "movement in cells", "from_node", "to_node"
def modernize_topology(topology, dim = None):
    #print("modernizing")
    if dim == None: # being called from the explicit list
        dim = len(topology[0][1]) - 1
    newtopology = []
    for t in topology:
        #print("got edge", t)
        if len(t) == 4: # seems to be a modern tuple
            newtopology.append(t)
        else:
            # semi legacy format, so label (v,n) (u,m) where v, u are tuples
            if type(t[1][0]) == tuple:
                name, offset, fromnode, tonode = t[0], vsub(t[2][0], t[1][0]), t[1][1], t[2][1]
            else:
                name, offset, fromnode, tonode = t[0], vsub(t[2][:-1], t[1][:-1]), t[1][dim], t[2][dim]
                #newtopology.append((name, graph.moves_to(offset), fromnode, tonode))
            newtopology.append((name, offset, fromnode, tonode))
        #print("produced edge", newtopology[-1])
    #print(newtopology)
    return newtopology

line = [("rt", (0,()), (1,())),
        ("lt", (0,()), (-1,()))]
line = modernize_topology(line)
grid = [("up", (0,0,()), (0,1,())),
        ("dn", (0,0,()), (0,-1,())),
        ("rt", (0,0,()), (1,0,())),
        ("lt", (0,0,()), (-1,0,()))]
grid = modernize_topology(grid)

"""
hexgrid = [("up", (0,0,0), (0,1,1)),
           ("dn", (0,0,1), (0,-1,0)),
           ("rt", (0,0,0), (0,0,1)),
           ("lt", (0,0,0), (-1,0,1)),
           ("rt", (0,0,1), (1,0,0)),
           ("lt", (0,0,1), (0,0,0))]
"""
hexgrid = [("N", (0,0,('0',)), (0,1,('1',))),
           ("S", (0,0,('1',)), (0,-1,('0',))),
           ("sE", (0,0,('0',)), (0,0,('1',))),
           ("sW", (0,0,('0',)), (-1,0,('1',))),
           ("nE", (0,0,('1',)), (1,0,('0',))),
           ("nW", (0,0,('1',)), (0,0,('0',)))]
hexgrid = modernize_topology(hexgrid)

kinggrid = [("E", (0,0,()), (1,0,())),
            ("NW", (0,0,()), (1,1,())),
            ("N", (0,0,()), (0,1,())),
            ("NW", (0,0,()), (-1,1,())),
            ("W", (0,0,()), (-1,0,())),
            ("SW", (0,0,()), (-1,-1,())),
            ("S", (0,0,()), (0,-1,())),
            ("SE", (0,0,()), (1,-1,()))]
kinggrid = modernize_topology(kinggrid)           
trianglegrid = [("E", (0,0,()), (1,0,())),
            ("Ne", (0,0,()), (1,1,())),
            ("Nw", (0,0,()), (0,1,())),
            ("W", (0,0,()), (-1,0,())),
            ("Sw", (0,0,()), (-1,-1,())),
            ("Se", (0,0,()), (0,-1,()))]
trianglegrid = modernize_topology(trianglegrid) 

Wang_nodes = ["E", "N", "W", "S"]
Wang_topology = [("up", (0,0,"N"), (0,1,"S")),
                 ("dn", (0,0,"S"), (0,-1,"N")),
                 ("rt", (0,0,"E"), (1,0,"W")),
                 ("lt", (0,0,"W"), (-1,0,"E"))]
Wang_topology = modernize_topology(Wang_topology)

# Cundy Rollet 4.8^2, see Wikipedia
# Euclidean tilings by convex regular polygons
CR4d8e2_nodes = sft.Nodes(["big", "small"])
CR4d8e2_topology = [('N', (0, 0, 'big'), (0, 1, 'small')),
                    ('NE', (0, 0, 'big'), (1, 1, 'big')),
                    ('E', (0, 0, 'big'), (0, 0, 'small')),
                    ('SE', (0, 0, 'big'), (0, -1, 'big')),
                    ('S', (0, 0, 'big'), (-1, -1, 'small')),
                    ('SW', (0, 0, 'big'), (-1, -1, 'big')),
                    ('W', (0, 0, 'big'), (-1, 0, 'small')),
                    ('NW', (0, 0, 'big'), (0, 1, 'big')),
                    ('N', (0, 0, 'small'), (1, 1, 'big')),
                    ('E', (0, 0, 'small'), (1, 0, 'big')),
                    ('S', (0, 0, 'small'), (0, -1, 'big')),
                    ('W', (0, 0, 'small'), (0, 0, 'big'))]
CR4d8e2_topology = modernize_topology(CR4d8e2_topology)                    


# You can toggle this to run a REPL without sending command line arguments.
forced_repl = False

if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("filename", type=str, nargs='*', help="Name of Griddy script to execute.")
    arg_parser.add_argument('-r', '--repl', action='store_true', help="Open a basic read-eval-print-loop.")

    if len(sys.argv) == 1 and not forced_repl:
        print("""If you want to test that Griddy is installed correctly, run \"python unit_tests.py\".
You can test that Tiler works by running \"python griddy.py tiler_test\" and pressing spacebar.\n""")
    
    args = arg_parser.parse_args()

    runner = Griddy()

    if len(args.filename) > 0:
        runner.run_file(args.filename[0])
    elif not args.repl and not forced_repl:
        arg_parser.error("please supply the argument filename, the -r flag, or both")

    if args.repl or forced_repl:
        print("Starting Griddy REPL mode.\nA command with ; at the end is run immediately.\nOtherwise a multiline input begins; then input an empty line to run and 'c' to cancel.\nInput 'quit' to quit.")
        running = True
        while running:
            command = ""
            while running:
                inp = input("> ")
                if len(command) == 0 and len(inp) > 0 and inp[-1] == ";":
                    runner.run(inp[:-1])
                    command = ""
                elif inp == "c":
                    command = ""
                    break
                elif inp == "" or inp == ";":
                    print("(running command)")
                    runner.run(command)
                    command = ""
                elif inp == "quit":
                    running = False
                    break
                else:
                    command += inp + "\n"
            




