

from general import *
from basic_things import *
from configuration import RecognizableConf
from finite_automata import NFA
import collections
import sft
from itertools import combinations
from frozendict import frozendict
from graphs import AbelianGroup

# Much of this is copied from period_automaton with minor modifications
# TODO: unify the common parts?


def words(length, trans_alph, nodes, forbs):
    if not length:
        yield tuple()
    else:
        for word in words(length-1, trans_alph, nodes, forbs):
            for syms in trans_alph:
                word2 = (syms,) + word
                if all(any(forb.get((i, node), sym) != sym
                           for (i, syms2) in enumerate(word2)
                           for (sym, node) in zip(syms2, nodes))
                       for forb in forbs
                       if max([p[0] for p in forb] + [0]) < length):
                    yield word2

def connected(states, trans, trans_alph):
    "Is this right-resolving transition graph strongly connected?"
    init = min(states)
    reachable = set() # reachables from init
    frontier = set([init])
    while frontier:
        new_frontier = set()
        for st in frontier:
            for sym in trans_alph:
                try:
                    new_st = trans[st, sym]
                except KeyError:
                    continue
                if new_st not in reachable:
                    reachable.add(new_st)
                    new_frontier.add(new_st)
        frontier = new_frontier
    if len(reachable) != len(states):
        return False

    flipped = dict()
    for ((st, sym), st2) in trans.items():
        try:
            flipped[st2, sym].add(st)
        except KeyError:
            flipped[st2, sym] = set([st])
    reachable = set() # reachables to init
    frontier = set([init])
    while frontier:
        new_frontier = set()
        for st in frontier:
            for sym in trans_alph:
                try:
                    new_sts = flipped[st, sym]
                except KeyError:
                    continue
                for new_st in new_sts:
                    if new_st not in reachable:
                        reachable.add(new_st)
                        new_frontier.add(new_st)
        frontier = new_frontier
    return len(reachable) == len(states)

class Sofic1D:
    """
    A finite automaton representing a 1D sofic shift.
    May or may not be right resolving.
    The main data is trans, which is:
    a) a dict[state, sym] -> state if right resolving, or
    b) a dict[state, sym] -> set(state) if not.
    sym here is a tuple of symbols, one for each node
    """
    
    def __init__(self, nodes, alph, topology, trans,
                 right_resolving=False, onesided=False, trans_alph=None,
                 debug = False):
        if debug:
            print("debugging")
            print(nodes)
            print(alph)
            print(topology)
            print(trans)
        self.dim = 1
        self.nodes = nodes
        self.alph = alph
        if trans_alph is None:
            trans_alph = list(iter_prod(*(iter(alph[node]) for node in nodes)))
        self.trans_alph = trans_alph
        self.topology = topology
        self.trans = trans
        if right_resolving:
            self.states = set(tr[0] for tr in self.trans) | set(self.trans.values())
        else:
            self.states = set(tr[0] for tr in self.trans) | set(st for sts in self.trans.values() for st in sts)
        self.right_resolving = right_resolving
        self.onesided = onesided
        self.minimal = False
        self.graph = AbelianGroup([0])
        
    def info_string(self, name, verbose=False):
        s = ["1-dimensional {} {}{}sofic shift {}".format(
                "onesided" if self.onesided else "two-sided",
                "right-resolving " if self.right_resolving else "",
                "minimized " if self.minimal else "",
                name)]
        s.append("Nodes: {}".format(list(self.nodes)))
        s.append("Alphabet: {}".format(self.alph))
        if verbose:
            s.append("Topology: {}".format(self.topology))
            s.append("States: {}".format(self.states))
            s.append("Transition graph: {}".format(self.trans))
        elif self.right_resolving:
            s.append("{} states, {} transitions".format(len(self.states), len(self.trans)))
        else:
            s.append("{} states, {} transitions".format(len(self.states), sum(len(tr) for tr in self.trans.values())))
        return "\n".join(s)

    def remove_sinks(self, verbose=False):
        i = 1

        if self.right_resolving:
            size = len(self.trans)
            if verbose:
                print("Trimming right-resolving automaton with {} transitions.".format(size))
            while True:
                not_sink = set()
                not_source = set()
                for ((st, sym), st2) in self.trans.items():
                    not_sink.add(st)
                    not_source.add(st2)
                self.trans = {(st, sym) : st2
                              for ((st, sym), st2) in self.trans.items()
                              if self.onesided or st in not_source
                              if st2 in not_sink}
                new_size = len(self.trans)
                if verbose:
                    print("Round {}: {} transitions left.".format(i, new_size))
                    i += 1
                if new_size == size:
                    break
                size = new_size
        else:
            size = sum(len(sts) for sts in self.trans.values())
            if verbose:
                print("Trimming automaton with {} transitions.".format(size))
            while True:
                not_sink = set()
                not_source = set()
                for ((st, sym), sts) in self.trans.items():
                    if sts:
                        not_sink.add(st)
                    not_source |= sts
                self.trans = {(st, sym) : set(st2
                                              for st2 in sts
                                              if st2 in not_sink)
                              for ((st, sym), sts) in self.trans.items()
                              if self.onesided or st in not_source}
                new_size = sum(len(sts) for sts in self.trans.values())
                if verbose:
                    print("Round {}: {} transitions left.".format(i, new_size))
                    i += 1
                if new_size == size:
                    break
                size = new_size
                
        self.states = set(tr[0] for tr in self.trans)
        
    def equals(self, other, return_radius=True, method=None, verbose=False):
        "Is this 1d sofic equal to the other?"
        if not isinstance(other, Sofic1D):
            raise Exception("Sofic shifts can only be compared to sofic shifts")
        if self.onesided != other.onesided:
            if return_radius:
                return False, None
            else:
                return False
            
        if not self.trans:
            if return_radius:
                return not other.trans, None
            else:
                return not other.trans
        if not other.trans:
            if return_radius:
                return False, None
            else:
                return False
        
        if self.minimal and connected(self.states, self.trans, self.trans_alph) and\
           other.minimal and connected(other.states, other.trans, other.trans_alph):
            # check number of states and transitions
            if verbose:
                print("checking sizes of automata")
            if len(self.states) != len(other.states):
                if return_radius:
                    return False, None
                else:
                    return False
            if len(self.trans) != len(other.trans):
                if return_radius:
                    return False, None
                else:
                    return False

            # compute separating words (positive and negative followers for each state)
            if verbose:
                print("computing followers")
            followers = {st : [set(), set()] for st in self.states}
            for (st1, st2) in combinations(self.states, 2):
                # if the states are already separate, do nothing
                if followers[st1][0] & followers[st2][1] or followers[st1][1] & followers[st2][0]:
                    continue
                # separate these states
                states1 = {tuple() : st1}
                states2 = {tuple() : st2}
                n = 0
                while True:
                    n += 1
                    new_states1 = dict()
                    new_states2 = dict()
                    for (word, state1) in states1.items():
                        state2 = states2[word]
                        for sym in self.trans_alph:
                            new1 = self.trans.get((state1, sym), None)
                            new2 = self.trans.get((state2, sym), None)
                            new_word = word + (sym,)
                            if new1 is None:
                                if new2 is not None:
                                    followers[st1][1].add(new_word)
                                    followers[st2][0].add(new_word)
                                    break
                            elif new2 is None:
                                followers[st1][0].add(new_word)
                                followers[st2][1].add(new_word)
                                break
                            else:
                                new_states1[new_word] = new1
                                new_states2[new_word] = new2
                        else:
                            continue
                        break
                    else:
                        states1.update(new_states1)
                        states2.update(new_states2)
                        continue
                    break

            # match the states
            if verbose:
                print("matching states")
            match = dict()
            for other_st in other.states:
                for (st, [poss, negs]) in followers.items():
                    if st not in match:
                        for word in poss:
                            cur = other_st
                            for sym in word:
                                try:
                                    cur = other.trans[cur, sym]
                                except KeyError:
                                    break
                            else:
                                continue
                            break
                        else:
                            for word in negs:
                                cur = other_st
                                for sym in word:
                                    try:
                                        cur = other.trans[cur, sym]
                                    except KeyError:
                                        break
                                else:
                                    break                                
                            else:
                                match[st] = other_st
                                break

            # check for isomorphism of automata (note that they have equally many transitions)
            if verbose:
                print("checking for isomorphism")
            for ((st, sym), st2) in self.trans.items():
                if other.trans.get((match[st],sym), None) != match[st2]:
                    if return_radius:
                        return False, None
                    else:
                        return False
            if return_radius:
                return True, None
            else:
                return True
            
        else:
            # We don't have minimal and connected graphs
            # Then we construct auxiliary transitive sofic shifts and compare those
            if verbose:
                print("Constructing auxiliary graphs")
            if self.right_resolving:
                aux_trans1 = {tr : set([st]) for (tr, st) in self.trans.items()}
            else:
                aux_trans1 = self.trans.copy()
            for st in self.states:
                aux_trans1[st, None] = set([None])
            aux_trans1[None, None] = self.states | set([None])
            aux_sofic1 = Sofic1D(None, None, None, aux_trans1, onesided=self.onesided, trans_alph=self.trans_alph + [None])
            aux_sofic1.determinize(verbose=verbose)
            aux_sofic1.minimize(verbose=verbose)
            assert connected(aux_sofic1.states, aux_sofic1.trans, aux_sofic1.trans_alph)
            
            if other.right_resolving:
                aux_trans2 = {tr : set([st]) for (tr, st) in other.trans.items()}
            else:
                aux_trans2 = other.trans.copy()
            for st in other.states:
                aux_trans2[st, None] = set([None])
            aux_trans2[None, None] = other.states | set([None])
            aux_sofic2 = Sofic1D(None, None, None, aux_trans2, onesided=other.onesided, trans_alph=self.trans_alph + [None])
            aux_sofic2.determinize(verbose=verbose)
            aux_sofic2.minimize(verbose=verbose)

            return aux_sofic1.equals(aux_sofic2, verbose=verbose, return_radius=return_radius)
                    
            
    def contains(self, other, return_radius_and_sep=None, method=None, verbose=False):
        "Does this 1d sofic contain the other?"
        # TODO: make more efficient
        assert other.minimal
        inter = self.intersection(other)
        inter.determinize(verbose=verbose)
        inter.minimize(verbose=verbose)
        res = other.equals(inter, return_radius=False)
        if return_radius_and_sep:
            return res, None, None
        else:
            return res
        
    @classmethod
    def from_SFT(cls, the_sft, verbose=False):
        "Construct a 1D sofic shift from a 1D SFT using forbidden patterns."
        assert the_sft.dim == 1
        assert the_sft.forbs is not None
        if verbose:
            print("Constructing sofic automaton.")

        trans_alph = list(iter_prod(*(iter(the_sft.alph[node]) for node in the_sft.nodes)))
        forbs = []
        is_empty = False
        for forb_pat in the_sft.forbs:
            if not forb_pat:
                is_empty = True
                break
            min_ix = min(nvec[0][0] for nvec in forb_pat)
            forbs.append({(i[0]-min_ix, n) : c for ((i,n),c) in forb_pat.items()})
        if is_empty:
            trans = {}
        else:
            max_len = max([nvec[0] for forb in forbs for nvec in forb] + [0])
            trans_words = set(words(max_len+1, trans_alph, the_sft.nodes, forbs))
            trans = {(word[:-1], word[-1]) : word[1:]
                     for word in trans_words}
        #trans = remove_sinks(trans, trans_alph, sources_too = 0 not in the_sft.onesided, verbose=verbose)
        sofic = cls(the_sft.nodes, the_sft.alph, the_sft.topology, trans, right_resolving=True, onesided = the_sft.onesided==[0])
        
        sofic.remove_sinks(verbose=verbose)
        
        return sofic
    
    @classmethod
    def trace(cls, the_sft, size, spec, verbose=False, extra_rad=0):
        """
        Compute the 1-dimensional trace of the given SFT of dimension >= 2.
        Size is a the_sft.dim-length list of integers,
        which represents the size of the rectangular "trace alphabet".
        The topology of the trace has nested tracks for the axes of the rectangle,
        plus a track for the nodes of the SFT.
        For example, if size is [2,3] and the SFT has nodes [a,b],
        then the trace topology has 2*3*2 = 12 nodes, named 0.0.a, 0.0.b, 0.1.a, ..., 1.2.b.
        The spec is a list of length the_sft.dim.
        Each element of the spec is one of the following.
        * "dir", signifying the direction of the trace. There must be exactly one of these.
        * ("per", p), signifying a periodic direction of period p.
        * A pair (a, b), where each of a and b is one of the following.
          - ("rad", r) for radius r (in addition to the size).
          - ("uper", t, p) for ultimately periodic with transient length t and ultimate period p.
        extra_rad gives an additional non-presistent radius.
        """
        if verbose:
            print("Computing trace from SFT")
        
        # TODO: add gluing to arbitrary 1D sofic in 2D case.
        trace_nodes = the_sft.nodes

        #print(trace_nodes, "flippant")
        for width in reversed(size):
            trace_nodes = sft.Nodes({i : trace_nodes for i in range(width)})
        #print(trace_nodes) -> [0.0]
            
        #print("sft nodes", the_sft.nodes)
        #print("trace nodes", trace_nodes)
        trace_topology = []
        for node in trace_nodes:
            trace_topology.append(("rt", (1,), node, node))
            trace_topology.append(("lt", (-1,), node, node))
        #print("trace topology", trace_topology)
        alph_domain = [vec + (node,)
                       for vec in hyperrect([(0,s) for s in size])
                       for node in the_sft.nodes]
        #trace_alph = {0 : [frozendict(pat) for pat in the_sft.all_patterns(alph_domain)]}
        #print("alph domain", alph_domain)
        
        # compute transition sizes from specification
        trans_bounds = []
        dir_ix = None
        period_structure = []
        for (ix, (width, struct)) in enumerate(zip(size, spec)):
            if struct == "dir":
                trans_bounds.append((0, max(width+1, the_sft.radii()[ix])))
                period_structure.append((None, None))
                if dir_ix is None:
                    dir_ix = ix
                else:
                    raise Exception("Multiple directions in trace spec")
            elif struct[0] == "per":
                assert struct[1] >= width
                trans_bounds.append((0, struct[1]))
                period_structure.append(None)
            else:
                left, right = struct
                if left[0] == "rad":
                    lower = -left[1]
                    lper = None
                elif left[0] == "uper":
                    lower = -(left[1]+left[2])
                    lper = left[2]
                else:
                    raise Exception("Unknown trace spec")
                if right[0] == "rad":
                    upper = width+right[1]
                    rper = None
                elif right[0] == "uper":
                    upper = width+right[1]+right[2]
                    rper = right[2]
                else:
                    raise Exception("Unknown trace spec")
                trans_bounds.append((lower, upper))
                period_structure.append((lper, rper))
        if dir_ix is None:
            raise Exception("No direction in trace spec")

        if verbose:
            print("Computing transitions")
        
        # compute transitions and states
        states = set()
        trans = dict()
        trans_alph = set()
        tr_vec = (0,)*dir_ix + (trans_bounds[dir_ix][1]-size[dir_ix],) + (0,)*(the_sft.dim-dir_ix-1)
        proj_size = list(size)
        proj_size[dir_ix] = trans_bounds[dir_ix][1]-size[dir_ix]+1
        proj_nvecs = set((vec, node)
                         for vec in hyperrect([(0,a) for a in proj_size])
                         for node in the_sft.nodes)
        #print("size", size, "trans_size", trans_bounds, "proj_size", proj_size, "tr_vec", tr_vec, "proj_nvecs form", min(proj_nvecs), max(proj_nvecs))
        i = 0
        for trans_pat in the_sft.all_hyperrect_patterns(trans_bounds, period_structure=period_structure, extra_rad=extra_rad):
            #print("trans pat", trans_pat)
            i += 1
            source = frozendict({nvec : sym
                                 for (nvec, sym) in trans_pat.items()
                                 if nvec[0][dir_ix] < trans_bounds[dir_ix][1]-1})
            #print(source, "matikainen")
            target = frozendict({nvsub(nvec, char_vector(the_sft.dim, dir_ix)) : sym
                                 for (nvec, sym) in trans_pat.items()
                                 if nvec[0][dir_ix] > 0})
            #print(trace_nodes)
            sym = tuple(trans_pat[(vadd(tr_node[:the_sft.dim], tr_vec), tr_node[the_sft.dim:])]
                        for tr_node in trace_nodes)
            #print(source)
            #print(target)
            #print(sym)
            #sym = frozendict({nvec : sym
            #                  for (nvec, sym) in trans_pat.items()
            #                  if all(0 <= nvec[ix] < size[ix] for ix in range(the_sft.dim))})
            states.add(source)
            states.add(target)
            #print("trans", source, sym, "->", target)
            try:
                trans[source, sym].add(target)
            except KeyError:
                trans[source, sym] = set([target])
            trans_alph.add(sym)
            if verbose and i%10000 == 0:
                print(i, "transitions handled")
        
        sofic_alph = {node : the_sft.alph[node[the_sft.dim:]]
                      for node in trace_nodes}

        is_onesided = dir_ix in the_sft.onesided
        #trans = remove_sinks(trans, trans_alph, sources_too = is_onesided, verbose = verbose)
        
        sofic = Sofic1D(trace_nodes, sofic_alph, trace_topology, trans, onesided = is_onesided)
        sofic.remove_sinks(verbose=verbose)
        return sofic
        
    def determinize(self, verbose=False):
        "Determinize this automaton using the powerset construction."
        if self.right_resolving:
            return
        
        # Maintain sets of seen and unprocessed state sets, and integer labels for seen sets
        if verbose:
            print("Determinizing automaton with {} states and {} transitions".format(len(self.states), sum(len(sts) for sts in self.trans.values())))
        
        init_st = frozenset(self.states)
        seen = {init_st : 0}
        frontier = collections.deque([(init_st, 0)])
        
        det_trans = {}
        num_seen = 1
        
        i = 1
        k = 0
        while frontier:
            if verbose:
                i -= 1
                if i == 0:
                    k += 1
                    print("{}: {} states found.".format(k,num_seen))
                    i = len(frontier)
                
            # Pick an unprocessed state set, go over its successors
            st_set, st_num = frontier.popleft()
            for sym in self.trans_alph:
                new_st_set = frozenset(st2 for st in st_set for st2 in self.trans.get((st, sym), set()))
                if new_st_set:
                    try:
                        # Use existing label
                        new_num = seen[new_st_set]
                    except KeyError:
                        # Pick a new label for the set
                        new_num = num_seen
                        num_seen += 1
                        frontier.append((new_st_set, new_num))
                        seen[new_st_set] = new_num
                    # Transitions are stored using the integer labels
                    det_trans[st_num, sym] = new_num

        self.trans = det_trans
        self.states = set(tr[0] for tr in det_trans) | set(det_trans.values())
        self.right_resolving = True

        # Trim the transitions
        self.remove_sinks(verbose=verbose)
        
        if verbose:
            print("Determinized to {} states and {} transitions".format(len(self.states), len(self.trans)))
        
    def minimize(self, verbose=False):
        "Minimize this right-resolving automaton using Moore's algorithm."
        assert self.right_resolving
        if self.minimal:
            return
        
        # Start with uniform color
        # 0 is the special "no state" color
        coloring = {st : 1 for st in self.states}
        colors = set([1])
        num_colors = 1
        
        # Iteratively update coloring based on the colors of successors
        i = 0
        while True:
            if verbose:
                i += 1
                print("Minimization round {}: {} states separated.".format(i, num_colors))
            # First, use tuples of colors as new colors
            new_coloring = dict()
            new_colors = set()
            for st in self.states:
                next_colors = [coloring[st]]
                for sym in self.trans_alph:
                    try:
                        next_colors.append(coloring[self.trans[st, sym]])
                    except KeyError:
                        next_colors.append(0)
                new_color = tuple(next_colors)
                new_coloring[st] = new_color
                new_colors.add(new_color)
            # Then, encode new colors as positive integers
            color_nums = { color : i for (i, color) in enumerate(new_colors, start=1) }
            new_coloring = { st : color_nums[color] for (st, color) in new_coloring.items() }
            new_num_colors = len(new_colors)
            # If strictly more colors were needed, repeat
            if num_colors == new_num_colors:
                break
            else:
                colors = new_colors
                coloring = new_coloring
                num_colors = new_num_colors

        # Compute new transition function and state set
        self.trans = {(coloring[st]-1, sym) : coloring[st2]-1
                      for ((st, sym), st2) in self.trans.items()}
        self.states = set(tr[0] for tr in self.trans)
        self.minimal = True
                    
    def deduce_transition(self, conf_word, fixed_axes, st1=None, st2=None, equal=False):
        "Deduce transition words and pairs along the finite/periodic word"
        assert self.right_resolving # for now
        period = len(conf_word)
        pairs = {(st, st) : tuple()
                 for st in (self.states if st1 is None else [st1])}
        word_len = 0
        seen = set()
        while pairs:
            found_new = False
            # extend the words by a single symbol of the periodic word
            conf_syms = conf_word[word_len % period]
            if None in conf_syms:
                # nonexistent node -> put arbitrary symbols, restart from arbitrary state
                new_pairs = dict()
                for ((st, stt), word) in pairs.items():
                    new_sym = tuple(min(sym) if type(sym) == list else sym for sym in conf_syms)
                    for new_st in self.states:
                        new_pairs[st, new_st] = word + (new_sym,)
            else:
                # all nodes exist -> compute new states
                new_pairs = dict()
                for ((st, stt), word) in pairs.items():
                    for sym in iter_prod(*(iter(syms if type(syms) == list else [syms])
                                           for syms in conf_syms)):
                        try:
                            new_st = self.trans[stt, sym]
                            new_pairs[st, new_st] = word+(sym,)
                        except KeyError:
                            pass
            pairs = new_pairs
            word_len += 1
            if word_len % period == 0:
                # check if we have found a configuration
                for ((st, stt), word) in pairs.items():
                    if (st, stt) not in seen:
                        seen.add((st, stt))
                        found_new = True
                        if (st1 is None or st == st1) and (st2 is None or stt == st2) and (st == stt or not equal):
                            # transition was found
                            yield (st, stt, word)
                if fixed_axes or not found_new:
                    # no configuration was found
                    break
        
    def deduce_global(self, conf, periodics=None, fixed_axes=None, bound=None):
        "Deduce a global configuration with variable structure."
        assert self.right_resolving # for now
        
        # conf is a recognizable configuration
        # periodics is a list of directions we want to be periodic (either [] or [0])
        # fixed_axes is a list of directions where we have fixed the markers (either [] or [0])
        
        [(a,b,c,d)] = conf.markers
        if a==b and c==d:
            # periodic configuration
            period = c-a
            conf_word = [tuple(conf[a+i,node] for node in self.nodes)
                         for i in range(period)]
            # find periodic result (since one must exist, if a result exists)
            for (st, stt, word) in self.deduce_transition(conf_word, fixed_axes, equal=True):
                word_len = len(word)
                markers = [(a,a, a+word_len, a+word_len)]
                pat = {(a+i, node) : sym
                       for (i, syms) in enumerate(word)
                       for (node, sym) in zip(self.nodes, syms)}
                return RecognizableConf(markers, pat, self.nodes, onesided=self.onesided)
        else:
            # general recognizable configuration
            # first find all possible periodic tails
            left_per = [tuple(conf[a+i,node] for node in self.nodes) for i in range(b-a)]
            middle = [tuple(conf[i,node] for node in self.nodes) for i in range(b,c)]
            right_per = [tuple(conf[c+i,node] for node in self.nodes) for i in range(d-c)]
            
            if self.onesided:
                left_per_tails = {st : tuple() for st in self.states}
            else:
                left_per_tails = {st : per
                                  for (st, _, per) in self.deduce_transition(left_per, fixed_axes, equal=True)}
            if fixed_axes:
                left_tails = {st : (per, tuple())
                              for (st, per) in left_per_tails.items()}
            else:
                left_tails = {st : (per, trans)
                              for (lst, per) in left_per_tails.items()
                              for (_, st, trans) in self.deduce_transition(left_per, False, st1=lst)}
            left_mids = {st : (per, trans, mid)
                         for (lst, (per, trans)) in left_tails.items()
                         for (_, st, mid) in self.deduce_transition(middle, True, st1=lst)}
            if fixed_axes:
                right_trans = left_mids
            else:
                right_trans = {st : (per, ltrans, mid+trans)
                         for (lst, (per, ltrans, mid)) in left_mids.items()
                         for (_, st, trans) in self.deduce_transition(right_per, False, st1=lst)}
            for (lst, (lper, ltrans, rtrans)) in right_trans.items():
                for (_, _, rper) in self.deduce_transition(right_per, fixed_axes, st1=lst, st2=lst):
                    # we have found the configuration
                    marker = (b-len(lper)-len(ltrans), b-len(ltrans), b+len(rtrans), b+len(rtrans)+len(rper))
                    pat = dict()
                    for (i, syms) in enumerate(lper + ltrans + rtrans + rper):
                        for (node, sym) in zip(self.nodes, syms):
                            pat[marker[0]+i, node] = sym
                    return RecognizableConf([marker], pat, self.nodes, onesided=self.onesided)
        return None
            
    def intersection(self, other):
        "Intersection of two 1D sofics."
        assert self.nodes == other.nodes and self.alph == other.alph and self.onesided == other.onesided
        if self.right_resolving:
            if other.right_resolving:
                trans = {((st1, st2), sym) : (res1, other.trans[st2, sym])
                         for ((st1, sym), res1) in self.trans.items()
                         for st2 in other.states
                         if (st2, sym) in other.trans}
            else:
                trans = {((st1, st2), sym) : set((res1, res2) for res2 in other.trans[st2, sym])
                         for ((st1, sym), res1) in self.trans.items()
                         for st2 in other.states
                         if (st2, sym) in other.trans}
        elif other.right_resolving:
            trans = {((st1, st2), sym) : set((res, other.trans[st2, sym]) for res in ress)
                     for ((st1, sym), ress) in self.trans.items()
                     for st2 in other.states
                     if (st2, sym) in other.trans}
        else:
            trans = {((st1, st2), sym) : set((res1, res2) for res1 in ress for res2 in other.trans[st2, sym])
                     for ((st1, sym), ress) in self.trans.items()
                     for st2 in other.states
                     if (st2, sym) in other.trans}
        res = Sofic1D(self.nodes, self.alph, self.topology, trans, right_resolving=self.right_resolving and other.right_resolving, onesided=self.onesided)
        res.remove_sinks()
        return res
        
    def union(self, other):
        "Union of two 1D sofic shifts."
        assert self.nodes == other.nodes and self.alph == other.alph and self.onesided == other.onesided
        if self.right_resolving:
            if other.right_resolving:
                trans = {((st,0), sym) : (res,0)
                         for ((st, sym), res) in self.trans.items()}
                trans.update({((st,1), sym) : (res,1)
                              for ((st, sym), res) in other.trans.items()})
            else:
                trans = {((st,0), sym) : set([(res,0)])
                         for ((st, sym), res) in self.trans.items()}
                trans.update({((st,1), sym) : set((res,1) for res in ress)
                              for ((st, sym), ress) in other.trans.items()})
        elif other.right_resolving:
            trans = {((st,0), sym) : set((res,0) for res in ress)
                     for ((st, sym), ress) in self.trans.items()}
            trans.update({((st,1), sym) : set([(res,1)])
                          for ((st, sym), res) in other.trans.items()})
        else:
            trans = {((st,0), sym) : set((res,0) for res in ress)
                     for ((st, sym), ress) in self.trans.items()}
            trans.update({((st,1), sym) : set((res,1) for res in ress)
                          for ((st, sym), ress) in other.trans.items()})
        return Sofic1D(self.nodes, self.alph, self.topology, trans, right_resolving=self.right_resolving and other.right_resolving, onesided=self.onesided)

    def language(self):
        alph = self.trans_alph
        states = self.states
        trans = dict()
        if self.right_resolving:
            for st in states:
                for sym in alph:
                    try:
                        trans[st, sym] = [self.trans[st, sym]]
                    except KeyError:
                        trans[st, sym] = []
        else:
            for st in states:
                for sym in alph:
                    try:
                        trans[st, sym] = self.trans[st, sym]
                    except KeyError:
                        trans[st, sym] = []
        aut = NFA(self.trans_alph, trans, states, states, states=states)
        aut.rename()
        return aut
        
def intersection(*sofics):
    cur = sofics[0]
    for nxt in sofics[1:]:
        cur = cur.intersection(nxt)
    return cur
    
def union(*sofics):
    cur = sofics[0]
    for nxt in sofics[1:]:
        cur = cur.union(nxt)
    return cur

def product(*sofics, track_names=None):
    if track_names is None:
        track_names = list(str(n) for n in range(len(sofics)))
    nodes = sft.Nodes({tr:sof.nodes for (tr, sof) in zip(track_names, sofics)})
    alph = {(tr,) + node : sof.alph[node]
            for (tr, sof) in zip(track_names, sofics)
            for node in sof.nodes}
    topology = []
    for (tr, sof) in zip(track_names, sofics):
        for t in sof.topology:
            # t[:1] is the name of an edge. We make a copy with track added.
            topology.append(t[:2] + tuple((tr,) + n for n in t[2:]))
            
    # build product transition graph
    if all(sof.right_resolving for sof in sofics):
        tr_vecs = iter_prod(*(iter(sof.trans.items()) for sof in sofics))
        trans = {(tuple(tr[0][0] for tr in tr_vec), tuple(c for tr in tr_vec for c in tr[0][1])) : 
                 tuple(tr[1] for tr in tr_vec)
                 for tr_vec in tr_vecs}
        right_resolving = True
    else:
        tr_vecs = iter_prod(*(((a, {b}) for (a,b) in sof.trans.items()) if sof.right_resolving else iter(sof.trans.items()) for sof in sofics))
        trans = {(tuple(tr[0][0] for tr in tr_vec), tuple(c for tr in tr_vec for c in tr[0][1])) : 
                 set(iter_prod(*(iter(sts) for sts in tr_vec[1])))
                 for tr_vec in tr_vecs}
        right_resolving = False
        
    return Sofic1D(nodes, alph, topology, trans, right_resolving=right_resolving, onesided=sofics[1].onesided)
