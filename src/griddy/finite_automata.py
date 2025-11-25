import time

class DFA:
    """
    Deterministic finite automata with several output symbols.
    Classical "acceptor" DFA have output alphabet {True, False}.
    """

    @classmethod
    def universal(self, alph):
        trans = {(0, sym) : 0 for sym in alph}
        return self(alph, trans, 0, {0})

    def __init__(self, alph, trans, init, finals=None, outputs=None, states=None):
        self.alph = alph
        self.trans = trans
        if states is None:
            self.states = {st for (st, _) in trans}
        else:
            self.states = states
        self.init = init
        if finals is not None:
            self.outputs = { st : st in finals for st in self.states}
        elif outputs is not None:
            self.outputs = outputs
        else:
            raise ValueError("DFA needs either finals or outputs")

    def info_string(self, name=None, verbose=False):
        if name is None:
            s = ["DFA on alphabet {} with {} states".format(self.alph, len(self.states))]
        else:
            s = ["DFA {} on alphabet {} with {} states".format(name, self.alph, len(self.states))]
        if verbose:
            s.append("Transitions: {}".format(self.trans))
            s.append("Initial state: {}".format(self.init))
            s.append("Outputs: {}".format(self.outputs))
        return "\n".join(s)

    def __call__(self, st, sym):
        return self.trans[st, sym]

    def extend_alph(self, new_syms):
        "Extend the alphabet by new symbols while keeping the same language."
        # Acceptor only
        nums = {st : i for (i, st) in enumerate(self.states)}
        trans = {(nums[st], sym) : nums[st2] for ((st, sym), st2) in self.trans.items()}

        new_syms = [sym for sym in new_syms if sym not in self.alph]
        new_alph = list(self.alph) + list(new_syms)
        sink = -1
        for sym in new_alph:
            trans[sink, sym] = sink
        for i in nums.values():
            for sym in new_syms:
                trans[i, sym] = sink
        outputs = { nums[st] : c for (st, c) in self.outputs.items() }
        outputs[sink] = False
        return DFA(new_alph, trans, nums[self.init], outputs=outputs)

    def read_word(self, st, word):
        the_st = st
        for sym in word:
            the_st = self.trans[the_st, sym]
        return the_st

    def map_outputs(self, f):
        return DFA(self.alph, self.trans, self.init, outputs={st : f(c) for (st, c) in self.outputs.items()})

    def accepts(self, word):
        # Acceptor only
        st = self.init
        for sym in word:
            st = self(st, sym)
        return self.outputs[st]

    def output(self, word):
        return self.accepts(word)
        
    def to_nfa(self):
        # Acceptor only
        return NFA(self.alph, {(st, sym) : [st2] for ((st, sym), st2) in self.trans.items()}, {self.init}, finals={st for st in self.states if self.outputs[st]}, states=self.states)

    def concat(self, other):
        # Acceptor only
        return self.to_nfa().concat(other)

    def plus(self):
        # Acceptor only
        return self.to_nfa().plus()

    def star(self):
        # Acceptor only
        return self.to_nfa().star()
        
    def negate(self):
        # Acceptor only
        return DFA(self.alph, self.trans, self.init, outputs={st : not c for (st,c) in self.outputs.items()})

    def intersect(self, other):
        # Acceptor only
        if isinstance(other, DFA):
            init = (self.init, other.init)
            states = {init}
            trans = dict()
            frontier = [init]
            while frontier:
                newfrontier = []
                for pair in frontier:
                    (st1, st2) = pair
                    for sym in self.alph:
                        trans[(st1, st2), sym] = res = (self(st1, sym), other(st2, sym))
                        if res not in states:
                            states.add(res)
                            newfrontier.append(res)
                frontier = newfrontier
            outputs = {(st1, st2) : self.outputs[st1] and other.outputs[st2]
                       for (st1, st2) in states}
            return DFA(self.alph, trans, init, outputs=outputs, states=states)
        else:
            return other.intersect(self)

    def union(self, other):
        # Acceptor only
        return self.to_nfa().union(other)

    def rename(self):
        nums = {st : i for (i, st) in enumerate(self.states)}
        self.trans = {(nums[st], sym) : nums[st2] for ((st, sym), st2) in self.trans.items()}
        self.states = {nums[st] for st in self.states}
        self.init = nums[self.init]
        self.outputs = {nums[st] : c for (st,c) in self.outputs.items()}

    def trim(self, verbose=False):
        if verbose:
            print("Trimming {}-state DFA".format(len(self.states)))
        reachables = {self.init}
        frontier = [self.init]
        while frontier:
            new_frontier = []
            for st in frontier:
                for sym in self.alph:
                    st2 = self(st, sym)
                    if st2 not in reachables:
                        reachables.add(st2)
                        new_frontier.append(st2)
            frontier = new_frontier
        self.trans = {(st, sym) : st2 for ((st, sym), st2) in self.trans.items()
                      if st in reachables}
        self.states &= reachables
        self.outputs = {st : c for (st,c) in self.outputs.items() if st in reachables}
        if verbose:
            print("Trimmed to {} states".format(len(self.states)))

    def minimize(self, verbose=False):
        """
            Minimize a DFA using Moore's algorithm.
            It is assumed that all states are reachable.
        """
        if verbose: print("Minimizing")

        # Maintain a coloring of the states; states with different colors are provably non-equivalent
        color_map = {c : i for (i,c) in enumerate(set(self.outputs.values()))}
        colors = set(color_map.values())
        coloring = {st : color_map[c] for (st, c) in self.outputs.items()}
        num_colors = len(colors)

        # Iteratively update coloring based on the colors of successors
        i = 0
        while True:
            i += 1
            if verbose: print("Round {}: {} states separated".format(i, num_colors))
            # First, use tuples of colors as new colors
            new_coloring = {}
            new_colors = set()
            for st in self.states:
                new_color = (coloring[st],) + tuple(coloring[self(st, sym)] for sym in self.alph)
                new_coloring[st] = new_color
                new_colors.add(new_color)
            # Then, encode new colors as integers
            color_nums = { color : i for (i, color) in enumerate(new_colors) }
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
        new_trans_dict = {}
        for st in self.states:
            for sym in self.alph:
                new_trans_dict[new_coloring[st], sym] = new_coloring[self(st, sym)]

        new_outputs = {new_coloring[st] : c for (st, c) in self.outputs.items()}
        new_states = {new_coloring[st] for st in self.states}
        return DFA(self.alph, new_trans_dict, new_coloring[self.init], outputs=new_outputs, states=new_states)

    def equals(self, other, ret_diff=False, incomplete=True):
        # If other is not DFA, acceptor only
        if isinstance(other, DFA):
            reachables = {(self.init, other.init) : []}
            frontier = list(reachables)
            i = 0
            while frontier:
                newfrontier = []
                for (st1, st2) in frontier:
                    if self.outputs[st1] != other.outputs[st2]:
                        if ret_diff:
                            return False, reachables[st1, st2]
                        else:
                            return False
                    for sym in self.alph:
                        try:
                            new = (self(st1, sym), other(st2, sym))
                        except KeyError as e:
                            if incomplete:
                                continue
                            else:
                                raise e
                        if new not in reachables:
                            reachables[new] = reachables[st1, st2] + [sym]
                            newfrontier.append(new)
                frontier = newfrontier
                i += 1
            if ret_diff:
                return True, None
            else:
                return True
        else:
            return self.contains(other) and other.contains(self)

    def contains(self, other, track=False, verbose=False, incomplete=True):
        # DFA-XFA containment, acceptor only
        if isinstance(other, DFA):
            if track:
                reachables = {(self.init, other.init) : []}
            else:
                reachables = {(self.init, other.init)}
            frontier = list(reachables)
            i = 0
            while frontier:
                newfrontier = []
                for (st1, st2) in frontier:
                    if (not self.outputs[st1]) and other.outputs[st2]:
                        if track:
                            return (False, reachables[st1, st2])
                        else:
                            return False
                    for sym in self.alph:
                        try:
                            new = (self(st1, sym), other(st2, sym))
                        except KeyError as e:
                            if incomplete:
                                continue
                            else:
                                raise e
                        if new not in reachables:
                            if track:
                                reachables[new] = reachables[st1, st2] + [sym]
                            else:
                                reachables.add(new)
                            newfrontier.append(new)
                frontier = newfrontier
                i += 1
                if verbose:
                    print("Round {}: {} states processed, {} in frontier".format(i, len(reachables), len(frontier)))
        else:
            if track:
                reachables = {(self.init, st) : [] for st in other.inits}
            else:
                reachables = {(self.init, st) for st in other.inits}
            frontier = list(reachables)
            i = 0
            while frontier:
                newfrontier = []
                for (st1, st2) in frontier:
                    if (not self.outputs[st1]) and st2 in other.finals:
                        if track:
                            return (False, reachables[st1, st2])
                        else:
                            return False
                    for sym in self.alph:
                        st3 = self(st1, sym)
                        for st4 in other(st2, sym):
                            new = (st3, st4)
                            if new not in reachables:
                                if track:
                                    reachables[new] = reachables[st1, st2] + [sym]
                                else:
                                    reachables.add(new)
                                newfrontier.append(new)
                frontier = newfrontier
                i += 1
                if verbose:
                    print("Round {}: {} states processed, {} in frontier".format(i, len(reachables), len(frontier)))
        if track:
            return (True, None)
        else:
            return True
        
class NFA:

    @classmethod
    def singleton(self, alph, sym):
        trans = dict()
        for sym2 in alph:
            if sym == sym2:
                trans[0, sym2] = [1]
            else:
                trans[0, sym2] = []
            trans[1, sym2] = []
        return self(alph, trans, {0}, {1})

    @classmethod
    def one_of(self, alph, syms):
        trans = dict()
        for sym in alph:
            if sym in syms:
                trans[0, sym] = [1]
            else:
                trans[0, sym] = []
            trans[1, sym] = []
        return self(alph, trans, {0}, {1})

    @classmethod
    def empty_word(self, alph):
        "NFA accepting only the empty word"
        trans = dict()
        for sym in alph:
            trans[0, sym] = []
        return self(alph, trans, {0}, {0})

    @classmethod
    def single_word(self, alph, word):
        trans = dict()
        for st in range(len(word)+1):
            for sym in alph:
                if st < len(word) and sym == word[st]:
                    trans[st, sym] = [st+1]
                else:
                    trans[st, sym] = []
        return self(alph, trans, {0}, {len(word)})
                    

    def __init__(self, alph, trans, inits, finals, states=None):
        self.alph = alph
        self.trans = trans
        if states is None:
            self.states = {st for (st, _) in trans}
        else:
            self.states = states
        self.inits = inits
        self.finals = finals

    def __call__(self, st, sym):
        return self.trans[st, sym]

    def info_string(self, name, verbose=False):
        s = ["NFA {} on alphabet {} with {} states".format(name, self.alph, len(self.states))]
        if verbose:
            s.append("Transitions: {}".format(self.trans))
            s.append("Initial states: {}".format(self.inits))
            s.append("Final states: {}".format(self.finals))
        return "\n".join(s)

    def rev_trans(self):
        rev = {(st, sym) : [] for st in self.states for sym in self.alph}
        for ((st, sym), sts) in self.trans.items():
            for st2 in sts:
                rev[st2, sym].append(st)
        return rev

    def concat(self, other):
        if isinstance(other, DFA):
            other = other.to_nfa()
        trans = dict()
        other_inits = {(1, st) for st in other.inits}
        init_followers = {sym : set((1, st2) for st in other.inits for st2 in other(st, sym))
                          for sym in self.alph}
        for ((st, sym), sts) in self.trans.items():
            trans[(0, st), sym] = {(0, st2) for st2 in sts}
            if st in self.finals:
                trans[(0, st), sym] |= init_followers[sym]
            if not set(sts).isdisjoint(self.finals):
                trans[(0, st), sym] |= other_inits
        for ((st, sym), sts) in other.trans.items():
            trans[(1, st), sym] = {(1, st2) for st2 in sts}
        inits = {(0, st) for st in self.inits}
        if not self.inits.isdisjoint(self.finals):
            inits |= other_inits
        finals = {(1, st) for st in other.finals}
        return NFA(self.alph, trans, inits, finals)

    def plus(self):
        trans = dict()
        for ((st, sym), sts) in self.trans.items():
            trans[st, sym] = sts = set(sts)
            if not sts.isdisjoint(self.finals):
                trans[st, sym] |= self.inits
        return NFA(self.alph, trans, self.inits, self.finals)

    def star(self):
        trans = dict()
        for ((st, sym), sts) in self.trans.items():
            trans[st, sym] = sts = set(sts)
            if not sts.isdisjoint(self.finals):
                trans[st, sym] |= self.inits
        return NFA(self.alph, trans, self.inits, self.inits | self.finals)

    def projection(self, func):
        alph = {func(sym) for sym in self.alph}
        trans = {(st, func(sym)) : set() for st in self.states for sym in self.alph}
        for ((st, sym), sts) in self.trans.items():
            trans[st, func(sym)] |= set(sts)
        return NFA(alph, trans, self.inits, self.finals, states=self.states)

    def intersect(self, other):
        if isinstance(other, DFA):
            inits = {(st, other.init) for st in self.inits}
            states = {st for st in inits}
            trans = dict()
            frontier = list(inits)
            while frontier:
                newfrontier = []
                for pair in frontier:
                    (st1, st2) = pair
                    for sym in self.alph:
                        trans[(st1, st2), sym] = res = {(res1, other(st2, sym))
                                                        for res1 in self(st1, sym)}
                        for new in res:
                            if new not in states:
                                states.add(new)
                                newfrontier.append(new)
                frontier = newfrontier
            finals = {(st1, st2) for (st1, st2) in states
                      if st1 in self.finals and other.outputs[st2]}
        else:
            inits = {(st1, st2) for st1 in self.inits for st2 in other.inits}
            states = {st for st in inits}
            trans = dict()
            frontier = list(inits)
            while frontier:
                newfrontier = []
                for pair in frontier:
                    (st1, st2) = pair
                    for sym in self.alph:
                        trans[(st1, st2), sym] = res = {(res1, res2)
                                                        for res1 in self(st1, sym)
                                                        for res2 in other(st2, sym)}
                        for new in res:
                            if new not in states:
                                states.add(new)
                                newfrontier.append(new)
                frontier = newfrontier
            finals = {(st1, st2) for (st1, st2) in states
                      if st1 in self.finals and st2 in other.finals}
        return NFA(self.alph, trans, inits, finals, states=states)

    def union(self, other):
        if isinstance(other, DFA):
            other = other.to_nfa()
        states = {(i, st)
                  for (i, aut) in enumerate([self, other])
                  for st in aut.states}
        inits = {(i, st) for (i, aut) in enumerate([self, other]) for st in aut.inits}
        finals = {(i, st) for (i, aut) in enumerate([self, other]) for st in aut.finals}
        trans = {((i, st), sym) : {(i, st2) for st2 in sts}
                 for (i, aut) in enumerate([self, other])
                 for ((st, sym), sts) in aut.trans.items()}
        return NFA(self.alph, trans, inits, finals, states=states)

    def left_quotient(self, other):
        if isinstance(other, DFA):
            other = other.to_nfa()
            
        new_inits = set()
        seen = {(st1, st2) for st1 in self.inits for st2 in other.inits}
        frontier = list(seen)
        while frontier:
            newfrontier = []
            for (st1, st2) in frontier:
                if st2 in other.finals:
                    new_inits.add(st1)
                for sym in self.alph:
                    for st3 in self(st1, sym):
                        for st4 in other(st2, sym):
                            pair = (st3, st4)
                            if pair not in seen:
                                seen.add(pair)
                                newfrontier.append(pair)
            frontier = newfrontier

        return NFA(self.alph, self.trans, new_inits, self.finals, states=self.states)

    def right_quotient(self, other):
        if isinstance(other, DFA):
            other = other.to_nfa()

        self_rev = self.rev_trans()
        other_rev = other.rev_trans()

        new_finals = set()
        seen = {(st1, st2) for st1 in self.finals for st2 in other.finals}
        frontier = list(seen)
        while frontier:
            newfrontier = []
            for (st1, st2) in frontier:
                if st2 in other.inits:
                    new_finals.add(st1)
                for sym in self.alph:
                    for st3 in self_rev[st1, sym]:
                        for st4 in other_rev[st2, sym]:
                            pair = (st3, st4)
                            if pair not in seen:
                                seen.add(pair)
                                newfrontier.append(pair)
            frontier = newfrontier

        return NFA(self.alph, self.trans, self.inits, new_finals, states=self.states)

    def rename(self):
        nums = {st : i for (i, st) in enumerate(self.states)}
        self.trans = {(nums[st], sym) : {nums[st2] for st2 in sts}
                 for ((st, sym), sts) in self.trans.items()}
        self.states = {nums[st] for st in self.states}
        self.inits = {nums[st] for st in self.inits}
        self.finals = {nums[st] for st in self.finals}
    
    def trim(self, forward=True, backward=True, verbose=False):
        if verbose:
            print("Trimming {}-state NFA".format(len(self.states)))
        if forward:
            reachables = set(self.inits)
            frontier = set(self.inits)
            while frontier:
                new_frontier = []
                for st in frontier:
                    for sym in self.alph:
                        for st2 in self(st, sym):
                            if st2 not in reachables:
                                reachables.add(st2)
                                new_frontier.append(st2)
                frontier = new_frontier
            self.trans = {(st, sym) : st2 for ((st, sym), st2) in self.trans.items()
                          if st in reachables}
            self.states &= reachables
            self.finals &= reachables
        if backward:
            rev_trans = {(st, sym) : [] for st in self.states for sym in self.alph}
            for ((st, sym), sts) in self.trans.items():
                for st2 in sts:
                    rev_trans[st2, sym].append(st)
            reachables = set(self.finals)
            frontier = set(self.finals)
            while frontier:
                new_frontier = []
                for st in frontier:
                    for sym in self.alph:
                        for st2 in rev_trans[st, sym]:
                            if st2 not in reachables:
                                reachables.add(st2)
                                new_frontier.append(st2)
                frontier = new_frontier
            self.trans = {(st, sym) : {st2 for st2 in sts if st2 in reachables}
                          for ((st, sym), sts) in self.trans.items()
                          if st in reachables}
            self.states &= reachables
            self.inits &= reachables
        if verbose:
            print("Trimmed to {} states".format(len(self.states)))

    def determinize(self, verbose=False):
        """
        Determinize using the powerset construction.
        """
        if verbose: print("Deteminizing")
        
        # Maintain sets of seen and unprocessed state sets, and integer labels for seen sets
        init_st = frozenset(self.inits)
        seen = {init_st : 0}
        new_finals = set([0] if any(i in self.finals for i in self.inits) else [])
        frontier = [(init_st, 0)]
        
        det_trans = {}
        num_seen = 1
        
        i = 0
        while frontier:
            i += 1
            newfrontier = []
            # Pick an unprocessed state set, go over its successors
            for (st_set, st_num) in frontier:
                for sym in self.alph:
                    new_st_set = frozenset(st2 for st in st_set for st2 in self(st, sym))
                    if new_st_set in seen:
                        new_num = seen[new_st_set]
                    else:
                        # Pick a new label for the set
                        new_num = num_seen
                        num_seen += 1
                        newfrontier.append((new_st_set, new_num))
                        seen[new_st_set] = new_num
                        if any(x in self.finals for x in new_st_set):
                            new_finals.add(new_num)
                    # Transitions are stored using the integer labels
                    det_trans[st_num, sym] = new_num
            frontier = newfrontier
            if verbose:
                print("Round {}: {} states found, {} in frontier".format(i, num_seen, len(frontier)))
        
        return DFA(self.alph, det_trans, 0, new_finals, states=set(seen.values()))

    def equals(self, other):
        return self.contains(other) and other.contains(self)
    
    def contains(self, other, track=False, verbose=False):
        
        # NFA-XFA containment
            
        if isinstance(other, DFA):
            other = other.to_nfa()

        clock = time.perf_counter()

        # Keep track of (compressed) processed states of pair automaton, B is implicitly determinized
        frontier = [(st, frozenset(self.inits)) for st in other.inits]
        #frontier = set([(init_A, inits_B, compre(init_A, inits_B))])
        if not track:
            reachables = {st : {comp} for (st, comp) in frontier}
        else:
            reachables = {st : {comp : []} for (st, comp) in frontier}

        # Share states for a potential decrease in memory use
        def compre(y):
            for sets in reachables.values():
                for the_set in sets:
                    if the_set == y:
                        return the_set
            return y

        # Process all reachable pairs in depth-first order, stopping if A accepts but B does not
        i = 0
        while frontier:
            if verbose:
                print("{}: {} states processed, {} in frontier, in {:.3f} seconds.".format(i, sum(len(x) for x in reachables.values()), len(frontier), time.perf_counter()-clock))
                #print("reachables", reachables)
            i += 1
            newfrontier = []
            
            #assert all(st_A in reachables and c_B in reachables[st_A] for (st_A, c_B) in frontier)
           
            for pair in frontier:
                st, the_set = pair
                #if st_A not in reachables or comp_B not in reachables[st_A]:
                    # a subset was already handled
                #    continue
                for sym in self.alph:
                    for new_st in other(st, sym):
                        new_set = frozenset(st2 for st1 in the_set for st2 in self(st1, sym))
                        if new_st in other.finals and all(st1 not in self.finals for st1 in new_set):
                            # A accepts but B does not: A\B is nonempty
                            #print("sep", set_B, news_B, finals_B)
                            if track:
                                return (False, reachables[st][the_set] + [sym])
                            else:
                                return False
                        #if new_p in reachables:
                        try:
                            if any(other_set <= new_set for other_set in reachables[new_st]):
                                continue
                        except KeyError:
                            pass
                        new_comp = compre(new_set)
                        if not track:
                            try:
                                reachables[new_st].add(new_comp)
                            except KeyError:
                                reachables[new_st] = {new_comp}
                        else:
                            old = reachables[st][the_set]
                            try:
                                reachables[new_st][new_comp] = old + [sym]
                            except KeyError:
                                reachables[new_st] = {new_comp : old + [sym]}
                        newfrontier.append((new_st, new_comp))
            frontier = newfrontier
        if track:
            return (True, None)
        return True

class NTrans:

    def __init__(self, alph, trans, init, finals, states=None):
        # Transition function is a dict (st, in_sym) -> [(st, [out_sym])]
        self.alph = alph
        self.trans = trans
        if states is None:
            self.states = {st for (st, _) in trans}
        else:
            self.states = states
        self.init = init
        self.finals = finals

    def __call__(self, st, sym):
        return self.trans[st, sym]
