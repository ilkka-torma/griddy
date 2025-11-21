#import debug_print_hook

import math
from fractions import Fraction as fr
import time
import multiprocessing as mp
from enum import Enum
import sys
import pickle
import argparse
import fractions
import frozendict as fd
from sft import *
from general import *

class CompMode(Enum):
    SQUARE_CYCLE = 0 # don't recompute, use O(n^2) space, return cycle
    LINSQRT_CYCLE = 1 # recompute twice, use O(n^{3/2}) space, return cycle
    LINEAR_NOCYCLE = 2 # recompute once, use O(n) space, return only density and length

COMP_MODE = CompMode.LINEAR_NOCYCLE

PRINT_NFA = False
PRINT_CYCLE = False

def vrot(vec, rots, heights):
    "Translate a vector cyclically in a hyperrectangle"
    return tuple((y+r)%h for(y,r,h) in zip(vec, rots, heights))

def hyperrectangle(heights):
    if not heights:
        yield tuple()
    else:
        for vec in hyperrectangle(heights[1:]):
            for coord in range(heights[0]):
                yield (coord,) + vec

def pats(domain, alph, forbs, i=0):
    #print("AM DOING PATS", domain, alph, forbs, i)
    if i >= len(domain):
        yield dict()
    else:
        nvec = domain[i]
        #print(nvec)
        if (nvec) == (0,0,()):
            raise Exception("da fuq")
        for pat in pats(domain, alph, forbs, i=i+1):
            for c in alph[nvec[1]][:-1]:
                pat2 = pat.copy()
                pat2[nvec] = c
                if all(any(pat2.get(v, None) != c
                           for (v, c) in forb.items())
                       for forb in forbs):
                    yield pat2
            pat[nvec] = alph[nvec[1]][-1]
            if all(any(pat.get(v, None) != c
                       for (v, c) in forb.items())
                   for forb in forbs):
                yield pat
        
def gcd_bezout(nums):
    "Return the pair (gcd, bezout_coefficients)"
    a = nums[0]
    if len(nums) == 1:
        if a > 0:
            return (a, [1])
        else:
            return (-a, [-1])
    if a == 1:
        return (1, [1] + [0*(len(nums)-1)])
    b, coeffs = gcd_bezout(nums[1:])
    # Extended euclidean algorithm
    s = 0
    r = b
    old_s = 1
    old_r = a
    while r:
        q = old_r // r
        old_r, r = r, old_r % r
        old_s, s = s, old_s - q*s
    if b:
        m = (old_r - old_s*a) // b
    else:
        m = 0
    if old_r > 0:
        return (old_r, [old_s] + [m*c for c in coeffs])
    else:
        return (-old_r, [-old_s] + [-m*c for c in coeffs])
        
def normalize_periods(pmat):
    "Put a period matrix in a 'row echelon form' of sorts"
    dim = len(pmat[0])
    pmat = [list(p) for p in pmat]
    for i in range(dim-1):
        # reduce column i
        if all(r[i+1] == 0 for r in pmat):
            raise Exception("bad periods")
        else:
            # compute gcd and Bezout coefficients
            g, cs = gcd_bezout([pmat[j][i+1] for j in range(i,dim-1)])
            m = pmat[i][i+1] // g
            pmat[i] = [pmat[i][k] - (m-1)*sum(c*x for (c,x) in zip(cs, [pmat[j][k] for j in range(i,dim-1)]))
                       for k in range(dim)]
            assert pmat[i][i+1] == g
            for k in range(i+1,dim-1):
                assert pmat[k][i+1] % pmat[i][i+1] == 0
                m = pmat[k][i+1] // pmat[i][i+1]
                for j in range(dim):
                    pmat[k][j] = pmat[k][j] - m*pmat[i][j]
    return pmat

def wrap(pmat, nvec):
    "Wrap a vector into the (essentially one-dimensional) fundamental domain of the period matrix"
    #print("wreap", pmat, nvec)
    vec = list(nvec[0])
    for (i, pvec) in enumerate(pmat, start=1):
        q = vec[i] // pvec[i]
        vec[0] -= q*pvec[0]
        vec[i] = vec[i] % pvec[i]
        for j in range(i+1,len(vec)):
            vec[j] -= q*pvec[j]
    #print("kitttt", (tuple(vec), nvec[1]))
    return (tuple(vec), nvec[1])
    
#def nvadd(nvec, vec):
#    return tuple(a+b for (a,b) in zip(nvec, vec)) + (nvec[-1],)

class PeriodAutomaton:
    # Transition labels are either frontier patterns or their weights
    # Frontier has size len(nodes) x height, and is slanted
    # States are collections of forbidden sets that intersect frontier and its right side
    # They are stored as integers to save space
    # trans has type dict[state] -> (dict[state] -> label(s))
    # After minimization, only the lowest weights are kept

    def __init__(self, sft, periods, rotate=False, sym_bound=None, verbose=False, immediately_relabel=True, check_periods=True, all_labels=True, weights=None):
        if verbose:
            print("constructing period automaton with periods", periods, "no symmetry" if sym_bound is None else "symmetry %s"%sym_bound, "rotated" if rotate else "not rotated")
        self.sft = sft
        if check_periods:
            if len(periods) != sft.dim-1:
                raise Exception("periods must form a rational basis with (1,0...0)")
            pmat = normalize_periods(periods)
            if verbose:
                print("normalized periods", pmat)
        else:
            pmat = periods
        self.pmat = pmat
        self.frontier = set()
        self.border_forbs = []
        heights = [pmat[i][i+1] for i in range(sft.dim-1)]
        for vec in hyperrectangle(heights):
            x = self.border_at(vec)
            self.frontier.add((x,) + vec)
            for forb in sft.forbs:
                #print("derp frob", forb)
                new_forb = dict()
                good = True
                for (nvec, c) in forb.items():
                    #print(nvec, c)
                    nvec2 = wrap(pmat, nvadd(nvec, (x,)+vec))
                    #print(nvec2, "milis")
                    if nvec2 in new_forb and new_forb[nvec2] != c:
                        good = False
                        break
                    else:
                        new_forb[nvec2] = c
                else:
                    #print("news",new_forb)
                    tr = 0
                    while any(nvec[0][0]+tr < self.border_at(nvec[0][1:]) for nvec in new_forb):
                        tr += 1
                    while all(nvec[0][0]+tr > self.border_at(nvec[0][1:]) for nvec in new_forb):
                        tr -= 1
                    new_forb = {((nvec[0][0]+tr,)+nvec[0][1:], nvec[1]) : c for (nvec, c) in new_forb.items()}
                if good and new_forb not in self.border_forbs:
                    self.border_forbs.append(new_forb)
        self.node_frontier = list(sorted((vec, q) for vec in self.frontier for q in self.sft.nodes))
        self.states = set([0])
        self.trans = dict()
        if verbose:
            print("done with #forbs", len(self.border_forbs), "#nodefrontier", len(self.node_frontier))
        self.immediately_relabel = immediately_relabel
        self.sym_bound = sym_bound
        self.rotate = rotate
        self.all_labels = all_labels

        #TODO here, just found out that frontier and node_fronteir were broken, maybe frontier still is

        self.weights = weights
        if weights == None:
            self.weight_numerators = {a:int(a) for sub_alph in self.sft.alph.values() for a in sub_alph}
            self.weight_denominator = 1
            #print("makkel")
        else:
            #print("fiwejif")
            denoms = []
            for a in weights:
                #print(weights[a])
                denoms.append(fr(weights[a], 1).denominator)
            self.weight_denominator = math.lcm(*denoms)
            self.weight_numerators = {}
            for a in weights:
                asrat = fr(weights[a], 1)
                numerator, denominator = asrat.numerator, asrat.denominator
                self.weight_numerators[a] = numerator * self.weight_denominator // denominator
            #print (self.weight_denominator, self.weight_numerators)
        #print("frontier is", self.frontier)
        #print("frontier is", self.node_frontier)

    def populate(self, num_threads=1, chunk_size=200, verbose=False, report=5000):
        debug_verbose = False
        if debug_verbose: print("asdf")
        self.s2idict = {}
        self.running = 0
        def state_to_idx(s):
            if not self.immediately_relabel:
                return s
            
            if s in self.s2idict:
                return self.s2idict[s]
            else:
                self.s2idict[s] = self.running
                self.running += 1
                return self.running-1
        
        # populate states and transitions
        if verbose:
            print("populating period automaton")
        n = 0
        task_q = mp.Queue()
        res_q = mp.Queue()
        processes = [mp.Process(target=populate_worker,
                                args=(self.pmat, self.sft.alph, self.border_forbs, self.node_frontier, self.sym_bound, self.rotate,
                                      task_q, res_q, self.weight_numerators, chunk_size))
                     for _ in range(num_threads)]
        if debug_verbose: print("processes built")
        for pr in processes:
            pr.start()
        if debug_verbose: print("processes started")
        undone = len(self.states)
        for state in self.states:
            task_q.put([state])

        assert len(self.states) == 1 # the above for loop is over singleton

        qq = []
        while undone:
            if debug_verbose: print("undoine")
            res = res_q.get()
            if debug_verbose: print("gottends")
            if type(res) == int: 
                undone -= res
                continue
            for (state, weight, new_state) in res:
                if new_state not in self.states:
                    self.states.add(new_state)
                    if verbose and (len(self.states) - undone)%report == 0:
                        print("states processed", len(self.states) - undone, "to process", undone, "total", len(self.states))
                    qq.append(new_state)
                    if len(qq) >= chunk_size:
                        task_q.put(qq)
                        undone += len(qq)
                        qq = []
                        
                    
                state_idx = state_to_idx(state)
                new_state_idx = state_to_idx(new_state)
                if state_idx not in self.trans:
                    self.trans[state_idx] = dict()
                try:
                    if self.all_labels:
                        self.trans[state_idx][new_state_idx].add(weight)
                    else:
                        self.trans[state_idx][new_state_idx] = min(self.trans[state_idx][new_state_idx], weight)
                except KeyError:
                    if self.all_labels:
                        self.trans[state_idx][new_state_idx] = set([weight])
                    else:
                        self.trans[state_idx][new_state_idx] = weight
            if qq != []:
                task_q.put(qq)
                undone += len(qq)
                qq = []
        for pr in processes:
            pr.terminate()
        news = []
        for sts in self.trans.values():
            for st in sts:
                if st not in self.trans:
                    news.append(st)
        for st in news:
            self.trans[st] = dict()
        if verbose:
            print("done with #states", len(self.states))
            
    def minimize(self, verbose=False):
        """Minimize using Moore's algorithm.
           Assumes that all states are reachable, and that the transitions are frontier patterns.
           In the minimized automaton, transitions are weights and only minimal ones are kept.
        """
        assert self.all_labels
        
        #print("before min")
        #print("trans", self.trans)
        #print("states", self.states)
        #print("i2s", self.i2sdict)
        #print("s2i", self.s2idict)
        # Maintain a coloring of the states; states with different colors are provably non-equivalent
        # Color 0 is "no state"
        #for tr in self.trans.values():
        #    print(tr)
        #    break
        
        trans = self.trans
        s2idict = self.s2idict
        alph = list(set(sym for tr in self.trans.values() for syms in tr.values() for sym in syms))
        #print("alph", alph)

        r = 1
        while True:
            if verbose:
                print("minimizing (round {})".format(r))
            r += 1
            coloring = {st : 1 for st in trans}
            colors = set([1])
            num_colors = 1
            # Iteratively update coloring based on the colors of successors
            i = 0
            while True:
                if verbose:
                    i += 1
                    print("sub-round {}: {} states separated.".format(i, num_colors))
                # First, use tuples of colors as new colors
                new_coloring = {}
                new_colors = set()
                for st in trans:
                    next_colors = {sym : {0} for sym in alph}
                    for (st2, syms) in trans[st].items():
                        for sym in syms:
                            next_colors[sym].add(coloring[st2])
                    new_color = (coloring[st],) + tuple(frozenset(next_colors[sym]) for sym in alph)
                    new_coloring[st] = new_color
                    new_colors.add(new_color)
                # Then, encode new colors as positive integers
                #print("coloring", new_coloring)
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
            all_single = True
            new_trans = {}
            for (st, tr) in trans.items():
                col = new_coloring[st]-1
                if col not in new_trans:
                    new_trans[col] = dict()
                for (st2, syms) in tr.items():
                    col2 = new_coloring[st2]-1
                    if col2 not in new_trans[col]:
                        new_trans[col][col2] = set()
                    new_trans[col][col2].add(min(sym for sym in syms))

            # If [some condition], then we are done; otherwise minimize again
            if all(len(syms) == 1 for tr in new_trans.values() for syms in tr.values()):
                for tr in new_trans.values():
                    for st in tr:
                        tr[st] = min(tr[st])
                self.trans = new_trans
                self.s2idict = {st:(new_coloring[ix]-1) for (st, ix) in s2idict.items()}
                self.i2sdict = {ix:st for (st, ix) in self.s2idict.items()}
                self.all_labels = False
                break
            else:
                trans = new_trans
                s2idict = {st:(new_coloring[ix]-1) for (st, ix) in s2idict.items()}
                #print(new_trans)
        
        #print("after min")
        #print("trans", self.trans)
        #print("states", self.states)
        #print("i2s", self.i2sdict)
        #print("s2i", self.s2idict)

    def relabel(self):
        if self.immediately_relabel:
            return
        else:
            st = list(sorted(self.states))
            ts = {s : i for (i,s) in enumerate(st)}
            self.states = set(range(len(st)))
            self.trans = {ts[p] : {ts[q] : w for (q,w) in qs.items()}
                          for (p,qs) in self.trans.items()}

    def square_min_density_cycle(self, bound_len=None, verbose=False, report=50, num_threads=1):
        "Assume states are relabeled to range(len(states))"
        if verbose:
            print("finding min density cycle in O(n^2) space")
        n = len(self.trans)
        if bound_len is None:
            m = n+1
        else:
            m = min(n+1, bound_len)
        # split transdict among processes; they can do the search backwards
        # each modifies only its own part of mins so we can share it
        # initialize with 2*height*m*max(alph), which is theoretical max val
        # access like mins[n*k+q]
        global mins, opt_prevs
        max_w = len(self.frontier)*len(self.sft.nodes)*m*max(self.weight_numerators.values())
        mins = mp.Array('i', [0 if q==k==0 else max_w
                              for k in range(m+1)
                              for q in range(n)],
                        lock=False)
        opt_prevs = mp.Array('i', [-1
                                   for k in range(m+1)
                                   for q in range(n)],
                             lock=False)
        task_qs = [((i*n)//num_threads, ((i+1)*n)//num_threads,  mp.Queue())
                   for i in range(num_threads)]
        res_q = mp.Queue()
        procs = [mp.Process(target=square_min_worker,
                            args=(mins, opt_prevs, n, m, max_w,
                                  {p : qs for (p,qs) in self.trans.items() if a <= p < b},
                                  task_q, res_q))
                 for (a, b, task_q) in task_qs]
        for proc in procs:
            proc.start()
        for k in range(1, m+1):
            if verbose and k%report==0:
                print("round", k, "/", m)
            for (_, _, task_q) in task_qs:
                task_q.put(k)
            for _ in range(num_threads):
                res = res_q.get()
                assert res is None
        for (_, _, task_q) in task_qs:
            task_q.put(None)
        
        min_num = math.inf
        min_val = None
        reachermost = None
        for _ in range(num_threads):
            num, val, reacher = res_q.get()
            if num < min_num or (num == min_num and (min_val == None or min_val < val)):
                min_num = num
                min_val = val
                reachermost = reacher
        for proc in procs:
            proc.terminate()

        #min_val *= 2
            
        path = [reachermost]
        cur = reachermost
        for i in range(m, 0, -1):
            nxt = opt_prevs[n*i+cur]
            path.append(nxt)
            cur = nxt

        #print("checking path", path)
        # check path length and weight
        #print(self.trans)
        #print(self.trans.keys())
        #print(path)
        assert len(path) == m+1
        assert sum(self.trans[path[k]][path[k+1]] for k in range(m)) == mins[n*m+path[0]]

        #print("finding cycle in", path, min_num)
        for cycle_len in range(1, m+1):
            for i in range(m+1 - cycle_len):
                if path[i] == path[i+cycle_len]:
                    summe = 0
                    for k in range(cycle_len):
                        summe += self.trans[path[i+k]][path[i+k+1]]
                    if summe/cycle_len == min_num:
                        min_cycle = list(path[i:i+cycle_len])
                        break
                    #else:
                    #    print("did not find", summe/cycle_len, min_num)
            else:
                continue
            break

        cyc_labels = self.get_cycle_labels(min_cycle, verbose=verbose)
            
        return min_num, len(cyc_labels), min_cycle, cyc_labels

    def linsqrt_min_density_cycle(self, bound_len=None, verbose=False, report=50, num_threads=1):
        "Assume states are relabeled to range(len(self.trans))"
        if verbose:
            print("finding min density cycle in O(n^(2/3)) space")
        n = len(self.trans)
        if bound_len is None:
            m = n+1
        else:
            m = min(n+1, bound_len)
        # split transdict among processes; they can do the search backwards
        # each modifies only its own part of mins so we can share it
        # initialize with 2*height*n, which is theoretical max val
        # access like sparse/dense_mins[n*k+q] and opt_prevs[n*k+q]
        # phases:
        # 1. compute sparse mins using dense mins
        #    in particular, last row is d_q(n) for each state q
        # 2. compute max of (d_q(n)-d_q(k))/(n-k) of each state q using dense mins
        #    take minimum over q, also get length of cycle
        # 3. for minimizing q, iteratively compute path segments between two rows of dense mins
        #    this needs dense mins and opt prevs
        #    stitch together into a single path, find cycle on it
        global dense_mins, sparse_mins, opt_prevs
        max_w = len(self.frontier)*len(self.sft.nodes)*m*max(self.weight_numerators.values())
        sqrtm = int(math.ceil(m**0.5))+1
        # dense_mins represents rows int(i*sqrt(n)) + j for 0 <= j <= ceil(sqrt(n)) for varying i
        dense_mins = mp.Array('i', [0 if k==q==0 else max_w
                                    for k in range(sqrtm)
                                    for q in range(n)],
                        lock=False)
        # sparse_mins represents rows int(i*sqrt(n)) for 0 <= i <= ceil(sqrt(n))
        sparse_rows = [max(0, min(m, (m*k)//sqrtm)) for k in range(sqrtm+1)]
        if verbose:
            print("using rows", sparse_rows)
        sparse_mins = mp.Array('i', [max_w
                                     for _ in sparse_rows
                                     for q in range(n)],
                        lock=False)
        opt_prevs = mp.Array('i', [-1
                                   for k in range(sqrtm)
                                   for q in range(n)],
                             lock=False)
        task_qs = [((i*n)//num_threads, ((i+1)*n)//num_threads,  mp.Queue())
                   for i in range(num_threads)]
        res_q = mp.Queue()
        procs = [mp.Process(target=linsqrt_min_worker,
                            args=(dense_mins, sparse_mins, opt_prevs, n, m, max_w, sparse_rows,
                                  {p : qs for (p,qs) in self.trans.items() if a <= p < b},
                                  task_q, res_q))
                 for (a, b, task_q) in task_qs]
        for proc in procs:
            proc.start()

        # phase 1: populate dense mins
        for k in range(0,m+1):
            if verbose and k%report==0:
                print("phase 1 round", k, "/", m)
            for (_, _, task_q) in task_qs:
                task_q.put(k)
            for _ in range(num_threads):
                res = res_q.get()
                assert res is None

        # phase 2: compute minimum q
        for p in self.trans:
            dense_mins[p] = 0 if p==0 else max_w
            dense_mins[n+p] = max_w
        min_things = math.inf, 0, 0
        for k in range(1, m):
            if verbose and k%report==0:
                print("phase 2 round", k, "/", m)
            for (_, _, task_q) in task_qs:
                task_q.put(k)
            for _ in range(num_threads):
                res = res_q.get()
                assert res is None
        for (_, _, task_q) in task_qs:
            task_q.put(None)
            res = res_q.get()
            min_things = min(min_things, res)
        min_d, min_len, min_q = min_things
        if verbose:
            print("min density", min_d/(len(self.sft.nodes)*len(self.frontier)), "min len", min_len)

        # phase 3: compute path from q
        path = [min_q]
        cur = min_q
        rnd = 1
        for (lo, hi) in reversed(list(zip(sparse_rows, sparse_rows[1:]))):
            for k in range(lo, hi+1):
                if verbose and rnd%report==0:
                    print("phase 3 round", rnd, "/", m+len(sparse_rows)-2)
                rnd += 1
                for (_, _, task_q) in task_qs:
                    task_q.put((lo,k))
                for _ in range(num_threads):
                    res = res_q.get()
                    assert res is None
            for i in reversed(range(lo+1, hi+1)):
                nxt = opt_prevs[n*(i-lo)+cur]
                path.append(nxt)
                cur = nxt
        
        for proc in procs:
            proc.terminate()
            
        # check path length and weight
        #print("path", path)
        #print("trans keys", self.trans.keys())
        #print("trans", self.trans)
        assert len(path) == m+1
        assert sum(self.trans[path[k]][path[k+1]] for k in range(m)) == sparse_mins[n*(len(sparse_rows)-1)+path[0]]

        #print(path)
        for cycle_len in range(1, m):
            for i in range(m - cycle_len):
                if path[i] == path[i+cycle_len]:
                    summe = 0
                    for k in range(cycle_len):
                        summe += self.trans[path[i+k]][path[i+k+1]]
                    if summe/cycle_len == min_d:
                        min_cycle = list(path[i:i+cycle_len])
                        break
            else:
                continue
            break

        cyc_labels = self.get_cycle_labels(min_cycle, verbose=verbose)
            
        return min_d, len(cyc_labels), min_cycle, cyc_labels

    def linear_min_density_cycle(self, bound_len=None, verbose=False, report=50, num_threads=1):
        "Assume states are relabeled to range(len(states))"
        if verbose:
            print("finding min density of cycle in O(n) space")
        n = len(self.trans)
        if bound_len is None:
            m = n+1
        else:
            m = min(n+1, bound_len)
        # split transdict among processes; they can do the search backwards
        # each modifies only its own part of mins so we can share it
        # access like mins[n*a+q] for a in [0,1,2]
        # initialize with 2*height*n, which is theoretical max val
        # 0 and 1 are "workspace" arrays, 2 is where we store values for n
        global mins
        max_w = len(self.frontier)*len(self.sft.nodes)*m*max(self.weight_numerators.values())
        mins = mp.Array('i', [0 if q==k==0 else max_w
                              for k in range(3)
                              for q in range(n)],
                        lock=False)
        task_qs = [((i*n)//num_threads, ((i+1)*n)//num_threads,  mp.Queue())
                   for i in range(num_threads)]
        res_q = mp.Queue()
        procs = [mp.Process(target=linear_min_worker,
                            args=(mins, n, m, max_w,
                                  {p : qs for (p,qs) in self.trans.items() if a <= p < b},
                                  task_q, res_q))
                 for (a,b,task_q) in task_qs]
        for proc in procs:
            proc.start()
        for p in [1,2]:
            for k in range(1, (m+1) if p == 1 else m):
                if verbose and k%report==0:
                    print("phase", p, "round", k, "/", m if p == 1 else (m-1))
                for (_, _, task_q) in task_qs:
                    task_q.put(k)
                for _ in range(num_threads):
                    res = res_q.get()
                    assert res is None
            if p == 1:
                for st in range(n):
                    mins[st] = 0 if st == 0 else max_w
        for (_, _, task_q) in task_qs:
            task_q.put(None)
        min_num = math.inf
        min_val = None
        min_state = 0
        for _ in range(num_threads):
            num, val, state, maxes = res_q.get()
            if num < min_num or (num == min_num and (min_val == None or min_val < val)):
                min_num = num
                min_val = val
                min_state = state
        for proc in procs:
            proc.terminate()
        return min_num, min_val, min_state


    def get_cycle_labels(self, cycle_as_states, verbose=False):
        #return cycle_as_states
        if verbose: print("computing transitions from state cycle")
        numf = len(self.border_forbs)
        border_sets = [set(forb) for forb in self.border_forbs]
        self.compute_i2sdict()
        labels = []
        states = [self.i2sdict[cycle_as_states[0]]]
        frontier = self.node_frontier
        if self.rotate:
            heights = [self.pmat[i][i+1] for i in range(len(self.pmat))]
        s = 1
        while True:
            a = states[-1]
            bix = cycle_as_states[s%len(cycle_as_states)]
            #if verbose: print("from", a, "to", b)
            shifted = [(f,0) for f in self.border_forbs]
            i = 0
            n = a
            while n:
                if n%2:
                    ix = i%numf
                    tr = i//numf
                    shifted.append((self.border_forbs[ix], tr+1))
                n = n//2
                i += 1
            pat_forbs = set()
            for (forb, tr) in shifted:
                pat_forb = dict()
                for (nvec, c) in forb.items():
                    if nvec[0][0]-tr > border_at(self.pmat, nvec[0][1:]):
                        break
                    tr_nvec = ((nvec[0][0]-tr,) + nvec[0][1:], nvec[1])
                    if tr_nvec in frontier:
                        pat_forb[tr_nvec] = c
                else:
                    pat_forbs.add(fd.frozendict(pat_forb))
            for new_front in pats(frontier, self.sft.alph, pat_forbs):
                try:
                    if weighted_sum(self.weight_numerators, new_front.values()) != self.trans[self.s2idict[a]][bix]:
                        continue
                except KeyError:
                    print(ass, self.trans[ass], bss)
                    1/0
                #if verbose: print("trying out", new_front)
                new_pairs = []
                sym_pairs = dict()
                for pair in shifted:
                    forb, tr = pair
                    over = False
                    for (nvec, c) in forb.items():
                        x = nvec[0][0]
                        ys = nvec[0][1:]
                        q = nvec[1]
                        if x-tr > border_at(self.pmat, ys):
                            over = True
                        if new_front.get(wrap(self.pmat, ((x-tr,)+ys,q)), c) != c:
                            # this forb can be discarded
                            break
                    else:
                        # forb was not discarded
                        if over:
                            # forb can still be handled later
                            new_pairs.append(pair)
                        else:
                            # forb can't be handled, reject state
                            break
                else:
                    # choose minimal state along rotations
                    if self.rotate:
                        min_state = math.inf
                        for rots in hyperrectangle(heights):
                            new_state = 0
                            for (forb, tr) in new_pairs:
                                ix = self.border_forbs.index({((nvec[0][0],) + vrot(nvec[0][1:], rots, heights), nvec[1]):c for (nvec, c) in forb.items()})
                                new_state += 2**(numf*tr + ix)
                            min_state = min(min_state, new_state)
                        new_state = min_state
                    else:
                        new_state = 0
                        for (forb, tr) in new_pairs:
                            ix = self.border_forbs.index(forb)
                            new_state += 2**(numf*tr + ix)
                    # note: new_state may be in a different component
                    if new_state in self.s2idict and self.s2idict[new_state] == bix:
                        labels.append(new_front)
                        try:
                            i = states.index(new_state)
                            return labels[i:]
                        except:
                            states.append(new_state)
                            break
            else:
                print(a,self.s2idict[a],bix,self.trans)
                raise Exception("bad cycle, no transition")
            s += 1


    def compute_i2sdict(self):
        self.i2sdict = {}
        for k in self.s2idict:
            self.i2sdict[self.s2idict[k]] = k
        
    def border_at(self, vec):
        return border_at(self.pmat, vec)
        
    def accepts(self, w_path, repetitions=True):
        cur = init = set(self.trans)
        r = 1
        while True:
            for (i, w) in enumerate(w_path):
                nexts = set(st for cst in cur for (st, tr_w) in self.trans[cst].items() if tr_w <= w)
                if nexts:
                    cur = nexts
                else:
                    return (False, (cur, w, i, r, [self.trans[cst] for cst in cur]))
            if (not repetitions) or cur == init:
                break
            r += 1
            init = cur
        return (True, r)

    def strong_components(self):
        "Tarjan's algorithm, implicit recursion"
        self.compute_i2sdict()
        #print("trans", self.trans)
        #print("states", self.states)
        #print("i2s", self.i2sdict)
        #print("s2i", self.s2idict)
        comps = []
        lows = {}
        stack = []
        for p in self.trans:
            if p not in lows:
                callstack = [(p,0,list(self.trans[p]),len(lows))]
                while callstack:
                    cur, ix, nxts, num = callstack.pop()
                    if ix == 0:
                        if cur in lows:
                            continue
                        lows[cur] = num
                        stack.append(cur)
                        nxts = list(self.trans[cur])
                    else:
                        lows[cur] = min(lows[cur], lows[nxts[ix-1]])
                    if ix < len(nxts):
                        callstack.append((cur, ix+1, nxts, num))
                        callstack.append((nxts[ix], 0, list(self.trans[nxts[ix]]), len(lows)))
                        continue
                    if num == lows[cur]:
                        comp = set()
                        while True:
                            nxt = stack.pop()
                            lows[nxt] = len(self.trans)
                            comp.add(nxt)
                            if nxt == cur:
                                break
                        if len(comp) > 1 or cur in self.trans.get(cur, []):
                            aut = PeriodAutomaton(self.sft, self.pmat, self.rotate, self.sym_bound, False, self.immediately_relabel, check_periods=False, weights=self.weights)
                            aut.weight_numerators = self.weight_numerators
                            aut.weight_denominator = self.weight_denominator

                            #idict = {ix:i for (i,ix) in
                            #         enumerate(ix for ix in set(self.s2idict.values()) if ix in comp)}
                            idict = {ix:i for (i,ix) in enumerate(comp)}
                            aut.s2idict = {st:idict[ix] for (st, ix) in self.s2idict.items() if ix in comp}
                            aut.i2sdict = {ix:st for (st,ix) in aut.s2idict.items()}
                            aut.states = set(aut.s2idict)
                            aut.trans = {idict[st] : {idict[st2] : c
                                                      for (st2, c) in self.trans[st].items()
                                                      if st2 in comp}
                                         for st in comp}

                            #print("old s2idict",self.s2idict)
                            #print("idict",idict)
                            #print("states",aut.states)
                            #print("s2idict",aut.s2idict)
                            #print("trans",aut.trans)
                            yield aut



def border_at(pmat, vec):
    if len(pmat) == 1:
        i, j = pmat[0]
        return (vec[0]*i)//j
    return 0 # TODO: change

def populate_worker(pmat, alph, border_forbs, frontier, sym_bound,
                    rotate, task_queue, res_queue, weights, chunk_size):
    #print("populating", border_forbs)
    numf = len(border_forbs)
    #border_sets = [set(forb) for forb in border_forbs]
    if rotate:
        heights = [pmat[i][i+1] for i in range(len(pmat))]
    while True:
        states = task_queue.get()
        ret = []
        for state in states:
            # state is a number encoding a set of shifted forbs
            shifted = [(f,0) for f in border_forbs]
            i = 0
            n = state
            while n:
                if n%2:
                    ix = i%numf
                    tr = i//numf
                    shifted.append((border_forbs[ix], tr+1))
                n = n//2
                i += 1
            #print(shifted)
            pat_forbs = set()
            for (forb, tr) in shifted:
                pat_forb = dict()
                for (nvec, c) in forb.items():
                    #print(nvec, c)
                    #print(frontier)
                    if nvec[0][0]-tr > border_at(pmat, nvec[0][1:]):
                        break
                    tr_nvec = ((nvec[0][0]-tr,) + nvec[0][1:]), nvec[1]
                    if tr_nvec in frontier:
                        pat_forb[tr_nvec] = c
                else:
                    pat_forbs.add(fd.frozendict(pat_forb))
            #print("pfff", pat_forbs)
            for new_front in pats(frontier, alph, pat_forbs):
                new_pairs = []
                sym_pairs = dict()
                for pair in shifted:
                    forb, tr = pair
                    over = False
                    for (nvec, c) in forb.items():
                        x = nvec[0][0]
                        ys = nvec[0][1:]
                        q = nvec[1]
                        if x-tr > border_at(pmat, ys):
                            over = True
                        #print("did", x-tr, ys, q, (x-tr,)+ys+(q,))
                        if new_front.get(wrap(pmat, ((x-tr,)+ys,q,)), c) != c:
                            # this forb can be discarded
                            break
                    else:
                        # forb was not discarded
                        if over:
                            # forb can still be handled later
                            new_pairs.append(pair)
                        else:
                            # forb can't be handled, reject state
                            break
                else:
                    # choose minimal state along rotations
                    # NB. the period matrix is assumed diagonal
                    if rotate:
                        min_state = math.inf
                        for rots in hyperrectangle(heights):
                            new_state = 0
                            for (forb, tr) in new_pairs:
                                ix = border_forbs.index({((nvec[0][0],) + vrot(nvec[0][1:], rots, heights), nvec[1]) : c for (nvec, c) in forb.items()})
                                # symmetry only available along first non-horizontal coordinate
                                if sym_bound is not None:
                                    sym_pairs[ix%(numf//2), tr] = 1 - sym_pairs.get((ix%(numf//2), tr), 0)
                                new_state += 2**(numf*tr + ix)
                            min_state = min(min_state, new_state)
                        new_state = min_state
                    else:
                        new_state = 0
                        for (forb, tr) in new_pairs:
                            ix = border_forbs.index(forb)
                            if sym_bound is not None:
                                sym_pairs[ix%(numf//2), tr] = 1 - sym_pairs.get((ix%(numf//2), tr), 0)
                            new_state += 2**(numf*tr + ix)
                    if sym_bound is None or sum(sym_pairs.values()) <= sym_bound:
                        ret.append((state, weighted_sum(weights, new_front.values()), new_state))
                        if len(ret) >= chunk_size:
                            res_queue.put(ret)
                            ret = []
                    
        if ret != []:
            res_queue.put(ret)
        res_queue.put(len(states))

def weighted_sum(weights, summed):
    if weights == None:
        return sum(summed)
    summa = 0
    for s in summed:
        summa += weights[s]
    return summa

def square_min_worker(the_mins, the_opt_prevs, n, m, max_w, trans, task_q, res_q):
    # share array
    global mins, opt_prevs
    mins = the_mins
    opt_prevs = the_opt_prevs
    # fill part of the distance array one layer at a time
    while True:
        k = task_q.get()
        for (p, qs) in trans.items():
            new_min, opt_prev = min((mins[n*(k-1)+q]+w, q) for (q, w) in qs.items())
            mins[n*k+p] = new_min
            opt_prevs[n*k+p] = opt_prev
        res_q.put(None)
        if k == m:
            break
    # compute minimum for assigned states
    dummy = task_q.get()
    assert dummy is None
    the_min = math.inf
    min_val = math.inf
    min_state = 0
    for p in trans:
        the_max = 0
        max_val = math.inf
        for k in range(1,m):
            num = (mins[m*n+p]-mins[k*n+p])/(m-k)
            if (num > the_max) or (num == the_max and m-k < max_val):
                the_max = num
                max_val = m-k
        if (the_max < the_min) or (the_max == the_min and max_val < min_val):
            the_min = the_max
            min_val = max_val
            min_state = p
    res_q.put((the_min, min_val, min_state))

def linsqrt_min_worker(the_dense_mins, the_sparse_mins, the_opt_prevs, n, m, max_w, sparse_rows, trans, task_q, res_q):
    # share arrays
    global dense_mins, sparse_mins, opt_prevs
    dense_mins = the_dense_mins
    sparse_mins = the_sparse_mins
    opt_prevs = the_opt_prevs
    
    # compute sparse distance array
    # expect to receive k,j, where k=0,1,...,n; send None after each
    while True:
        k = task_q.get()
        if k is None:
            break
        cur = n*(k%2)
        pre = n*((k-1)%2)
        if k > 0:
            for (p, qs) in trans.items():
                new_min = min(dense_mins[pre+q]+w for (q,w) in qs.items())
                dense_mins[cur+p] = min(max_w, new_min)
        try:
            i = sparse_rows.index(k)
            for p in trans:
                sparse_mins[n*i+p] = dense_mins[cur+p]
        except ValueError:
            pass
        res_q.put(None)
        if k == m:
            break
    
    # recompute previous layers, simultaneously compute minimum for assigned states
    # expect to receive 1, ..., n, send None after each
    # finally receive None
    maxes = {p : (-1, math.inf) for p in trans}
    while True:
        k = task_q.get()
        if k is None:
            break
        cur = n*(k%2)
        pre = n*((k-1)%2)
        for (p, qs) in trans.items():
            new_min = min(dense_mins[pre+q]+w for (q,w) in qs.items())
            dense_mins[cur+p] = min(max_w, new_min)
            the_max, max_val = maxes[p]
            num = (sparse_mins[n*(len(sparse_rows)-1)+p]-dense_mins[cur+p])/(m-k)
            if (num > the_max) or (num == the_max and m-k < max_val):
                maxes[p] = (num, m-k)
        res_q.put(None)
        
    the_min = math.inf
    min_val = math.inf
    min_state = 0
    for (p, (the_max, max_val)) in maxes.items():
        if (the_max < the_min) or (the_max == the_min and max_val < min_val):
            the_min = the_max
            min_val = max_val
            min_state = p
    res_q.put((the_min, min_val, min_state))

    # recompute each gap in reverse order, also computing optimal predecessors
    # expect to receive tuples (k, k==low), send None after each
    # finally receive None
    
    while True:
        task = task_q.get()
        if task is None:
            break
        lo, k = task
        if lo == k:
            i = sparse_rows.index(k)
            for q in trans:
                dense_mins[q] = sparse_mins[n*i+q]
        else:
            k2 = k-lo
            for (p, qs) in trans.items():
                min_w, min_q = min((dense_mins[n*(k2-1)+q]+w, q) for (q, w) in qs.items())
                dense_mins[n*k2+p] = min_w
                opt_prevs[n*k2+p] = min_q
        res_q.put(None)

def linear_min_worker(the_mins, n, m, max_w, trans, task_q, res_q):
    # share array
    global mins
    mins = the_mins
    # compute the last layer of distance array
    # expect to receive 1, ..., n, send None after each
    while True:
        k = task_q.get()
        if k < m:
            cur = n*(k%2)
            pre = n*((k-1)%2)
        elif k == m:
            cur = n*2
            pre = n*((k-1)%2)
        for (p, qs) in trans.items():
            new_min = min(mins[pre+q]+w for (q,w) in qs.items())
            mins[cur+p] = min(max_w, new_min)
        res_q.put(None)
        if k == m:
            break
    # recompute previous layers, simultaneously compute minimum for assigned states
    # expect to receive 1, ..., n-1, send None after each, then receive None and send result
    maxes = {p : (-1, math.inf) for p in trans}
    while True:
        k = task_q.get()
        if k is None:
            break
        cur = n*(k%2)
        pre = n*((k-1)%2)
        for (p, qs) in trans.items():
            new_min = min(mins[pre+q]+w for (q,w) in qs.items())
            mins[cur+p] = min(max_w, new_min)
            the_max, max_val = maxes[p]
            num = (mins[2*n+p]-mins[cur+p])/(m-k)
            if (num > the_max) or (num == the_max and m-k < max_val):
                maxes[p] = (num, m-k)
        res_q.put(None)
    the_min = math.inf
    min_val = math.inf
    min_state = 0
    for (p, (the_max, max_val)) in maxes.items():
        if (the_max < the_min) or (the_max == the_min and max_val < min_val):
            the_min = the_max
            min_val = max_val
            min_state = p
    res_q.put((the_min, min_val, min_state, maxes))


def prints(x,y):
    print(x, y)
    return(y)

def kek(f):
    return str(f)+"~"+("%.3f"%float(f))
    
if __name__ == "__main__":
    #for vec in hyperrectangle([2]):
    #    print(vec)
    #quit()

    starttime = time.time()
    
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("height", metavar='h', type=int)
    arg_parser.add_argument("shear", metavar='s', type=int)
    arg_parser.add_argument("mode", metavar='m', type=str, choices=['L','S','Q'])
    arg_parser.add_argument("--symbreak", '-S', type=int, required=False)
    arg_parser.add_argument("--karpbound", '-K', type=int, required=False)
    arg_parser.add_argument("--rotate", '-R', action="store_true", required=False)
    arg_parser.add_argument("--infile", '-i', type=str, required=False)
    arg_parser.add_argument("--outfile", '-o', type=str, required=False)
    arg_parser.add_argument("--autosave", '-a', action="store_true", required=False)
    arg_parser.add_argument("--reportpop", '-r1', type=int, required=False, default=5000)
    arg_parser.add_argument("--reportcyc", '-r2', type=int, required=False, default=50)
    arg_parser.add_argument("--threads", '-t', type=int, required=False, default=1)
    arg_parser.add_argument("--chunksize", '-c', type=int, required=False, default=200)
    args = arg_parser.parse_args()
    
    h = args.height
    s = args.shear
    bound_len = args.karpbound
    sym_b = args.symbreak
    rotate = args.rotate
    infile = args.infile
    reportcyc = args.reportcyc
    reportpop = args.reportpop
    if sym_b is not None and h%2:
        print("for symmetry breaking, height must be even")
        quit()
    if rotate and s:
        print("for rotation symmetry, shear must be 0")
        quit()
    if sym_b is not None and rotate:
        print("warning: symmetry breaking may be incompatible with rotation")
    if args.mode == "L":
        COMP_MODE = CompMode.LINEAR_NOCYCLE
    elif args.mode == "S":
        COMP_MODE = CompMode.LINSQRT_CYCLE
    elif args.mode == "Q":
        COMP_MODE = CompMode.SQUARE_CYCLE
    if rotate and COMP_MODE != CompMode.LINEAR_NOCYCLE:
        print("warning: rotation produces a cycle with each label independently rotated/reflected")
    print("threads", args.threads, "chunk size", args.chunksize)
    print("using height %s shear %s mode %s symmetry-breaking %s Karp bound %s rotation symmetry %s" % (h, s, COMP_MODE, sym_b, bound_len, rotate))
    
    if infile is None:
        # Define identifying codes on the hexagonal grid as in SFT
        # Vertices of hex grid are either (x,y,0) or (x,y,1).
        # The graph looks like this.
        # We don't actually use the graph structure since
        # we define the forbidden patterns of identifying codes by hand.
        #
        # (0,2,0)--(0,2,1)--(1,2,0)--(1,2,1)--(2,2,0)--(2,2,1)
        #      \                 \                 \
        #       `-.               `-.               `-.
        #          \                 \                 \
        # (0,1,0)--(0,1,1)--(1,1,0)--(1,1,1)--(2,1,0)--(2,1,1)
        #       \                 \                \
        #        `-.               `-.              `-.
        #           \                 \                \
        # (0,0,0)--(0,0,1)--(1,0,0)--(1,0,1)--(2,0,0)--(2,0,1)
        #       \                \                 \
        #        `-.              `-.               `-.
        #           \                \                 \
        # (0,-1,0)-(0,-1,1)-(1,-1,0)-(1,-1,1)-(2,-1,0)-(2,-1,1)

        
        # Nodes modulo translations
        nodes = [0,1]
        # Alphabet of identifying codes
        alph = [0,1]
        # Forbidden patterns of identifying codes
        forbs = []
        # neighborhoods centered at (x,y,0) or (x,y,1)
        forbs.append({(0,0,0):0,(0,0,1):0,(-1,0,1):0,(0,-1,1):0})
        forbs.append({(0,0,1):0,(0,0,0):0,(1,0,0):0,(0,1,0):0})
        # confused horizontal neighbors
        forbs.append({(-1,0,1):0,(0,-1,1):0,(0,1,0):0,(1,0,0):0})
        forbs.append({(0,0,0):0,(0,1,0):0,(1,-1,1):0,(1,0,1):0})
        # confused vertical neighbors
        forbs.append({(0,0,0):0,(1,0,0):0,(-1,1,1):0,(0,1,1):0})
        # confused distance-1 at angle
        forbs.append({(0,0,0):0,(-1,0,1):0,(0,-1,1):0,(0,1,0):0,(-1,1,1):0,(0,1,1):0})
        forbs.append({(0,0,0):0,(-1,0,1):0,(0,0,1):0,(1,-1,0):0,(1,-1,1):0,(1,-2,1):0})
        forbs.append({(0,0,1):0,(0,0,0):0,(1,0,0):0,(0,1,1):0,(0,2,0):0,(1,1,0):0})
        forbs.append({(0,0,1):0,(0,0,0):0,(0,1,0):0,(1,-1,1):0,(1,-1,0):0,(2,-1,0):0})
        # confused straight distance-1
        forbs.append({(0,0,0):0,(-1,0,1):0,(0,-1,1):0,(1,0,0):0,(1,0,1):0,(1,-1,1):0})
        forbs.append({(0,0,1):0,(0,0,0):0,(0,1,0):0,(1,0,1):0,(2,0,0):0,(1,1,0):0})
        
        hex_iden_sft = SFT(2, nodes, alph, forbs)
        print("using", hex_iden_sft)
                     
        nfa = PeriodAutomaton(hex_iden_sft,[(s,h)],sym_bound=sym_b,verbose=True,immediately_relabel=True,rotate=rotate, all_labels=True)
        nfa.populate(verbose=True, report=reportpop, num_threads=args.threads, chunk_size=args.chunksize)
        print("time taken after pop:", time.time()-starttime, "seconds")
        nfa.relabel()
        nfa.minimize(verbose=True)
        print("done with #states", len(nfa.trans))
        print("time taken after minimization:", time.time()-starttime, "seconds")
        if PRINT_NFA:
            print(nfa.trans)
        if args.outfile is not None or args.autosave:
            if args.autosave:
                savename = "grid-aut-%s-%s-%s-%s.pickle"%(h,s,sym_b,rotate)
            else:
                savename = args.outfile
            with open(savename, 'wb') as f:
                print("saving automaton to", savename)
                pickle.dump(nfa, f)
    else:
        print("loading automaton from", infile)
        with open(infile, 'rb') as f:
            nfa = pickle.load(f)

    comps = list(nfa.strong_components())
    del nfa
    #print("#components", len(comps))
    min_data = (math.inf,)
    min_comp = None
    for (ic, comp) in enumerate(comps):
        # TODO: special case components that are cycles
        print("analyzing connected component", ic+1, "/", len(comps), "with", len(comp.trans), "states")
        if COMP_MODE == CompMode.SQUARE_CYCLE:
            data = comp.square_min_density_cycle(bound_len=bound_len, verbose=True, report=reportcyc, num_threads=args.threads)
        elif COMP_MODE == CompMode.LINSQRT_CYCLE:        
            data = comp.linsqrt_min_density_cycle(bound_len=bound_len, verbose=True, report=reportcyc, num_threads=args.threads)
        elif COMP_MODE == CompMode.LINEAR_NOCYCLE:
            data = comp.linear_min_density_cycle(bound_len=bound_len, verbose=True, report=reportcyc, num_threads=args.threads)
        if data[:1] < min_data[:1]:
            min_data = data
            min_aut = comp
    print("height %s, shear %s, bound %s, symmetry %s, rotation %s completed" % (h, s, bound_len, sym_b, rotate))
    #print(dens,minlen,stcyc,cyc)
    if bound_len is not None and all(len(comp.trans) for comp in comps) <= bound_len:
        print("bound was not needed")

    denom = len(min_aut.frontier)*len(min_aut.sft.nodes)
    #print(denom, min_data)
    # the known bounds are for identifying codes on the infinite hexagonal grid
    if COMP_MODE == CompMode.LINEAR_NOCYCLE:
        dens, minlen, minst = min_data
        print("density", dens/denom, "known bounds", 23/55, 53/126)
    else:
        dens, minlen, stcyc, cyc = min_data
        print("density", fractions.Fraction(sum(b for fr in cyc for b in fr.values()), denom*len(cyc)), "~", dens/denom, "known bounds", 23/55, 53/126)
    print("cycle length", minlen, "in minimized automaton" if COMP_MODE == CompMode.LINEAR_NOCYCLE else "")
    if COMP_MODE != CompMode.LINEAR_NOCYCLE and PRINT_CYCLE:
        print("cycle:")
        print([tuple(sorted(pat.items())) for pat in cyc])
        cyc_w = [sum(x.values()) for x in cyc]
        # sanity check: cycle is accepted by nfa
        res, reason = min_aut.accepts(cyc_w, repetitions=True)
        if res:
            print("cycle^n accepted for all n,", reason, "was enough")
        else:
            st, front, ix, n, tr = reason
            print("cycle ^", n, "not accepted due to state", st, "with label", front, "at position", ix)
            print("available transitions:", tr)
            print("(this is bad)")
    print("total time taken:", time.time()-starttime, "seconds")
