
class GriddyRuntimeError(Exception):
    pass

class GriddyCompileError(Exception):
    pass

def vadd(vec1, vec2):
    return tuple(a+b for (a,b) in zip(vec1, vec2))

def vsub(vec1, vec2):
    return tuple(a-b for (a,b) in zip(vec1, vec2))

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
    for v in onesided_hypercube(dim-1, rad):
        for a in range(0, rad):
            yield v + (a,)

def hyperrect(bounds):
    if bounds:
        xmin, xmax = bounds[0]
        for vec in hyperrect(bounds[1:]):
            for a in range(xmin, xmax):
                yield (a,) + vec
    else:
        yield ()

def vmod(m, vec):
    return tuple(a%m for a in vec)

def nvmod(m, nvec):
    return tuple(a%m for a in nvec[:-1]) + nvec[-1:]
    
def nvmods(mods, nvec):
    return tuple(a if m is None else a%m for (m,a) in zip(mods, nvec[:-1])) + nvec[-1:]
    
def nvwraps(markers, nvec):
    "Wrap a nodevector around recognizability markers"
    #print("wrapping", nvec, "around", markers)
    ret = []
    for ((a,b,c,d), x) in zip(markers, nvec[0]):
        if b <= x:
            if x < c:
                ret.append(x)
            elif c < d:
                ret.append(c + (x-c) % (d-c))
            else: # periodic right tail
                ret.append(b + (x-b) % (c-b))
        elif a < b:
            ret.append(a + (x-a) % (b-a))
        else: # periodic left tail
            ret.append(b + (x-b) % (c-b))
    #ret.append(nvec[-1])
    #print("nvwraps", markers, nvec, tuple(ret))
    return tuple(ret), nvec[1]

def vneg(vec):
    return tuple(-a for a in vec)

# in these modern times (Nov 2025), positions are (cell,node)
def nvadd(nvec, vec):
    return (tuple(a+b for (a,b) in zip(nvec[0], vec)), nvec[1])

def nvsub(nvec, vec):
    return (tuple(a-b for (a,b) in zip(nvec[0], vec)), nvec[1])

def nvmul(nvec, scalar):
    return (tuple(a*scalar for a in nvec[0]), nvec[1])

def pats(domain, alph):
    if not domain:
        yield dict()
    else:
        vec = domain.pop()
        for pat in pats(domain, alph):
            for c in alph[:-1]:
                pat2 = pat.copy()
                pat2[vec] = c
                yield pat2
            pat[vec] = alph[-1]
            yield pat
        domain.add(vec)
        
def cart_prod_ix(ix_sum, *lists):
    "Cartesian product with fixed (1-based) index sum"
    #print("cart", ix_sum, lists)
    if not (ix_sum or lists):
        yield ()
    elif sum(len(l) for l in lists) >= ix_sum:
        head, tail = lists[0], lists[1:]
        #print("head", head, "tail", tail)
        for i in range(1, min(len(head)+1, ix_sum+1)):
            item = head[i-1]
            #print("head", item, i)
            for rest in cart_prod_ix(ix_sum-i, *tail):
                yield (item,) + rest
    
        
        
def iter_prod(*iters):
    "Lazy Cartesian product of iterators"
    memos = [[] for _ in iters]
    ix_sum = len(iters)
    while True:
        for (memo, iterator) in zip(memos, iters):
            try:
                memo.append(next(iterator))
            except StopIteration:
                pass
        #print("looping with", memos, ix_sum)
        if ix_sum > sum(len(memo) for memo in memos):
            break
        for tup in cart_prod_ix(ix_sum, *memos):
            #print("yielding", tup, "from", memos, "with sum", ix_sum)
            yield tup
        ix_sum += 1

def naturals():
    k = 0
    while True:
        yield k
        k += 1
        
def words(n, alph):
    if n:
        for word in words(n-1, alph):
            for sym in alph:
                yield word + (sym,)
    else:
        yield tuple()


