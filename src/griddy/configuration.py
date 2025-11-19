from general import *

# Markers are used to structure recognizable configurations
# Markers for a single axis can be given as
# a) None (equivalent to (min-1,min,max+1,max+2) with padded nonexisting nodes)
# b) integer n (equivalent to (0,0,n,n))
# c) pair (a,b) (equivalent to (a,a,b,b))
# d) triple (a,b,c) (equivalent to (a,b,b,c)
# e) quadruple (a,b,c,d)
# Each quadruple (a,b,c,d) gives the positions of eventual periodicity markers on its axis
# a=b & c=d means we are periodic
# b=c means we are concatenation of periodic tails

def normalize_markers(i, markers, domain=None):
    "Normalize a marker specification into a quadruple"
    #print("normalizing", i, markers)
    if markers is None: # Here domain should not be None
        minpos = min(nvec[i] for nvec in domain)
        maxpos = max(nvec[i] for nvec in domain)
        return (minpos-1, minpos, maxpos+1, maxpos+2)
    elif type(markers) == int:
        return (0,0, markers,markers)
    elif len(markers) == 2:
        a, b = markers
        return (a,a, b,b)
    elif len(markers) == 3:
        a, b, c = markers
        return (a, b,b, c)
    elif len(markers) == 4:
        return markers
    else:
        raise Exception("Bad marker specification: {}".format(axis))
        
def gen_markers_from_minimal(markers, periodic=None, inits=None):
    """
    Generate quadruples of markers that are in principle compatible with the given ones (and possibly periodic).
    The input markers are assumed to be minimized.
    """
    a, b, c, d = markers
    if periodic:
        #print("AM HERE")
        if (a != b) or (c != d):
            # incompatible with periodic
            #print("Incomparable with periodic.")
            return
        if inits is None:
            inits = 5
        k = inits
        while True:
            yield (a, a, a+k*(c-a), a+k*(c-a))
            k += 1
    else:
        #print("AM OTHER")
        if a==b:
            a = a-(c-b)
        if c==d:
            d = d+(c-b)
        if inits is None:
            inits = (5,0,0,5)
        k1, k2, k3, k4 = inits
        left_period = ((k+k1+1)*(b-a) for k in naturals())
        left_border = (b-k-k2 for k in naturals())
        right_border = (c+k+k3 for k in naturals())
        right_period = ((k+k4+1)*(d-c) for k in naturals())
        for (p1, b1, b2, p2) in iter_prod(left_period, left_border, right_border, right_period):
            #print("generated markers", (b1-p1, b1, b2, b2+p2), "from", markers)
            candidate = (b1-p1, b1, b2, b2+p2)
            if candidate[0] == candidate[1] == candidate[2] == candidate[3]:
                continue
            yield candidate
    
    

class Conf:
    """
    A configuration of some full shift,
    possibly with missing and/or indeterminate values.
    A missing value (i.e. node where the local rule is not checked) is modeled as None.
    An indeterminate value is modeled as a list of possible values.
    """

    def __init__(self, onesided=None):
        if onesided is None:
            onesided = []
        self.onesided = onesided

    def __getitem__(self, nvec):
        raise Exception("Base configuration class has no methods")
        
    def __contains__(self, nvec):
        raise Exception("Base configuration class has no methods")

    def display_str(self):
        return "An abstract configuration"

class RecognizableConf(Conf):
    "A recognizable configuration"

    def __init__(self, markers, pat, nodes, onesided=None, dim=None):
        super().__init__(onesided)
        # markers is a list of (possibly not normalized) markers
        # pat is a dict from nvecs to symbols
        # it will be wrapped around the markers
        if dim is None:
            if type(markers) == list:
                dim = len(markers)
            elif pat:
                dim = len(min(pat)) - 1
            else:
                raise Exception("Cannot deduce dimension for configuration")
            
        self.dim = dim
        
        self.nodes = nodes
        
        #print("got markers", markers)
        if type(markers) == tuple and type(markers[0]) == tuple:
            raise Exception("bad marker tuple")
        if type(markers) != list:
            markers = [markers]*dim
        #print("markers are now", markers)
        self.markers = [normalize_markers(i, marker, domain=set(pat))
                        for (i, marker) in enumerate(markers)]
                        
        #print("normalized markers to", self.markers)
        
        self.pat = {(vec, node) : None
                    for vec in hyperrect([(a,d) for (a,_,_,d) in self.markers])
                    for node in nodes}
        
        for (nvec, sym) in pat.items():
            self.pat[nvwraps(self.markers, nvec)] = sym

    def __getitem__(self, nvec):
        #print("getting", nvec, "from", self.pat, "markers", self.markers)
        try:
            return self.pat[nvwraps(self.markers, nvec)]
        except KeyError:
            print("getting", nvec, "wrapped to", nvwraps(self.markers, nvec), "from", self.pat, "markers", self.markers)
            raise Exception()
        
    def can_be_equal_at(self, *nvecs):
        "Check if values are equal in these nodes; nonexistent nodes are equal."
        #print("equal at", nvecs)
        if not nvecs:
            return True
        return all(self[nvec] == self[nvecs[0]] for nvec in nvecs[1:])
        
    def minimized_markers(self, fixed_axes=None):
        "Move the markers as close to each other as possible and return them."
        # more specifically, first minimize periods of both periodic tails, then rewind right and left tail
        # TODO: handle all special cases
        if fixed_axes is None:
            fixed_axes = []
        markers = self.markers[:]
        #print("pattern", self.pat)
        for (i, (a, b, c, d)) in enumerate(markers):
            #print("minimizing marker", (a,b,c,d), "on axis", i)
            if i in fixed_axes:
                continue
            # if we are periodic, minimize period
            if a==b and c==d:
                p = min(p for p in range(1, c-a+1)
                        if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (p,) + (0,)*(self.dim-i-1)))
                               for nvec in self.pat))
                markers[i] = (a,a, a+p,a+p)
                continue
            # minimize left periodic tail
            for p in range(1, b-a):
                if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (-p,) + (0,)*(self.dim-i-1)))
                       for nvec in self.pat
                       if nvec[i] < b):
                    markers[i] = (b-p, b, c, d)
                    break
            (a, b, c, d) = markers[i]
            #print(1, i, markers[i])
            # minimize right periodic tail
            for p in range(1, d-c):
                if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (p,) + (0,)*(self.dim-i-1)))
                       for nvec in self.pat
                       if nvec[i] >= c):
                    markers[i] = (a, b, c, c+p)
                    break
            (a, b, c, d) = markers[i]
            #print(2, i, markers[i])
            # check if everything is periodic
            if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (b-a,) + (0,)*(self.dim-i-1)), nvadd(nvec, (0,)*i + (a-b,) + (0,)*(self.dim-i-1)))
                       for nvec in self.pat):
                markers[i] = (a, a, b, b)
                # 
                #print(3, i, markers[i])
                continue
            # rewind right tail
            t = min(t for t in range(b+1, c+1)
                    if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (d-c,) + (0,)*(self.dim-i-1)))
                           for nvec in self.pat
                           if nvec[i] >= t))
            #print("right tail", b+1, c+1, t)
            #print(self.pat)
            # rewind left tail
            s = max(s for s in range(a, b+1)
                    if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (a-b,) + (0,)*(self.dim-i-1)))
                           for nvec in self.pat
                           if nvec[i] < s))
            #print("left tail", a, b+1, s)
            markers[i] = (s-b+a, s, t, t+d-c)
            #print(4, i, markers[i])
        #print("minimized to", markers)
        return markers
        
    def compatible(self, axis, new_markers):
        "Is this configuration compatible with the given marker structure?"
        a, b, c, d = new_markers
        amin, bmin, cmin, dmin = self.minimized_markers()[axis]
        if a==b and c==d:
            # new markers are periodic -> old ones should be periodic and consistent
            return amin == bmin and cmin == dmin and (c-a) % (cmin-amin) == 0
        elif amin == bmin and cmin == dmin:
            # new markers are not periodic, old ones are -> tail periods must be consistent
            return (b-a) % (cmin-amin) == (d-c) % (cmin-amin) == 0
        else:
            # neither markers are periodic -> tail periods are consistent, transient part is contained
            return (b-a) % (bmin-amin) == (d-c) % (dmin-cmin) == 0 and b <= bmin and c >= cmin
        
    def remark(self, new_markers):
        """
        Produce a restructured configuration using the new marker structure.
        The markers are assumed to be compatible.
        """
        
        nodes = set(nvec[-1] for nvec in self.pat)
        
        new_pat = dict()
        for vec in hyperrect([(a,d) for (a,_,_,d) in new_markers]):
            for node in nodes:
                nvec = vec + (node,)
                new_pat[nvec] = self[nvec]
        
        return RecognizableConf(new_markers, new_pat, nodes, onesided=self.onesided)
        
    def is_periodic(self, axis):
        "Is this configuration periodic along the given axis?"
        a, b, c, d = self.minimized_markers()[axis]
        return a==b and c==d

    def display_str(self, hide_contents=False):
        s = "recognizable configuration with markers {}".format(self.markers)
        if not hide_contents:
            s += ":\n{" + ", ".join(["{}: {}".format(nvec, '_' if sym is None else sym) for (nvec, sym) in sorted(self.pat.items())]) + "}"
        return s

    def info_string(self, name, verbose=False):
        s = ["{}-dimensional recognizable configuration {}".format(self.dim, name)]
        s.append("Nodes: {}".format(list(self.nodes)))
        s.append("Markers: {}".format(self.markers))
        s.append("Onesided along axes {}".format(self.onesided))
        if verbose:
            s.append("Contents: {" + ", ".join(["{}: {}".format(nvec, '_' if sym is None else sym) for (nvec, sym) in sorted(self.pat.items())]) + "}")
        return "\n".join(s)
