# A super slow Game of Life implementation with explicit enumeration of cases.
import os.path
import sys
sys.path.append(os.path.abspath(os.path.join(__file__, os.pardir, os.pardir, "src", "griddy")))
import griddy
d = griddy.Griddy()
d.run("""
%topology king
%CA gol
1 Ao let threeE x := Ea[x:1] Eb[x:1] Ec[x:1] a!@b!@c!@a & a=b=c=1 & Ad[x:1] d = 1 -> ((d@a) | (d@b) | (d@c)) in
let fourE x := Ea[x:1] Eb[x:1] Ec[x:1] Ed[x:1] a!@b!@c!@d!@a!@c & b!@d & a=b=c=d=1 & Ae[x:1] e = 1 -> (e@a | e@b | e@c | e@d) in
(o = 1 & fourE o) | threeE o
-- %spacetime_diagram golst gol
%SFT @verbose zero Ao o=0
%preimage zeropre gol zero
%tiler x_size=5 y_size=5 zeropre
""")


#d.run("""
#%topology king
#%CA xx
#0 1 Ao o@o
#%spacetime_diagram xx
#""")
