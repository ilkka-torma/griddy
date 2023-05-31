import diddy
from circuit import *

d = diddy.Diddy()

k = 3
n = 4

def dgeq(cxt, a, b, distbound):
    nodes, dim, topology, alphabet, formula, variables, aux_var, all_vars = cxt
    apos = variables[a]
    bpos = variables[b]
    # we explicitly list all pairs and make circuits manually
    alphabet = alphabet[0]
    circ = F
    for x in alphabet:
        for y in alphabet:
            if type(x) !=int or type(y) != int or abs(x - y) >= distbound:
                #print(apos, x, bpos, y)
                circ = OR(circ, AND(V(apos + (x,)), V(bpos + (y,))))
    return circ

# for 0...7 got up to 157
d.add_external("dgeq", dgeq)
d.run("""
%alphabet 0 1 2 3 4 5 6 e -- n lett34s
%topology line
%SFT all_e Ao o=e
--%SFT fullshift Ao 0=0

%SFT radio Ao Ap[o3]
  (o ~^1 p -> dgeq o p 3) &
  (o ~^2 p -> dgeq o p 2) &
  (o ~^3 p -> dgeq o p 1) &
  (o = e -> o.lt = e & o.rt = e)

%equal radio all_e
""")
# d.run("%tiler radio")


"""
--%SFT radio Ao Ap[o3]
--  (o ~^1 p -> dgeq o p 3) &
--  (o ~^2 p -> dgeq o p 2) &
--  (o ~^3 p -> dgeq o p 1)
"""



