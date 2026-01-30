import os.path
import sys
sys.path.append(os.path.abspath(os.path.join(__file__, os.pardir, os.pardir, "src", "griddy")))
import griddy
import time
import circuit

print(griddy)

unit_tests = []
unit_tests2 = []

# whether we test the ones that take like 10 seconds
#long_ones_too = True <- currently nothing takes long



# just some basic checks
code_basic_comparisons = """
%SFT full_shift             Ao 0 = 0
%info @verbose full_shift
%SFT ver_golden_mean_shift  Ao o = 1 -> o.dn = 0
%info @verbose ver_golden_mean_shift
%SFT ver_golden_mean_shift2 Ao o.dn = 1 -> o = 0
%SFT hor_golden_mean_shift  Ao o = 1 -> o.rt = 0
%SFT golden_mean_shift      Ao o = 1 -> o.up = 0 & o.rt = 0
%SFT hor_golden_mean_shift2
(0,0):1 (1,0):1
%contains conf_name=c1 expect=F ver_golden_mean_shift hor_golden_mean_shift
%contains expect=T hor_golden_mean_shift c1
%contains expect=F ver_golden_mean_shift c1
%contains conf_name=c2 expect=F golden_mean_shift hor_golden_mean_shift
%contains expect=T hor_golden_mean_shift c2
%contains expect=F golden_mean_shift c2
%contains expect=T ver_golden_mean_shift golden_mean_shift
%contains conf_name=c3 expect=F ver_golden_mean_shift full_shift
%contains expect=T full_shift c3
%contains expect=F ver_golden_mean_shift c3
%contains expect=T full_shift hor_golden_mean_shift
%equal expect=T hor_golden_mean_shift2 hor_golden_mean_shift
%equal expect=T ver_golden_mean_shift ver_golden_mean_shift2
"""
unit_tests.append(("basic comparisons", code_basic_comparisons))




# crazy golden mean shift formula / forbs
code_crazy_gms = """
%SFT hor_golden_mean_shift  Ao (o.rt.rt = 1 -> o.rt = 0) & Ae[o:3] e.up = 0 | e.lt.up != e.rt.up.lt
%SFT hor_golden_mean_shift2
(0,0):1 (1,0):1 (0,3):0;
(0,0):1 (1,0):1 (0,3):1;
(0,0):1 (1,0):1 (2,2):0;
(0,0):1 (1,0):1 (2,2):1
%SFT hor_golden_mean_shift3 Ao (o.(2,0) = 1 -> o.(1,0) = 0) & Ae[o:3] e.(0,1) = 0 | e.(-1,1) != e.(0,1)
%show_formula hor_golden_mean_shift
%show_formula hor_golden_mean_shift2
%show_formula hor_golden_mean_shift3
%equal expect=T hor_golden_mean_shift2 hor_golden_mean_shift
%equal expect=T hor_golden_mean_shift3 hor_golden_mean_shift
"""
unit_tests.append(("crazy gms", code_crazy_gms))



# golden mean shift on hexagon grid
code_hex_gms = """
%topology hex
%SFT gms Ao Ae[o:1] o=0|e=0|o@e
%SFT gms2 Ao Ae[o:5] o~~e -> (o=0| e = 0)
%SFT broken_gms Ao Ae[o:1] o=0|e=0
%SFT broken_gms2 Ao Ae[o:5] o~e -> (o=0| e = 0)
--%SFT empty Ao 0=1
%SFT all_zero Ao o=0
%SFT fullshift Ao 0=0
%SFT byforbs
(0,0;0):1 (0,0;1):1;
(0,0;0):1 (-1,0;1):1;
(0,0;0):1 (0,1;1):1
-- %compare_SFT_pairs_equality
%equal expect=T gms gms2
%equal expect=F gms broken_gms2
%equal expect=T all_zero broken_gms2
%equal expect=T byforbs gms
"""
unit_tests.append(("hex gms", code_hex_gms))

# = ""
code_hex_idcodes = """ 
%topology hex
%SFT idcode Ao let c u v := v = 1 & u ~ v in
(Ed[o:1] c o d) & (Ap[o:2] p !@ o -> Eq[o:1+p:1] (c o q & ! c p q) | (c p q & !c o q))
%SFT idcode2
(0,0;1):0 (0,0;0):0 (1,0;0):0 (0,-1;0):0;
(0,0;1):0 (1,1;1):0 (2,0;0):0 (1,-1;0):0;
(0,0;1):0 (1,1;0):0 (1,0;1):0 (2,1;0):0;
(0,0;0):0 (0,0;1):0 (0,-1;0):0 (1,1;0):0 (1,1;1):0 (2,1;0):0;
(0,0;0):0 (0,0;1):0 (1,0;0):0 (0,-1;1):0 (1,-1;0):0 (0,-2;0):0;
(0,0;0):0 (0,0;1):0 (0,-1;0):0 (1,0;1):0 (2,0;0):0 (1,-1;0):0;
(0,0;1):0 (1,0;0):0 (1,0;1):0 (1,1;1):0;
(0,0;0):0 (0,-1;0):0 (1,0;1):0 (1,1;1):0;
(0,0;1):0 (1,0;0):0 (1,1;1):0 (0,-1;1):0 (1,-1;0):0 (1,-1;1):0;
(0,0;1):0 (1,0;0):0 (1,0;1):0 (2,1;0):0 (2,1;1):0 (2,2;1):0;
(0,0;1):0 (1,0;0):0 (1,1;1):0 (2,0;0):0 (2,0;1):0 (2,1;1):0
-- %compare_SFT_pairs
--%calculate_forbidden_patterns idcode idcode3 3
--%show_formula idcode2
--%show_formula idcode3
%equal expect=T idcode idcode2
"""
unit_tests.append(("hex idcodes", code_hex_idcodes))

code_basic = """
%alphabet 0 1
%SFT fullshift      Ao 0=0
%SFT fullshift2      Ao o=o
%SFT not_fullshift  Ao o=0
-- %compare_SFT_pairs
%calculate_forbidden_patterns not_fullshift nf 2
"""
# unit_tests.append(code_basic)

#testing one-dimensional XORs; first two are equal
code_basic_xors = """
%topology grid
%SFT test Ao let xor a b := (a & !b) | (!a & b) in
xor (xor (o=1) (o.up=1)) (xor (o.dn=1) (o.up.up=1))
%SFT test2 Ao let xor a b := (a & !b) | (!a & b) in
xor (xor (xor (o=1) (o.dn=1)) (o.up.up!=0)) (o.up=1)
%SFT test3 Ao let xor a b := (a & !b) | (!a & b) in
xor (xor (xor (o=1) (o.dn.up=1)) (o.up.up!=0)) (o.up=1)
%show_formula test2
-- %compare_SFT_pairs_equality
%equal expect=T test test2
%equal expect=F test test3
"""
unit_tests.append(("basic xors", code_basic_xors))

# ledrappier test
code_ledra = """
%topology grid
%SFT Ledrappier Ao let xor a b := (a & !b) | (!a & b) in
xor (xor (o=1) (o.up=1)) (o.rt=1)
%SFT LedrappierSquare Ao let xor a b := (a & !b) | (!a & b) in
xor (xor (o=1) (o.up.up=1)) (o.rt.rt=1)
--%compare_SFT_pairs
%contains expect=F Ledrappier LedrappierSquare
%contains expect=T LedrappierSquare Ledrappier
"""
unit_tests.append(("ledrappier", code_ledra))

code_trivial_WangTest = """
%nodes N E S W
%alphabet 0 1 2 3
%topology
up (0,0;N) (0,1;S);
dn (0,0;S) (0,-1;N);
rt (0,0;E) (1,0;W);
lt (0,0;W) (-1,0;E);
%SFT WangTest ACo
let WangConstraint o := o.N = o.up.S & o.E = o.rt.W in
WangConstraint o.rt.up &
o.N = o.up.S & o.E = o.rt.W &
(o.N=0|o.N=1) &
o.S=0 &
(o.W=0|o.W=1) &
o.E=0
%SFT WangTest2 Ao o=0
%show_formula WangTest2
%equal expect=T WangTest WangTest2
"""
unit_tests.append(("trivial Wang test", code_trivial_WangTest))

# jeandel-rao
code_JR = """
%nodes N E S W
%alphabet 0 1 2 3 4
%topology
up (0,0,N) (0,1,S)
dn (0,0,S) (0,-1,N)
rt (0,0,E) (1,0,W)
lt (0,0,W) (-1,0,E)
%SFT JeandelRao ACo
let WangConstraint o := o.N = o.up.S & o.E = o.rt.W in
WangConstraint o &
-- 1131
(o.E=1 & o.N=1 & o.W=3 & o.S=1) |
-- 1232
(o.E=1 & o.N=2 & o.W=3 & o.S=2) |
-- 3133
(o.E=3 & o.N=1 & o.W=3 & o.S=3) |
-- 2421
(o.E=2 & o.N=4 & o.W=2 & o.S=1) |
-- 2220
(o.E=2 & o.N=2 & o.W=2 & o.S=0) |
-- 0001
(o.E=0 & o.N=0 & o.W=0 & o.S=1) |
-- 3102
(o.E=3 & o.N=1 & o.W=0 & o.S=2) |
-- 0212
(o.E=0 & o.N=2 & o.W=1 & o.S=2) |
-- 1214
(o.E=1 & o.N=2 & o.W=1 & o.S=4) |
-- 3312
(o.E=3 & o.N=3 & o.W=1 & o.S=2) |
-- 0131
(o.E=0 & o.N=1 & o.W=3 & o.S=1)
%SFT empty Ao 0=1
%contains empty JeandelRao
"""
# not appended because it's aperiodic and would not work

code_locdomrad2 = """
-- using a cache multiplies time usage by up to 5
-- but drops memory usage to fraction
--%start_cache 10 60 
%topology grid

%SFT locdomrad22 Ao
o=0 -> (Ep[o:2] p=1) &
       (Ap[o:1] p=0 -> (Eq[o:2] q=1 & !Er[p:1] r~q) |
                       (Eq[p:2] q=1 & !Er[o:1] r~q))

%SFT locdomrad24 Ao
o=0 -> (Ep[o:2] p=1) &
       (Ap[o:4] p=0 -> (Eq[o:2] q=1 & Ar[p:2] r!@q) |
                       (Eq[p:2] q=1 & Ar[o:2] r!@q))


%SFT locdomrad2x Ao let c a b := b=1 & Ed[a:1] d~b in
o=0 -> (Et[o:2] c o t) &
       (Ap[o:4] p=0 -> Eq[o:2+p:2] (c o q & !c p q) | (!c o q & c p q))

-- %compare_SFT_pairs
%equal expect=T locdomrad22 locdomrad24
%equal expect=T locdomrad22 locdomrad2x
--%end_cache
"""
#if long_ones_too: <- used to take long, but now doesn't seem to
unit_tests.append(("loc dom rad 2", code_locdomrad2))

code = """
%topology grid
%CA @verbose a
1 Ao o!=o.rt
%equal expect=T a a
%compose @verbose aa a a
%compose aa_a aa a
%compose a_aa a aa
%equal expect=T a_aa aa_a
"""
unit_tests.append(("trivial CA associativity", code))

code = """
%alphabet 0 1
%nodes top bot -- two tracks, top and bottom
%dim 1
%topology
rt (0; top) (1; top);
rt (0; bot) (1; bot);
lt (0; top) (-1; top);
lt (0; bot) (-1; bot)

%CA identity
top 1 ACo o.top=1;
bot 1 ACo o.bot=1

%CA flip
top 1 ACo o.top=0;
bot 1 ACo o.bot=0

%equal expect=F identity flip
"""
unit_tests.append(("identity is identity", code))


# The following is the usual faithful lamplighter group action
# by cellular automata. We check some identities, construct 
# the spacetime subshift, and check injectivity of some composition.
code = """
%alphabet 0 1
%nodes top bot -- two tracks, top and bottom
%dim 1
%topology
rt (0; top) (1; top);
rt (0; bot) (1; bot);
lt (0; top) (-1; top);
lt (0; bot) (-1; bot)
%CA R -- partial right shift on the top track
top 1 ACo o.rt.top=1;
bot 1 ACo o.bot=1
%CA L -- partial left shift on the top track
top 1 ACo o.lt.top=1;
bot 1 ACo o.bot=1
%CA A -- add top track to bottom track
top 1 ACo o.top=1;
bot 1 ACo (o.bot=1 | o.top=1) & (o.bot=0 | o.top=0)
%CA id -- identity
top 1 ACo o.top=1;
bot 1 ACo o.bot=1
%compose ARRRALLLLLARR A R R R A L L L L L A R R
%compose LLARRRRRALLLA L L A R R R R R A L L L A
%equal expect=T ARRRALLLLLARR LLARRRRRALLLA
%compose ARRRALLLLARR A R R R A L L L L A R R
%compose LLARRRRALLLA L L A R R R R A L L L A
%spacetime_diagram st ARRRALLLLARR
%equal expect=F ARRRALLLLARR LLARRRRALLLA
%has_retraction ARRRALLLLARR radius=1 expect=F
%has_retraction ARRRALLLLARR radius=2 expect=T
"""
unit_tests.append(("lamplighter", code))

code = """
%alphabet a b
%SFT goldenmean Ao o=a -> o.rt=b & o.up=b
%compute_forbidden_patterns radius=2 goldenmean
%set_weights a:0 b:2
%minimum_density conf_name=c1 expect=2 goldenmean (0,1)
--%minimum_density conf_name=c2 expect=1 goldenmean (0,2)
--%minimum_density conf_name=c3 expect=6/5 goldenmean (2,3)
%contains expect=T goldenmean c1
--%contains expect=T goldenmean c2
--%contains expect=T goldenmean c3
"""
unit_tests.append(("golden mean upper density", code))

code = """
%alphabet a b
%SFT goldenmean Ao o=a -> o.rt=b & o.up=b
%set_weights a:0 b:2
%density_lower_bound expect=1 goldenmean (0,1) (1,0); (0,0) (1,0) (-1,0) (0,1) (0,-1)
"""
unit_tests.append(("golden mean lower density", code))

code = """
%SFT quarter Ao o=1 -> o.up=1 & o.rt=1
%SFT half Ao (o=o.lt=o.rt & (o=1 -> o.up=1)) | (o=o.up=o.dn & (o=1 -> o.rt=1))
%SFT two Ao o=o.up=o.rt
%contains expect=T quarter half
%contains expect=T half two
%contains conf_name=c1 expect=F method=recognizable two half
%contains expect=T half c1
%contains expect=F two c1
%contains conf_name=c2 expect=F method=recognizable two quarter
%contains expect=T quarter c2
%contains expect=F two c2
%contains conf_name=c3 expect=F method=recognizable half quarter
%contains expect=T quarter c3
%contains expect=F half c3
"""
unit_tests.append(("recog comparison", code))

code = """
%SFT onezero Ao (o=0 -> o.up=0) & (o=1 -> o.dn.dn=0)
%SFT zero Ao o=0
%equal expect=T onezero zero
%SFT onezero1 onesided=[1] Ao (o=0 -> o.up=0) & (o=1 -> o.dn.dn=0)
%SFT zero1 onesided=[1] Ao o=0
%contains expect=T onezero1 zero1
%contains conf_name=c1 expect=F zero1 onezero1
%contains expect=T onezero1 c1
%contains expect=F zero1 c1
"""
unit_tests.append(("onesided comparison", code))

code = """
%dim 1
%topology succ (0) (1)
%CA xor
1 Ao o!=o.succ
%spacetime_diagram diagram xor
--%show_environment
--%show_environment sft=diagram
%dim 2
%topology grid
%SFT var onesided=[1] Ao o!=o.rt <-> o.up=1
--%show_environment sft=var
%equal expect=T diagram var @verbose
%SFT var2 onesided=[1] Ao o!=o.rt -> o.up=1
%equal expect=F diagram var2 @verbose
"""
unit_tests.append(("spacetime diagram", code))

code = """
%alphabet 0 1 2
%SFT long_dist Ao o=1 -> Ep[o:4] p=2 & o ~^1,3 p
%SFT long_dist2 Ao o=1 ->
o.(3,0)=2 | o.(2,1)=2 | o.(1,2)=2 | o.(0,3)=2 |
o.(-1,2)=2 | o.(-2,1)=2 | o.(-3,0)=2 |
o.(-2,-1)=2 | o.(-1,-2)=2 | o.(0,-3)=2 |
o.(1,-2)=2 | o.(2,-1)=2 |
o.(0,1)=2 | o.(1,0)=2 | o.(0,-1)=2 | o.(-1,0)=2
%equal expect=T long_dist long_dist2
"""
unit_tests.append(("distance", code))

code = """
%nodes {t1 : {a} t2 : {t21:{0 1} t22:{a b}}}
%topology
e1 (0,0;t1.a) (0,0;t2.t21.0);
e2 (0,0;t1.a) (0,0;t2.t21.1);
e3 (0,0;t1.a) (0,0;t2.t22.a);
e4 (0,0;t1.a) (0,0;t2.t22.b);
e5 (0,0;t2.t21.0) (0,0;t1.a);
e6 (0,0;t2.t21.1) (0,0;t1.a);
e7 (0,0;t2.t22.a) (0,0;t1.a);
e8 (0,0;t2.t22.b) (0,0;t1.a)
%SFT a0 Ao o._.t1.a=0 <-> o=0
%SFT a1 Ao Ax[o:1] o=x
%SFT a2
(0,0;t1.a):0 (0,0;t2.t21.0):1;
(0,0;t1.a):0 (0,0;t2.t21.1):1;
(0,0;t1.a):0 (0,0;t2.t22.a):1;
(0,0;t1.a):0 (0,0;t2.t22.b):1;
(0,0;t1.a):1 (0,0;t2.t21.0):0;
(0,0;t1.a):1 (0,0;t2.t21.1):0;
(0,0;t1.a):1 (0,0;t2.t22.a):0;
(0,0;t1.a):1 (0,0;t2.t22.b):0
%equal expect=T a0 a1
%equal expect=T a0 a2
"""
unit_tests.append(("tracks", code))

code = """
%nodes 0 1 2 3
%alphabet default=[0 1] {2 : [2 X] 3 : [1 2]}
%SFT test ACo o.0!=1 -> (o.up.1=1 & o.3=2 & o.rt.0=1) | o.2=X
%compute_forbidden_patterns test
%set_weights 0:1 1:3 2:2 X:4
%minimum_density conf_name=c test (0,3)
%contains expect=T test c
"""
unit_tests.append(("node-specific alphabets", code))

code = """
%sft empty Ao 0=1
%sft empty2 Ao 1=0
%sft nonempty Ao o=0
%sft nontriv_empty Ao
(o=0 -> o.rt=0 & o.up=1) &
(o=1 -> o.rt.rt=0)
%sft nonempty Ao o!=o.rt
%equal expect=F empty nonempty
%equal expect=T empty empty2
%equal expect=T empty nontriv_empty
%empty expect=T empty
%empty expect=T empty2
%empty expect=T nontriv_empty
%empty expect=F nonempty
"""
unit_tests.append(("emptiness", code))




#unit_tests = []

code = """
%CA a
0 Ao o=o.rt=0
%CA b
0 Ao o=o.up=0
%calculate_CA_ball 3 a b
"""
unit_tests.append(("CA ball", code))

code = """
%nodes a b
%topology
sw (0,0;a) (0,0;b);
sw (0,0;b) (0,0;a)
%alphabet X Y
%save_environment env
%topology grid
%alphabet 0 1
%block_map domain=env b1
0 Ao o=o.sw
%block_map domain=env b2
0 ACo o.a=o.b
%equal expect=T b1 b2
"""
unit_tests.append(("environments and block maps", code))

code = """
%CA f
0 Ao o=o.up=0
%SFT domino Ao o!=o.rt
%preimage preim f domino
%SFT alternative Ao o=o.up=0 <-> (o.rt=1 | o.rt.up=1)
%equal expect=T preim alternative
"""
unit_tests.append(("preimage", code))

code = """
%SFT test Ao [o o.rt o.up] != [0 0 0]
%SFT test2 Ao o=1 | o.rt=1 | o.up=1
%SFT test3 Ao [o o.rt o.up] = [0 1 1] | o=1
%SFT test4 Ao o=0 -> o.rt=o.up!=0
%equal expect=T test test2
%equal expect=F test2 test3
%equal expect=T test3 test4
"""
unit_tests.append(("node lists", code))

code = """
%CA xor
0 Ao o=o.up=o.rt=0 | o=o.up!=o.rt=0 | 0=o!=o.up=o.rt | o=o.rt!=o.up=0
%fixed_points fps xor
%SFT diag Ao o.up=o.rt
%equal expect=T fps diag
"""
unit_tests.append(("fixed points", code))

code = """
%SFT a1 Ao o=o.rt
%SFT a2 Ao o=o.up
%intersection a3 a1 a2
%SFT b1 Ao o=o.rt=o.up
%equal expect=T a3 b1
%product tracks=[a b] a4 a1 a2
%nodes {a b}
%SFT b2 ACo o.a=o.(1,0).a & o.b=o.(0,1).b
%equal expect=T a4 b2
"""
unit_tests.append(("intersection and product", code))

code = """
%save_environment bin
%alphabet a b c
%block_map codomain=bin f
1 Ao o=o.rt=a | o=o.up=b
%relation tracks=[D C] rel f
%nodes D C
%alphabet {D:[a b c] C:[0 1]}
%SFT a ACo o.C=1 <-> (o.D=o.(1,0).D=a | o.D=o.(0,1).D=b)
%equal expect=T rel a
"""
unit_tests.append(("relation", code))

code = """
%CA f
1 Ao o=1 | o.rt=1
%CA g
1 Ao o=1 | o.up=1
%compose fg f g
%compose gf g f
%equal expect=T fg gf
%relation rfg fg
%relation rgf gf
%equal expect=T rfg rgf
"""
unit_tests.append(("nontrivial commutation", code))

code = """
%SFT count1 Ao 1 <= #[o=1 o.rt=1 o.up=1 o.up.rt=1] <= 3
%SFT man1 Ao !(o=o.rt=o.up=o.up.rt)
%equal expect=T count1 man1
%SFT count2 Ao let v a := a=1 in letnum n := 1 in #p[o:1] v p <= n
%SFT man2 Ao !Ex[o:1] Ey[o:1] y!@x=y=1
%equal expect=T count2 man2
%SFT count3 Ao let v a := letnum n := 1 in #p[a:1] p=1 <= n in v o
%equal expect=T count3 man2
%SFT count4 Ao (#p[o:1] p=1 | p.up=0) + 1 <= abs (#q[o:1] q=0 | q.rt=1)
%SFT count5 Ao ((#p[o:1] p=1 | p.up=0) + 2)*3 >= ((#q[o:1] q=0 | q.rt=1) + 1)*3
%SFT count6 Ao ((#p[o:1] p=1 | p.up=0) + 4)*(-1) == ((#q[o:1] q=0 | q.rt=1) + 3)*(-1)
%intersection count7 count4 count5
%equal expect=T count6 count7
%SFT empty Ao 0=1
%equal expect=F empty count7
%SFT count8 Ao Ax[o:2] dist o x + #[o=0 x=1] <= 3
%SFT uni_chess Ao (o = o.rt = o.up = o.up.rt) | (o != o.rt = o.up != o.up.rt)
%equal expect=T count8 uni_chess
"""
unit_tests.append(("counting", code))

code = """
%alphabet 0 d 3 1 e
%SFT x Ao #o <= 2
%SFT y Ao o=0 | o=1
%equal expect=T x y
"""
unit_tests.append(("numeric symbols", code))

# by P. Guillon
code = """
%alphabet d g h b
%SFT domino Ao (o=d & o.rt=g) | (o=g & o.lt=d) | (o=h & o.up=b) | (o=b & o.dn=h)
%compute_forbidden_patterns domino
"""
unit_tests.append(("domino forbidden patterns", code))

#unit_tests = []

code = """
%topology line
%alphabet 0 1 2
%SFT neq1 Ao o != o.rt
--%SFT neq2 Ao o.lt != o != o.rt
%SFT neq_gap Ao o.lt != o.rt
--%SFT shift Ao
--(o=0 -> o.rt != 2) &
--(o=1 -> o.rt != 0) &
--(o=2 -> o.rt != 1)
--%SFT nil Ao o != o
%compute_forbidden_patterns neq1
--%compute_forbidden_patterns neq2
%compute_forbidden_patterns neq_gap
--%compute_forbidden_patterns shift
--%compute_forbidden_patterns nil
%sofic1D sofic_neq1 neq1
--%sofic1D sofic_neq2 neq2
%sofic1D sofic_neq_gap neq_gap
--%sofic1D sofic_shift shift
--%sofic1D sofic_nil nil
%minimize sofic_neq1
--%minimize sofic_neq2
%minimize sofic_neq_gap
--%minimize sofic_shift
--%minimize sofic_nil
--%equal expect=T sofic_neq1 sofic_neq2
%equal expect=F sofic_neq1 sofic_neq_gap
--%equal expect=F sofic_neq1 sofic_shift
--%equal expect=F sofic_shift sofic_neq_gap
--%equal expect=F sofic_shift sofic_nil
--%empty expect=F sofic_neq1
--%empty expect=T sofic_nil
"""
unit_tests.append(("1d sofic (SFT) equality", code))

code = """
%alphabet 0 1 2
%SFT x Ao
(o=1 -> o.up=o.up.rt=1) &
(o=o.rt=1 -> o.lt=1 & o.rt.rt=1) &
(o=2 -> o.up!=1)
%trace tr x [1 1] [dir [[rad 0] [rad 1]]] extra_rad=1
%load_environment tr
%SFT f1 Ao o!=2 & (o=o.rt=1 -> o.lt=o.rt.rt=1)
%compute_forbidden_patterns f1
%sofic1D s1 f1
%SFT f2 Ao o!=1
%compute_forbidden_patterns f2
%sofic1D s2 f2
%union u s1 s2
%equal expect=T tr u
%trace tr2 x [1 1] [dir [per 2]] extra_rad=1
%SFT f3 Ao o=1 -> o.lt=o.rt=1
%compute_forbidden_patterns f3
%sofic1D s3 f3
%equal expect=T tr2 s3
%equal expect=F tr tr2
"""
unit_tests.append(("approximate and periodic trace", code))

code = """
%topology line
%SFT neq Ao o=1 -> o.rt=0
%compute_forbidden_patterns neq
%sofic1d neq_s neq
%product p neq_s neq_s
%load_environment p
%SFT eq ACo o.0 = 0 -> o.1 = 0
%compute_forbidden_patterns eq
%sofic1d eq_s eq
%intersection int eq_s p
%minimize int
%SFT int2 ACo (o.0 = 0 -> o.1 = 0) & (o.0 = 1 -> o.rt.0 = 0) & (o.1 = 1 -> o.rt.1 = 0)
%compute_forbidden_patterns int2
%sofic1d int2_s int2
%minimize int2_s
%equal expect=T int int2_s
"""
unit_tests.append(("1D sofic product and intersection", code))

code = """
%SFT x1 Ao
let f a b := a.rt = b in
f o.rt 0
%SFT x2 Ao
let f a b := b = a.rt in
f o.rt 0
%SFT x3 Ao o=0
%equal expect=T x1 x2
%equal expect=T x2 x3
"""
unit_tests.append(("symbols in let", code))

code = """
%SFT x1 Ao o.rt.rt=0
%SFT x2 Ao o.up.up=0
%SFT x3 Ao o=0
%equal expect=T x1 x2
%equal expect=T x1 x3
%equal expect=T method=recognizable x1 x2
%equal expect=T method=recognizable x1 x3
"""
unit_tests.append(("disjoint supports", code))

code = """
%nodes a b
%topology
rt (0,0;a) (1,0;a)
%sft x Ao has o rt -> o=0
%sft y ACo o.a=0
%equal x y expect=T
"""
unit_tests.append(("edge existence", code))

code = """
%dim 1
%nodes a b.0 b.1.X b.1.Y
%topology
rt (0;a) (1;a);
rt (0;b.0) (1;b.0);
rt (0;b.1.X) (1;b.1.X);
rt (0;b.1.Y) (1;b.1.Y);
rt (0;c) (1;c)
%SFT a1 Ao o.a = o.rt._.b.0
%nodes {a b:{0 1:{X Y}}}
%topology
rt (0;a) (1;a);
rt (0;b.0) (1;b.0);
rt (0;b.1.X) (1;b.1.X);
rt (0;b.1.Y) (1;b.1.Y);
rt (0;c) (1;c)
%SFT a2 Ao o.a = o.rt._.b.0
%equal expect=T a1 a2

%product tracks=[t1 t2] a3 a1 a2
%load_environment a3
%info
%SFT a4 ACo o.t1.a = o.rt.t1.b.0 & o.t2.a = o.rt.t2.b.0
%equal expect=T a3 a4

%compute_forbidden_patterns a1
%sofic1d s1 a1
%minimize s1
%compute_forbidden_patterns a2
%sofic1d s2 a2
%minimize s2
%compute_forbidden_patterns a3
%sofic1d s3 a3
%minimize s3
%product s3a s1 s2
%minimize s3a
%equal expect=T s3 s3a
"""
unit_tests.append(("tracks of varying depths", code))

code = """
%topology line
%SFT gms Ao o=0 | o.rt=0
%compute_forbidden_patterns gms
%sofic1d gms_s gms
%language aut gms_s
%SFT gms2 Ao (o=o.rt=1 -> o.rt.rt=1) & (o=1 -> !(o.lt=o.lt.lt=1))
%compute_forbidden_patterns gms2
%sofic1d gms_s2 gms2
%language aut2 gms_s2
%equals expect=T aut aut2
%determinize aut
%minimize aut
%equals expect=T aut aut2
%determinize aut2
%minimize aut2
%equals expect=T aut aut2
%SFT gms3 Ao o=0 | o.rt=0 | o.lt=0
%compute_forbidden_patterns gms3
%sofic1d gms_s3 gms3
%language aut3 gms_s3
%equals expect=F aut aut3
"""
unit_tests.append(("language comparison", code))

code = """
%topology line
%SFT gms Ao o=0 | o.rt=0
%compute_forbidden_patterns gms
%sofic1d gms_s gms
%language aut gms_s
%SFT inc Ao o=1 -> o.rt=1
%compute_forbidden_patterns inc
%sofic1d inc_s inc
%blockmap xor
1 Ao o!=o.rt
%sofic_image img xor inc_s
%language aut2 img
%regexp aut3 (1|())(0|0 1)*
%regexp aut4 0*(1|())0*
%equal expect=T aut aut3
%equal expect=T aut2 aut4
%contains expect=T aut aut2
%contains expect=F aut2 aut
%equal expect=F aut2 aut3
"""
unit_tests.append(("sofic image and regex", code))


code = """
%topology line
%regexp r 0* 1 0*
%sofic1d s r
%regexp r2 1 0* 1
%sofic1d s2 r2 @forbs
%SFT step Ao o=1 -> o.rt=1
%compute_forbidden_patterns step
%sofic1d step_s step
%CA xor
1 Ao o!=o.rt
%sofic_image s3 xor step_s
%equal expect=T s s2
%equal expect=T s2 s3
"""
unit_tests.append(("sofic from regexp", code))

code = """
%SFT x Ao #p[o:1] p=1 >= 2
%density_lower_bound x (1,0) (0,1); (0,0) (0,1) (1,0) (0,-1) (-1,0)
%density_lower_bound x [[(1,0)] [(0,0) (0,1) (1,0)]] [[(0,1)] [(0,0) (0,-1) (-1,0)]]
%density_lower_bound x [(1,0)] [(0,0) (0,1) (1,0)]; [(0,1)] [(0,0) (0,-1) (-1,0)]
"""
unit_tests.append(("density linear program syntax", code))

code = """
%SFT x Ao subst o:=0 in o=0
%SFT zero Ao o=0
%SFT univ Ao o=o
%equals expect=F x zero
%equals expect=T x univ
"""
unit_tests.append(("local substitution", code))

code = """
%alphabet 0 1 2
%SFT x1 Ao o=2 -> Ap[No o] p.up.up=1
%SFT x2 Ao o=2 -> Ap[N o.up.up - {o.up.up}] p=1
%SFT x3 Ao o=2 -> Ap[{o.up, o.up.up.lt, o.up.up.rt, o.(0,3)}] p=1
%equal expect=T x1 x2
%equal expect=T x2 x3
%SFT x4 Ao o=2 -> Ap[Sop 2 o] p=1
%SFT x5 Ao o=2 -> Ap[{o.(2,0) o.(1,1) o.(0,2) o.(1,-1)}] p=1
%equal expect=T x4 x5
%SFT x6 Ao o=2 -> Ap[B 2 o.(3,0) <> B 2 o.(5,0)] p=1
%SFT x7 Ao o=2 -> Ap[(B 2 o.(3,0) + B 2 o.(5,0)) - B 1 o.(4,0)] p=1
%equal expect=T x6 x7
%SFT x8 Ao o=2 -> Ap[B 2 o.(3,0) * B 2 o.(5,0)] p=1
%SFT x9 Ao o=2 -> Ap[B 1 o.(4,0)] p=1
%equal expect=T x8 x9
%SFT x10 Ao o=2 -> Ap[Bp 1(o.(4,0):1)] p=1
%SFT x11 Ao o=2 -> Ap[B 1 o.(4,0)] Aq[Bp 1 p] q=1
%equal expect=T x10 x11
"""

unit_tests.append(("finite sets", code))

code = """
%nodes a1 B_2 0 01 00
%alphabet _x 27 x27 01 0_1 "a.b.#\\"!"
%topology
A7 (0,0;B_2) (1,0;00);
7A (0,0;01) (1,0;0)
%sft "%sft test" ACo o.01.7A = "a.b.#\\"!"
%info
"""
unit_tests.append(("node and symbol names", code))


code = """
%sft x onesided=[0 1] Ao o=o.up=1 | o.rt=o.rt.rt=1
%sft y onesided=[0 1] Ao o=1 -> (o.up = o.up.up = o.up.up.rt = 0)
%find_automatic_conf mode=angluin c x
%contains expect=T x c
%contains expect=F y c
%find_automatic_conf mode=gold c2 x
%contains expect=T x c2
%contains expect=F y c2
"""

unit_tests.append(("automatic conf search", code))

code = """
%nodes a b
%alphabet {a:[0 1 2] b:[0 1]}
%topology
up (0, 0; a) (0, 1; a);
up (0, 0; b) (0, 1; b);
dn (0, 0; a) (0, -1; a);
dn (0, 0; b) (0, -1; b);
lt (0, 0; a) (-1, 0; a);
lt (0, 0; b) (-1, 0; b);
rt (0, 0; a) (1, 0; a);
rt (0, 0; b) (1, 0; b);
%CA test
a 0 Ao o.a=0;
a 1 Ao (o.a=2 & o.up.rt.b=1) | (o.a=1 & o.rt.up.b=0);
a 2 Ao (o.a=1 & o.rt.up.b=1) | (o.a=2 & o.up.rt.b=0);
b 0 Ao o.b=0;
b 1 Ao o.b=1;
%has_post_inverse test radius=0 expect=F
%has_post_inverse test radius=1 expect=F
%has_post_inverse test radius=2 expect=T
"""
unit_tests.append(("Post-inverses of CA (= injectivity)", code))

code = """
%topology line
%alphabet 0 1 2
%CA full
0 Ao o=0&o.rt=1 | o=1&o.rt=2;
1 Ao o@o
%has_post_inverse full radius=4 expect=F
%CA partial
0 Ao o=0&o.rt=1 | o=1&o.rt=2;
nil Ao o@o
%has_post_inverse partial radius=4 expect=T
"""
unit_tests.append(("Post-inverses of partial CA", code))

code = """
%topology grid
%info
%sft goldenmean @verbose Ao (o=0|o.rt=0) & (o=0|o.up=0)
%clopen test Ao o=1 & o.rt.rt = 1
%clopen test2 Ao o.rt=1
%intersection int goldenmean test
%intersection int2 goldenmean test2
%empty int expect=F
%empty int2 expect=F
%intersection int3 int int2
%empty int3 expect=T
"""
unit_tests.append(("Intersecting SFTs and clopen sets", code))

code = """
%sft a Ao is_zero o
%sft b Ao o=0
%equal expect=T a b
"""
unit_tests.append(("External functions", code))

code = """
%sft test Ao o=o.up=1 -> o.rt=1
%entropy_upper_bound test 3 4
%entropy_lower_bound test 1 2; 5 3
"""
unit_tests.append(("Entropy", code))

code = """
%alphabet encoding=unary 0 1 2
%sft x1 Ao Aq[Bo 1 o] q != o
%alphabet 0 1 2
%sft x2 Ao Aq[Bo 1 o] q != o
%product tracks=[a b] p1 x1 x2
%load_environment p1
%sft d1 ACo o.a != o.b
%intersection i1 p1 d1
%save_environment e

%topology grid
%alphabet 0 1 2 3
%sft y1 Ao Aq[Bo 1 o] q != o
%alphabet encoding=unary 0 1 2
%sft y2 Ao Aq[Bo 1 o] q != o
%product tracks=[a b] p2 y1 y2
%load_environment p2
%sft d2 ACo o.a != o.b
%intersection i2 p2 d2

%CA id1 codomain=e
a 0 ACo o.a=0;
a 1 ACo o.a=1;
b 0 ACo o.b=0;
b 1 ACo o.b=1

%has_post_inverse expect=F id1 radius=1

%CA id2 domain=e
a 0 ACo o.a=0;
a 1 ACo o.a=1;
b 0 ACo o.b=0;
b 1 ACo o.b=1

%has_post_inverse expect=T id2 radius=1
"""
unit_tests.append(("Alphabet encodings", code))

if __name__ == "__main__":

    t = time.time()

    import os
    import psutil
    process = psutil.Process(os.getpid())
    start_mem = process.memory_info().rss/1000

    for (i, (name, code)) in enumerate(unit_tests, start=1):
        griddy_inst = griddy.Griddy()
        if name == "External functions":
            def is_zero(cxt, a):
                graph, topology, nodes, alphabet, formula, variables = cxt
                apos = variables[a]
                zero, _ = alph = alphabet[()]
                avars = [circuit.V(apos + (label,)) for label in alph.node_vars]
                return alph.node_eq_sym(avars, zero)
            griddy_inst.add_external("is_zero", is_zero)
        print()
        print("Running test {}/{}: {}".format(i, len(unit_tests), name))
        griddy_inst.run(code, "assert")
#print("total time", time.time()-t)
        #a =bb
    
    total_time = time.time() - t
    end_mem = process.memory_info().rss/1000

    print("All tests were successful.")
    print("time", total_time, "memory", start_mem, "->", end_mem)



