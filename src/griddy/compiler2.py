#from circuit import *
import circuit
from circuit import NOT, V, AND, OR, T, F, IMP, IFF, tech_simp, Circuit
import mocircuits as moc
import abstract_SAT_simplify as ass
import sft
from general import *
import graphs

"""
THIS VARIANT OF COMPILER COMPILES TO MOVES IN ARBITRARY GRAPH, OTHERWISE THE SAME

A graph consists of cells, and transitions between them.
Nodes are as before, they live on top of the graph.

From now on, all circuit variables are just (cell, node, symbol).

(cell,) and (cell, node) are used. node can be multilevel.

---

# we construct a circuit whose input variables are of the form (u, n)->a --
# or just (u, n) if alphabet is binary -- and which evaluates to true iff, well.
# CURRENTLY, ACTUALLY WE NEVER USE (u, n, 0), I DON'T KNOW IF THAT'S A GOOD IDEA THOUGH

# pos_variables tells us which positions the variables point to... of course
# those positions will correspond to roughly the variables of the actual formula.

# we can also produce auxiliary variables called aux_0, ..., aux_n
# which can be used for variables ranging over symbols <- outdated!!!!!!!!!!!!!

# all_vars is all the variables that we talk about <- IT IS NOT USED FOR ANYTHING

circuit_variables are aa little tricky... they should be functions

global_restr are things that must be true even if formula is part of larger formula
"""

"""


graph.distance
"""


def formula_to_circuit_(graph, topology, nodes, alphabet, formula,
                        variables, subst, externals, global_restr):

    def is_letter(a):
        return any(a in local_alph for local_alph in alphabet.values())
    def is_cell(p):
        return len(p) == 1

    #print("F2C", formula)

    #if type(nodes) == list:
    #    nodes = sft.Nodes(nodes)
    op = formula[0]
    if op == "BOOL":
        ret = variables[formula[1]]
    elif op == "CALL":
        var = formula[1]
        args = formula[2:]
        # calling a macro
        if var in variables:
            arg_names, code, closure = variables[var]
            variables_new = {}
            if len(args) != len(arg_names):
                raise Exception("Wrong number of parameters in call %s." % (str(var) + " " + str(args)))
            for a in closure:
                variables_new[a] = closure[a]
            for i,a in enumerate(arg_names):
                if type(args[i]) != tuple: 
                    try:
                        pos = eval_to_position(graph, topology, nodes, args[i], variables) # eval_to_position can use a list of moves
                    except KeyError:
                        pos = args[i] # it's actually a value... hopefully!
                        while pos in variables:
                            pos = variables[pos]
                    variables_new[a] = pos
                elif args[i][0] == "ADDR": # eval_to_position can also use an ADDR command for some reason
                    pos = eval_to_position(graph, topology, nodes, args[i], variables, nodes)
                    variables_new[a] = pos
                # if argument is a formula, we will evaluate it (in old context)
                else:
                    circ = formula_to_circuit_(graph, topology, nodes, alphabet, args[i], variables, subst, externals, global_restr)
                    variables_new[a] = circ
            ret = formula_to_circuit_(graph, topology, nodes, alphabet, code, variables_new, subst, externals, global_restr)
        # call a Python function
        elif var in externals:
            func = externals[var]
            cxt = graph, topology, nodes, alphabet, formula, variables
            ret = func(cxt, *args)
            # convert Python truth values to truth values
            if ret == True:
                ret = T
            elif ret == False:
                ret = F
            # if returns a circuit, in case V(pos + (sym,)) we must fix alphabet[0]
            # because we are using the space efficient coding
            if type(ret) == Circuit:
                def eliminate_zero(v):
                    pos = v[1]
                    sym = v[2]
                    if sym != alphabet[pos][0]:
                        return v
                    return AND(*(NOT(V(pos + (a,))) for a in alphabet[pos][1:]))
                #print("before elimination", ret)
                circuit.transform(ret, eliminate_zero)
                #print("after elimination", ret)
        else:
            # default functions
            if var == "has":
                node = args[0]
                ret = T
                for step in args[1:]:
                    try:
                        #print(variables, ("ADDR", node, step))

                        p = eval_to_position(graph, topology, nodes, ("ADDR", node, step), variables)
                        #print("speijf", p)
                        if p == None:
                            ret = F
                            break
                    except:
                        ret = F
                        break
            
    elif op in ["CELLFORALL", "CELLEXISTS", "NODEFORALL", "NODEEXISTS"]:
        var = formula[1]
        bound = formula[2]
        #if bound == None:
        #    bound = {}
        rem_formula = formula[3] # remaining formula
        pos_formulas = []
        typ = op[:4] # cell and node happen to be four letters
        op = op[4:]
        for q in get_area(graph, topology, nodes, variables, bound, typ): # graphs can choose whether they care about nodes or not
            #print(q)
            variables_new = dict(variables)
            variables_new[var] = q
            pos_formulas.append(formula_to_circuit_(graph, topology, nodes, alphabet, rem_formula,
                                                    variables_new, subst, externals, global_restr))
        if op == "FORALL":
            ret = AND(*pos_formulas)
        elif op == "EXISTS":
            ret = OR(*pos_formulas)
        else:
            raise Exception("Unknown quantifier " + typ + op)
    
    # TODO: Add this some day. Code makes no sense ATM. Should allow a list of values to range over,
    # or be given a node over whose alphabet ranges.
    elif False and op in ["FORALLVAL", "EXISTSVAL"]:
        valvar = formula[1] # variable that ranges over all values
        rem_formula = formula[2]
        val_formulas = []
        for a in variables:
            variables_new = dict(variables)
            variables_new[valvar] = a
            val_formulas.append(formula_to_circuit_(graph, topology, nodes,
                                                    alphabet, rem_formula, variables_new,
                                                    subst, externals, global_restr))
        if op == "FORALL":
            ret = AND(*val_formulas)
        elif op == "EXISTS":
            ret = OR(*val_formulas)
        else:
            raise Exception("what is" + op)
    
    elif op in "TF":
        if op == "T":
            ret = T
        elif op == "F":
            ret = F
    elif op in ["OR", "AND", "NOT", "IMP", "IFF"]:
        args = formula[1:]
        arg_formulas = []
        for arg in args:
            res = formula_to_circuit_(graph, topology, nodes, alphabet, arg,
                                      variables, subst, externals, global_restr)
            arg_formulas.append(res)
        if op == "OR":
            ret = OR(*arg_formulas)
        elif op == "AND":
            ret = AND(*arg_formulas)
        if op == "NOT":
            ret = NOT(*arg_formulas)
        if op == "IMP":
            ret = IMP(*arg_formulas)
        if op == "IFF":
            ret = IFF(*arg_formulas)
    # bool behaves like a circuit variable without variables; more efficient maybe since we just calculate a circuit
    elif op == "SETBOOL":
        var = formula[1]
        form = formula_to_circuit_(graph, topology, nodes, alphabet, formula[2],
                                   variables, subst, externals, global_restr)
        variables_new = dict(variables)
        variables_new[var] = form
        ret = formula_to_circuit_(graph, topology, nodes, alphabet, formula[3],
                                  variables_new, subst, externals, global_restr)
    # cvn[var] should be just the code, and a closure
    elif op == "LET":
        var = formula[1][0]
        #print(var)
        arg_names = formula[1][1:]
        #print(arg_names)
        circuit_code = formula[2]
        #print("ccode", circuit_code)
        unbound_vars = collect_unbound_vars(circuit_code, set(arg_names))
        ret_code = formula[3]
        closure = {}
        for v in unbound_vars:
            if v in arg_names or any(v in local_alph for local_alph in alphabet.values()):
                continue
            closure[v] = variables[v]
        #print(closure)
        variables_new = dict(variables)
        variables_new[var] = (arg_names, circuit_code, closure)
        
        ret = formula_to_circuit_(graph, topology, nodes, alphabet, ret_code,
                                  variables_new, subst, externals, global_restr)
    elif op == "SETNUM":
        var = formula[1]
        num_circ = numexpr_to_circuit(graph, topology, nodes, alphabet, formula[2], variables, subst, externals, global_restr)
        variables_new = dict(variables)
        variables_new[var] = num_circ
        ret = formula_to_circuit_(graph, topology, nodes, alphabet, formula[3], variables_new, subst, externals, global_restr)
        
    elif op == "POSEQ":
        # p1 and p2 must be position expressions
        p1 = eval_to_position(graph, topology, nodes, formula[1], variables)
        ret = None
        if p1 == None:
            ret = F
        p2 = eval_to_position(graph, topology, nodes, formula[2], variables)
        if p2 == None:
            ret = F
        if ret == None and p2 == p1:
            ret = T
        else:
            ret = F

    elif op == "VALEQ":
        
        ret = None
        arg1 = formula[1]
        arg2 = formula[2]
        #print(arg1, arg2, "valeq")

        # check that these are not numeric variables, as for now they are compared with == (for some reason)
        while arg1 in variables:
            val = variables[arg1]
            if type(val) == tuple and isinstance(val[0], moc.MOCircuit):
                # We have a numeric variable instead of a node
                raise Exception("Cannot compare numeric variable {} with =, use ==.".format(formula[1]))
            arg1 = val
        while arg2 in variables:
            val = variables[arg2]
            if type(val) == tuple and isinstance(val[0], moc.MOCircuit):
                # We have a numeric variable instead of a node
                raise Exception("Cannot compare numeric variable {} with =, use ==.".format(formula[1]))
            arg2 = val
        
        p1ispos = True
        # horrible hack
        try:
            p1 = eval_to_position(graph, topology, nodes, arg1, variables)
            if p1 == None:
                # return None and not a circuit at all; soft error handling to simulate lazy evaluation
                return None # = F
            # evaluates to cell or symbol
            if is_cell(p1):
            #elif type(p1) == tuple and len(p1) != dim+1:
                raise Exception("Cannot compare value of cell, only node.")
            # if the node has been substituted, use the substituted value instead
            if p1 in subst:
                p1ispos = False
                p1val = subst[p1]

        # This means we will interpret as value, as we ended up looking up a
        # value as variable. I suppose the reasoning is that we may want to use
        # something like "a" as both a variable and a symbol, and we only know
        # at runtime whether something is a variable, because the parser is very basic.
        except KeyError: 
            #print("eval to pos failed for arg1", arg1)
            p1ispos = False
            #print(formula[1], "formula 1 fast")
            if is_letter(arg1):
                p1val = arg1
            else:
                raise Exception("Could not handle argument {} for =".format(arg1))

        p2ispos = True
        try: # horrible hack #2
            p2 = eval_to_position(graph, topology, nodes, arg2, variables)
            if p2 == None:
                # return None and not a circuit at all; soft error handling to simulate lazy evaluation
                return None
            if is_cell(p2):
                raise Exception("Cannot compare value of cell, only node.")
            # if the node has been substituted, use the substituted value instead
            if p2 in subst:
                p2ispos = False
                p2val = subst[p2]
            
        except KeyError:
            #print("eval to pos failed for arg2", arg2)
            #print("eval to pos failed, alphabet", alphabet)
            p2ispos = False
            if is_letter(arg2):
                p2val = arg2
            else:
                raise Exception("Could not handle argument {} for =".format(arg2))

        #print("arg1", arg1, "p1ispos", p1ispos, "arg2", arg2, "p2ispos", p2ispos, "subst", subst)
        
        if not p1ispos and not p2ispos:
            if p1val == p2val:
                return T
            return F

        elif p1ispos and p2ispos:
            if ret == None:
                args = []
                p1_alph = alphabet[p1[1]]
                p2_alph = alphabet[p2[1]]
                if p1_alph == p2_alph:
                    # the nice case: equal alphabets
                    for a in p1_alph[1:]:
                        args.append(IFF(V(p1 + (a,)), V(p2 + (a,))))
                else:
                    # the messy case: different alphabets
                    for (i,a) in enumerate(p1_alph):
                        for (j,b) in enumerate(p2_alph):
                            if a == b:
                                # force the occurrences to be logically equivalent
                                if i and j:
                                    args.append(IFF(V(p1 + (a,)), V(p2 + (a,))))
                                elif i:
                                    args.append(IFF(NOT(V(p1 + (a,))), OR(*(V(p2 + (a2,)) for a2 in p2_alph[1:]))))
                                elif j:
                                    args.append(IFF(OR(*(V(p1 + (a2,)) for a2 in p1_alph[1:])), NOT(V(p2 + (a,)))))
                                else:
                                    args.append(IFF(OR(*(V(p1 + (a2,)) for a2 in p1_alph[1:])),
                                                    OR(*(V(p2 + (a2,)) for a2 in p2_alph[1:]))))
                        else:
                            # a is not in the other alphabet; forbid it
                            if i:
                                args.append(NOT(V(p1 + (a,))))
                            else:
                                args.append(OR(*(V(p1 + (a2,)) for a2 in p1_alph[1:])))
                        # for good measure, also forbid everything unmatched in the other alphabet
                        for (i,a) in enumerate(p2_alph):
                            if a not in p1_alph:
                                if i:
                                    args.append(NOT(V(p2 + (a,))))
                                else:
                                    args.append(OR(*(V(p2 + (a2,)) for a2 in p2_alph[1:])))
                ret = AND(*args)

        else:
            if not p1ispos and p2ispos:
                p1, p2val = p2, p1val
            #print("here p1", p1, "p2val", p2val)
            local_alph = alphabet[p1[1]]
            if p2val not in local_alph:
                ret = F
            if p2val == local_alph[0]:
                ret = AND(*(NOT(V(p1 + (sym,))) for sym in local_alph[1:]))
            else:
                ret = V(p1 + (p2val,))
            
    elif op == "ISNEIGHBOR" or op == "ISPROPERNEIGHBOR":
        #print("test nbr")
        ret = None
        p1 = eval_to_position(graph, topology, nodes, formula[1], variables)
        if p1 == None:
            ret = F
        #print(formula[1], p1)
        #all_vars.add(var_of_pos_expr(formula[1]))
        p2 = eval_to_position(graph, topology, nodes, formula[2], variables)
        if p2 == None:
            ret = F
        #print(formula[2], p2)
        #all_vars.add(var_of_pos_expr(formula[2]))
        if ret == None:
            if op == "ISNEIGHBOR":
                nbhd = get_closed_nbhd(graph, topology, nodes, p1)
            else:
                nbhd = get_open_nbhd(graph, topology, nodes, p1)
            for n in nbhd:
                #print(n)
                if n == p2:
                    ret = T
                    break
            else:
                ret = F
        #print(ret)
    elif op == "HASDIST":
        ret = None
        dist_ranges = formula[1]
        p1 = eval_to_position(graph, topology, nodes, formula[2], variables)
        if p1 == None:
            ret = F
        #all_vars.add(var_of_pos_expr(formula[2]))
        p2 = eval_to_position(graph, topology, nodes, formula[3], variables)
        if p2 == None:
            ret = F
        #all_vars.add(var_of_pos_expr(formula[3]))
        if ret is None:
            dist = get_distance(graph, topology, nodes, p1, p2)
            for (start, end) in dist_ranges:
                if start <= dist and (dist <= end or end == "inf"):
                    ret = T
                    break
            else:
                ret = F
    elif op in ["NUM_EQ", "NUM_LEQ"]:
        circ1, range1 = numexpr_to_circuit(graph, topology, nodes, alphabet, formula[1], variables, subst, externals, global_restr)
        circ2, range2 = numexpr_to_circuit(graph, topology, nodes, alphabet, formula[2], variables, subst, externals, global_restr)
        if circ1 is None:
            if circ2 is None:
                if (op == "NUM_EQ" and range1 == range2) or (op == "NUM_LEQ" and range1 <= range2):
                    ret = T
                else:
                    ret = F
            elif all(range1 > n for n in range2):
                ret = F
            else:
                (j, val) = min(p for p in enumerate(range2) if range1 <= p[1])
                if op == "NUM_EQ" and val == range1:
                    ret = circ2[j]
                elif op == "NUM_LEQ":
                    ret = OR(*(circ2[k] for k in range(j, len(range2))))
                else:
                    ret = F
        elif circ2 is None:
            # Now circ1 is a list and range2 a number; we want n in range1, n OP range2
            if all(n > range2 for n in range1):
                ret = F
            else:
                (i, val) = max(p for p in enumerate(range1) if p[1] <= range2)
                if op == "NUM_EQ" and val == range2:
                    ret = circ1[i]
                elif op == "NUM_LEQ":
                    ret = NOT(OR(*(circ1[k] for k in range(i+1, len(range1)))))
                else:
                    ret = F
        else:
            # Both range1 and range2 are lists
            anded = []
            for (j, b) in enumerate(range2):
                if all(a > b for a in range1):
                    # A forbidden value for b
                    anded.append(NOT(circ2[j]))
                    continue
                i, a = max(p for p in enumerate(range1) if p[1] <= b)
                if op == "NUM_EQ" and a != b:
                    anded.append(NOT(circ2[j]))
                elif op == "NUM_EQ" and a == b:
                    anded.append(IFF(circ1[i], circ2[j]))
                elif op == "NUM_LEQ":
                    anded.append(IMP(circ2[j], NOT(OR(*(circ1[k] for k in range(i+1, len(range1)))))))
                ret = AND(*anded)
                
    elif op == "SUBSTITUTE":
        #print("subst", formula)
        subst_new = subst.copy()
        subst_new.update({eval_to_position(graph, topology, nodes, node, variables) : value
                          for (node, value) in formula[1].items()})
        #print("subst_new", subst_new)
        ret = formula_to_circuit_(graph, topology, nodes, alphabet, formula[2], variables, subst_new, externals, global_restr)
    
    else:
        raise Exception("Unknown operation: " + op)
    #print ("from formula", formula)
    #print("ret", ret)
    #print(op)
    return ret

# wrap to graph, use the new compiler, go back
def formula_to_circuit(nodes, dim, topology, alphabet, formula, externals, simplify=True, graph=None):
    #print(nodes, dim, topology, alphabet, formula, externals)

    # Actual graph being used, so compile to modern format.
    if graph!=None:
        return formula_to_circuit2(graph, topology, nodes, alphabet, formula, externals, simplify)

    graph = graphs.AbelianGroup(range(dim))
    newtopology = []
    for t in topology:
        name, offset, fromnode, tonode = t[0], vsub(t[2][:-1], t[1][:-1]), t[1][dim], t[2][dim]
        #newtopology.append((name, graph.moves_to(offset), fromnode, tonode))
        newtopology.append((name, graph.move_rel(graph.origin(), offset), fromnode, tonode))
    form = formula_to_circuit2(graph, newtopology, nodes, alphabet, formula, externals, simplify)
    # we want something like C!V(0, 0, (), 1)
    # but get C!V((0, 0), (), 1)
    # so in all nodes we should unravel the vector
    def tr(var):
        #print(var)
        if type(var[0]) != tuple:
            return var
        return var[0] + var[1:]
    #print(form)
    #for f in form.get_variables():
    #    print(f)
    circuit.transform(form, tr)
    #print(form)

    return form

# exp    C|(!V(0, 0, (), 1), !V(0, -1, (), 1))
# actual C|(!V(0, 0, (), 1), !V(0, 0, (), 1))

# this will perhaps be used later directly
def formula_to_circuit2(graph, topology, nodes, alphabet, formula, externals, simplify=True):

    # if there is no topology, we make a default topology that's just graph moves between any two nodes
    if topology == [] or topology == None:
        counter = 1044
        topology = []
        for n1 in nodes:
            for n2 in nodes:
                for m in graph.moves():
                    topology.append([str(counter), (m, 1), n1, n2])
                    counter += 1
                    topology.append([str(counter), (m, -1), n1, n2])
                    counter += 1
            
    variables = {}
    global_restr = []
    subst = {}
    form = formula_to_circuit_(graph, topology, nodes, alphabet, formula, variables, subst, externals, global_restr)
    #return tech_simp(form)
    form = tech_simp(AND(*([form]+global_restr)))
    if simplify:
        _, form = ass.simplify_circ_eqrel(form)
    return form


    
def sum_circuit(summands, global_restr):
    # Separate constants
    const = sum(num for (circ, num) in summands if circ is None)
    summands = [pair for pair in summands if pair[0] is not None]
    if not summands:
        # If we have only constants, return their sum
        return None, const
    if len(summands) == 1:
        # If we have one argument, return it
        circ, rng = summands[0]
        return circ, [num + const for num in rng]
    if len(summands) == 2:
        # If we have two arguments, do the sum
        (circ1, range1), (circ2, range2) = summands
        new_range = list(sorted(set(a1+a2 for a1 in range1 for a2 in range2)))
        oreds = {num : [] for num in new_range}
        for (i,a1) in enumerate(range1):
            for (j,a2) in enumerate(range2):
                oreds[a1+a2].append(AND(circ1[i], circ2[j]))
        new_circ = moc.MOCircuit({i : OR(*circs) for (i, (_, circs)) in enumerate(sorted(oreds.items()))})
        #global_restr.append(OR(*(new_circ[i] for i in range(len(oreds)))))
        #for i in range(len(oreds)):
        #    for j in range(i+1, len(oreds)):
        #        global_restr.append(NOT(AND(new_circ[i], new_circ[j])))
        return new_circ, [num+const for num in new_range]
    # Otherwise find a good index to divide and conquer
    # TODO: this could be smarter
    split = min((i for i in range(1, len(summands)-1)),
                key=lambda i: abs(sum(len(s[1])-1 for s in summands[:i]) - sum(len(s[1])-1 for s in summands[i:])))
    left = sum_circuit(summands[:split], global_restr)
    right = sum_circuit(summands[split:], global_restr)
    circ, rng = sum_circuit([left, right], global_restr)
    return circ, [num+const for num in rng]
    
def prod_circuit(factors, global_restr):
    # Separate constants
    const = 1
    for (circ, num) in factors:
        if circ is None:
            const *= num
    if const == 0:
        return None, 0
    factors = [pair for pair in factors if pair[0] is not None]
    if not factors:
        # If we have only constants, return their product
        return None, const
    if len(factors) == 1:
        # If we have one argument, return it
        circ, rng = factors[0]
        if const > 0:
            return circ, [num * const for num in rng]
        else:
            # Reverse the order
            the_len = len(rng)
            return moc.MOCircuit({the_len-i-1 : circ for (i, circ) in circ.circuits.items()}), [num * const for num in reversed(rng)]
    if len(factors) == 2:
        # If we have two arguments, do the product
        (circ1, range1), (circ2, range2) = factors
        new_range = list(sorted(set(a1*a2*const for a1 in range1 for a2 in range2)))
        oreds = {num : [] for num in new_range}
        for (i,a1) in enumerate(range1):
            for (j,a2) in enumerate(range2):
                oreds[a1*a2].append(AND(circ1[i], circ2[j]))
        new_circ = moc.MOCircuit({i : OR(*circs) for (i, (_, circs)) in enumerate(sorted(oreds.items()))})
        #global_restr.append(OR(*(new_circ[i] for i in range(len(oreds)))))
        #for i in range(len(oreds)):
        #    for j in range(i+1, len(oreds)):
        #        global_restr.append(NOT(AND(new_circ[i], new_circ[j])))
        return new_circ, new_range
    # Otherwise find a good index to divide and conquer
    # TODO: this could be smarter
    split = min((i for i in range(1, len(factors)-1)),
                key=lambda i: abs(sum(len(s[1])-1 for s in factors[:i]) - sum(len(s[1])-1 for s in factors[i:])))
    left = prod_circuit(factors[:split], global_restr)
    right = prod_circuit(factors[split:], global_restr)
    circ, rng = prod_circuit([left, right], global_restr)
    if const > 0:
        return circ, [num*const for num in rng]
    else:
        the_len = len(rng)
        return moc.MOCircuit({the_len-i-1 : circ for (i, circ) in circ.circuits.items()}), [num * const for num in reversed(rng)]
    
# Apply a numeric function to a numeric circuit    
def num_func_circ(func, arg, global_restr):
    circ, rng = arg
    new_rng = list(sorted(set(func(num) for num in rng)))
    oreds = {num : [] for num in new_rng}
    for (i, num) in enumerate(rng):
        oreds[func(num)].append(circ[i])
    new_circ = moc.MOCircuit({i : OR(*circs) for (i, (_, circs)) in enumerate(sorted(oreds.items()))})
    #global_restr.append(OR(*(new_circ[i] for i in range(len(oreds)))))
    #for i in range(len(oreds)):
    #    for j in range(i+1, len(oreds)):
    #        global_restr.append(NOT(AND(new_circ[i], new_circ[j])))
    return new_circ, new_rng

# Transform a numeric expression into an MOCircuit.
# Return the MOCircuit and a list of values that's the range of the numeric expression.
# Each value has a corresponding output (accessed by its index).
def numexpr_to_circuit(graph, topology, nodes, alphabet, formula, variables, subst, externals, global_restr):
    op = formula[0]
    if op == "NUM_VAR":
        return variables[formula[1]]
    elif op == "TRUTH_AS_NUM":
        cond = formula[1]
        circ = formula_to_circuit_(graph, topology, nodes, alphabet, cond, variables, subst, externals, global_restr)
        ret = (moc.MOCircuit({0 : NOT(circ), 1 : circ}), [0,1])
    elif op == "SUM":
        args = formula[1:]
        summands = []
        for numexpr in args:
            summands.append(numexpr_to_circuit(graph, topology, nodes, alphabet, numexpr, variables, subst, externals, global_restr))
        ret = sum_circuit(summands, global_restr)
    elif op == "PROD":
        args = formula[1:]
        factors = []
        for numexpr in args:
            factors.append(numexpr_to_circuit(graph, topology, nodes, alphabet, numexpr, variables, subst, externals, global_restr))
        ret = prod_circuit(factors, global_restr)
    elif op in ["ABS"]:
        numcirc = numexpr_to_circuit(graph, topology, nodes, alphabet, formula[1], variables, subst, externals, global_restr)
        if op == "ABS":
            func = abs
        ret = num_func_circ(func, numcirc, global_restr)
    elif op == "CONST_NUM":
        ret = (None, formula[1])
    elif op == "DISTANCE":
        node1 = eval_to_position(graph, topology, nodes, formula[1], variables)
        node2 = eval_to_position(graph, topology, nodes, formula[2], variables)
        ret = (None, get_distance(graph, topology, nodes, node1, node2))
    elif op == "NODECOUNT":
        var = formula[1]
        bound = formula[2]
        rem_formula = formula[3]
        summands = []
        #print(var, typ)
        for q in get_area(graph, topology, nodes, variables, bound, "NODE"):
            #print(var, typ, q)
            variables_new = dict(variables)
            variables_new[var] = q
            circ = formula_to_circuit_(graph, topology, nodes, alphabet, rem_formula, variables_new, subst, externals, global_restr)
            summands.append((moc.MOCircuit({0 : NOT(circ), 1 : circ}), [0,1]))
        ret = sum_circuit(summands, global_restr)
    elif op == "SYM_TO_NUM":
        nvec = eval_to_position(graph, topology, nodes, formula[1], variables)
        ret = sym_to_num(nvec, alphabet, global_restr)
    else:
        raise Exception("what is " + op)
    #if ret[0] is None:
    #    print("numexpr_to_circ", formula, ret)
    #else:
    #    print("numexpr_to_circ", formula, ret[0].circuits, ret[1])
    return ret

# Does this string represent a number?
def is_nat(string):
    if not string:
        return False
    if string == '0':
        return True
    if string[0] != '0' and all(c in "0123456789" for c in string):
        return True
    return False
    
# Make a numeric circuit that
# (a) restricts the node to have a "numeric" symbol, and
# (b) evaluates to the corresponding number
def sym_to_num(nvec, alphabet, global_restr):
    node = nvec[1]
    node_alph = alphabet[node]
    nums = list(sorted(sym for sym in node_alph if is_nat(sym)))
    circs = dict()
    for (i, num) in enumerate(nums):
        if num == node_alph[0]:
            circ = AND(*(NOT(V(nvec + (sym,))) for sym in node_alph[1:]))
        else:
            circ = V(nvec + (num,))
        circs[i] = circ
    for sym in node_alph:
        if sym not in nums:
            if sym == node_alph[0]:
                circ = OR(*(V(nvec + (sym2,)) for sym2 in node_alph[1:]))
            else:
                circ = NOT(V(nvec + (sym,)))
            global_restr.append(circ)

    return moc.MOCircuit(circs), [int(num) for num in nums]

def collect_unbound_vars(formula, bound = None):
    #print("collecting", formula)
    if bound == None:
        bound = set()
    bound = set(bound)
    op = formula[0]
    #print(op, bound)
    possibles = set()
    if op == "BOOL":
        possibles.add(formula[1]) # a boolean variable's value is copied from enclosing
    elif op == "CALL":
        possibles.add(formula[1]) # same for circuit
        # but also collect in args
        args = formula[2:]
        #print("collect args", args)
        for arg in args:
            if type(arg) == tuple:
                possibles.update(collect_unbound_vars(arg, bound))
            else:
                possibles.add(arg)
    elif op in ["CELLFORALL", "CELLEXISTSCELL", "NODEFORALL", "NODEEXISTS", "NODECOUNT"]:
        var = formula[1]
        bound.add(var)
        for q in collect_unbound_vars(formula[2], bound): # collect vars used in bounds
            possibles.add(q)
        for q in collect_unbound_vars(formula[3], bound): # collect vars recursively in code
            possibles.add(q)
    elif op in ["FORALLVAL", "EXISTSVAL"]:
        valvar = formula[1]
        bound.add(valvar)
        rem_formula = formula[2]
        for q in collect_unbound_vars(rem_formula, bound): # collect vars recursively in code
            possibles.add(q)
    elif op in "TF":
        pass
    elif op in ["OR", "AND", "NOT", "IMP", "IFF", "NUM_EQ", "NUM_LEQ", "SETMINUS", "SETSYMDIF", "SETUNION", "SETINTER"]:
        args = formula[1:]
        for arg in args:
            possibles.update(collect_unbound_vars(arg, bound))
    # bool behaves like a circuit variable without variables; more efficient maybe since we just calculate a circuit
    elif op in ["SETBOOL", "SETNUM"]:
        var = formula[1]
        possibles.update(collect_unbound_vars(formula[2], bound)) # variable is not bound in the code to be binded
        bound.add(var)
        possibles.update(collect_unbound_vars(formula[3], bound)) # but is in evaluation of actual 
    # cvn[var] should be just the code, and a closure
    elif op == "LET":
        var = formula[1][0]
        arg_names = formula[1][1:]
        circuit_code = formula[2]
        argbound = set(bound)
        argbound.update(arg_names)
        possibles.update(collect_unbound_vars(circuit_code, argbound))
        bound.add(var)
        possibles.update(collect_unbound_vars(formula[3], bound))
    elif op in ["POSEQ", "VALEQ", "ISNEIGHBOR", "DISTANCE"]:
        possibles.add(var_of_pos_expr(formula[1]))
        possibles.add(var_of_pos_expr(formula[2]))
    elif op == "HASVAL":
        possibles.add(var_of_pos_expr(formula[1]))
    elif op == "HASDIST":
        possibles.add(var_of_pos_expr(formula[2]))
        possibles.add(var_of_pos_expr(formula[3]))
    elif op == "CONST_NUM":
        pass
    elif op in ["NUM_VAR", "SYM_TO_NUM"]:
        possibles.add(formula[1])
    elif op == "SET_LITERAL":
        for pos in formula[1]:
            possibles.add(var_of_pos_expr(pos))
    elif op == "SET_NHOOD":
        possibles.update(collect_unbound_vars(formula[2], bound))
    elif op in ["SET_BALL", "SET_SPHERE"]:
        possibles.update(collect_unbound_vars(formula[3], bound))
    else:
        raise Exception("Unknown operation " + op)
    ret = set()
    for p in possibles:
        if p not in bound:
            ret.add(p)
    #print("now", ret)
    return ret

def var_of_pos_expr(f):
    if type(f) == tuple:
        f = f[1]
    return f

def eval_to_position(graph, topology, nodes, expr, pos_variables, top=True):
    #print("Evaluating to pos", graph, topology, nodes, expr, pos_variables, top)
    ret = eval_to_position_(graph, topology, nodes, expr, pos_variables, top)
    #print("Result", ret)
    return ret

def eval_to_position_(graph, topology, nodes, expr, pos_variables, top=True):
    #print("e2p context", graph, topology, nodes)
    #print("expr", expr)
    #print()
    # should be name of variable
    if type(expr) != tuple:
        # this may raise keyerror, which we catch...
        pos = pos_variables[expr] 
        # if not tuple, it's a chain of variables, just go down
        if type(pos) != tuple:
            return eval_to_position_(graph, topology, nodes, pos, pos_variables, top=False)
        #print("got 1 pos", pos)
        return pos
    if expr[0] != "ADDR":
        # we have a node with tracks
        #print("expr is node:", expr)
        return expr
    pos = pos_variables[expr[1]]
    #print(pos, "kos")
    if type(pos) != tuple:
        pos = eval_to_position_(graph, topology, nodes, pos, pos_variables, nodes, top=False)

    #print("pos", pos, expr,  "going through topo")
    for i in expr[2:]:
        #print("i", i)
        # underscore means go to cell level
        if i == '_':
            pos = (pos[0], ())
            continue

        for t in topology:
            #print(t, i)
            # all should have length 4 now: label, offset, fromnode, tonode
            if len(t) == 4:
                name, offset, fromnode, tonode = t
                if name == i and (pos[1] == () or fromnode == pos[1]):
                    #print("found edge", t)
                    #print(pos, "kos")
                    if pos[1] == ():
                        #print("cell")
                        pos = graph.move_rel(pos[0], offset), () #vadd(vsub(pos[0], a[0]), b[0]) + ((),)
                    else:
                        #print("node")
                        pos = graph.move_rel(pos[0], offset), tonode #vadd(vsub(pos[0], a[0]), b[0]) + (b[1],)
                        #print(",a")
                    break
                
        else:
            # nothing applicable found in topology, try moving in graph
            # by generator, direction
            #print("kjerwf", graph, pos[0], i, graph.has_cell(i))

            # I think this is what moves SHOULD look like, because we do want to be able to go both ways
            # but e.g. (0, 1) will be interpreted currently as a positive move by generator 0...
            """if type(i) == tuple and len(i) == 2 and graph.has_move(pos[0], i[0]):
                print("had")
                newpos = graph.move(pos[0], i)
                if newpos:
                    # copy node from previous, all cells have same nodes
                    pos = (newpos, pos[1])
            """
            if (i,) in nodes: # single thing => change node
                    pos = (pos[0], (i,))
                    continue
            
            # move to node
            #print("stil2")
            #if pos[1] == (): 
            #    items = (i,)
            #el
            #print("here", i)
            if type(pos[1]) == tuple:
                items = pos[1] + (i,)
            #else: # Deprecated, nowadays cells are just graph-cell + ()
            #    items = (pos[1], i)
            #print(nodes)
            if nodes.compatible(items):
                #print("compa")
                pos = (pos[0], items)
                continue
            #else:
                # finally assume it's an actual graph node
                #print("kek")
                #pos = graph.move_rel(pos[0], i), pos[1]
            #else:
            #    raise Exception("Could not process transition {} from node {}".format(i, pos))

            # by just generator without direction
            if graph.has_move(pos[0], i):
                #print("actualy")
                newpos = graph.move(pos[0], (i, 1))
                if newpos:
                    # copy node from previous, all cells have same nodes
                    pos = (newpos, pos[1])
                    continue
            
            elif graph.has_cell(i):
                #print("here", pos, i, graph.move_rel(pos[0], i), pos[1])
                pos = graph.move_rel(pos[0], i), pos[1]
                continue
            raise Exception("") # exception raised if 
        #print(pos)
    #print ("got 2 pos", pos)
    if top:
        assert pos[1] == () or pos[1] in nodes
    return pos

# given topology, positions of variables and bound dict
# list positions
def get_area(graph, topology, nodes, pos_variables, bound, typ):
    #print("getting area", bound)
    # for now, no bound means we're at the beginning
    if bound is None:
        ret = set()
        ##print(typ)
        if typ == "NODE":
            for n in nodes:
                ret.add((graph.origin(), n)) #(0,)*dim + (n,))
        else:
            ret.add((graph.origin(), ()))
        return ret
    
    # branch based on set expression's form
    if bound[0] == "SET_LITERAL":
        area = set()
        for pos in bound[1]:
            node = eval_to_position(graph, topology, nodes, pos, pos_variables)
            area.add(node)
            
    elif bound[0] == "SET_NHOOD":
        area = set()
        arg_area = get_area(graph, topology, nodes, pos_variables, bound[2], typ)
        for node in arg_area:
            new_area = set()
            for t in get_ball(graph, topology, nodes, node, 1):
                if typ == "CELL":
                    t = (t[0], ())
                if "POSITIVE" in bound[1] and t < node:
                    continue
                if "NEGATIVE" in bound[1] and t > node:
                    continue
                if "OPEN" in bound[1] and t == node:
                    continue
                new_area.add(t)
            area |= new_area
            
    elif bound[0] == "SET_BALL":
        area = set()
        arg_area = get_area(graph, topology, nodes, pos_variables, bound[3], typ)
        for node in arg_area:
            new_area = set()
            for t in get_ball(graph, topology, nodes, node, bound[2]):
                if typ == "CELL":
                    t = (t[0], ())
                if "POSITIVE" in bound[1] and t < node:
                    continue
                if "NEGATIVE" in bound[1] and t > node:
                    continue
                if "OPEN" in bound[1] and t == node:
                    continue
                new_area.add(t)
            area |= new_area
            
    elif bound[0] == "SET_SPHERE":
        area = set()
        arg_area = get_area(graph, topology, nodes, pos_variables, bound[3], typ)
        for node in arg_area:
            new_area = set()
            for t in get_ball(graph, topology, nodes, node, bound[2]):
                if typ == "CELL":
                    t = (t[0], ())
                if "POSITIVE" in bound[1] and t < node:
                    continue
                if "NEGATIVE" in bound[1] and t > node:
                    continue
                if "OPEN" in bound[1] and t == node:
                    continue
                new_area.add(t)
            for t in get_ball(graph, topology, nodes, node, bound[2]-1):
                if typ == "CELL":
                    t = (t[0], ())
                new_area.discard(t)
            area |= new_area

    elif bound[0] == "SETMINUS":
        area = get_area(graph, topology, nodes, pos_variables, bound[1], typ)
        area -= get_area(graph, topology, nodes, pos_variables, bound[2], typ)

    elif bound[0] == "SETSYMDIF":
        area = get_area(graph, topology, nodes, pos_variables, bound[1], typ)
        area ^= get_area(graph, topology, nodes, pos_variables, bound[2], typ)

    elif bound[0] == "SETUNION":
        area = get_area(graph, topology, nodes, pos_variables, bound[1], typ)
        area |= get_area(graph, topology, nodes, pos_variables, bound[2], typ)

    elif bound[0] == "SETINTER":
        area = get_area(graph, topology, nodes, pos_variables, bound[1], typ)
        area &= get_area(graph, topology, nodes, pos_variables, bound[2], typ)

    #print("got area", area)
    return area

def get_distance(graph, topology, nodes, p1, p2):
    if p1 == p2:
        return 0
    dist = 0
    # compute distance with bidirectional BFS
    seen1 = {p1}
    frontier1 = [p1]
    seen2 = {p2}
    frontier2 = [p2]
    while True:
        dist += 1
        new_frontier = []
        for p in frontier1:
            for n in get_open_nbhd(graph, topology, nodes, p):
                if n in seen2:
                    # found middle vertex
                    break
                if n not in seen1:
                    seen1.add(n)
                    new_frontier.append(n)
            else:
                # did not find middle vertex
                continue
            # found middle vertex
            break
        else:
            # did not find any middle vertex
            frontier1, frontier2 = frontier2, new_frontier
            seen1, seen2 = seen2, seen1
            continue
        # found middle vertex
        return dist

def get_ball(graph, topology, nodes, pos, radius):
    # radius 0 of cell is special, and
    # probably the only sensible thing to do with cells
    if radius == 0 and pos[-1] == None:
        ret = set()
        for n in nodes:
            ret.add(pos[:-1] + (n,))
        return ret
    
    #print(pos, radius)
    frontier = set([pos])
    ball = set([pos])
    while radius > 0:
        radius -= 1
        newfrontier = set()
        for f in frontier:
            for n in get_open_nbhd(graph, topology, nodes, f):
                #print(n)
                if n in ball:
                    continue
                newfrontier.add(n)
                ball.add(n)
        frontier = newfrontier
    #print(ball)
    return ball

# return NODES in immediate neighborhood w.r.t. topology
def get_open_nbhd(graph, topology, nodes, pos):
    ret = set()
    #print(topology)
    #print(pos)
    for t in topology:
        name, offset, a, b = t
        # if pos is a, then we add b
        if pos[1] == () or a == pos[1]:
            if graph.is_cell(offset):
                v = graph.move_rel(pos[0], offset)
            else:
                v = graph.move(pos[0], offset) #vadd(vsub(pos[0], a[0]), b[0])
            ret.add((v, b))
    return ret

def get_closed_nbhd(dim, topology, nodes, pos):
    return get_open_nbhd(dim, topology, nodes, pos).union(set([pos]))

def start_cache(mini, maxi):
    #print("cahcae stat")
    circuit.Circuit.global_simplify = True
    circuit.Circuit.global_set = None
    #print(mini, maxi)
    circuit.Circuit.global_simplify_threshold_min = mini
    circuit.Circuit.global_simplify_threshold_max = maxi

def end_cache():
    #print("end ca")
    circuit.Circuit.global_simplify = False
    circuit.Circuit.global_set = None



"""

import sft
nodes = sft.Nodes()
dim = 2
topo = [('up', (0, 0, ()), (0, 1, ())), ('dn', (0, 0, ()), (0, -1, ())), ('rt', (0, 0, ()), (1, 0, ())), ('lt', (0, 0, ()), (-1, 0, ()))]
alpha = {(): [0, 1]}
formu = ('NODEFORALL', 'o', {}, ('VALEQ', 'o', 0))
#print(formula_to_circuit(nodes, dim, topo, alpha, ('NODEFORALL', 'o', {}, ('VALEQ', 'o', 0)), {}))
print(formula_to_circuit(nodes, dim, topo, alpha,
                         ('NODEFORALL', 'o', {},
                           ('VALEQ', ('ADDR', 'o', (2,0)), 0)), {}))
print()
a = bbb
"""

# stuff below is early testing and mostly doesn't work
"""
# golden mean shift
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("dn", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                   ("SETCIRCUIT", "c", ("F",),
                                    ("OR", ("HASVAL", "o", 0),
                                    ("POSEQ", "o", "v"),
                                    ("HASVAL", "v", 0),
                                     ("CIRCUIT", "c"))))))

print(c)
"""

"""
assert str(c) == "C&(|(!(0, 0, 0), !(0, 1, 0)), |(!(0, 0, 0), !(0, -1, 0)), |(!(0, 0, 0), !(1, 0, 0)), |(!(0, 0, 0), !(-1, 0, 0)))"


# same with more letters
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("dn", (0,0,0), (-1,0,0))], # topology
                       pos_variable_names = ["o", "v"],
                       circuit_variable_names = ["c"],
                       val_variable_names = [],
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1, 2],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                   ("SETCIRCUIT", "c", ("F",),
                                    ("OR", ("HASVAL", "o", 0),
                                    ("POSEQ", "o", "v"),
                                    ("HASVAL", "v", 0),
                                     ("CIRCUIT", "c"))))))

assert str(c) == "C&(|((0, 0, 0, 0), (0, 1, 0, 0)), |((0, 0, 0, 0), (0, -1, 0, 0)), |((0, 0, 0, 0), (1, 0, 0, 0)), |((0, 0, 0, 0), (-1, 0, 0, 0)))"


# one forces one up
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("lt", (0,0,0), (-1,0,0))], # topology
                       pos_variable_names = ["o", "v"],
                       circuit_variable_names = ["c"],
                       val_variable_names = [],
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                    ("IMP", ("HASVAL", "o", 1),
                                     ("IMP", ("POSEQ", ["o", "up"], "v"),
                                      ("HASVAL", "v", 1))))))

assert str(c) == "C|(!(0, 0, 0), (0, 1, 0))"
"""

"""
# function test
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("dn", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("SETCIRCUIT", ("c", "u", "v"),
                                   ("VALEQ", "u", "v"),
                                   ("CIRCUIT", ("c", "o", ["o", "up"])))))

assert str(c) == "C&(|(!(0, 0, 0), (0, 1, 0)), |(!(0, 1, 0), (0, 0, 0)))"
"""

"""
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("dn", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ('NODEFORALL', 'o', None, ('IMP', ('HASVAL', 'o', 1), ('HASVAL', ['o', 'dn'], 0))))

print(c)
"""

"""
# identifying code
c = formula_to_circuit(nodes = [0, 1], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,1)),
                                   ("dn", (0,0,1), (0,-1,0)),
                                   ("rt", (0,0,0), (0,0,1)),
                                   ("lt", (0,0,0), (-1,0,1)),
                                   ("rt", (0,0,1), (1,0,0)),
                                   ("lt", (0,0,1), (0,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("SETCIRCUIT", ("c", "u", "v"), # c = code word neighbor
                                   ("AND", ("HASVAL", "v", 1), ("ISNEIGHBOR", "u", "v")),
                                   ("AND", ("NODEEXISTS", "d", {"o": 1}, ("CIRCUIT", ("c", "o", "d"))),
                                    ("NODEFORALL", "p", {"o": 2},
                                     ("IMP", ("NOT", ("POSEQ", "p", "o")),
                                      ("NODEEXISTS", "q", {"o" : 1, "p" : 1},
                                       ("OR", ("AND", ("CIRCUIT", ("c", "o", "q")),
                                               ("NOT", ("CIRCUIT", ("c", "p", "q")))),
                                        ("AND", ("CIRCUIT", ("c", "p", "q")),
                                         ("NOT", ("CIRCUIT", ("c", "o", "q"))))))))))))
assert str(c) == "C&(&(|((0, 0, 0), (0, 0, 1), (-1, 0, 1), (0, 1, 1)), &(|((-1, 0, 0), (-1, -1, 0), (0, 0, 1), (0, 1, 1)), |((1, 2, 1), (-1, 0, 1), (1, 1, 0), (0, 0, 0), (0, 0, 1), (1, 1, 1)), |((0, 2, 1), (-1, 0, 1), (0, 1, 0), (-1, 1, 1), (0, 0, 0), (0, 0, 1)), |((-1, 0, 1), (0, -1, 1), (0, 0, 0), (0, -1, 0), (-1, -1, 1), (0, 1, 1)), |((1, 0, 1), (-1, 0, 1), (0, 0, 0), (1, 0, 0), (1, 1, 1), (0, 1, 1)), |((-2, 0, 1), (-1, 1, 1), (0, 0, 0), (-1, 0, 0), (0, 0, 1), (0, 1, 1)), |((0, 0, 0), (-2, -1, 1), (-1, -1, 1), (-1, -1, 0), (0, 0, 1), (0, 1, 1)), |((-1, 0, 1), (0, -1, 0), (1, 0, 0), (0, 1, 1)), |((-1, 0, 1), (1, 1, 0), (0, 1, 0), (0, 0, 1)))), &(|((1, 0, 0), (0, 0, 0), (0, -1, 0), (0, 0, 1)), &(|((1, 0, 1), (0, 0, 0), (0, -1, 0), (2, 0, 0), (1, -1, 0), (0, 0, 1)), |((-1, 0, 1), (0, -1, 0), (1, 0, 0), (-1, 0, 0), (-1, -1, 0), (0, 0, 1)), |((0, -1, 1), (0, 0, 0), (0, -2, 0), (1, 0, 0), (1, -1, 0), (0, 0, 1)), |((-1, 0, 1), (0, -1, 0), (1, 0, 0), (0, 1, 1)), |((0, -1, 1), (0, 0, 0), (-1, -1, 1), (1, 0, 0)), |((0, 0, 0), (-1, -1, 0), (-1, -1, 1), (1, 0, 0), (-1, -2, 0), (0, 0, 1)), |((1, 0, 1), (0, 0, 0), (0, -1, 0), (1, 1, 1)), |((1, 1, 0), (2, 1, 0), (0, 0, 0), (0, -1, 0), (0, 0, 1), (1, 1, 1)), |((1, 1, 0), (0, 1, 0), (0, -1, 0), (1, 0, 0), (0, 0, 1), (0, 1, 1)))))"

d = formula_to_circuit(nodes = [0, 1], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,1)),
                                   ("dn", (0,0,1), (0,-1,0)),
                                   ("rt", (0,0,0), (0,0,1)),
                                   ("lt", (0,0,0), (-1,0,1)),
                                   ("rt", (0,0,1), (1,0,0)),
                                   ("lt", (0,0,1), (0,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("SETCIRCUIT", ("c", "u", "v"), # c = code word neighbor
                                   ("AND", ("HASVAL", "v", 1), ("ISNEIGHBOR", "u", "v")),
                                   ("AND", ("NODEEXISTS", "d", {"o": 2}, ("CIRCUIT", ("c", "o", "d"))),
                                    ("NODEFORALL", "p", {"o": 3},
                                     ("IMP", ("NOT", ("POSEQ", "p", "o")),
                                      ("NODEEXISTS", "q", {"o" : 1, "p" : 1},
                                       ("OR", ("AND", ("CIRCUIT", ("c", "o", "q")),
                                               ("NOT", ("CIRCUIT", ("c", "p", "q")))),
                                        ("AND", ("CIRCUIT", ("c", "p", "q")),
                                         ("NOT", ("CIRCUIT", ("c", "o", "q"))))))))))))

"""

#for n in get_closed_nbhd(dim, topology, p1)
#variables {'u': ['o', 1], 'v': 'q', 'o': (0, 0, 0), 'q': (0, 0, 0)}
#from formula ('ISNEIGHBOR', 'u', 'v')
#ret CF()

"""

                       ("|", (":", ("var", 0), ("val", 0)), # either origin has value 0...
            ("@", ("var", 0), ("var", 1)),
            (":", ("var", 1), ("val", 0))) # or there is a neighbor w/ 0
           , [0, 1, 2])
"""

"""
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("lt", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ('NODEFORALL', 'o', None,
                                  ('SETCIRCUIT', ('xor', 'a', 'b'),
                                   ('OR', ('AND', ('BOOL', 'a'), ('NOT', ('BOOL', 'b'))),
                                    ('AND', ('NOT', ('BOOL', 'a')), ('BOOL', 'b'))),
                                   ('CIRCUIT', ('xor', ('CIRCUIT', ('xor', ('HASVAL', 'o', 1),
                                                                    ('HASVAL', ['o', 'up'], 1))),
                                                ('HASVAL', ['o', 'dn'], 1))))))
print(c)
"""
"""
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("lt", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ('NODEFORALL', 'o', None,
                                  ('SETCIRCUIT', ('xor', 'a', 'b'),
                                   ('OR', ('AND', ('BOOL', 'a'), ('NOT', ('BOOL', 'b'))),
                                    ('AND', ('NOT', ('BOOL', 'a')), ('BOOL', 'b'))),
                                   ('CIRCUIT', ('xor', ('HASVAL', 'o', 1), ('HASVAL', 'o', 1))))))
print(c)
"""



#("SET", ("c", "a"), ())

# quantification is like
# Av(u3 a4)  or
# Av7
# in this basic version, i.e. you can just say how far you look from u along the basic moves
