#from circuit import *
import circuit
from circuit import NOT, V, AND, OR, T, F, IMP, IFF, tech_simp, Circuit
import mocircuits as moc
import abstract_SAT_simplify as ass
import sft
from general import *

"""
# we construct a circuit whose input variables are of the form (u, n)->a --
# or just (u, n) if alphabet is binary -- and which evaluates to true iff, well.

# pos_variables tells us which positions the variables point to... of course
# those positions will correspond to roughly the variables of the actual formula.

# we can also produce auxiliary variables called aux_0, ..., aux_n
# which can be used for variables ranging over symbols <- outdated!!!!!!!!!!!!!

# all_vars is all the variables that we talk about <- IT IS NOT USED FOR ANYTHING

circuit_variables are aa little tricky... they should be functions
"""


def formula_to_circuit_(nodes, dim, topology, alphabet, formula, variables, externals, global_restr):
    #print("to_circuit", formula, "variables", variables)
    #print([n for n in nodes])
    #a = bbb
    #print("nodes", nodes, "topology", topology)
    if type(nodes) == list:
        nodes = sft.Nodes(nodes)
    #print("variables", variables)
    # print ("aux vars", aux_var)
    # print ("alls", all_vars)
    op = formula[0]
    #print("op", op, "dim", dim)
    if op == "BOOL":
        ret = variables[formula[1]]
    elif op == "CALL":
        var = formula[1]
        args = formula[2:]
        #print("function %s called" % var)
        # calling a macro
        if var in variables:
            #print(var, "being called with", args, "in", formula)
            #varvar = variables[var]
            arg_names, code, closure = variables[var]
            variables_new = {}
            if len(args) != len(arg_names):
                raise Exception("Wrong number of parameters in call %s." % (str(var) + " " + str(args)))
            #print("rgs", args)
            #print("nems", arg_names)
            for a in closure:
                variables_new[a] = closure[a]
            for i,a in enumerate(arg_names):
                #print("arg", i, "is", a)
                if type(args[i]) != tuple:
                    #variables_new[a] = args[i]
                    try:
                        pos = eval_to_position(dim, topology, args[i], variables, nodes)
                    except KeyError:
                        pos = args[i] # it's actually a value... hopefully!
                        while pos in variables:
                            pos = variables[pos]
                    variables_new[a] = pos
                elif args[i][0] == "ADDR":
                    pos = eval_to_position(dim, topology, args[i], variables, nodes)
                    variables_new[a] = pos
                # if argument is a formula, we will evaluate it
                else:
                    circ = formula_to_circuit_(nodes, dim, topology, alphabet, args[i], variables, externals, global_restr)
                    variables_new[a] = circ
            """
            for i in args:
                if type(i) == tuple:
                    #col = collect_unbound_vars(i)
                    col = []
                elif type(i) == list:
                    col = [var_of_pos_expr(i)]
                else:
                    col = [i]
                for j in col:
                    if j in variables:
                        variables_new[j] = variables[j]
            """
            ret = formula_to_circuit_(nodes, dim, topology, alphabet, code, variables_new, externals, global_restr)
        # call a Python function
        elif var in externals:
            func = externals[var]
            cxt = nodes, dim, topology, alphabet, formula, variables
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
                    pos = v[:-2]
                    node = v[-2]
                    sym = v[-1]
                    if sym != alphabet[node][0]:
                        return v
                    return AND(*(NOT(V(pos + (node, a))) for a in alphabet[node][1:]))
                #print("before elimination", ret)
                circuit.transform(ret, eliminate_zero)
                #print("after elimination", ret)
        else:
            # default functions
            if var == "has":
                node = args[0]
                #print("has check", node, eval_to_position(dim, topology, node, variables, nodes))
                ret = T
                for step in args[1:]:
                    #print("try", step)
                    try:
                        p = eval_to_position(dim, topology, ("ADDR", node, step), variables, nodes)
                        #print("eval to", p)
                        if p == None:
                            ret = F
                            break
                    except:
                        #print("Seom problem")
                        ret = F
                        break
            
    elif op in ["CELLFORALL", "CELLEXISTS", "NODEFORALL", "NODEEXISTS"]:
        var = formula[1]
        bound = formula[2]
        if bound == None:
            bound = {}
        rem_formula = formula[3]
        pos_formulas = []
        typ = op[:4]
        op = op[4:]
        #print(var, typ)
        for q in get_area(dim, topology, variables, bound, typ, nodes):
            #print(var, typ, q)
            variables_new = dict(variables)
            variables_new[var] = q
            pos_formulas.append(formula_to_circuit_(nodes, dim, topology, alphabet, rem_formula, variables_new, externals, global_restr))
                                    
            #print(q)
        #print(a = bbb)
        if op == "FORALL":
            ret = AND(*pos_formulas)
        elif op == "EXISTS":
            ret = OR(*pos_formulas)
        else:
            raise Exception("what is" + op)
    elif op in ["FORALLVAL", "EXISTSVAL"]:
        valvar = formula[1]
        rem_formula = formula[2]
        val_formulas = []
        for a in variables:
            variables_new = dict(variables)
            variables_new[valvar] = a
            val_formulas.append(formula_to_circuit_(nodes, dim, topology, alphabet, rem_formula, variables_new, externals, global_restr))
        if op == "FORALL":
            ret = AND(*pos_formulas)
        elif op == "EXISTS":
            ret = OR(*pos_formulas)
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
        #print(op, "stepping into")
        for arg in args:
            #print(arg)
            res = formula_to_circuit_(nodes, dim, topology, alphabet, arg, variables, externals, global_restr)
            arg_formulas.append(res)
            #print(res)
        if op == "OR":
            ret = OR(*arg_formulas)
        elif op == "AND":
            ret = AND(*arg_formulas)
        if op == "NOT":
            #print ("NOT", arg_formulas[0], NOT(*arg_formulas))
            ret = NOT(*arg_formulas)
        if op == "IMP":
            ret = IMP(*arg_formulas)
        if op == "IFF":
            ret = IFF(*arg_formulas)
    # bool behaves like a circuit variable without variables; more efficient maybe since we just calculate a circuit
    elif op == "SETBOOL":
        #new_var = aux_var[0]
        #aux_var[0] += 1
        var = formula[1]
        form = formula_to_circuit_(nodes, dim, topology, alphabet, formula[2], variables, externals, global_restr)
        variables_new = dict(variables)
        variables_new[var] = form
        ret = formula_to_circuit_(nodes, dim, topology, alphabet, formula[3], variables_new, externals, global_restr)
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
        
        ret = formula_to_circuit_(nodes, dim, topology, alphabet, ret_code, variables_new, externals, global_restr)
    elif op == "SETNUM":
        #new_var = aux_var[0]
        #aux_var[0] += 1
        var = formula[1]
        num_circ = numexpr_to_circuit(nodes, dim, topology, alphabet, formula[2], variables, externals, global_restr)
        variables_new = dict(variables)
        variables_new[var] = num_circ
        ret = formula_to_circuit_(nodes, dim, topology, alphabet, formula[3], variables_new, externals, global_restr)
    elif op == "POSEQ":
        """
        if formula[1] == ["o", "up"]:
            print(pos_variables, nodes)
        else:
            print("waa")
        """
        #print(formula, pos_variables)
        # p1 and p2 must be position expressions
        p1 = eval_to_position(dim, topology, formula[1], variables, nodes)
        ##print("kili", p1)
        ret = None
        if p1 == None:
            #raise Exception("Could)
            ret = F
        #all_vars.add(var_of_pos_expr(formula[1]))
        p2 = eval_to_position(dim, topology, formula[2], variables, nodes)
        if p2 == None:
            ret = F
        #all_vars.add(var_of_pos_expr(formula[2]))
        if ret == None and p2 == p1:
            ret = T
        else:
            ret = F
    elif op == "HASVAL":
        ret = None
        p1 = eval_to_position(dim, topology, formula[1], variables, nodes)
        if p1 == None:
            ret = F
        #all_vars.add(var_of_pos_expr(formula[1]))
        v = formula[2]
        if ret == None:
            #print("here", p1, v, type(v), alphabet)
            local_alph = alphabet[p1[-1]]
            if v not in local_alph:
                #print("%s not in", alphabet)
                if v not in variables:
                    raise Exception("%s is not in alphabet nor a variable" % v)
                v = variables[v] # variables can also contain symbols
            if v == local_alph[0]:
                ret = AND(*(NOT(V(p1 + (sym,))) for sym in local_alph[1:]))
            else:
                ret = V(p1 + (v,))
    # the idea was that we would use hasval when we want to directly
    elif op == "VALEQ":
        
        ret = None
        arg1 = formula[1]
        arg2 = formula[2]
        
        while arg1 in variables:
            val = variables[arg1]
            if type(val) == tuple and isinstance(val[0], moc.MOCircuit):
                # We have a numeric variable instead of a node
                raise Exception("Cannot compare numeric variable {} with =".format(formula[1]))
            arg1 = val
        
        while arg2 in variables:
            val = variables[arg2]
            if type(val) == tuple and isinstance(val[0], moc.MOCircuit):
                # We have a numeric variable instead of a node
                raise Exception("Cannot compare numeric variable {} with =".format(formula[1]))
            arg2 = val
        
        p1ispos = True
        try: # horrible hack
            p1 = eval_to_position(dim, topology, arg1, variables, nodes)
            #print("computed p1", p1)
            if p1 == None:
                # return None and not a circuit at all; soft error handling to simulate lazy evaluation
                return None # = F
            # evaluates to cell or symbol
            elif type(p1) == tuple and len(p1) != dim+1:
                raise Exception("Cannot compare value of cell, only node.")
        except KeyError:
            #print("eval to pos failed for arg1", arg1)
            p1ispos = False
            #print(formula[1], "formula 1 fast")
            if any(arg1 in local_alph for local_alph in alphabet.values()):
                p1val = arg1
            else:
                raise Exception("Could not handle argument {} for =".format(arg1))

        p2ispos = True
        try: # horrible hack #2
            p2 = eval_to_position(dim, topology, arg2, variables, nodes)
            if p2 == None:
                # return None and not a circuit at all; soft error handling to simulate lazy evaluation
                return None
            elif type(p2) == tuple and len(p2) != dim+1:
                raise Exception("Cannot compare value of cell, only node.")
        except KeyError:
            #print("eval to pos failed, alphabet", alphabet)
            p2ispos = False
            if any(arg2 in local_alph for local_alph in alphabet.values()):
                p2val = arg2
            else:
                raise Exception("Could not handle argument {} for =".format(arg2))

        #print("arg1", arg1, "p1ispos", p1ispos, "arg2", arg2, "p2ispos", p2ispos)
        
        if not p1ispos and not p2ispos:
            if p1val == p2val:
                return T
            return F

        elif p1ispos and p2ispos:
            if ret == None:
                args = []
                p1_alph = alphabet[p1[-1]]
                p2_alph = alphabet[p2[-1]]
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
            #pina = wfe
            local_alph = alphabet[p1[-1]]
            if p2val not in local_alph:
                ret = F
            if p2val == local_alph[0]:
                ret = AND(*(NOT(V(p1 + (sym,))) for sym in local_alph[1:]))
            else:
                ret = V(p1 + (p2val,))
            
    elif op == "ISNEIGHBOR" or op == "ISPROPERNEIGHBOR":
        #print("test nbr")
        ret = None
        p1 = eval_to_position(dim, topology, formula[1], variables, nodes)
        if p1 == None:
            ret = F
        #print(formula[1], p1)
        #all_vars.add(var_of_pos_expr(formula[1]))
        p2 = eval_to_position(dim, topology, formula[2], variables, nodes)
        if p2 == None:
            ret = F
        #print(formula[2], p2)
        #all_vars.add(var_of_pos_expr(formula[2]))
        if ret == None:
            if op == "ISNEIGHBOR":
                nbhd = get_closed_nbhd(dim, topology, p1)
            else:
                nbhd = get_open_nbhd(dim, topology, p1)
            for n in nbhd: #get_closed_nbhd(dim, topology, p1):
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
        p1 = eval_to_position(dim, topology, formula[2], variables, nodes)
        if p1 == None:
            ret = F
        #all_vars.add(var_of_pos_expr(formula[2]))
        p2 = eval_to_position(dim, topology, formula[3], variables, nodes)
        if p2 == None:
            ret = F
        #all_vars.add(var_of_pos_expr(formula[3]))
        if ret is None:
            dist = get_distance(dim, topology, nodes, p1, p2)
            for (start, end) in dist_ranges:
                if start <= dist and (dist <= end or end == "inf"):
                    ret = T
                    break
            else:
                ret = F
    elif op in ["NUM_EQ", "NUM_LEQ"]:
        circ1, range1 = numexpr_to_circuit(nodes, dim, topology, alphabet, formula[1], variables, externals, global_restr)
        circ2, range2 = numexpr_to_circuit(nodes, dim, topology, alphabet, formula[2], variables, externals, global_restr)
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
    else:
        raise Exception("What " + op)
    #print ("from formula", formula)
    #print("ret", ret)
    return ret

def formula_to_circuit(nodes, dim, topology, alphabet, formula, externals, simplify=True, graph=None):
    #print(nodes, dim, topology, alphabet, formula, externals)
    assert graph==None
    variables = {}
    global_restr = []
    form = formula_to_circuit_(nodes, dim, topology, alphabet, formula, variables, externals, global_restr)
    #return tech_simp(form)
    form = tech_simp(AND(*([form]+global_restr)))
    if simplify:
        _, form = ass.simplify_circ_eqrel(form)
    #print(form)
    #a = Bb
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
def numexpr_to_circuit(nodes, dim, topology, alphabet, formula, variables, externals, global_restr):
    op = formula[0]
    if op == "NUM_VAR":
        return variables[formula[1]]
    elif op == "TRUTH_AS_NUM":
        cond = formula[1]
        circ = formula_to_circuit_(nodes, dim, topology, alphabet, cond, variables, externals, global_restr)
        ret = (moc.MOCircuit({0 : NOT(circ), 1 : circ}), [0,1])
    elif op == "SUM":
        args = formula[1:]
        summands = []
        for numexpr in args:
            summands.append(numexpr_to_circuit(nodes, dim, topology, alphabet, numexpr, variables, externals, global_restr))
        ret = sum_circuit(summands, global_restr)
    elif op == "PROD":
        args = formula[1:]
        factors = []
        for numexpr in args:
            factors.append(numexpr_to_circuit(nodes, dim, topology, alphabet, numexpr, variables, externals, global_restr))
        ret = prod_circuit(factors, global_restr)
    elif op in ["ABS"]:
        numcirc = numexpr_to_circuit(nodes, dim, topology, alphabet, formula[1], variables, externals, global_restr)
        if op == "ABS":
            func = abs
        ret = num_func_circ(func, numcirc, global_restr)
    elif op == "CONST_NUM":
        ret = (None, formula[1])
    elif op == "DISTANCE":
        node1 = eval_to_position(dim, topology, formula[1], variables, nodes)
        node2 = eval_to_position(dim, topology, formula[2], variables, nodes)
        ret = (None, get_distance(dim, topology, nodes, node1, node2))
    elif op == "NODECOUNT":
        var = formula[1]
        bound = formula[2]
        rem_formula = formula[3]
        summands = []
        #print(var, typ)
        for q in get_area(dim, topology, variables, bound, "NODE", nodes):
            #print(var, typ, q)
            variables_new = dict(variables)
            variables_new[var] = q
            circ = formula_to_circuit_(nodes, dim, topology, alphabet, rem_formula, variables_new, externals, global_restr)
            summands.append((moc.MOCircuit({0 : NOT(circ), 1 : circ}), [0,1]))
        ret = sum_circuit(summands, global_restr)
    elif op == "SYM_TO_NUM":
        nvec = eval_to_position(dim, topology, formula[1], variables, nodes)
        ret = sym_to_num(nvec, nodes, alphabet, global_restr)
    else:
        raise Exception("what is " + op)
    #if ret[0] is None:
    #    print("numexpr_to_circ", formula, ret)
    #else:
    #    print("numexpr_to_circ", formula, ret[0].circuits, ret[1])
    return ret
    
# Make a numeric circuit that
# (a) restricts the node to have a "numeric" symbol (TODO), and
# (b) evaluates to the corresponding number
def sym_to_num(nvec, nodes, alphabet, global_restr):
    node = nvec[-1]
    node_alph = alphabet[node]
    nums = list(sorted(sym for sym in node_alph if type(sym) == int))
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
    return moc.MOCircuit(circs), nums

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
        for q in formula[2]: # collect vars used in bounds
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
    elif op in ["OR", "AND", "NOT", "IMP", "IFF", "NUM_EQ", "NUM_LEQ"]:
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
    else:
        raise Exception("What " + op)
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

# a position expression is a list where
# we have first a position variable,
# then a bunch of edges. we will go forward along
# those edges
def eval_to_position(dim, topology, expr, pos_variables, nodes, top=True):
    #print("EVALTOPOS", expr, pos_variables, nodes, topology)
    if type(expr) != tuple:
        #print("tking", pos_variables[expr])
        pos = pos_variables[expr]
        if type(pos) != tuple:
            #print("recurse")
            return eval_to_position(dim, topology, pos, pos_variables, nodes, top=False)
        #print("got 1 pos", pos)
        return pos
    if expr[0] != "ADDR":
        # we have a node with tracks
        #print("expr is node:", expr)
        return expr
    pos = pos_variables[expr[1]]
    #print(pos, "ke")
    if type(pos) != tuple:
        #print("temp recurse")
        pos = eval_to_position(dim, topology, pos, pos_variables, nodes, top=False)
    #print("pos", pos)
    #print(topology)
    for i in expr[2:]:
        #print("i", i)
        # underscore means go to cell level
        if i == '_':
            pos = pos[:-1] + ((),)
            continue
        for t in topology:
            if len(t) == 3:
                #print("test edge", t)
                a, b = t[1], t[2]
                if t[0] == i and (pos[dim] == () or a[dim] == pos[dim]):
                    #print("found edge", t)
                    if pos[dim] == ():
                        #print("cell")
                        pos = vadd(vsub(pos[:-1], a[:-1]), b[:-1]) + ((),)
                    else:
                        #print("node")
                        pos = vadd(vsub(pos[:-1], a[:-1]), b[:-1]) + (b[dim],)
                    break
        else:
            # print("not edge", t, expr)
            if (i,) in nodes: # single thing => change node
                pos = pos[:-1] + ((i,),)
                continue
            #if pos[-1] == (): # removed because obviously does nothing
            #    items = (i,)
            #el
            if type(pos[-1]) == tuple:
                items = pos[-1] + (i,)
            #else: This is deprecated, nowadays cells are just cell + node ().
            #    raise Exception("Aha")
            #    items = (pos[-1], i)
            #print(nodes)
            if nodes.compatible(items):
                pos = pos[:-1] + (items,)
            elif type(i) == tuple and len(i) == dim: # tuple of len dim => move
                pos = vadd(pos[:-1], i) + (pos[-1],)
            #elif type(i) == tuple and len(i) == dim+1: # tuple of len dim+1 => both
            #    pos = vadd(pos[:-1], i[:-1]) + (i[-1],)
            #    a = bbb
            else:
                # return None
                raise Exception("Could not process transition {} from node {}".format(i, pos))
        #print(pos)
    #print ("got 2 pos", pos)
    if top:
        assert pos[-1] == () or pos[-1] in nodes
    return pos

# given topology, positions of variables and bound dict
# list positions
def get_area(dim, topology, pos_variables, bound, typ, nodes):
    #print("getting area", bound)
    # for now, no bound means we're at the beginning
    if bound == {}:
        ret = set()
        ##print(typ)
        if typ == "NODE":
            for n in nodes:
                ret.add((0,)*dim + (n,))
        else:
            ret.add((0,)*dim + ((),))
        return ret
    area = set()
    for u in pos_variables:
        p = pos_variables[u]
        while type(p) != tuple:
            u = p
            p = pos_variables[u]
        #print(p, bound)
        if u not in bound:
            continue
        for t in get_ball(dim, topology, p, bound[u], nodes):
            if typ == "CELL":
                t = t[:-1] + ((),)
            area.add(t)
    #print(area)
    return area

def get_distance(dim, topology, nodes, p1, p2):
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
            for n in get_open_nbhd(dim, topology, p):
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

def get_ball(dim, topology, pos, radius, nodes):
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
            for n in get_open_nbhd(dim, topology, f):
                #print(n)
                if n in ball:
                    continue
                newfrontier.add(n)
                ball.add(n)
        frontier = newfrontier
    #print(ball)
    return ball

def get_open_nbhd(dim, topology, pos):
    ret = set()
    for t in topology:
        a, b = t[1], t[2]
        # if pos is a, then we add b
        #if pos[dim] == None or
        if t[1][dim] == pos[dim]:
             v = vadd(vsub(pos[:-1], a[:-1]), b[:-1])
             ret.add(v + (b[-1],))
    return ret

def get_closed_nbhd(dim, topology, pos):
    return get_open_nbhd(dim, topology, pos).union(set([pos]))
    """
    ret = set()
    if pos[-1] != None:
        ret.add(pos)
    for t in topology:
        a, b = t[1], t[2]
        # if pos is a, then we add b
        if pos[dim] == None or t[1][dim] == pos[dim]:
             v = vadd(vsub(pos[:-1], a[:-1]), b[:-1])
             ret.add(v + (b[-1],))
    return ret
    """

""" 
def get_nbhd(dim, topology, pos):
    ret = set()
    for t in topology:
        if len(t) <= 1:
            raise Exception("Topology has invalid edge %s." % str(t))
        if len(t) != 3:
            raise Exception("Topology edge %s has unsupported size." % str(t))
        a, b = t[1], t[2]
        # if pos is a, then we add b
        if pos[dim] == None or t[1][dim] == pos[dim]:
             v = vadd(vsub(pos[:-1], a[:-1]), b[:-1])
             ret.add(v + (b[-1],))
    return ret
"""

"""
def vsub(a, b):
    c = []
    for i in range(len(a)):
        c.append(a[i] - b[i])
    return tuple(c)

def vadd(a, b):
    c = []
    for i in range(len(a)):
        c.append(a[i] + b[i])
    return tuple(c)
"""

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


# golden mean shift
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
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                   ("SET", "c", ("F",),
                                    ("OR", ("HASVAL", "o", 0),
                                    ("POSEQ", "o", "v"),
                                    ("HASVAL", "v", 0),
                                     ("CIRCUIT", "c"))))),
                       externals = [])

print(c)
a = bbb
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
