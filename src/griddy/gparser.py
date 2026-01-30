
from lark import Lark, Transformer_NonRecursive, Tree
from fractions import Fraction

class Opts:
    def __init__(self, items):
        self.items = items

class Just:
    def __init__(self, item):
        #print("making Just", item)
        self.item = item
    def __repr__(self):
        return "Just({})".format(self.item)

def cmd_opts_grammar(cmd):
    "Generate Lark grammar for optional arguments and flags."
    rules = []
    if type(cmd.opts) == dict:
        for (label, typ) in cmd.opts.items():
            rules.append('option\{"{}", {}\}'.format(label, typ))
    else:
        rules.append('option\{"{}", value\}'.format(label))
    for label in cmd.flags:
        rules.append('flag\{"{}"\}'.format(label))
    return "({})*".format("|".join(rules))

griddy_grammar = """

start: ("%" command)+

### COMMAND GRAMMAR

command: (/sft/ | /SFT/ | /clopen/) cmd_opts STRICT_LABEL cmd_opts (quantified | list_of{dict_of{vector, LABEL}}) cmd_opts -> cmd_sft_default
       | (/sft/ | /SFT/ | /clopen/) cmd_opts STRICT_LABEL cmd_opts (dict_of{vector, LABEL} cmd_opts)* -> cmd_sft_open_forbs
       | (/sft/ | /SFT/ | /clopen/) cmd_opts STRICT_LABEL cmd_opts ((dict_pair_of{vector, LABEL} cmd_opts)* /;/ cmd_opts)* (dict_pair_of{vector, LABEL} cmd_opts)+ -> cmd_sft_open_open_forbs
       | "info" cmd_opts (STRICT_LABEL cmd_opts)* -> cmd_info
       | ("contain" | "contains") cmd_opts STRICT_LABEL cmd_opts STRICT_LABEL cmd_opts -> cmd_contains
       | ("equal" | "equals") cmd_opts STRICT_LABEL cmd_opts STRICT_LABEL cmd_opts -> cmd_equals
       | ("show_formula" | "print_formula") STRICT_LABEL -> cmd_show_formula
       | "topology" (STRICT_LABEL | list_of{top_edge}) -> cmd_topology_default
       | "topology" (top_edge (";"? top_edge)* ";"?)? -> cmd_topology_open_edges
       | ("nodes" | "vertices") cmd_opts (list_of{node_name} | nested_default_dict_of{LABEL} cmd_opts) -> cmd_nodes_default
       | ("nodes" | "vertices") node_name* -> cmd_nodes_open
       | ("alphabet" | "alph") cmd_alph_opts (list_of{LABEL} | dict_of{node_name, list_of{LABEL}}) cmd_alph_opts -> cmd_alph_default
       | ("alphabet" | "alph") cmd_alph_opts (LABEL cmd_alph_opts)+ -> cmd_alph_open
       | ("blockmap" | "block_map" | "CA") cmd_opts STRICT_LABEL cmd_opts LABEL cmd_opts quantified cmd_opts (";" cmd_opts LABEL cmd_opts quantified cmd_opts)* -> cmd_blockmap_sym
       | ("blockmap" | "block_map" | "CA") cmd_opts STRICT_LABEL cmd_opts node_name cmd_opts LABEL cmd_opts quantified cmd_opts (";" cmd_opts node_name cmd_opts LABEL cmd_opts quantified cmd_opts)* ";"? -> cmd_blockmap_node_sym
       | "compose" cmd_opts STRICT_LABEL cmd_opts list_of{STRICT_LABEL} -> cmd_compose_default
       | "compose" cmd_opts STRICT_LABEL cmd_opts (STRICT_LABEL cmd_opts)+ -> cmd_compose_open
       | ("dim" | "dimension") cmd_opts NAT cmd_opts -> cmd_dimension
       | ("spacetime_diagram" | "spacetime") cmd_opts STRICT_LABEL cmd_opts STRICT_LABEL cmd_opts -> cmd_spacetime
       | ("has_post_inverse" | "has_retraction") cmd_opts STRICT_LABEL cmd_opts -> cmd_has_retraction
       | ("compute_forbidden_patterns" | "calculate_forbidden_patterns") cmd_opts STRICT_LABEL cmd_opts -> cmd_compute_forbs
       | "set_weights" cmd_opts dict_of{node_name, fraction} cmd_opts -> cmd_set_weights_default
       | "set_weights" cmd_opts dict_pair_of{node_name, fraction} (cmd_opts dict_pair_of{node_name, fraction})* cmd_opts -> cmd_set_weights_open
       | "minimum_density" cmd_opts STRICT_LABEL cmd_opts list_of{vector} cmd_opts -> cmd_min_density_default
       | "minimum_density" cmd_opts STRICT_LABEL cmd_opts vector (cmd_opts vector)* cmd_opts -> cmd_min_density_open
       | "density_lower_bound" cmd_opts STRICT_LABEL cmd_opts list_of{vector} cmd_opts list_of{vector} cmd_opts -> cmd_density_bound_single_default
       | "density_lower_bound" cmd_opts STRICT_LABEL cmd_opts list_of{list_of{vector}} cmd_opts -> cmd_density_bound_multi_default
       | "density_lower_bound" cmd_opts STRICT_LABEL cmd_opts vector (cmd_opts vector)* /;/ cmd_opts vector (cmd_opts vector)* cmd_opts -> cmd_density_bound_single_open
       | "density_lower_bound" cmd_opts STRICT_LABEL cmd_opts (list_of{list_of{vector}} cmd_opts)+ -> cmd_density_bound_multi_open
       | "density_lower_bound" cmd_opts STRICT_LABEL cmd_opts list_of{vector} cmd_opts list_of{vector} (";" cmd_opts list_of{vector} cmd_opts list_of{vector} cmd_opts)* -> cmd_density_bound_multi_open_open
       | "empty" cmd_opts STRICT_LABEL cmd_opts -> cmd_empty
       | ("compute_CA_ball" | "calculate_CA_ball") cmd_opts NAT cmd_opts list_of{STRICT_LABEL} cmd_opts -> cmd_ca_ball_default
       | ("compute_CA_ball" | "calculate_CA_ball") cmd_opts NAT cmd_opts (STRICT_LABEL cmd_opts)* -> cmd_ca_ball_open
       | "save_environment" STRICT_LABEL -> cmd_save_env
       | "load_environment" STRICT_LABEL -> cmd_load_env
       | "preimage" STRICT_LABEL STRICT_LABEL STRICT_LABEL -> cmd_preimage
       | "fixed_points" STRICT_LABEL STRICT_LABEL -> cmd_fixed_points
       | "intersection" cmd_opts STRICT_LABEL cmd_opts list_of{STRICT_LABEL} cmd_opts -> cmd_intersection_default
       | "intersection" cmd_opts STRICT_LABEL cmd_opts (STRICT_LABEL cmd_opts)+ -> cmd_intersection_open
       | "product" cmd_product_opts STRICT_LABEL cmd_product_opts list_of{STRICT_LABEL} -> cmd_product_default
       | "product" cmd_product_opts STRICT_LABEL cmd_product_opts (STRICT_LABEL cmd_product_opts)+ -> cmd_product_open
       | "relation" cmd_relation_opts STRICT_LABEL cmd_relation_opts STRICT_LABEL cmd_relation_opts -> cmd_relation
       | ("sofic1D" | "sofic1d") cmd_opts STRICT_LABEL cmd_opts STRICT_LABEL cmd_opts -> cmd_sofic
       | "minimize" STRICT_LABEL-> cmd_minimize
       | "trace" cmd_opts STRICT_LABEL cmd_opts STRICT_LABEL cmd_opts list_of{NAT} cmd_opts list cmd_opts -> cmd_trace
       | "union" cmd_opts STRICT_LABEL cmd_opts list_of{STRICT_LABEL} cmd_opts -> cmd_union_default
       | "union" cmd_opts STRICT_LABEL cmd_opts (STRICT_LABEL cmd_opts)+ -> cmd_union_open
       | "language" STRICT_LABEL STRICT_LABEL -> cmd_language
       | "determinize" STRICT_LABEL-> cmd_determinize
       | "sofic_image" STRICT_LABEL STRICT_LABEL STRICT_LABEL-> cmd_sofic_image
       | "regexp" cmd_opts STRICT_LABEL cmd_opts regexp cmd_opts-> cmd_regexp
       | "find_automatic_conf" cmd_opts STRICT_LABEL cmd_opts STRICT_LABEL cmd_opts-> cmd_find_automatic
       | "restrict_codomain" STRICT_LABEL STRICT_LABEL -> cmd_restrict_codomain
       | "tiler" cmd_tiler_opts STRICT_LABEL cmd_tiler_opts -> cmd_tiler
       | "graph" STRICT_LABEL -> cmd_graph
       | "run" LABEL -> cmd_run
       | "load_forbidden_patterns" STRICT_LABEL STRICT_LABEL -> cmd_load_forbs
       | "image_intersects" cmd_opts STRICT_LABEL cmd_opts STRICT_LABEL cmd_opts -> cmd_image_intersects
       | ("show_conf" | "print_conf") cmd_opts STRICT_LABEL cmd_opts -> cmd_show_conf
       | ("show_parsed" | "print_parsed") cmd_opts STRICT_LABEL cmd_opts -> cmd_show_parsed
       | ("show_forbidden_patterns" | "print_forbidden_patterns") cmd_opts STRICT_LABEL cmd_opts -> cmd_show_forbs
       | ("show_graph" | "print_graph") cmd_opts STRICT_LABEL cmd_opts -> cmd_show_graph
       | ("show_environment" | "print_environment") cmd_opts STRICT_LABEL cmd_opts -> cmd_show_environment
       | ("compare_sft_pairs" | "compare_SFT_pairs") cmd_opts -> cmd_compare_sft_pairs
       | ("compare_sft_pairs_equality" | "compare_SFT_pairs_equality") cmd_opts -> cmd_compare_sft_pairs_eq
       | "entropy_upper_bound" cmd_opts STRICT_LABEL cmd_opts list_of{NAT} cmd_opts -> cmd_entropy_upper_default
       | "entropy_upper_bound" cmd_opts STRICT_LABEL cmd_opts (NAT cmd_opts)* -> cmd_entropy_upper_open
       | "entropy_lower_bound" cmd_opts STRICT_LABEL cmd_opts list_of{NAT} cmd_opts list_of{NAT} cmd_opts -> cmd_entropy_lower_default
       | "entropy_lower_bound" cmd_opts STRICT_LABEL cmd_opts (NAT cmd_opts)* /;/ cmd_opts (NAT cmd_opts)* -> cmd_entropy_lower_open
       | "tile_box" STRICT_LABEL NAT -> cmd_tile_box
       | "keep_tiling" cmd_opts STRICT_LABEL cmd_opts -> cmd_keep_tiling

top_edge: LABEL vector~1..3

cmd_opts: cmd_opt*
cmd_opt: | STRICT_LABEL "=" value -> option
         | "@" STRICT_LABEL       -> flag

cmd_alph_opts: (/default/ "=" list_of{LABEL} | /encoding/ "=" LABEL)*
cmd_product_opts: (/tracks/ "=" list_of{LABEL} | /env/ "=" LABEL)*
cmd_relation_opts: ("tracks" "=" list_of{LABEL})?
cmd_tiler_opts: ( /x_size/ "=" NAT
                | /y_size/ "=" NAT
                | /node_offsets/ "=" dict_of{node_name, list_of{fraction}}
                | /gridmoves/ "=" list_of{list_of{fraction}}
                | /pictures/ "=" (dict_of{node_name, list_of{LABEL}} | list_of{LABEL})
                | /topology/ "=" STRICT_LABEL
                | /initial/ "=" STRICT_LABEL
                | /colors/ "=" dict_of{LABEL, list_of{NAT}}
                | /hidden/ "=" list_of{node_name}
                | "@" ( /x_periodic/ | /y_periodic/ ))*

### FORMULA GRAMMAR

# We want quantifiers, let expressions etc to extend as far to the right as possible:
# let b:=a in a=1 & b=1 should not be parsed as (let b:=a in a=1) & b=1.
# This means that an and_formula (or any other binary operator) cannot contain a let_formula
# except on the very right.

quantified: QUANTIFIER STRICT_LABEL imp_formula

QUANTIFIER: "A" | "AC" | "E" | "EC"

?formula: imp_formula
?imp_formula: iff_formula
            | left_iff_formula "->" imp_formula
?iff_formula: (left_or_formula "<->")* or_formula
?left_iff_formula: (left_or_formula "<->")* left_or_formula
?or_formula: (left_and_formula "|")* and_formula
?left_or_formula: (left_and_formula "|")* left_and_formula
?and_formula: (left_neg_formula "&")* neg_formula
?left_and_formula: (left_neg_formula "&")* left_neg_formula
?neg_formula: NEG* (rightmost_formula | atomic_formula)
?left_neg_formula: NEG* atomic_formula

?sym_or_node: LABEL | pos_expr

?atomic_formula: "(" formula ")"
               | STRICT_LABEL (LABEL | pos_expr | "(" formula ")")*            -> bool_or_call
               | (sym_or_node | list_of{sym_or_node}) (NEG? comp_op (sym_or_node | list_of{sym_or_node}))+ -> node_comp
               | num_formula (num_comp_op num_formula)+ -> num_comp

!num_comp_op: "==" | "/=" | "<=" | "<" | ">=" | ">"

rightmost_formula: QUANTIFIER STRICT_LABEL "[" finite_set "]" formula  -> restr_quantified
                 | "subst" (pos_expr ":=" LABEL)+ "in" formula         -> subst_formula
                 | "let" STRICT_LABEL+ ":=" formula "in" formula       -> let_formula
                 | "letnum" STRICT_LABEL ":=" num_formula "in" formula -> letnum_formula

?num_formula: sum_num_formula
?sum_num_formula: prod_num_formula ("+" prod_num_formula)*
?prod_num_formula: atomic_num_formula ("*" atomic_num_formula)*

?atomic_num_formula: "(" num_formula ")"
                   | "abs" atomic_num_formula                    -> num_call
                   | "#" list_of{formula}                        -> num_count_list
                   | INT                                         -> num_const
                   | STRICT_LABEL                                -> num_var
                   | "#" STRICT_LABEL "[" finite_set "]" formula -> count_quantified
                   | "dist" pos_expr pos_expr                    -> num_dist
                   | "#" pos_expr                                -> num_node

!comp_op: "=" | "@" | "~" | "~~" | "~^" nat_set

nat_set: nat_range ("," nat_range)*
!nat_range: NAT ("-" NAT?)?

?pos_expr: STRICT_LABEL ("." (LABEL | vector))*

### FINITE SETS GRAMMAR

?finite_set: set_diff
?set_diff: (set_diff "-")? set_symdiff
?set_symdiff: set_union ("<>" set_symdiff)?
?set_union: set_int ("+" set_union)?
?set_int: atomic_set ("*" set_int)?

?atomic_set: pos_expr ":" NAT                   -> set_short_ball
           | "{" pos_expr (","? pos_expr)* "}"  -> set_literal
           | "N" set_mods pos_expr             -> set_node_nhood
           | "N" set_mods atomic_set           -> set_set_nhood
           | (/B|S/) set_mods NAT pos_expr     -> set_node_ball
           | (/B|S/) set_mods NAT atomic_set   -> set_set_ball
           | "(" finite_set ")"

set_mods: (/o/ | /p/ | /n/)*

### REGULAR EXPRESSION GRAMMAR

?regexp: regexp_union
?regexp_union: regexp_intersection ("|" regexp_union)?
?regexp_intersection: regexp_prefix ("&" regexp_intersection)?
?regexp_prefix: (/!/ | /~/)* regexp_concat
?regexp_concat: regexp_suffix regexp_concat?
?regexp_suffix: atomic_regexp (/\*/ | /\+/ | /\?/)*

?atomic_regexp: "(" regexp ")"
              | "(" ")"        -> regexp_empty_word
              | LABEL          -> regexp_symbol
              | list_of{LABEL} -> regexp_symbol_list

### COMMON DEFINITIONS

node_name: LABEL ("." LABEL)*

vector: "(" INT ("," INT)* ")"               -> plain_vector
      | "(" INT ("," INT)* ";" node_name ")" -> node_vector

NEG: "!"

?value: quantified
      | STRICT_LABEL
      | INT
      | vector
      | list
      | dict

list: "[" (value (","? value)*)? "]"
list_of{val}: "[" (val (","? val)*)? "]"
open_list_of{val}: val (","? val)*

nested_default_dict_of{key}: "{" (just{key} | dict_pair_of{key, nested_default_dict_of{key}}) (","? (just{key} | dict_pair_of{key, nested_default_dict_of{key}}))* "}"
dict_of{key, val}: "{" (dict_pair_of{key, val} (","? dict_pair_of{key, val})*)? "}"
open_dict_of{key, val}: (dict_pair_of{key, val} (";"? dict_pair_of{key, val})*)?
dict_pair_of{key, val}: key ":" val
just{val}: val

dict: "{" (dict_pair (","? dict_pair))? "}"
dict_pair: value ":" value

LABEL: /[a-zA-Z0-9_]+/ |  ESCAPED_STRING
STRICT_LABEL: /[a-zA-Z_][a-zA-Z0-9_]*/ | ESCAPED_STRING
NAT: /0|[1-9][0-9]*/
INT: /0|-?[1-9][0-9]*/
?fraction: INT ("/" NAT)?

COMMENT: /--[^\n]*/x
%ignore COMMENT

%import common.WS
%import common.ESCAPED_STRING
%ignore WS
"""

class GriddyTransformer(Transformer_NonRecursive):

    NAT = int
    INT = int
    LABEL = str
    #STRICT_LABEL = str

    def STRICT_LABEL(self, items):
        return items

    def fraction(self, items):
        return Fraction(*items)

    list = list
    list_of = list
    open_list_of = list
    
    dict_pair = tuple
    dict_pair_of = tuple

    dict = dict
    dict_of = dict
    open_dict_of = dict

    def nested_default_dict_of(self, items):
        #print("nddo", items)
        the_dict = dict()
        for item in items:
            if isinstance(item, Just):
                # single key -> pair with None
                the_dict[item.item] = None
            else:
                the_dict[item[0]] = item[1]
        return the_dict

    def just(self, items):
        return Just(items[0])

    plain_vector = tuple

    def node_vector(self, items):
        return (tuple(items[:-1]), items[-1])

    node_name = tuple

    def dict_of(self, pairs):
        return dict(pairs)

    

    def quantified(self, item):
        quant, var, formula = item
        if quant == "A":
            qtype = "NODEFORALL"
        elif quant == "E":
            qtype = "NODEEXISTS"
        elif quant == "AC":
            qtype = "CELLFORALL"
        elif quant == "EC":
            qtype = "CELLEXISTS"
        return (qtype, var, None, formula)

    def restr_quantified(self, item):
        quant, var, finset, formula = item
        if quant == "A":
            qtype = "NODEFORALL"
        elif quant == "E":
            qtype = "NODEEXISTS"
        elif quant == "AC":
            qtype = "CELLFORALL"
        elif quant == "EC":
            qtype = "CELLEXISTS"
        return (qtype, var, finset, formula)

    def set_short_ball(self, finset):
        return ("SET_BALL", [], finset[1], ("SET_LITERAL", [finset[0]]))

    def set_literal(self, nodes):
        return ("SET_LITERAL", nodes)

    def set_node_nhood(self, args):
        return ("SET_NHOOD", args[0], ("SET_LITERAL", [args[1]]))

    def set_set_nhood(self, args):
        return ("SET_NHOOD", args[0], args[1])

    def set_node_ball(self, args):
        if args[0] == "B":
            ball = "SET_BALL"
        elif args[0] == "S":
            ball = "SET_SPHERE"
        return (ball, args[1], args[2], ("SET_LITERAL", [args[3]]))

    def set_set_ball(self, args):
        if args[0] == "B":
            ball = "SET_BALL"
        elif args[0] == "S":
            ball = "SET_SPHERE"
        return (ball, args[1], args[2], args[3])

    def set_mods(self, items):
        ret = []
        for item in items:
            if item == "o":
                ret.append("OPEN")
            if item == "p":
                ret.append("POSITIVE")
            if item == "n":
                ret.append("NEGATIVE")
        return ret

    def set_diff(self, args):
        return ("SETMINUS", *args)

    def set_symdiff(self, args):
        return ("SETSYMDIF", *args)

    def set_union(self, args):
        return ("SETUNION", *args)

    def set_int(self, args):
        return ("SETINTER", *args)

    def pos_expr(self, address):
        return ("ADDR", *address)

    def nat_range(self, items):
        if len(items) == 1:
            return (items[0], items[0])
        elif len(items) == 2:
            return (items[0], "inf")
        else:
            return (items[0], items[2])

    nat_set = list

    def comp_op(self, items):
        if len(items) == 1:
            op = items[0]
            if op == "=":
                the_op = "VALEQ"
            elif op == "@":
                the_op = "POSEQ"
            if op == "~":
                the_op = "ISNEIGHBOR"
            elif op == "~~":
                the_op = "ISPROPERNEIGHBOR"
            return lambda x,y: (the_op, x, y)
        else:
            return lambda x,y: ("HASDIST", items[1], x, y)

    def node_comp(self, comps):
        first, *rest = comps
        anded = []
        while rest:
            if rest[0] == "!":
                negate = True
                rest = rest[1:]
            else:
                negate = False
            op_func, second, *rest = rest
            if type(first) == list:
                term = ("AND", *(op_func(x,y) for (x,y) in zip(first, second)))
            else:
                term = op_func(first, second)
            if negate:
                term = ("NOT", term)
            anded.append(term)
            first = second
        if len(anded) == 1:
            return anded[0]
        return ("AND", *anded)

    def iff_formula(self, formulas):
        if len(formulas) == 2:
            return ("IFF", *formulas)
        return ("AND", *(("IFF", formulas[i], formulas[i+1]) for i in range(len(formulas)-1)))

    def left_iff_formula(self, formulas):
        return self.iff_formula(formulas)

    def imp_formula(self, formulas):
        return ("IMP", formulas[0], formulas[1])

    def left_imp_formula(self, formulas):
        return self.imp_formula(formulas)

    def or_formula(self, formulas):
        return ("OR", *formulas)

    def left_or_formula(self, formulas):
        return self.or_formula(formulas)

    def and_formula(self, formulas):
        return ("AND", *formulas)

    def left_and_formula(self, formulas):
        return self.and_formula(formulas)

    def neg_formula(self, negs_and_formula):
        formula = negs_and_formula[-1]
        if not len(negs_and_formula) % 2:
            formula = ("NOT", formula)
        return formula

    def left_neg_formula(self, formulas):
        return self.neg_formula(formulas)

    def let_formula(self, letexpr):
        call = letexpr[:-2]
        result = letexpr[-2]
        rest = letexpr[-1]
        return ("LET", tuple(call), result, rest)

    def letnum_formula(self, letexpr):
        var, result, rest = letexpr
        return ("SETNUM", var, result, rest)

    def subst_formula(self, substexpr):
        subst = {substexpr[2*i] : substexpr[2*i+1]
                 for i in range(len(substexpr)//2)}
        rest = substexpr[-1]
        return ("SUBSTITUTE", subst, rest)

    def bool_or_call(self, call):
        if len(call) == 1:
            return ("BOOL", call[0])
        else:
            return ("CALL", *call)

    def sum_num_formula(self, formulas):
        return ("SUM", *formulas)

    def prod_num_formula(self, formulas):
        return ("PROD", *formulas)

    def num_comp_op(self, op):
        op = op[0]
        if op == "==":
            return lambda a, b: ("NUM_EQ", a, b)
        if op == "/=":
            return lambda a, b: ("NOT", ("NUM_EQ", a, b))
        if op == "<=":
            return lambda a, b: ("NUM_LEQ", a, b)
        if op == "<":
            return lambda a, b: ("NOT", ("NUM_LEQ", b, a))
        if op == ">=":
            return lambda a, b: ("NUM_LEQ", b, a)
        if op == ">":
            return lambda a, b: ("NOT", ("NUM_LEQ", a, b))

    def num_comp(self, comps):
        first, *rest = comps
        anded = []
        while rest:
            op_func, second, *rest = rest
            term = op_func(first, second)
            anded.append(term)
            first = second
        if len(anded) == 1:
            return anded[0]
        return ("AND", *anded)

    def num_call(self, formula):
        return ("ABS", formula[0])

    def num_count_list(self, formulas):
        return ("SUM", *(("TRUTH_AS_NUM", formula) for formula in formulas[0]))

    def num_const(self, number):
        return ("CONST_NUM", number[0])

    def num_var(self, var):
        return ("NUM_VAR", var[0])

    def count_quantified(self, items):
        label, finset, formula = items
        return ("NODECOUNT", label, finset, formula)

    def num_dist(self, items):
        return ("DISTANCE", *items)

    def num_node(self, items):
        return ("SYM_TO_NUM", items[0])

    def regexp_empty_word(self, items):
        return "EMPTYWORD"

    def regexp_symbol(self, items):
        return ("SYMBOL", items[0])

    def regexp_symbol_list(self, items):
        return ("SYMBOLS", items[0])

    def regexp_union(self, items):
        return ("UNION", *items)

    def regexp_intersection(self, items):
        return ("ISECT", *items)

    def regexp_prefix(self, items):
        ret = items[-1]
        for prefix in reversed(items[:-1]):
            if prefix == "!":
                ret = ("NOT", ret)
            elif prefix == "~":
                ret = ("CONTAINS", ret)
        return ret

    def regexp_concat(self, items):
        return ("CONCAT", *items)

    def regexp_suffix(self, items):
        ret = items[0]
        for suffix in items[1:]:
            if suffix == "*":
                ret = ("STAR", ret)
            elif suffix == "+":
                ret = ("PLUS", ret)
            elif suffix == "?":
                ret = ("UNION", "EMPTYWORD", ret)
        return ret

    def option(self, items):
        return tuple(items)

    def flag(self, items):
        return items[0]
    
    def cmd_opts(self, items):
        if isinstance(items[0], Tree):
            return Opts([])
        return Opts(items)

    def cmd_default(self, name, arguments):
        opts = dict()
        flags = set()
        args = []
        for arg in arguments:
            if isinstance(arg, Opts):
                for opt_arg in arg.items:
                    if type(opt_arg) == tuple:
                        opts[opt_arg[0]] = opt_arg[1]
                    else:
                        flags.add(opt_arg)
            else:
                args.append(arg)
        return (name, args, opts, flags)

    def cmd_sft_default(self, args):
        if args[0] == "clopen":
            name = "clopen"
        else:
            name = "sft"
        return self.cmd_default(name, args[1:])

    def cmd_sft_open_forbs(self, args):
        if args[0] == "clopen":
            name = "clopen"
        else:
            name = "sft"
        (name, pos_args, opts, flags) = self.cmd_default(name, args)
        return (name, [pos_args[1], pos_args[2:]], opts, flags)

    def cmd_sft_open_open_forbs(self, args):
        if args[0] == "clopen":
            name = "clopen"
        else:
            name = "sft"
        (name, pos_args, opts, flags) = self.cmd_default(name, args)
        forbs = []
        forb = dict()
        for item in pos_args[2:]:
            if type(item) == tuple:
                forb[item[0]] = item[1]
            else:
                #semicolon -> new forb
                forbs.append(forb)
                forb = dict()
        if forb:
            forbs.append(forb)
        return (name, [pos_args[1], forbs], opts, flags)

    def cmd_info(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("info", args)
        return (name, [pos_args], opts, flags)

    def cmd_contains(self, args):
        return self.cmd_default("contains", args)

    def cmd_equals(self, args):
        return self.cmd_default("equal", args)

    def cmd_show_formula(self, args):
        return self.cmd_default("show_formula", args)

    def cmd_topology_default(self, args):
        return self.cmd_default("topology", args)

    def cmd_topology_open_edges(self, args):
        return self.cmd_default("topology", [args])

    def top_edge(self, args):
        return tuple(args)

    def cmd_nodes_default(self, args):
        return self.cmd_default("nodes", args)

    def cmd_nodes_open(self, args):
        #print("nodes open", args)
        return self.cmd_default("nodes", [args])

    def cmd_alph_default(self, args):
        return self.cmd_default("alphabet", args)

    def cmd_alph_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("alphabet", args)
        return (name, [pos_args], opts, flags)

    def cmd_alph_opts(self, items):
        #print("cmd_alph_opts", items)
        opts = []
        while items:
            opts.append(tuple(items[:2]))
            items = items[2:]
        return Opts(opts)

    def cmd_blockmap_sym(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("block_map", args)
        label, *rules = pos_args 
        return (name, [label, [rules[2*i:2*i+2] for i in range(len(rules)//2)]], opts, flags)

    def cmd_blockmap_node_sym(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("block_map", args)
        label, *rules = pos_args 
        return (name, [label, [rules[3*i:3*i+3] for i in range(len(rules)//3)]], opts, flags)

    def cmd_compose_default(self, args):
        return self.cmd_default("compose", args)

    def cmd_compose_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("compose", args)
        return (name, [pos_args[0], pos_args[1:]], opts, flags)

    def cmd_dimension(self, args):
        return self.cmd_default("dim", args)

    def cmd_spacetime(self, args):
        return self.cmd_default("spacetime_diagram", args)

    def cmd_has_retraction(self, args):
        return self.cmd_default("has_post_inverse", args)

    def cmd_compute_forbs(self, args):
        return self.cmd_default("compute_forbidden_patterns", args)

    def cmd_set_weights_default(self, args):
        return self.cmd_default("set_weights", args)

    def cmd_set_weights_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("set_weights", args)
        return (name, [dict(pos_args)], opts, flags)

    def cmd_min_density_default(self, args):
        return self.cmd_default("minimum_density", args)

    def cmd_min_density_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("minimum_density", args)
        return (name, [pos_args[0], pos_args[1:]], opts, flags)

    def cmd_density_bound_single_default(self, args):
        return self.cmd_default("density_lower_bound", args)

    def cmd_density_bound_multi_default(self, args):
        return self.cmd_default("density_lower_bound", args)

    def cmd_density_bound_single_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("density_lower_bound", args)
        label = pos_args.pop(0)
        trans_vecs = []
        while pos_args:
            arg = pos_args.pop(0)
            if arg == ";":
                break
            else:
                trans_vecs.append(arg)
        nhood_nvecs = pos_args
        return (name, [label, [trans_vecs, nhood_nvecs]], opts, flags)

    def cmd_density_bound_multi_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("density_lower_bound", args)
        label, *specs = pos_args
        return (name, [label, specs], opts, flags)

    def cmd_density_bound_multi_open_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("density_lower_bound", args)
        label, *specs = pos_args
        return (name, [label, [specs[2*i:2*i+2] for i in range(len(specs)//2)]], opts, flags)

    def cmd_empty(self, args):
        return self.cmd_default("empty", args)

    def cmd_ca_ball_default(self, args):
        return self.cmd_default("compute_CA_ball", args)

    def cmd_ca_ball_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("compute_CA_ball", args)
        return (name, [pos_args[0], pos_args[1:]], opts, flags)

    def cmd_save_env(self, args):
        return self.cmd_default("save_environment", args)

    def cmd_load_env(self, args):
        return self.cmd_default("load_environment", args)

    def cmd_preimage(self, args):
        return self.cmd_default("preimage", args)

    def cmd_fixed_points(self, args):
        return self.cmd_default("fixed_points", args)

    def cmd_intersection_default(self, args):
        return self.cmd_default("intersection", args)

    def cmd_intersection_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("intersection", args)
        return (name, [pos_args[0], pos_args[1:]], opts, flags)

    def cmd_product_default(self, args):
        return self.cmd_default("product", args)

    def cmd_product_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("product", args)
        return (name, [pos_args[0], pos_args[1:]], opts, flags)

    def cmd_product_opts(self, items):
        args = []
        for i in range(len(items)//2):
            label, val = items[i*2:i*2+2]
            if label == "tracks":
                args.append(("tracks", val))
            if label == "env":
                args.append(("env", val))
        return Opts(args)

    def cmd_relation(self, args):
        return self.cmd_default("relation", args)

    def cmd_relation_opts(self, items):
        if items:
            return Opts([("tracks", items[0])])
        else:
            return Opts([])

    def cmd_sofic(self, args):
        return self.cmd_default("sofic1D", args)

    def cmd_minimize(self, args):
        return self.cmd_default("minimize", args)

    def cmd_trace(self, args):
        return self.cmd_default("trace", args)

    def cmd_union_default(self, args):
        return self.cmd_default("union", args)

    def cmd_union_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("union", args)
        return (name, [pos_args[0], pos_args[1:]], opts, flags)

    def cmd_language(self, args):
        return self.cmd_default("language", args)

    def cmd_determinize(self, args):
        return self.cmd_default("determinize", args)

    def cmd_sofic_image(self, args):
        return self.cmd_default("sofic_image", args)

    def cmd_regexp(self, args):
        return self.cmd_default("regexp", args)

    def cmd_find_automatic(self, args):
        return self.cmd_default("find_automatic_conf", args)

    def cmd_restrict_codomain(self, args):
        return self.cmd_default("restrict_codomain", args)

    def cmd_tiler(self, args):
        return self.cmd_default("tiler", args)

    def cmd_tiler_opts(self, items):
        opts = []
        while items:
            label = items.pop(0)
            if label in ["x_periodic", "y_periodic"]:
                opts.append(label)
            else:
                data = items.pop(0)
                opts.append((label, data))
        return Opts(opts)

    def cmd_graph(self, args):
        return self.cmd_default("graph", args)

    def cmd_run(self, args):
        return self.cmd_default("run", args)

    def cmd_load_forbs(self, args):
        return self.cmd_default("load_forbidden_patterns", args)

    def cmd_image_intersects(self, args):
        return self.cmd_default("image_intersects", args)

    def cmd_show_conf(self, args):
        return self.cmd_default("show_conf", args)

    def cmd_show_parsed(self, args):
        return self.cmd_default("show_parsed", args)

    def cmd_show_forbs(self, args):
        return self.cmd_default("show_forbidden_patterns", args)

    def cmd_show_graph(self, args):
        return self.cmd_default("show_graph", args)

    def cmd_show_envinronment(self, args):
        return self.cmd_default("show_environment", args)

    def cmd_compare_sft_pairs(self, args):
        return self.cmd_default("compare_sft_pairs", args)

    def cmd_compare_sft_pairs_eq(self, args):
        return self.cmd_default("compare_sft_pairs_equality", args)

    def cmd_entropy_upper_default(self, args):
        return self.cmd_default("entropy_upper_bound", args)

    def cmd_entropy_upper_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("entropy_upper_bound", args)
        return (name, [pos_args[0], pos_args[1:]], opts, flags)

    def cmd_entropy_lower_default(self, args):
        return self.cmd_default("entropy_lower_bound", args)

    def cmd_entropy_lower_open(self, args):
        (name, pos_args, opts, flags) = self.cmd_default("entropy_lower_bound", args)
        label = pos_args.pop(0)
        border_periods = []
        while True:
            per = pos_args.pop(0)
            if per == ";":
                break
            border_periods.append(per)
        return (name, [label, border_periods, pos_args], opts, flags)

    def cmd_tile_box(self, args):
        return self.cmd_default("tile_box", args)

    def cmd_keep_tiling(self, args):
        return self.cmd_default("keep_tiling", args)

    def start(self, cmds):
        return list(cmds)

parser = Lark(griddy_grammar, parser="earley")

def parse_griddy(program):
    return GriddyTransformer().transform(parser.parse(program))

def test():
    prog = """
    %sft test @verbose onesided=[0 1] {(0,0):1 (0,1):0}
    %sft test2 (0,0):1; (0,1):0; @verbose (1,0):0
    """
    res = parse_griddy(prog)
    for cmd in res:
        print(cmd)

if __name__ == "__main__":
    test()
