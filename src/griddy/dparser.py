"""
parse takes a string which represents a full program
in our language, and parses the entire program

token means string or integers or whatever
name is a string
"""

from fractions import Fraction
import parsy as p
from general import *
from enum import Enum, Flag, auto
from functools import reduce, wraps

### Top-level parsing functions

def parse_griddy(code):
    "Parse a Griddy file. Return a list of commands or raise a ParseError."
    return (whitespace >> griddy_file).parse(code)
    
def parse_formula(code):
    "Parse a FO formula."
    return (quantified | formula).parse(code)

### Common utilities

def many_strict(parser):
    """Parse zero or more times, return results in a list.
       Fail if the parser fails and consumes input.
       The purpose is to give better error messages than parser.many()."""

    @p.Parser
    def many_strict_parser(stream, index):
        values = []
        result = None
        while True:
            result = parser(stream, index).aggregate(result)
            if result.status:
                values.append(result.value)
                index = result.index
            elif result.furthest > index:
                return result
            else:
                return p.Result.success(index, values).aggregate(result)

    return many_strict_parser

# Whitespace and comments
whitespace = p.regex(r'(\s|--.*((\r|\n)+|$))*')

def lexeme(p):
    "p followed by whitespace."
    return p << whitespace

# Parentheses    
lparen = lexeme(p.string('('))
rparen = lexeme(p.string(')'))
lbracket = lexeme(p.string('['))
rbracket = lexeme(p.string(']'))
lbrace = lexeme(p.string('{'))
rbrace = lexeme(p.string('}'))
# Separators
period = lexeme(p.string('.'))
comma = lexeme(p.string(','))
colon = lexeme(p.string(':'))
semicolon = lexeme(p.string(';'))

# Protected keywords
keyword = p.regex(r'(let|letnum|in|dist|subst)(\W|$)')

# Range of nonnegative integers; "inf" means no upper bound
@p.generate
def natural_range():
    start = yield natural
    end = yield (lexeme(p.string('-')) >> natural.optional(default="inf")).optional(start)
    return (start, end)

# Set of nonnegative integers (union of ranges)
natural_set = natural_range.sep_by(comma, min=1)

# Stuff to be defined later
set_expr = p.forward_declaration()
formula = p.forward_declaration()
quantified = p.forward_declaration()
regexp = p.forward_declaration()

### Command arguments

class ArgType(Flag):
    LABEL = auto()
    NUMBER = auto()
    SIMPLE_LIST = auto()
    SETTER_LIST = auto()
    PATTERN_LIST = auto()
    NESTED_LIST = auto()
    PATTERN = auto()
    MAPPING = auto() # mainly for weights
    FORMULA = auto()
    TOPOLOGY_KEYWORD = auto()

# Unsigned integer (can be used as label)
natural = lexeme(p.regex(r'0|[1-9]\d*').map(int))
# Negative integer
neg_nat = (p.string('-') >> natural).map(lambda n: -n)
# Signed integer
integer = natural | neg_nat
# Fraction
@p.generate("fraction")
def fraction():
    numerator = yield integer
    maybe_denominator = yield (lexeme(p.string('/')) >> natural).optional()
    if maybe_denominator is None:
        return numerator
    else:
        return Fraction(numerator, maybe_denominator)

# Label of constant (alphabet symbol or node): any alphanumeric sequence
const_label = lexeme(keyword.should_fail("keyword") >> p.regex(r'\w+')).desc("node or symbol name")
# Label of variable (variable in formula, command, or Diddy object like SFT or block map): must begin with non-digit
var_label = lexeme(keyword.should_fail("keyword") >> p.regex(r'[a-zA-Z]\w*')).desc("variable name")

topology_keyword = lexeme(p.regex(r'line|grid|square|squaregrid|king[0-9]*|kinggrid|triangle|trianglegrid|hex|hexgrid|CR')).desc("topology name")
graph_keyword = lexeme(p.regex(r'Aleshin|none')).desc("graph name")

# Optional argument / setter; value is a signed number or label
# Type checking is not done at parse time
@p.generate("optional argument / setter")
def set_arg_value():
    arg_name = yield var_label
    yield lexeme(p.string('='))
    arg_value = yield fraction | const_label | nested_list | nested_mapping(node_name | const_label, flat_value | nested_list)
    return (arg_name, arg_value)

# Optinal argument / setter from given names
def set_arg_value_of(name_dict):
    @p.generate
    def setter():
        arg_name, kind = yield p.alt(*(lexeme(p.string(name)) >> p.success((name, item))
                                       for (name, item) in name_dict.items()))
        yield lexeme(p.string('='))
        arg_value = yield kind
        return (arg_name, arg_value)
    return setter
    
# Node name: period-separated sequence of labels
node_name = const_label.sep_by(period, min=1).map(tuple)
#node_name = (label | natural).sep_by(period, min=1).map(lambda items: items[0] if len(items) == 1  else tuple(items))

# Vector or node vector
@p.generate("vector")
def vector():
    yield lparen
    nums = yield integer.sep_by(comma << p.peek(integer >> (comma | semicolon | rparen)))
    maybe_node = yield (semicolon >> node_name).optional()
    yield rparen
    if maybe_node is None:
        return tuple(nums)
    else:
        return tuple(nums + [maybe_node])
    
# Pattern/mapping pair
def mapping_pair(key, value):
    @p.generate("mapping pair")
    def part():
        the_key = yield key
        #print("the key", the_key)
        yield colon
        val = yield value
        #print("val", val)
        return (the_key, val)
    return part

# Mapping: list of key:value pairs, parsed into a dict
def mapping(key, value):
    return (lbrace >> mapping_pair(key, value).many().map(dict) << rbrace).desc("mapping")
def nested_mapping(key, value):
    @p.generate
    def nested_map():
        the_map = yield mapping(key, value | nested_mapping(key, value))
        return the_map
    return nested_map
# Mapping without braces
def open_mapping(key, value):
    return mapping_pair(key, value).many().map(dict).desc("mapping")
# Nested mapping with default value
def nested_default_mapping(key, value, default=None):
    @p.generate
    def nested():
        yield lbrace
        elems = yield (mapping_pair(key, nested_default_mapping(key, value, default) | value) | key.map(lambda k: (k, default))).many().map(dict)
        yield rbrace
        return elems
    return nested
        

# Pattern: vector:label/number mapping
pattern = mapping(vector, const_label|fraction)
open_pattern = open_mapping(vector, const_label|fraction)

# Flat value
flat_value = vector | set_arg_value.desc("setter") | fraction | node_name | pattern

# List of specified items
def list_of(item):
    @p.generate
    def lst_of():
        yield lbracket
        vals = yield item.many()
        yield rbracket
        return vals
    return lst_of

# Possibly open list of specified items
def olist_of(item):
    @p.generate
    def olst_of():
        br = yield lbracket.optional()
        vals = yield item.many()
        if br:
            yield rbracket
        return vals
    return olst_of

# List (possibly nested) of numbers, vectors, labels, setters and patterns
@p.generate("list")
def nested_list():
    yield lbracket
    vals = yield (quantified | flat_value | nested_list).many()
    yield rbracket
    return vals
    
# List without braces
open_nested_list = nested_list.many().desc("list")

# Command argument parser
# An argument spec is either:
# a) a parser, to be used as such;
# b) ("LIST", a1, ..., an), to be parsed as a possibly heterogenous list of length n; or
# c) ("MANY", a), to be parsed as a list of a's of arbitrary length.
# Trailing lists of depth 1 can be parsed in "list mode" as semicolon-separated open lists.
# A trailing list of depth 2 can be parsed in "nested list mode" as semicolon-separated open lists.
# Setting opts=flags=False prevents their parsing.

# TODO: fix this
# add separate modes for top level and list item
def cmd_args(cmd, opts, flags, arg_specs, mode="normal", depth=0):
    if opts is None:
        opts = dict()
    if flags is None:
        flags = set()
    #print("cmdargs outer", cmd.name, arg_specs, mode)
    @p.generate
    def parse_arg():
        nonlocal cmd, opts, flags, arg_specs, mode, depth
        debug_print = False
        if debug_print: print("cmdargs inner", cmd.name, arg_specs, mode, depth)
        
        # Parse options and flags
        while opts != False and flags != False:
            maybe_flag = yield (p.string('@') >> var_label).desc("flag").optional()
            if maybe_flag is not None:
                if maybe_flag not in cmd.flags:
                    return p.fail("valid flag for {}".format(cmd.name))
                flags.add(maybe_flag)
                continue
            the_opts = cmd.opts
            if type(the_opts) == list:
                maybe_opt = yield set_arg_value.optional()
                if maybe_opt is not None:
                    if maybe_opt[0] not in cmd.opts:
                        return p.fail("valid option for {}".format(cmd.name))
                    name, value = maybe_opt
                    opts[name] = value
                    continue
            elif type(the_opts) == dict:
                maybe_opt = yield set_arg_value_of(the_opts).optional()
                if maybe_opt is not None:
                    name, value = maybe_opt
                    opts[name] = value
                    continue
            break
        
        if not arg_specs:
            if mode == "normal":
                yield p.peek(p.string('%') | p.eof)
            return []
        elif mode == "normal":
            modes = []
            if all(type(item) == list and item[0] in ["LIST","MANY"]
                   for item in arg_specs):
                modes.append("list")
            if len(arg_specs) == 1 and type(arg_specs[0]) == list and\
               arg_specs[0][0] in ["LIST","MANY"] and\
               all(type(r) == list and r[0] in ["LIST","MANY"] for r in arg_specs[0][1:]):
                modes.append("nested")
            if len(arg_specs) == 1 and type(arg_specs[0]) == list and\
               arg_specs[0][0] == "MANY" and\
               type(arg_specs[0][1]) == list and arg_specs[0][1][0] == "MAP":
                modes.append("map list")
            if debug_print:print("possible modes", modes)
            if modes:
                res = yield p.alt(*[cmd_args(cmd, opts, flags, arg_specs, mode=newmode)
                                    for newmode in modes]).optional()
                if res is not None:
                    return res
                
        if type(arg_specs[0]) == list and arg_specs[0][0] == "OR":
            ret = yield p.alt(*[cmd_args(cmd, opts, flags, [term]+arg_specs[1:],
                                         mode=mode, depth=depth+1)
                                for term in arg_specs[0][1:]])
            return ret
        # Modes:
        # normal -> parse a single argument normally
        # list -> parse all remaining arguments as open lists, separated by semicolons
        # nested -> parse the one remaining argument as open list of semicolon-separated open lists
        # map list -> parse the one remaining argument as open list of semicolon-separated open patterns
        # map in list -> parse one such mapping pair
        if mode in ["list", "sublist"]:
            if debug_print:print("mode", mode)
            ret = []
            for (i,spec) in enumerate(arg_specs):
                if spec[0] == "LIST":
                    lst = yield p.seq(*[cmd_args(cmd, opts, flags, [item], mode="item", depth=depth+1) for item in spec[1:]])
                elif spec[0] == "MANY":
                    if debug_print:print("mode list many, spec", spec)
                    lst = yield cmd_args(cmd, opts, flags, [spec[1]], mode="item", depth=depth+1).many()
                if i < len(arg_specs)-1:
                    yield semicolon
                if debug_print:print("got", lst, "as list")
                #if lst[-1] == []:
                #    lst = lst[:-1]
                ret.append([item[0] for item in lst])
            if debug_print:print("got", ret, "from mode", mode)
            if mode == "list":
                yield semicolon.optional() >> p.peek(p.string('%') | p.eof)
            return ret
        elif mode == "nested":
            spec = arg_specs[0]
            if spec[0] == "LIST":
                ret = yield p.seq(*[(cmd_args(cmd, opts, flags, [subspec], mode="sublist", depth=depth+1) << semicolon.optional()) for subspec in spec[1:]])
            elif spec[0] == "MANY":
                ret = yield cmd_args(cmd, opts, flags, [spec[1]], mode="sublist", depth=depth+1).sep_by(semicolon)
                yield semicolon.optional() >> p.peek(p.string('%') | p.eof)
            if debug_print:print("got", ret, "from nested")
            return [[y for [y] in ret]]
        elif mode == "map list":
            spec = arg_specs[0]
            ret = yield cmd_args(cmd, opts, flags, [spec[1]], mode="map in list", depth=depth+1).many().sep_by(semicolon)
            yield semicolon.optional() >> p.peek(p.string('%') | p.eof)
            if debug_print:print("ret", ret, "from map list")
            ret = [[{key : val for [(key, val)] in item} for item in ret]]
            if debug_print:print("new ret", ret, "from map list")
            return ret
        elif mode == "map in list":
            spec = arg_specs[0]
            arg = yield mapping_pair(spec[1], spec[2])
            return [arg]
        elif mode in ["normal", "item"]:
            # Parse one argument and recurse
            spec = arg_specs[0]
            rest = arg_specs[1:]
            if isinstance(spec, p.Parser):
                if debug_print:print("normal plain")
                # We have a plain parser -> parse one item with it
                arg = yield spec
                if debug_print:print("got", arg, "from normal plain")
            elif type(spec) != list:
                raise Exception("Bad command spec: {}".format(spec))
            elif spec[0] == "LIST":
                if debug_print:print("normal list")
                yield lbracket
                arg = yield cmd_args(cmd, False, False, spec[1:], mode="item", depth=depth+1)
                yield rbracket
            elif spec[0] == "MANY":
                if debug_print:print("normal many")
                yield lbracket
                arg = yield cmd_args(cmd, False, False, [spec[1]], mode="item", depth=depth+1).many()
                yield rbracket
                arg = [x[0] for x in arg]
            elif spec[0] == "MAP":
                if debug_print:print("normal map")
                arg = yield mapping(spec[1], spec[2])
                if debug_print:print("got from normal map", arg)
            else:
                raise Exception("Unknown command argument spec: {}".format(spec))
            rest_args = yield cmd_args(cmd, opts, flags, rest, mode=mode, depth=depth+1)
            if debug_print:print("returning", [arg]+rest_args, "from normal")
            return [arg] + rest_args
    return parse_arg

### Command parser

class Command:
    "A container for a Griddy command definition."
    
    def __init__(self, name, pos_args, opts=None, flags=None, aliases=None):
        self.name = name
        self.pos_args = pos_args
        if opts is None:
            opts = []
        self.opts = opts
        if flags is None:
            flags = []
        self.flags = flags
        if aliases is None:
            aliases = []
        self.aliases = aliases

# List of commands
# Each entry has command names, positional arguments and types, optional arguments (whose values are flat), and flags
commands = [
    # Setting up the environment
    Command("alphabet",
            [["OR",
              ["MANY", const_label],
              mapping(node_name, const_label|list_of(const_label))]],
            opts = {"default" : list_of(const_label)},
            aliases = ["alph"]),
    Command("topology",
            [["OR",
              topology_keyword,
              # legacy edges, with are dim+1-length vectors with nodes at the end
              ["MANY", ["LIST", const_label, vector, vector]],
              # modern edges, with a cell movement instruction, and then zero or two node specifications
              ["MANY", ["LIST", const_label, vector]],
              ["MANY", ["LIST", const_label, vector, vector, vector]]]]),
    Command("dim",
            [natural],
            opts = ["onesided"],
            aliases = ["dimension"]),
    Command("graph",
            [graph_keyword]),
    
    Command("nodes",
            [["OR",
              ["MANY", node_name],
              nested_default_mapping(const_label, const_label)]],
            aliases = ["vertices"]),
    Command("set_weights",
            [mapping(node_name, fraction) | open_mapping(node_name, fraction)]),
    Command("save_environment",
            [var_label]),
    Command("load_environment",
            [var_label]),
    Command("run",
            [var_label]),

    # Defining objects
    Command("sft",
            [var_label,
             ["OR",
              quantified,
              ["MANY", ["MAP", vector, const_label]]]],
            aliases = ["SFT"],
            opts = ["onesided"],
            flags = ["simplify", "verbose"]),

    # This is copy/paste from SFT, could be an alias but
    # as far as I know we can't detect which cmd was used then.
    Command("clopen",
            [var_label,
             ["OR",
              quantified,
              ["MANY", ["MAP", vector, const_label]]]],
            opts = ["onesided"],
            flags = ["simplify", "verbose"]),
    
    Command("sofic1D",
            [var_label, var_label],
            aliases = ["sofic1d"],
            flags = ["forbs", "onesided", "verbose"]),
    Command("trace",
            [var_label,
             var_label,
             ["MANY", natural],
             ["MANY",
              ["OR",
               var_label, # dir
               ["LIST", var_label, natural], # per p
               ["LIST", # [a b]
                ["OR", ["LIST", var_label, natural], ["LIST", var_label, natural, natural]],
                ["OR", ["LIST", var_label, natural], ["LIST", var_label, natural, natural]]]]]],
            opts = ["extra_rad"],
            flags = ["onesided", "verbose"]),
    Command("regexp",
            [var_label, regexp],
            flags = ["minimize", "verbose"]),
    Command("language",
            [var_label, var_label]),
    Command("compute_forbidden_patterns",
            [var_label],
            opts = ["radius", "filename"],
            flags = ["verbose"],
            aliases = ["calculate_forbidden_patterns"]),
    Command("load_forbidden_patterns",
            [var_label, var_label]),
    Command("determinize",
            [var_label]),
    Command("minimize",
            [var_label]),        
    Command("wang",
            [var_label, "tiles", nested_list], # TODO: figure out how this works
            opts = ["inverses"],
            flags = ["topology", "use_topology", "custom_topology"],
            aliases = ["Wang"]),
    Command("intersection",
            [var_label,
             ["MANY", var_label]]),
    Command("sofic_image",
            [var_label, var_label, var_label]),
    Command("union",
            [var_label,
             ["MANY", var_label]]),
    Command("product",
            [var_label,
             ["MANY", var_label]],
            opts = {"tracks" : list_of(const_label), "env" : var_label}),
    Command("block_map",
            [var_label,
             ["OR",
              ["MANY", ["LIST", const_label, quantified]],
              ["MANY", ["LIST", node_name, const_label, quantified]]]],
            opts = ["domain", "codomain"],
            flags = ["simplify", "verbose", "ignore_overlaps", "check_overlaps"],
            aliases = ["blockmap", "CA"]),
    Command("compose",
            [var_label,
             ["MANY", var_label]],
            flags = ["verbose"]),
    Command("restrict_codomain",
            [var_label, var_label]),
    Command("has_post_inverse",
            [var_label],
            opts = ["radius", "expect"],
            flags = ["verbose"],
            aliases = ["has_retraction"]),
    Command("image_intersects",
            [var_label, var_label],
            flags = ["verbose"]),
    Command("relation",
            [var_label, var_label],
            opts = {"tracks" : list_of(const_label)}),
    Command("preimage",
            [var_label, var_label, var_label]),
    Command("fixed_points",
            [var_label, var_label]),
    Command("spacetime_diagram",
            [var_label, var_label],
            opts = ["time_axis"],
            flags = ["twosided"],
            aliases = ["spacetime"]),
    
    # TFG stuff not implemented yet
    Command("TFG",
            [var_label, "nested list"], # TODO
            aliases = ["topological_full_group_element"]),

    # Printing objects' basic properties
    Command("show_conf",
            [var_label],
            flags = ["hide_contents"],
            aliases = ["print_conf"]),
    Command("show_formula",
            [var_label],
            aliases = ["print_formula"]),
    Command("show_parsed",
            [var_label],
            aliases = ["print_parsed"]),
    Command("show_forbidden_patterns",
            [var_label],
            aliases = ["print_forbidden_patterns"]),
    Command("show_graph",
            [var_label],
            aliases = ["print_graph"]),
    Command("show_environment",
            [],
            opts = ["sft"]),
    Command("info",
            [["MANY", var_label]],
            flags = ["verbose"]),

    # Comparing objects
    Command("empty",
            [var_label],
            opts = ["conf_name", "expect"],
            flags = ["verbose"]),
    Command("equal",
            [var_label, var_label],
            opts = ["method", "expect"],
            flags = ["verbose"],
            aliases = ["equals"]),
    Command("contains",
            [var_label, var_label],
            opts = ["method", "expect", "conf_name"],
            flags = ["verbose"],
            aliases = ["contain"]),
    Command("compare_sft_pairs", [],
            opts = ["method"],
            aliases = ["compare_SFT_pairs"]),
    Command("compare_sft_pairs_equality", [],
            opts = ["method"],
            aliases = ["compare_SFT_pairs_equality"]),
    Command("compute_CA_ball",
            [natural,
             ["MANY", var_label]],
            opts = ["filename"],
            aliases = ["calculate_CA_ball"]),

    # Analyzing dynamical properties
    Command("minimum_density",
            [var_label,
             ["MANY", vector]],
            opts = ["threads", "mode", "chunk_size", "symmetry", "print_freq_pop", "print_freq_cyc", "expect", "conf_name"],
            flags = ["verbose", "rotate"]),
    Command("density_lower_bound",
            [var_label,
             ["OR",
              ["MANY",
               ["LIST",
                ["MANY", vector],
                ["MANY", vector]]],
              ["LIST",
               ["MANY", vector],
               ["MANY", vector]]]],
            opts = ["radius", "print_freq", "expect", "save_constr", "load_constr"],
            flags = ["verbose", "show_rules"]),
    Command("entropy_upper_bound",
            [var_label,
             ["MANY", natural]],
            opts = ["radius"]),
    Command("entropy_lower_bound",
            [var_label,
             ["MANY", natural],
             ["MANY", natural]]),
    Command("TFG_loops",
            [var_label, var_label],
            aliases = ["topological_full_group_element_loops"]),
    Command("find_automatic_conf",
            [var_label, var_label],
            opts = ["arity", "extra_rad", "buffer_rad", "print_freq", "infer_print_freq", "mode", "backtrack_depth", "max_lookahead"],
            flags = ["verbose"]),

    # Visualization / finding individual tilings in SFT
    Command("tiler",
            [var_label],
            opts = {"x_size" : natural,
                    "y_size" : natural,
                    "node_offsets" : mapping(node_name, list_of(fraction)),
                    "pictures" : mapping(node_name, list_of(var_label)),
                    "gridmoves" : list_of(list_of(fraction)),
                    "topology" : var_label,
                    "initial" : var_label,
                    "colors" : mapping(const_label, list_of(natural)),
                    "hidden" : list_of(node_name)},
            flags = ["x_periodic", "y_periodic"]),
    Command("tile_box",
            [var_label, natural]),
    Command("keep_tiling",
            [var_label],
            opts = ["min", "max"]),

    # Technical commands
    Command("start_cache",
            [natural, natural]),
    Command("end_cache", [])
]

command_dict = {alias : cmd for cmd in commands for alias in [cmd.name] + cmd.aliases}


# Parse any command
@p.generate
def command():
    yield p.string('%')
    alias = yield var_label
    try:
        opts = dict()
        flags = set()
        cmd = command_dict[alias]
        com = yield cmd_args(cmd, opts, flags, cmd.pos_args)
        #print("parsed command", cmd.name, com, opts, flags)
        return cmd.name, com, opts, flags
    except KeyError:
        yield p.fail("valid command name")

# Parse a full Griddy file
griddy_file = many_strict(command)


### Formula parser

# Operator associativity
# Prefix, left and right are self-explanatory
# Flatten collects all arguments into a single list (the operator is associative)
# Chain joins the propositions with ANDs
class Assoc(Flag):
    PREFIX = auto()
    SUFFIX = auto()
    LEFT = auto() # unused for now
    RIGHT = auto()
    FLATTEN = auto()
    CHAIN = auto()
    STRICT_CHAIN = auto()
    
# Create a parser out of a precedence table
def expr_with_ops(prec_table, atomic, prec_index=0):

    if prec_index == len(prec_table):
        return atomic
        
    else:
        @p.generate
        def parse_the_expr():
            name, assoc, operators = prec_table[prec_index]
            #print("parsing", name, "expression, precedence", prec_index)
            parse_next = expr_with_ops(prec_table, atomic, prec_index=prec_index+1)
            if assoc == Assoc.PREFIX:
                # Parse a chain of prefix operators
                prefixes = yield p.alt(*operators).many()
                value = yield parse_next
                ret = reduce(lambda val, op: op(val), reversed(prefixes), value)
            if assoc == Assoc.SUFFIX:
                # Parse a chain of suffix operators
                value = yield parse_next
                suffixes = yield p.alt(*operators).many()
                ret = reduce(lambda val, op: op(val), suffixes, value)
            elif assoc == Assoc.LEFT:
                # Parse tokens separated by a left associative operator
                raise NotImplementedError
            elif assoc == Assoc.RIGHT:
                # Parse tokens separated by a right associative operator
                first = yield parse_next
                maybe_others = yield p.alt(*operators).bind(lambda op: parse_the_expr.map(lambda second: op(first, second))).optional()
                if maybe_others is not None:
                    #print("Parsed many", maybe_others, "at level", table_ix, assoc_name[table_ix])
                    ret = maybe_others
                else:
                    #print("Parsed one", first, "at level", table_ix, assoc_name[table_ix])
                    ret = first
            elif assoc == Assoc.FLATTEN:
                # Parse tokens separated by a flattening operator
                op_parser, op_func = operators
                values = yield parse_next.sep_by(op_parser, min=1)
                if len(values) > 1:
                    #print("Parsed many", values, "at level", table_ix, assoc_name[table_ix])
                    ret = op_func(values)
                else:
                    #print("Parsed one", values, "at level", table_ix, assoc_name[table_ix])
                    ret = values[0]
            elif assoc in Assoc.CHAIN | Assoc.STRICT_CHAIN:
                # Parse tokens separated by a chained operator
                first = yield parse_next
                maybe_others = yield p.alt(*operators).bind(lambda op: parse_next.map(lambda val: (op, val))).at_least(1 if assoc == Assoc.STRICT_CHAIN else 0)
                if len(maybe_others) == 1:
                    op, val = maybe_others[0]
                    #print("Parsed two", op(first, val), "at level", table_ix, assoc_name[table_ix])
                    ret = op(first, val)
                elif maybe_others:
                    propositions = ["AND"]
                    for (op, val) in maybe_others:
                        propositions.append(op(first, val))
                        first = val
                    #print("Parsed many", propositions, "at level", table_ix, assoc_name[table_ix])
                    ret = tuple(propositions)
                else:
                    #print("Parsed one", first, "at level", table_ix, assoc_name[table_ix])
                    ret = first
            #print("parsed", ret)
            return ret
        return parse_the_expr

# Alphabetic label
# strict_label = lexeme((keyword | p.regex(r'[AEO].*')).should_fail("keyword") >> p.regex(r'[a-zA-Z_]\w*')).desc("formula variable")

# Positional expression
pos_expr = p.seq(const_label,
                 (lexeme(p.string('.')) >> (const_label | vector | p.string('_')).desc("address")).many()).combine(lambda var, addrs: ("ADDR", var, *addrs) if addrs else var)

# List of positional expressions
pos_expr_list = lbracket >> pos_expr.many() << rbracket

## Set expressions (finite sets of nodes)

# Table of set operators
# The first operator binds the loosest
set_op_table = [
    ("set difference", Assoc.RIGHT, [lexeme(p.string('-')) >> p.success(lambda x, y: ("SETMINUS", x, y))]),
    ("set symmetric difference", Assoc.RIGHT, [lexeme(p.string('<>')) >> p.success(lambda x, y: ("SETSYMDIF", x, y))]),
    ("set union", Assoc.RIGHT, [lexeme(p.string('+')) >> p.success(lambda x, y: ("SETUNION", x, y))]),
    ("set intersection", Assoc.RIGHT, [lexeme(p.string('*')) >> p.success(lambda x, y: ("SETINTER", x, y))])
]

# Set literal
@p.generate
def set_literal():
    yield lbrace
    elems = yield pos_expr.sep_by(comma.optional(), min=1)
    yield rbrace
    return ("SET_LITERAL", elems)

# Neighborhood and ball modifiers
nhood_modifiers = lexeme(p.alt(p.string("o") >> p.success("OPEN"),
                               p.string("p") >> p.success("POSITIVE"),
                               p.string("n") >> p.success("NEGATIVE")).many())

# Neighborhoods (one argument)
@p.generate
def set_neighborhood():
    yield p.string("N")
    mods = yield nhood_modifiers
    arg = yield pos_expr.map(lambda pos: ("SET_LITERAL", [pos])) | set_expr
    return ("SET_NHOOD", mods, arg)

# Balls and spheres (two arguments)
@p.generate
def ball_or_sphere():
    func = yield p.alt(p.string("B") >> p.success("SET_BALL"),
                       p.string("S") >> p.success("SET_SPHERE"))
    mods = yield nhood_modifiers
    radius = yield natural
    arg = yield pos_expr.map(lambda pos: ("SET_LITERAL", [pos])) | set_expr
    return (func, mods, radius, arg)

# Shorthand for ball
@p.generate
def short_ball():
    node = yield pos_expr
    yield colon
    radius = yield natural
    return ("SET_BALL", [], radius, ("SET_LITERAL", [node]))

# A set expression
set_expr.become(expr_with_ops(set_op_table, set_literal | set_neighborhood | ball_or_sphere | short_ball | (lparen >> set_expr << rparen)))

## Logical expressions

# Distance operator: specify allowed distances between two nodes
@p.generate
def dist_operation():
    neg = yield p.string('!').optional()
    yield lexeme(p.string('~^'))
    dist_ranges = yield natural_set
    if neg:
        return lambda x, y: ("NOT", vectorize(lambda a, b: ("HASDIST", dist_ranges, a, b))(x, y))
    else:
        return vectorize(lambda x, y: ("HASDIST", dist_ranges, x, y))

# Vectorize binary proposition over lists of equal length
def vectorize(op):
    def vect_op(x, y):
        if type(x) == list and type(y) == list:
            return ("AND", *(op(a, b) for (a, b) in zip(x, y)))
        else:
            return op(x, y)
    return vect_op
    
# Chainable comparison operators
comp_table = [("node comparison", Assoc.STRICT_CHAIN,
               [lexeme(p.string('~~')) >> p.success(vectorize(lambda x, y: ("ISPROPERNEIGHBOR", x, y))),
                dist_operation,
                lexeme(p.string('~')) >> p.success(vectorize(lambda x, y: ("ISNEIGHBOR", x, y))),
                lexeme(p.string('=')) >> p.success(vectorize(lambda x, y: ("VALEQ", x, y))),
                lexeme(p.string('@')) >> p.success(vectorize(lambda x, y: ("POSEQ", x, y))),
                lexeme(p.string('!~~')) >> p.success(lambda x, y: ("NOT", vectorize(lambda a, b: ("ISPROPERNEIGHBOR", a, b))(x, y))),
                lexeme(p.string('!~')) >> p.success(lambda x, y: ("NOT", vectorize(lambda a, b: ("ISNEIGHBOR", a, b))(x, y))),
                lexeme(p.string('!=')) >> p.success(lambda x, y: ("NOT", vectorize(lambda a, b: ("VALEQ", a, b))(x, y))),
                lexeme(p.string('!@')) >> p.success(lambda x, y: ("NOT", vectorize(lambda a, b: ("POSEQ", a, b))(x, y)))])]

# Atomic proposition that compares nodes or lists of nodes
node_expr = expr_with_ops(comp_table, pos_expr) | expr_with_ops(comp_table, pos_expr_list)

# Function call
@p.generate("boolean variable or function call")
def bool_or_call():
    #print("parsing call")
    name = yield var_label
    args = yield (pos_expr | lparen >> formula << rparen).many()
    #print("parsed call", name, args)
    if args:
        return ("CALL", name, *args)
    else:
        return ("BOOL", name)

# Logical quantifier, potentially restricted
@p.generate
def quantified_formula():
    #print("parsing quantified")
    the_quantifier = yield p.alt(p.string("AC") >> p.success("CELLFORALL"),
                                 p.string("EC") >> p.success("CELLEXISTS"),
                                 p.string("OC") >> p.success("CELLORIGIN"),
                                 p.string("A") >> p.success("NODEFORALL"),
                                 p.string("E") >> p.success("NODEEXISTS"),
                                 p.string("O") >> p.success("NODEORIGIN")).desc("quantifier")
    yield whitespace#.optional()
    var = yield var_label
    restr = yield (lbracket >> set_expr << rbracket).optional()
    #print("parsed quantifier part", the_quantifier, var)
    the_formula = yield formula
    #print("parsed formula", the_formula)
    return (the_quantifier, var, restr, the_formula)

quantified.become(quantified_formula)

# Table of operators and their associativities
# The first operator binds the loosest, the last one the tightest
# Prefix expects a list of parsers that return a unary function
# Left, right and chain expect a list of parsers that return binary functions (TODO: maybe they should be pairs instead)
# Flatten expects a pair (parser, variable-arity function)
boolean_ops = [
    # Logical connectives
    ("implication", Assoc.RIGHT, [lexeme(p.string('->')) >> p.success(lambda x, y: ("IMP", x, y))]),
    ("equivalence", Assoc.CHAIN, [lexeme(p.string('<->')) >> p.success(lambda x, y: ("IFF", x, y))]),
    ("disjunction", Assoc.FLATTEN, (lexeme(p.string('|')), lambda xs: ("OR",) + tuple(xs))),
    ("conjunction", Assoc.FLATTEN, (lexeme(p.string('&')), lambda xs: ("AND",) + tuple(xs))),
    # Negation
    ("negation", Assoc.PREFIX, [lexeme(p.string('!')) >> p.success(lambda x: ("NOT", x))])
    ]

# A let-in definition
@p.generate
def let_expr():
    yield lexeme(p.string('let'))
    call = yield var_label.at_least(1)
    yield lexeme(p.string(':='))
    result = yield formula
    yield lexeme(p.string('in'))
    rest = yield formula
    return ("LET", tuple(call), result, rest)

# A substitution pair
@p.generate
def substitution_pair():
    the_node = yield pos_expr
    yield lexeme(p.string(':='))
    the_value = yield const_label
    return (the_node, the_value)

# A local substitution
@p.generate
def subst_expr():
    yield lexeme(p.string('subst'))
    subst_pairs = yield substitution_pair.at_least(1)
    subst = {node : value for (node, value) in subst_pairs}
    yield lexeme(p.string('in'))
    rest = yield formula
    return ("SUBSTITUTE", subst, rest)

num_expr = p.forward_declaration()

# A numeric let-in definition
@p.generate
def num_let_expr():
    yield lexeme(p.string('letnum'))
    var = yield var_label
    yield lexeme(p.string(':='))
    result = yield num_expr
    yield lexeme(p.string('in'))
    rest = yield formula
    return ("SETNUM", var, result, rest)

num_comp_op = p.alt(lexeme(p.string('==')) >> p.success(lambda a, b: ("NUM_EQ", a, b)),
                    lexeme(p.string('/=')) >> p.success(lambda a, b: ("NOT", ("NUM_EQ", a, b))),
                    lexeme(p.string('<=')) >> p.success(lambda a, b: ("NUM_LEQ", a, b)),
                    lexeme(p.string('<')) >> p.success(lambda a, b: ("NOT", ("NUM_LEQ", b, a))),
                    lexeme(p.string('>=')) >> p.success(lambda a, b: ("NUM_LEQ", b, a)),
                    lexeme(p.string('>')) >> p.success(lambda a, b: ("NOT", ("NUM_LEQ", a, b))))

# A numeric comparison
@p.generate
def num_comparison():
    expr = yield num_expr
    rest = yield p.seq(num_comp_op, num_expr).at_least(1)
    anded = []
    for (op, rhs) in rest:
        anded.append(op(expr, rhs))
        expr = rhs
    return ("AND", *anded)

# Binary numeric operations
# TODO: implement subtraction in a reasonable way
numeric_ops = [
    ("addition", Assoc.FLATTEN, (lexeme(p.string('+')), lambda xs: ("SUM",) + tuple(xs))),
    ("multiplication", Assoc.FLATTEN, (lexeme(p.string('*')), lambda xs: ("PROD",) + tuple(xs)))
    ]
    
# Unary numeric functions
numeric_funcs = [
    lexeme(p.string("abs")) >> p.success(lambda n: ("ABS", n))
    ]
    
# Numeric function call
@p.generate
def numeric_call():
    func = yield p.alt(*numeric_funcs)
    arg = yield num_expr
    return func(arg)

# Count true values in a list of formulas
@p.generate
def count_list():
    yield lexeme(p.string('#'))
    yield lbracket
    formulas = yield formula.at_least(1).map(lambda f: tuple(("TRUTH_AS_NUM", x) for x in f))
    yield rbracket
    return ("SUM",) + tuple(formulas)
    
# Count true values of a quantified variable
@p.generate
def count_quantified():
    yield lexeme(p.string('#'))
    var = yield var_label
    restr = yield lbracket >> set_expr << rbracket
    #print("parsed quantifier part", the_quantifier, var)
    the_formula = yield formula
    return ("NODECOUNT", var, restr, the_formula)
    
# Convert symbol of node into number
@p.generate
def sym_to_num():
    yield lexeme(p.string('#'))
    node = yield pos_expr
    return ("SYM_TO_NUM", node)

# Distance function for nodes
@p.generate
def distance_func():
    yield lexeme(p.string("dist"))
    node1 = yield pos_expr
    node2 = yield pos_expr
    return ("DISTANCE", node1, node2)

num_expr.become(expr_with_ops(numeric_ops, count_list | count_quantified | sym_to_num | distance_func | numeric_call | var_label.map(lambda s: ("NUM_VAR", s)) | integer.map(lambda n: ("CONST_NUM", n)) | lparen >> num_expr << rparen))

# A full formula
formula.become(expr_with_ops(boolean_ops, quantified | let_expr | subst_expr | num_let_expr | num_comparison | node_expr | bool_or_call | (lparen >> formula << rparen)))


### Regexp parser

# Language consisting of the empty word
empty_word_lang = lexeme(lparen) >> lexeme(rparen) >> p.success("EMPTYWORD")

# Language consisting of a single word
symbol_lang = (const_label.map(lambda sym: ("SYMBOL", sym)) | list_of(const_label).map(lambda syms: ("SYMBOLS", syms)))

# Regexp operation table
regexp_ops = [
    # Boolean ops
    ("union", Assoc.RIGHT, [lexeme(p.string("|")) >> p.success(lambda x, y: ("UNION", x, y))]),
    ("intersection", Assoc.RIGHT, [lexeme(p.string("&")) >> p.success(lambda x, y: ("ISECT", x, y))]),
    ("negation", Assoc.PREFIX, [lexeme(p.string("!")) >> p.success(lambda x: ("NOT", x))]),
    # Containment
    ("containment", Assoc.PREFIX, [lexeme(p.string("~")) >> p.success(lambda x: ("CONTAINS", x))]),
    # Concatenation
    ("concat", Assoc.RIGHT, [p.peek(regexp) >> p.success(lambda x, y: ("CONCAT", x, y))]),
    # Star
    ("star/plus", Assoc.SUFFIX, [lexeme(p.string("*")) >> p.success(lambda x: ("STAR", x)),
                                 lexeme(p.string("+")) >> p.success(lambda x: ("PLUS", x)),
                                 lexeme(p.string("?")) >> p.success(lambda x: ("UNION", "EMPTYWORD", x))])]

# Regular expression
regexp.become(expr_with_ops(regexp_ops, empty_word_lang | symbol_lang | (lparen >> regexp << rparen)))#.at_least(1).map(lambda auts: reduce(lambda x,y: ("CONCAT", x, y), auts)))

### Testing



#print(read_formula("0"))


"""
%SFT id_code
(x,y,0)=0 (x+1,y,0)=1
(x,y,0)=0 (x+1,y,0)=0
"""

"""
%set idcode Oo let c u v := v = 1 & u ~ v in   -- v is code word neighbor of u
       (Ed[o1] c o d) &              -- o must have some code word neighbor, and
       (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q)) -- any pair is separated
"""




s = """
%nodes 0
%dim 2
%topology grid
%alphabet 0 1
%set idcode Oo let c u v := v = 1 & u ~ v in   -- v is code word neighbor of u
       (Ed[o1] c o d) &              -- o must have some code word neighbor, and
       (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q)) -- any pair is separated
%density idcode
"""



"""
%set idcode Ao let c u v := v = 1 & u ~ v in -- v is code word neighbor of u
       (Ed[o1] c o d) &              -- o must have some code word neighbor, and
       (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q)) -- any pair is separated
"""

"""

"""

#parsed = parse(s)
#print(parsed)






