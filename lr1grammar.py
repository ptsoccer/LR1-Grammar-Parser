from __future__ import print_function
import itertools
import math
import re
from lr1generator import Production, is_token, is_nonterminal, build_parse_table

class TreeNode(object):
    def __init__(self, value, parent = None, children = None):
        self.value = value

        if children == None:
            self.children = []
        else:
            self.children = list(children)
            
        self.parent = parent

    def add_child(self, node):
        node.parent = self
        self.children.append(node)

    def add_children(self, nodes):
        for node in nodes:
            node.parent = self
            self.children.append(node)

    def print_postfix(self, pretext = ""):
        print("-+= " + str(self.value))
        pretext_inter = pretext + " |"
        pretext_final = pretext + "  "

        for i, child in enumerate(self.children):
            if i == len(self.children) - 1:
                print(pretext + " \\", end="")
                child.print_postfix(pretext_final)
            else:
                print(pretext_inter, end="")
                child.print_postfix(pretext_inter)

    def __repr__(self):
        return "TreeNode({0}, {1})".format(self.value, self.children)


def read_productions(production_file):
    contents = production_file.read()
    match = re.match("\s*(?P<initial_code>{([^}\"\']|(\".*?\")|[^}])*})?(?P<prods>.*)", contents, re.DOTALL)
    initial_code, prod_list = match.group("initial_code"), match.group("prods").strip()

    if not initial_code is None:
        initial_code = initial_code[1:-1]
    
    regex = re.compile("(?P<production>[^\n{]*)(?P<action>{([^}\"\']|(\".*?\")|[^}\n])*})")
    productions = list()
    actions = list()

    for production_line in prod_list.split("\n"):
        result = regex.match(production_line)
        items, action = result.group("production").split(), result.group("action")

        actions.append(action[1:-1].strip())
        productions.append(Production(items[0], items[1:]))

    return productions, actions, initial_code


def print_parse_table(table):
    tokens = list({sym for p in productions for sym in p.rhs
                   if is_token(sym)})
    nonterminals = list({sym for p in productions for sym in p.rhs
                         if is_nonterminal(sym)})

    item_num_space = int(math.log(len(table))) + 1
    
    print(" " * item_num_space + "".join("{:6}".format(token) for token in tokens) +
          " | " + "".join("{:6}".format(nt) for nt in nonterminals))

    format_string = "{:<" + str(item_num_space) + "}"

    for i, events in enumerate(table):
        out_str = format_string.format(i)
        
        for token in tokens:
            out_str += "{:6}".format("/".join(events[token]))
            
        out_str += "   "
        for nt in nonterminals:
            
            out_str += "{:6}".format("/".join(events[nt]))
            
        print(out_str)

def get_input():
    while True:
        line = raw_input()

        if (len(line)) == 0:
            while True:
                yield "$"
        else:
            tokens = line.split()

            for token in tokens:
                tmp_tok = token

                while len(tmp_tok) > 0:
                    if tmp_tok[0].isalpha():
                        next_tok = "".join(itertools.takewhile(lambda ch: ch.isalpha() or ch.isdigit(), tmp_tok))
                        yield next_tok
                        tmp_tok = tmp_tok[len(next_tok):]
                    #elif tmp_tok[0].isdigit():
                        #next_tok = "".join(itertools.takewhile(lambda ch: ch.isdigit(), tmp_tok))
                        #yield next_tok
                        #tmp_tok = tmp_tok[len(next_tok):]
                    else:
                        yield tmp_tok[0]
                        tmp_tok = tmp_tok[1:]

def execute_semantic_action(semantic_vars, symbol_values, reduced_production, action):
    semantic_vars["val"] = symbol_values[-len(reduced_production.rhs):]
    semantic_vars["ret"] = None

    exec action in semantic_vars
    
    return semantic_vars["ret"]

def parse_inputs(table):
    while True:
        print("Enter input:")
        inp = iter(get_input())
        next_ch = next(inp)
        
        state_stack = [0]
        parse_tree = []
        symbol_values = list()
        semantic_vars = dict()

        if not initial_code is None:
            exec initial_code in semantic_vars

        try:
            while True:
                state = state_stack[-1]
                events = table[state].get(next_ch, [])

                if len(events) == 0:
                    raise SyntaxError("No rule for \"{0}\" in state {1}".format(next_ch,state))
                elif len(events) > 1:
                    print("\n".join(str(item) for item in item_sets[state]))
                    raise SyntaxError("More than one action for \"{0}\" in state {1} ({2})".format(next_ch, state,
                                                                                                   "/".join(events)))

                event = events[0]
                if event[0] == "S":
                    new_state = int(event[1:])
                    
                    state_stack.append(new_state)
                    symbol_values.append(next_ch)
                    parse_tree.append(TreeNode(next_ch))
                    
                    next_ch = next(inp)
                elif event[0] == "R":
                    reduction_number = int(event[1:])
                    reduce_action = actions[reduction_number]
                    reduce_production = productions[reduction_number]
                    reduce_nonterminal = reduce_production.lhs

                    reduce_length = len(reduce_production.rhs)

                    new_node = TreeNode(reduce_nonterminal)
                    if reduce_length > 0:
                        for node in parse_tree[-reduce_length:]:
                            new_node.add_child(node)

                    reduction_val = execute_semantic_action(semantic_vars, symbol_values,
                                                            reduce_production, reduce_action)

                    for i in xrange(reduce_length):
                        parse_tree.pop()
                        state_stack.pop()
                        symbol_values.pop()

                    parse_tree.append(new_node)
                    symbol_values.append(reduction_val)

                    if reduce_nonterminal == productions[0].lhs:
                        parse_tree[0].print_postfix()
                        print("In language")
                        break

                    new_state = state_stack[-1]
                    events = table[new_state].get(reduce_nonterminal, [])

                    new_state = int(events[0])
                    state_stack.append(new_state)
        except SyntaxError as e:
            print("Not in language ({0})".format(e))
    

if __name__ == "__main__":
    with file("productions", "r") as f:
        productions, actions, initial_code = read_productions(f)

    print('\n'.join(str(p) for p in productions))

    #for i, item_set in enumerate(item_sets):
        #print("*" * 10 + "Item Set " + str(i) + "*" * 10)
        #print('\n'.join(str(item) for item in item_set))

    parse_table, item_sets = build_parse_table(productions)
    print_parse_table(parse_table)

    parse_inputs(parse_table)
