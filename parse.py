import sys
import os.path
import math
from lark import Lark
from lark.indenter import PythonIndenter
from lark.visitors import Transformer

kwargs = dict(postlex=PythonIndenter(), start='file_input', maybe_placeholders=False)

python3_parser = Lark.open("python.lark", rel_to=__file__, parser="lalr", **kwargs)

class IfToCOQ():
    def __init__(self, transform):
        self.condition = transform["condition"]
        self.block = transform["block"]
        self.elif_ = transform["elif"]
        self.else_ = transform["else"]
        
        # if:
        self.translation = f"match {self.condition["lhe"]} with\n| {self.condition["rhe"]} => {self.block[0]["expression"]}"
        # elif:
        for elif_ in self.elif_: 
            self.translation = self.translation + f"\n| {elif_["condition"]["rhe"]} => {elif_["block"][0]["expression"]}"
        # else:
        self.translation = self.translation + f"\n| _ => {self.else_["block"][0]["expression"]}\nend."

    def __str__(self):
        return self.translation

class ForToCOQ():
    def __init__(self, transform):
        self.iterable = transform["iterable"]
        self.range = transform["range"]
        self.block = transform["block"]
        
        # Definition:
        self.translation = "Fixpoint for_loop {A : Type}\n\t(init : A)\n\t(start end : nat)\n\t(body : nat -> A -> A)\n\t: A :=\n\tif start <? end then\n\t\tfor_loop (body start init) (start + 1) end body\n\telse\n\t\tinit\n\n"
        
        # range()
        start = int(self.range["parameters"][0]) if len(self.range["parameters"]) > 1 else 0
        stop = int(self.range["parameters"][1]) if len(self.range["parameters"]) == 2 else int(self.range["parameters"][0])
        step = int(self.range["parameters"][2]) if len(self.range["parameters"]) == 3 else 1
        end = start + math.floor((stop - start - 1)/step) * step

        # Operation:
        self.translation = self.translation + f"Definition for_loop_operation (n : nat) : nat :=\n\tfor_loop 0 {str(end)} (n + 1) (fun {self.iterable} {self.block[0]["variable"]} => {self.block[0]["value"]["lhe"]} {self.block[0]["value"]["operator"]} {self.block[0]["value"]["rhe"]})\n\n"

    def __str__(self):
        return self.translation

class WhileToCOQ():
    def __init__(self, transform):
        self.condition = transform["condition"]
        self.block = transform["block"]
        
        # Definition:
        self.translation = f"Fixpoint while_loop ({self.condition["lhe"]} : nat) : nat :=\n\tif {self.condition["lhe"]} {self.condition["operator"]}? {self.condition["rhe"]} then\n\t\twhile_loop ({self.block[0]["value"]["lhe"]} {self.block[0]["value"]["operator"]} {self.block[0]["value"]["rhe"]})\n\telse\n\t\t{self.condition["lhe"]}.\n"

    def __str__(self):
        return self.translation

class PythonToCOQ(Transformer):
    visit_tokens = True

    def flag_stmt(self, args):
        marker, content = args
        return {
            "type": "flag",
            "content": content
        }

    def number(self, args):
        return args[0].value

    def string(self, args):
        return args[0].value[1:-1].replace('\\"', '"')

    def name(self, args):
        return args[0].value

    def comp_op(self, args):
        return args[0].value

    def var(self, args):
        return args[0]

    def list_(self, args):
        return args

    def set_(self, args):
        return args

    def comparison(self, args):
        return {
            "lhe": args[0],
            "operator": args[1],
            "rhe": args[2]
        }
    
    def return_stmt(self, args):
        return {
            "type": "return",
            "expression": args[0]
        }
    
    def suite(self, args):
        return args
    
    def elif_(self, args):
        return {
            "type": "elif",
            "condition": args[0],
            "block": args[1],
        }
    
    def elifs(self, args):
        return args
    
    def else_(self, args):
        return {
            "type": "else",
            "block": args[0],
        }
    
    def assign(self, args):
        return args
    
    def arith_expr(self, args):
        return {
            "lhe": args[0],
            "operator": args[1].value,
            "rhe": args[2]
        }

    def assign_stmt(self, args):
        return {
            "type": "assignment",
            "variable": args[0][0],
            "value": args[0][1],
        }

    def parameters(self, args):
        return [x for x in filter(lambda x : x != None, args)]

    def arguments(self, args):
        return args

    def funcdef(self, args):
        return {
            "type": "function",
            "name": args[0],
            "parameters": args[1],
            "block": args[3],
        }

    def funccall(self, args):
        return {
            "type": "function",
            "name": args[0],
            "parameters": args[1]
        }

    def if_stmt(self, args):
        return {
            "type": "if",
            "condition": args[0],
            "block": args[1],
            "elif": args[2] if 2 < len(args) else None,
            "else": args[3] if 3 < len(args) else None,
        }

    def for_stmt(self, args):
        return {
            "type": "for",
            "iterable": args[0],
            "range": args[1],
            "block": args[2]
        }

    def while_stmt(self, args):
        return {
            "type": "while",
            "condition": args[0],
            "block": args[1]
        }
    
    def file_input(self, args):
        print(args)
        blocks = []
        for transform in args:
            match transform["type"]:
                case "if":
                    blocks.append(str(IfToCOQ(transform)))
                case "for":
                    blocks.append(str(ForToCOQ(transform)))
                case "while":
                    blocks.append(str(WhileToCOQ(transform)))
                case _:
                    blocks.append("")
        return blocks

def _read(fn, *args):
    kwargs = {'encoding': 'iso-8859-1'}
    with open(fn, *args, **kwargs) as f:
        return f.read()

if __name__ == '__main__':
    input_filepath = sys.argv[1]

    if not os.path.isfile(input_filepath):
        exit(f"Error: '{input_filepath}' not found.")
        
    output_filepath = sys.argv[2]

    output_file = open(output_filepath, "w")
    if os.path.isfile(output_filepath):
        output_file.truncate(0)

    parse_tree = python3_parser.parse(_read(input_filepath) + "\n")
    # print(parse_tree.pretty())
    for block in PythonToCOQ().transform(parse_tree):
        output_file.write(block)