import math
import os.path
import re

from lark import Lark
from lark.indenter import PythonIndenter
from lark.visitors import Transformer

kwargs = dict(postlex=PythonIndenter(), start='file_input', maybe_placeholders=False)

python3_parser = Lark.open("python.lark", rel_to=__file__, parser="lalr", **kwargs)

class IfToCOQ():
    def __init__(self, transform, flags):
        self.condition = transform["condition"]
        self.block = transform["block"]
        self.elif_ = transform["elif"]
        self.else_ = transform["else"]
        self.flags = flags

        # Possible Values
        self.translation = "Inductive A : Type :=\n"
        for pv in self.flags["possible_values"]:
            self.translation += f"\t| {str(pv)}\n"
        
        # if:
        self.translation += f"\nDefinition if_struct ({self.condition["lhe"]} : A) : A :=\n\tmatch {self.condition["lhe"]} with\n\t| {self.condition["rhe"]} => {self.__get_rhe_val(self.block[0])}"
        # elif:
        for elif_ in self.elif_: 
            self.translation += f"\n\t| {elif_["condition"]["rhe"]} => {self.__get_rhe_val(elif_["block"][0])}"
        # else:
        self.translation += f"\n\t| _ => {self.__get_rhe_val(self.else_["block"][0])}\n\tend.\n\n"

    def __get_rhe_val(self, block):
        match block["type"]:
            case "assignment":
                if not isinstance(block["value"], dict):
                    return block["value"]
                else:
                    match block["value"]["type"]:
                        case "arith_expr":
                            return " ".join([str(block["value"]["lhe"]), str(block["value"]["operator"]), str(block["value"]["rhe"])])
                        case _:
                            sys.exit("IfToCOQ Error: Unknown scenario type")
            case "return_stmt":
                return block["expression"]
            case _:
                sys.exit("IfToCOQ Error: Unknown block type")

    def __str__(self):
        return self.translation

class ForToCOQ():

    def __init__(self, transform, flags):
        self.supported_range_functions = ["range"]
        self.iterable = transform["iterable"]
        self.range = transform["range"]
        self.block = transform["block"]
        self.flags = flags
        
        # Definition:
        self.translation = "Fixpoint for_loop {A : Type}\n\t(init : A)\n\t(start end : nat)\n\t(body : nat -> A -> A)\n\t: A :=\n\tif start <? end then\n\t\tfor_loop (body start init) (start + 1) end body\n\telse\n\t\tinit\n\n"
        
        if self.range["type"] == "function":
            match self.range["name"]:
                case "range":
                    # range()
                    start = int(self.range["parameters"][0]) if len(self.range["parameters"]) > 1 else 0
                    stop = int(self.range["parameters"][1]) if len(self.range["parameters"]) == 2 else int(self.range["parameters"][0])
                    step = int(self.range["parameters"][2]) if len(self.range["parameters"]) == 3 else 1
                    end = start + math.floor((stop - start - 1)/step) * step
                    
                    init_var = next(
                        (var for var in self.flags["variables"] if var.get("variable") == self.block[0]["value"]["lhe"]),
                        None
                    )

                    # Operation:
                    self.translation = self.translation + f"Definition for_loop_operation (n : nat) : nat :=\n\tfor_loop {init_var["value"] if init_var is not None else '0'} 0 {str(end + 1)} (fun {self.iterable} {self.block[0]["variable"]} => {self.block[0]["value"]["lhe"]} {self.block[0]["value"]["operator"]} {self.block[0]["value"]["rhe"]})\n\n"
                case _:
                    sys.exit("ForToCOQ Error: Unsupported function used as range")
        elif self.range["type"] == "assignment":
            #TODO: Handle cases like 'for i in list'
            pass
        else:
            sys.exit("ForToCOQ Error: Unknown token used as range")
        

    def __str__(self):
        return self.translation

class WhileToCOQ():
    def __init__(self, transform, flags):
        self.condition = transform["condition"]
        self.block = transform["block"]
        self.flags = flags
        
        # Definition:
        self.translation = f"Fixpoint while_loop ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} : nat) : nat :=\n\tif {self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} {self.condition["operator"]}? {self.condition["rhe"]} then\n\t\twhile_loop ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} {self.block[0]["value"]["operator"]} {self.block[0]["value"]["rhe"]})\n\telse\n\t\t{self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]}.\n\n"

    def __str__(self):
        return self.translation

class PythonToCOQ(Transformer):
    visit_tokens = True
    variables = []
    flags = []

    def flag_stmt(self, args):
        marker, content = args

        # Flags:
        #   '#s<n>:' => Scenario (int, list, or str manipulation)
        #   '#v<n>:' => Variables (for context)
        #   '#p<n>:' => Possible Variables (in the form of a set)
        #
        # Model:
        # {
        #   "type": "flag",
        #   "scenario": (value is a str that can either be <int, str, or list>),
        #   "variables": (list of variables that were assigned earlier and is used for context),
        #   "possible_values": (set of possible values)
        # }

        flag_type = None
        match = None
        if "s" in marker:
            flag_type = "s"
            match = re.search(r'#s(\d+):', marker)
        elif "v" in marker:
            flag_type = "v"
            match = re.search(r'#v(\d+):', marker)
        elif "p" in marker:
            flag_type = "p"
            match = re.search(r'#p(\d+):', marker)
        else:
            sys.exit("PythonToCOQ Error: Unknown flag type")
        
        index = int(match.group(1))
        if index < 0:
            sys.exit("PythonToCOQ Error: Invalid flag index")
        
        if index >= len(self.flags) or self.flags[index] is None:
            curr = len(self.flags)
            while curr <= index:
                self.flags.append(None)
                curr += 1
            self.flags[index] = {
                "type": "flag",
                "scenario": None,
                "variables": [],
                "possible_values": None
            }

        match flag_type:
            case "s":
                self.flags[index]["scenario"] = content
            case "v":
                self.flags[index]["variables"].append(content)
            case "p":
                self.flags[index]["possible_values"] = content
            case _:
                sys.exit("PythonToCOQ Error: Invalid flag type")
        
        # print("Flags: ", self.flags)
        return self.flags[index]

    def number(self, args):
        try:
            return int(args[0].value)
        except ValueError:
            return sys.exit("PythonToCOQ Error: Invalid number value")
        

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
        return set(args)

    def comparison(self, args):
        return {
            "type": "comparison",
            "lhe": args[0],
            "operator": args[1],
            "rhe": args[2]
        }
    
    def return_stmt(self, args):
        return {
            "type": "return_stmt",
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
            "type": "arith_expr",
            "lhe": args[0],
            "operator": args[1].value,
            "rhe": args[2],
        }

    def assign_stmt(self, args):
        variable = args[0][0]
        value = args[0][1]
        data_type = None
        match value:
            case int():
                data_type = "int"
            case float():
                data_type = "float"
            case str():
                data_type = "str"
            case list():
                data_type = "list"
            case set():
                data_type = "set"
            case dict():
                # TODO: Change in the future to allow for dict objects
                if "type" in value:
                    match value["type"]:
                        case "assignment":
                            data_type = value["data_type"]
                        case "arith_expr":
                            lhe_var = next(
                                (var for var in self.variables if var.get("variable") == value["lhe"]),
                                None
                            )
                            rhe_var = next(
                                (var for var in self.variables if var.get("variable") == value["rhe"]),
                                None
                            )

                            if lhe_var is not None:
                                data_type = lhe_var["data_type"]
                            elif rhe_var is not None:
                                data_type = rhe_var["data_type"]
                            else:
                                sys.exit(f"PythonToCOQ Error: Variables '{value["lhe"]}' and '{value["rhe"]}' have no known data types")
                        case _:
                            sys.exit("PythonToCOQ Error: Unsupported scenario type")
            case _:
                sys.exit("PythonToCOQ Error: Unsupported data type")
        
        variable = {
            "type": "assignment",
            "data_type": data_type,
            "variable": variable,
            "value": value,
        }

        exists = next(
            (var for var in self.variables if var.get("variable") == variable),
            None
        )
        if (exists is None):
            self.variables.append(variable)

        return variable

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
        # print(args)
        return {
            "type": "for",
            "iterable": args[0],
            "range": args[1],
            "block": args[2]
        }

    def while_stmt(self, args):
        # print(args)
        return {
            "type": "while",
            "condition": args[0],
            "block": args[1]
        }
    
    def file_input(self, args):
        blocks = []
        # Filter out certain code blocks
        ignore_list = ["flag", "assignment"]
        transforms = list(filter(lambda x: x["type"] not in ignore_list, args))
        # print("transforms: ", transforms)
        for transform in transforms:
            pass_flags = self.flags[transforms.index(transform)] if transforms.index(transform) < len(self.flags) else []
            print("Passed flags: ", pass_flags)
            match transform["type"]:
                case "if":
                    blocks.append(str(IfToCOQ(transform, pass_flags)))
                case "for":
                    blocks.append(str(ForToCOQ(transform, pass_flags)))
                case "while":
                    blocks.append(str(WhileToCOQ(transform, pass_flags)))
                case _:
                    blocks.append("")
        GenerateTheorem(args)

        return blocks, GenerateTheorem(args)

def _read(fn, *args):
    kwargs = {'encoding': 'iso-8859-1'}
    with open(fn, *args, **kwargs) as f:
        return f.read()
    
def GenerateTheorem(parsed_ast):
    theorem = "No recognizable theorem pattern found."
    for node in parsed_ast:
        if node["type"] == "for":
            loop_var = node["iterable"]
            loop_range = node["range"]
            if loop_range["name"] == "range":
                n = int(loop_range["parameters"][0])

                for stmt in node["block"]:
                    if stmt["type"] == "assignment":
                        lhs = stmt["variable"]
                        rhs = stmt["value"]

                        if (isinstance(rhs, dict) and
                            rhs["lhe"] == lhs and
                            rhs["operator"] == "+" and
                            rhs["rhe"] == loop_var):
                            
                            theorem = write_arithmetic_summation_theorem(n)

                        if (isinstance(rhs, dict) and
                            rhs["lhe"] == lhs and
                            rhs["operator"] == "*" and
                            rhs["rhe"] == loop_var):

                            theorem = write_arithmetic_product_theorem(n)

    return theorem

def write_arithmetic_summation_theorem(n):
  theorem = """
Theorem sum_first_n :
  forall (n : nat),
    loop n 0 = n * (n + 1) / 2.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. 
    unfold loop at 1.
  ring.
Qed.
"""
  return theorem

def write_arithmetic_product_theorem(n):
  theorem = """"""
  return theorem

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
    blocks, theorem = PythonToCOQ().transform(parse_tree)
    for block in blocks:
        output_file.write(block)

    output_file.write(theorem)
    output_file.close()