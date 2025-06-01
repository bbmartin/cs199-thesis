import sys

from lark.visitors import Transformer

from src.theoremGenerator import TheoremGenerator

from .translators import ForToCOQ, IfToCOQ, WhileToCOQ


class PythonToCOQ(Transformer):
    visit_tokens = True
    variables = []
    flags = []
    curr_flag_index = None

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
        #   "variables": (list of variables to be used for context),
        #   "possible_values": (set of possible values)
        # }

        flag_type = None
        match = None
        if "s" in marker:
            flag_type = "s"

            if (self.curr_flag_index is None):
                self.curr_flag_index = 0
            else:
                self.curr_flag_index += 1
            
            self.variables = []
        elif "v" in marker:
            flag_type = "v"
        elif "p" in marker:
            flag_type = "p"
        else:
            sys.exit("PythonToCOQ Error: Unknown flag type")
        
        index = self.curr_flag_index
        if index < 0:
            sys.exit("PythonToCOQ Error: Invalid flag index")
        
        if index >= len(self.flags) or self.flags[index] is None:
            curr = len(self.flags)
            while curr <= index:
                self.flags.append(None)
                curr += 1
            self.flags[index] = {
                "ID": self.curr_flag_index,
                "type": "flag",
                "scenario": None,
                "variables": None,
                "possible_values": None
            }

        match flag_type:
            case "s":
                self.flags[index]["scenario"] = content
            case "v":
                self.flags[index]["variables"] = content
            case "p":
                self.flags[index]["possible_values"] = content
            case _:
                sys.exit("PythonToCOQ Error: Invalid flag type")
        
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
    
    def factor(self, args):
        if '-' in args and len(args) == 2:
            return int(args[0].value + str(args[1]))
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

        existing_var = next(
            (var for var in self.variables if var.get("variable") == variable["variable"]),
            None
        )
        if (existing_var is None):
            self.variables.append(variable)
        else:
            self.variables[self.variables.index(existing_var)] = variable

        # Replace variable declarations in current flag
        var_dec = next(
            (var for var in self.flags[self.curr_flag_index]["variables"] if var == variable["variable"]),
            None
        )
        if var_dec is not None:
            flag_var_index = self.flags[self.curr_flag_index]["variables"].index(var_dec)
            self.flags[self.curr_flag_index]["variables"][flag_var_index] = variable

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
        range_ = args[1]
        if isinstance(range_, str) and range_ in [variable["variable"] for variable in self.variables]:
            range_ = next(
                (var for var in self.variables if var["variable"] == range_),
                None
            )

            if range_ is None:
                sys.exit("PythonToCOQ Error: Unknown range object")

        return {
            "type": "for",
            "iterable": args[0],
            "range": range_,
            "block": args[2]
        }

    def while_stmt(self, args):
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

        if len(transforms) < len(self.flags):
            sys.exit("PythonToCOQ Error: Flag count exceed the number of code blocks")

        for transform in transforms:
            pass_flags = self.flags[transforms.index(transform)] if transforms.index(transform) < len(self.flags) else []
            # print("Passed flags: ", pass_flags)
            match transform["type"]:
                case "if":
                    blocks.append(str(IfToCOQ(transform, pass_flags)))
                case "for":
                    blocks.append(str(ForToCOQ(transform, pass_flags)))
                case "while":
                    blocks.append(str(WhileToCOQ(transform, pass_flags)))
                case _:
                    blocks.append("")
        
        # Include any imports
        blocks.insert(0, "Require Import Arith.\nRequire Import Arith.Compare_dec.\nRequire Import List.\nRequire Import List String.\nRequire Import Recdef.\nRequire Import String.\nRequire Import ZArith.\nImport ListNotations.\n\n(* Translations *)\n")

        theorems = TheoremGenerator().generate(args)
        return theorems, blocks

