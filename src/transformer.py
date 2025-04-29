import sys

from lark.visitors import Transformer

from src.theoremGenerator import TheoremGenerator

from .translators import ForToCOQ, IfToCOQ, WhileToCOQ


class PythonToCOQ(Transformer):
    
    visit_tokens = True
    
    def __init__(self):
        super().__init__()
        self.variables = []
        self.flags = []

    def flag_stmt(self, args):
        marker, content = args
        flag = {
            "type": "flag",
            "content": content
        }
        self.flags.append(flag)
        return flag

    def number(self, args):
        try:
            return int(args[0].value)
        except ValueError:
            try:
                return float(args[0].value)
            except ValueError:
                return sys.exit("PythonToCOQ Error: Invalid number value")
        
    def string(self, args):
        return args[0].value[1:-1].replace('\\"', '"')

    def name(self, args):
        return args[0].value

    def comp_op(self, args):
        return args[0].value

    def var(self, args):
        variable = next(
            (v for v in self.variables if v.get('variable') == args[0]),
            None
        )
        if variable == None:
            return args[0]
        else:
            return variable

    def list_(self, args):
        return args

    def set_(self, args):
        return args

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
            "rhe": args[2]
        }

    def assign_stmt(self, args):
        variable = args[0][0]
        value = args[0][1]
        data_type = None
        match args[0][1]:
            case int():
                data_type = "int"
            case float():
                data_type = "float"
            case str():
                data_type = "str"
            case list():
                data_type = "list"
            case dict():
                # TODO: Change in the future to allow for dict objects
                if "type" in value:
                    match value["type"]:
                        case "assignment":
                            data_type = value["data_type"]
                        case "arith_expr":
                            if "data_type" in value["lhe"]:
                                data_type = value["lhe"]["data_type"]
                            elif "data_type" in value["rhe"]:
                                data_type = value["rhe"]["data_type"]
                            else:
                                sys.exit("PythonToCOQ Error: Variables have no data type")
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
      return {
            "type": "while",
            "condition": args[0],
            "block": args[1]
      }
    
    def file_input(self, args):
        blocks = []
        print(args)
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
        theorem = TheoremGenerator().generate(args)
        return theorem, blocks