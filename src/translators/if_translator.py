import sys


class IfToCOQ():
    def __init__(self, transform, flags):
        self.condition = transform["condition"]
        self.block = transform["block"]
        self.elif_ = transform["elif"]
        self.else_ = transform["else"]
        self.flags = flags

        self.translation = self.__get_translation(self.flags["scenario"])

    def __get_translation(self, scenario):
        translation = ""
        
        # int
        if scenario == "int":
            comparison_operators = {
                "<": "Z.ltb",
                "<=": "Z.leb",
                ">": "Z.gtb",
                ">=": "Z.geb",
                "==": "Z.eqb",
                "!=": "negb"
            }
            
            # Definition
            translation += f"Definition if_struct ({self.condition["lhe"]} : Z) : Z :=\n"
            
            # If
            if self.condition["operator"] != "!=":
                translation += f"\tif {comparison_operators[self.condition["operator"]]} x ({self.condition["rhe"]}) then\n\t\t{self.__get_rhe_val(self.block[0])}{"." if self.else_ is None else ""}\n"
            else:
                translation += f"\tif {comparison_operators[self.condition["operator"]]} (Z.eqb x ({self.condition["rhe"]})) then\n\t\t{self.__get_rhe_val(self.block[0])}{"." if self.else_ is None else ""}\n"
            
            # Elif
            for elif_ in self.elif_:
                if self.condition["operator"] != "!=":
                    translation += f"\telse if {comparison_operators[elif_["condition"]["operator"]]} x ({elif_["condition"]["rhe"]}) then\n\t\t{self.__get_rhe_val(elif_["block"][0])}\n"
                else:
                    translation += f"\telse if {comparison_operators[elif_["condition"]["operator"]]} (Z.eqb x ({elif_["condition"]["rhe"]})) then\n\t\t{self.__get_rhe_val(elif_["block"][0])}\n"
            
            # Else
            translation += f"\telse\n\t\t{self.__get_rhe_val(self.else_["block"][0])}.\n\n"
        # str
        elif scenario == "str":
            # Definition
            translation += f"Definition if_struct ({self.condition["lhe"]} : string) : string :=\n"
            
            # If
            if self.condition["operator"] == "==":
                translation += f"\tif string_dec x \"{self.condition["rhe"]}\"%string then\n\t\t\"{self.__get_rhe_val(self.block[0])}\"%string{"." if self.else_ is None else ""}\n"
            elif self.condition["operator"] == "!=":
                translation += f"\tif negb (string_dec x \"{self.condition["rhe"]}\"%string) then\n\t\t\"{self.__get_rhe_val(self.block[0])}\"%string{"." if self.else_ is None else ""}\n"
            else:
                sys.exit("IfToCOQ Error: Unsupported comparison operator for strings (if)")
            
            # Elif
            for elif_ in self.elif_:
                if self.condition["operator"] == "==":
                    translation += f"\telse if string_dec x \"{elif_["condition"]["rhe"]}\"%string then\n\t\t\"{self.__get_rhe_val(elif_["block"][0])}\"%string\n"
                elif self.condition["operator"] == "!=":
                    translation += f"\telse if negb (string_dec x \"{elif_["condition"]["rhe"]}\"%string) then\n\t\t\"{self.__get_rhe_val(elif_["block"][0])}\"%string\n"
                else:
                    sys.exit("IfToCOQ Error: Unsupported comparison operator for string (elif)")
            
            # Else
            translation += f"\telse\n\t\t\"{self.__get_rhe_val(self.else_["block"][0])}\"%string.\n\n"
        else:
            sys.exit("IfToCOQ Error: Unknown scenario type")

        return translation
    
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