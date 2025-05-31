import math
import sys


class ForToCOQ():

    def __init__(self, transform, flags):
        # print("Transform: ", transform)

        self.supported_range_functions = ["range"]
        self.iterable = transform["iterable"]
        self.range = transform["range"]
        self.block = transform["block"]
        self.flags = flags
        
        # Definition:
        self.translation = self.__get_translation(self.flags["scenario"])
        
    def __get_translation(self, scenario):
        translation = ""
        
        # print(self.flags, "\n\n")

        # int
        if scenario == "int":
            if self.range["type"] == "function":
                match self.range["name"]:
                    case "range":
                        translation += "Definition for_loop" + "_" + str(self.flags["ID"]) + " {A : Type}\n\t(start end_ : nat)\n\t(body : nat -> A -> A)\n\t(init : A) : A :=\n\tlet fix helper remaining current init :=\n\t\tmatch remaining with\n\t\t| O => init\n\t\t| S rem =>\n\t\t\tif current <? end_ then\n\t\t\t\thelper rem (current + 1) (body current init)\n\t\t\telse\n\t\t\t\tinit\n\t\tend\n\tin helper (end_ - start) start init.\n\n"

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
                        translation += f"Definition for_loop_operation_{self.flags["ID"]} (n : nat) : nat :=\n\tfor_loop_{self.flags["ID"]} {init_var["value"] if init_var is not None else '0'} {str(end + 1)} (fun {self.iterable} {self.block[0]["variable"]} => {self.block[0]["value"]["lhe"]} {self.block[0]["value"]["operator"]} {self.block[0]["value"]["rhe"]}) n.\n\n"
                    case _:
                        sys.exit("ForToCOQ Error: Unsupported function used as range")
            elif self.range["type"] == "assignment":
                match self.range["data_type"]:
                    case "list":
                        # Definition:
                        translation += "Fixpoint for_loop_list" + "_" + str(self.flags["ID"]) + " {A B : Type}\n\t(op : A -> B -> B)\n\t(init : B)\n\t(lst : list A)\n: B :=\n\tmatch lst with\n\t| [] => init\n\t| x :: xs => for_loop_list" + "_" + str(self.flags["ID"]) + " op (op x init) xs\n\tend.\n\n"

                        init_var = next(
                            (var for var in self.flags["variables"] if var.get("variable") == self.block[0]["value"]["lhe"]),
                            None
                        )

                        if init_var is None:
                            sys.exit(f"ForToCOQ Error: Unknown variable '{self.block[0]["value"]["lhe"]}'")

                        # Operation
                        operation = f"(fun x acc => acc {self.block[0]["value"]["operator"]} x)"
                        translation += f"Definition for_loop_list_operation_{self.flags["ID"]} (nums : list nat) : nat :=\n\tfor_loop_list_{self.flags["ID"]} {operation} {init_var["value"]} nums.\n\n"
                    case _:
                        sys.exit("ForToCOQ Error: Unknown data type for range object")
            else:
                sys.exit("ForToCOQ Error: Unknown token used as range")
        # str
        elif scenario == "str":
            # Definition
            translation += "Definition for_loop" + "_" + str(self.flags["ID"]) + " {A : Type}\n\t(start end_ : nat)\n\t(body : nat -> A -> A)\n\t(init : A) : A :=\n\tlet fix helper remaining current init :=\n\t\tmatch remaining with\n\t\t| O => init\n\t\t| S rem =>\n\t\t\tif current <? end_ then\n\t\t\t\thelper rem (current + 1) (body current init)\n\t\t\telse\n\t\t\t\tinit\n\t\tend\n\tin helper (end_ - start) start init.\n\n"

            if self.range["type"] == "assignment":
                match self.range["data_type"]:
                    case "list":
                        init_var = next(
                            (var for var in self.flags["variables"] if var.get("variable") == self.block[0]["value"]["lhe"]),
                            None
                        )

                        if init_var is None:
                            sys.exit(f"ForToCOQ Error: Unknown variable '{self.block[0]["value"]["lhe"]}'")
                        
                        list_var = next(
                            (var for var in self.flags["variables"] if var.get("data_type") == 'list'),
                            None
                        )

                        if list_var is None:
                            sys.exit(f"ForToCOQ Error: No list variable found to be used in translation.")
                        
                        # Converting the list variable into a definition to be used in the for_loop_operation
                        translation += "Definition list_strings : list string := ["
                        for el in list_var["value"]:
                            if el == list_var["value"][-1]:
                                translation += f"\"{el}\"%string].\n"
                            else:
                                translation += f"\"{el}\"%string; "

                        # Operation
                        if self.block[0]["value"]["operator"] == "+":
                            translation += f"Definition for_loop_operation_{self.flags["ID"]} : string :=\n\t@for_loop_{self.flags["ID"]} string 0 (List.length list_strings)\n\t\t(fun ({self.iterable} : nat) (acc : string) =>\n\t\t\tString.append acc (nth {self.iterable} list_strings \"\"%string))\n\t\t\"{init_var["value"] if init_var is not None else ""}\"%string.\n\n"
                        else:
                            sys.exit(f"ForToCOQ Error: Unsupported operation for string manipulation.")
                    case _:
                        sys.exit("ForToCOQ Error: Unknown data type for range object")
            else:
                sys.exit("ForToCOQ Error: Unknown token used as range")
        else:
            sys.exit("ForToCOQ Error: Unsupported scenario type")
        
        return translation

    def __str__(self):
        return self.translation