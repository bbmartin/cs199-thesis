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

        # int
        if scenario == "int":
            if self.range["type"] == "function":
                match self.range["name"]:
                    case "range":
                        translation += "Fixpoint for_loop {A : Type}\n\t(init : A)\n\t(start end : nat)\n\t(body : nat -> A -> A)\n\t: A :=\n\tif start <? end then\n\t\tfor_loop (body start init) (start + 1) end body\n\telse\n\t\tinit\n\n"

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
                        translation += f"Definition for_loop_operation (n : nat) : nat :=\n\tfor_loop {init_var["value"] if init_var is not None else '0'} 0 {str(end + 1)} (fun {self.iterable} {self.block[0]["variable"]} => {self.block[0]["value"]["lhe"]} {self.block[0]["value"]["operator"]} {self.block[0]["value"]["rhe"]})\n\n"
                    case _:
                        sys.exit("ForToCOQ Error: Unsupported function used as range")
            elif self.range["type"] == "assignment":
                match self.range["data_type"]:
                    case "list":
                        # Definition:
                        translation += "Fixpoint for_loop_list {A B : Type}\n\t(op : A -> B -> B)\n\t(init : B)\n\t(lst : list A)\n: B :=\n\tmatch lst with\n\t| [] => init\n\t| x :: xs => for_loop_list op (op x init) xs\n\tend.\n\n"

                        init_var = next(
                            (var for var in self.flags["variables"] if var.get("variable") == self.block[0]["value"]["lhe"]),
                            None
                        )

                        if init_var is None:
                            sys.exit(f"ForToCOQ Error: Unknown variable '{self.block[0]["value"]["lhe"]}'")

                        # Operation
                        operation = f"(fun x acc => acc {self.block[0]["value"]["operator"]} x)"
                        translation += f"Definition for_loop_list_operation (nums : list nat) : nat :=\n\tfor_loop_list {operation} {init_var["value"]} nums\n\n"
                    case _:
                        sys.exit("ForToCOQ Error: Unknown data type for range object")
            else:
                sys.exit("ForToCOQ Error: Unknown token used as range")
        # str
        elif scenario == "str":
            # Definition
            translation += "Fixpoint for_loop {A : Type}\n\t(init : A)\n\t(start end : nat)\n\t(body : nat -> A -> A)\n\t: A :=\n\tif start <? end then\n\t\tfor_loop (body start init) (start + 1) end body\n\telse\n\t\tinit\n\n"

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

                        if self.block[0]["value"]["operator"] != "+":
                            sys.exit("ForToCOQ Error: Unsupported string operation")

                        # Operation:
                        translation += f"Definition for_loop_operation : string :=\n\tfor_loop \"{init_var["value"] if init_var is not None else ""}\"%string {start} {str(end + 1)} (fun _ acc => acc ++ \"{self.block[0]["value"]["rhe"]}\"%string).\n\n"
                    case _:
                        sys.exit("ForToCOQ Error: Unsupported function used as range")
            elif self.range["type"] == "assignment":
                match self.range["data_type"]:
                    case "list":
                        init_var = next(
                            (var for var in self.flags["variables"] if var.get("variable") == self.block[0]["value"]["lhe"]),
                            None
                        )

                        if init_var is None:
                            sys.exit(f"ForToCOQ Error: Unknown variable '{self.block[0]["value"]["lhe"]}'")

                        # Operation
                        translation += f"Definition for_loop_operation : string :=\n\tfor_loop \"{init_var["value"] if init_var is not None else ""}\"%string 0 (length strings) (fun {self.iterable} acc => acc ++ (nth {self.iterable} strings \"\"%string)).\n\n"
                    case _:
                        sys.exit("ForToCOQ Error: Unknown data type for range object")
            else:
                sys.exit("ForToCOQ Error: Unknown token used as range")
        else:
            sys.exit("ForToCOQ Error: Unsupported scenario type")
        
        return translation

    def __str__(self):
        return self.translation