import sys


class WhileToCOQ():
    def __init__(self, transform, flags):
        self.condition = transform["condition"]
        self.block = transform["block"]
        self.flags = flags
        
        # Definition:
        self.translation = self.__get_translation(self.flags["scenario"])

    def __get_translation(self, scenario):
        translation = ""

        if scenario == "int":
            # Definition:
            translation += f"Fixpoint while_loop ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} : nat) : nat :=\n\tif {self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} {self.condition["operator"]}? {self.condition["rhe"]} then\n\t\twhile_loop ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} {self.block[0]["value"]["operator"]} {self.block[0]["value"]["rhe"]})\n\telse\n\t\t{self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]}.\n\n"
        elif scenario == "str":
            # Definition:
            translation += f"Fixpoint while_loop_str ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} : string) (count : nat) : string :=\n\tif count {self.condition["operator"]}? {self.condition["rhe"]} then\n\t\twhile_loop_str ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} ++ \"{self.block[0]["value"]["rhe"]}\"%string)\n\telse\n\t\t{self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]}.\n\n"
        else:
            sys.exit("WhileToCOQ Error: Unsupported scenario type")
        
        return translation

    def __str__(self):
        return self.translation