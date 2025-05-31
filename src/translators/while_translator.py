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
            translation += f"Fixpoint while_loop_{self.flags["ID"]} ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} : nat) (fuel : nat) {"{struct fuel}"} : nat :=\n\tmatch fuel with\n\t| O => {self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]}\n\t| S fuel' =>\n\t\tif {self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} <? 10 then\n\t\t\twhile_loop_5 ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} + 1) fuel'\n\t\telse {self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]}\n\tend.\n\n"
        elif scenario == "str":
            # Definition:
            translation += f"Fixpoint while_loop_str_{self.flags["ID"]} ({self.block[0]["variable"]} : string) ({self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} : nat) (fuel : nat) {"{struct fuel}"} : string :=\n\tmatch fuel with\n\t| O => {self.block[0]["variable"]}\n\t| S fuel' =>\n\t\tif {self.condition["lhe"] if isinstance(self.condition["lhe"], str) else self.condition["lhe"]["variable"]} {self.condition["operator"]}? {self.condition["rhe"]} then\n\t\t\twhile_loop_str_{self.flags["ID"]} ({self.block[0]["variable"]} ++ \"{self.block[0]["value"]["rhe"]}\"%string) ({self.block[1]["variable"]} {self.block[1]["value"]["operator"]} {self.block[1]["value"]["rhe"]}) fuel'\n\t\telse\n\t\t\t{self.block[0]["variable"]}\n\tend.\n\n"
        else:
            sys.exit("WhileToCOQ Error: Unsupported scenario type")
        
        return translation

    def __str__(self):
        return self.translation