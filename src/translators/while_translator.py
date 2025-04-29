from .base import BaseTranslator


class WhileToCOQ(BaseTranslator):
    
    def translate(self):
        self.condition = self.transform["condition"]
        self.block = self.transform["block"]
      
        lhe = self.condition["lhe"]
        lhe_value = lhe if isinstance(lhe, str) else lhe["variable"]
        
        self.translation = (
            f"Fixpoint while_loop ({lhe_value} : nat) : nat :=\n"
            f"\tif {lhe_value} {self.condition['operator']}? {self.condition['rhe']} then\n"
            f"\t\twhile_loop ({lhe_value} {self.block[0]['value']['operator']} "
            f"{self.block[0]['value']['rhe']})\n"
            f"\telse\n"
            f"\t\t{lhe_value}.\n"
        )