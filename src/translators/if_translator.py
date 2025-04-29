from .base import BaseTranslator


class IfToCOQ(BaseTranslator):
    
    def translate(self):
        self.condition = self.transform["condition"]
        self.block = self.transform["block"]
        self.elif_ = self.transform["elif"]
        self.else_ = self.transform["else"]
        
        lhe = self.condition["lhe"]
        lhe_value = lhe if isinstance(lhe, str) else lhe["variable"]
        
        self.translation = f"match {lhe_value} with\n| {self.condition['rhe']} => {self.block[0]['expression']}"
        
        if self.elif_:
            for elif_ in self.elif_:
                self.translation += f"\n| {elif_['condition']['rhe']} => {elif_['block'][0]['expression']}"
        
        self.translation += f"\n| _ => {self.else_['block'][0]['expression']}\nend."