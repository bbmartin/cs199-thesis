import math
import sys

from .base import BaseTranslator


class ForToCOQ(BaseTranslator):
    
    def translate(self):
        self.supported_range_functions = ["range"]
        self.iterable = self.transform["iterable"]
        self.range = self.transform["range"]
        self.block = self.transform["block"]
        
        self.translation = self._build_fixpoint_definition()

        if self.range["type"] == "function":
            self._handle_function_range()
        elif self.range["type"] == "assignment":
            self._handle_assignment_range()
        else:
            sys.exit("ForToCOQ Error: Unknown token used as range")
    
    def _build_fixpoint_definition(self):
        return ("Fixpoint for_loop {A : Type}\n"
                "\t(init : A)\n"
                "\t(start end : nat)\n"
                "\t(body : nat -> A -> A)\n"
                "\t: A :=\n"
                "\tif start <? end then\n"
                "\t\tfor_loop (body start init) (start + 1) end body\n"
                "\telse\n"
                "\t\tinit\n\n")
    
    def _handle_function_range(self):
        if self.range["name"] == "range":
            self._handle_range_function()
        else:
            sys.exit("ForToCOQ Error: Unsupported function used as range")
    
    def _handle_range_function(self):
        params = self.range["parameters"]
        start = int(params[0]) if len(params) > 1 else 0
        stop = int(params[1]) if len(params) == 2 else int(params[0])
        step = int(params[2]) if len(params) == 3 else 1
        end = start + math.floor((stop - start - 1)/step) * step
        
        block_var = self._get_block_variable()
        block_lhe = self._get_block_lhe()
        block_op = self.block[0]["value"]["operator"]
        block_rhe = self._get_block_rhe()
        
        operation = (f"Definition for_loop_operation (n : nat) : nat :=\n"
                    f"\tfor_loop {block_lhe} 0 {str(end + 1)} "
                    f"(fun {self.iterable} {block_var} => "
                    f"{block_lhe} {block_op} {block_rhe})\n\n")
        
        self.translation += operation
    
    def _handle_assignment_range(self):
        # TODO: Implement translation for 'for i in list' type loops
        pass
    
    def _get_block_variable(self):
        var = self.block[0]["variable"]
        return var if isinstance(var, str) else var["variable"]
    
    def _get_block_lhe(self):
        lhe = self.block[0]["value"]["lhe"]
        return lhe if isinstance(lhe, str) else lhe["variable"]
    
    def _get_block_rhe(self):
        rhe = self.block[0]["value"]["rhe"]
        return rhe if isinstance(rhe, str) else rhe["variable"]