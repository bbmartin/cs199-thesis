def GenerateTheorem(parsed_ast):
    for node in parsed_ast:
        if node["type"] == "for":
            loop_var = node["iterable"]
            loop_range = node["range"]
            if loop_range["name"] == "range":
                n = int(loop_range["parameters"][0])

                for stmt in node["block"]:
                    if stmt["type"] == "assignment":
                        lhs = stmt["variable"]
                        rhs = stmt["value"]

                        if (isinstance(rhs, dict) and
                            rhs["lhe"] == lhs and
                            rhs["operator"] == "+" and
                            rhs["rhe"] == loop_var):
                            
                            theorem = f"""
Theorem sum_first_{n-1} : compute_sum {n} = {n * (n - 1) // 2}.
Proof.
  (* proof would show sum of 0 to {n-1} *)
Qed.
"""
                            print(theorem)
    return "No recognizable theorem pattern found."
