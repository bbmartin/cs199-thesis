class TheoremGenerator:
    def __init__(self):
        self.theorem = "No recognizable theorem pattern found."

    def generate(self, parsed_ast):
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

                            if (
                                isinstance(rhs, dict)
                                and rhs["lhe"] == lhs
                                and rhs["operator"] == "+"
                                and rhs["rhe"] == loop_var
                            ):
                                self.theorem = self.write_arithmetic_summation_theorem(
                                    n
                                )

                            if (
                                isinstance(rhs, dict)
                                and rhs["lhe"] == lhs
                                and rhs["operator"] == "*"
                                and rhs["rhe"] == loop_var
                            ):
                                self.theorem = self.write_arithmetic_product_theorem(n)

            elif node["type"] == "if":
                if_node = node
                if_mapping = self.extract_conditional_mapping(if_node)
                print(if_mapping)

        return self.theorem
    
    def analyze_conditional(self, node):
        theorems = []
        mapping = self.extract_conditional_mapping(node)

        else_branch = node["else"]
        if else_branch is not None:
            """exhaustive mapping"""
        
        cycles = self.check_for_cycles(mapping)
        if cycles:
            """handle cycles"""

        if all(isinstance(v, str) for v in mapping.values()):
            """idempotency check"""
        

    def write_arithmetic_summation_theorem(self):
        theorem = """
    Theorem sum_first_n :
      forall (n : nat),
        loop n 0 = n * (n + 1) / 2.
    Proof.
      intros n.
      induction n.
      - simpl. reflexivity.
      - simpl. rewrite IHn. 
        unfold loop at 1.
      ring.
    Qed.
    """
        return theorem

    def write_arithmetic_product_theorem(self):
        # TODO: test and check for correctness
        # TODO: add needed imports if any
        theorem = """
    Fixpoint fact (n : nat) : nat :=
      match n with
      | 0 => 1
      | S n' => n * fact n'
      end.

    Theorem product_first_n :
      forall n,
        loop n 1 = fact n.
    Proof.
      intros n.
      induction n.
      - simpl. reflexivity.
      - simpl. rewrite IHn.
        unfold loop at 1.
        simpl.
        ring.
    Qed.
    """
        return theorem
    
    def extract_conditional_mapping(self, if_node):
        mapping = {}
        pattern = if_node["condition"]["rhe"]
        result = if_node["block"][0]["expression"]
        mapping[pattern] = result
        elifs = if_node.get("elif", [])
        for elif_branch in elifs:
            pattern = elif_branch["condition"]["rhe"]
            result = elif_branch["block"][0]["expression"]
            mapping[pattern] = result
        else_branch = if_node.get("else")
        if else_branch:
            for seen_pattern in mapping.values():
                if seen_pattern not in mapping:
                    mapping[seen_pattern] = else_branch["block"][0]["expression"]
        print("Mapping found:")
        for k, v in mapping.items():
            print(f"{k} -> {v}") 
        return mapping
        
    
    def check_for_cycles(self, parsed_ast):
        visited = set()
        cycles = []

        for start in parsed_ast.keys():
            if start in visited:
                continue
            
            path = []
            current = start

            while current not in path:
                path.append(current)
                visited.add(current)
                current = parsed_ast.get(current)

                if current is None:
                    break
            
            if current == start:
                cycle_length = len(path)
                cycles.append((start, cycle_length))
        
        print("Cycles found:")
        for cycle in cycles:
            print(f"Cycle starting at {cycle[0]} with length {cycle[1]}")
        return cycles