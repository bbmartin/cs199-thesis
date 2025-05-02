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
                self.analyze_conditional(node)

        return self.theorem
  
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
    
    def analyze_conditional(self, node):
        theorems = []

        domain = set()
        mapping = self.extract_conditional_mapping(node)

        else_branch = node["else"]
        if (else_branch is not None or self.is_exhaustive(mapping, else_branch)):
            theorems.append(self.write_exhaustiveness_theorem("x", domain))
        
        if self.is_mutually_exclusive(mapping):
            theorems.append(self.write_mutually_exclusive_theorem("x", mapping))
            
        cycles = self.check_for_cycles(mapping)
        if cycles:
          theorems.append(self.write_cycle_theorem("x", cycles))

        if self.is_idempotent(mapping):
          theorems.append(self.write_idempotency_theorem("x"))
            
        fixed_points = self.has_fixed_point(mapping)
        if fixed_points:
          theorems.append(self.write_fixed_point_theorem("x", fixed_points))
        return theorems
    
    def extract_conditional_mapping(self, if_node):
        mapping = {}

        seen_inputs = set()
        seen_outputs = set()

        pattern = if_node["condition"]["rhe"]
        result = if_node["block"][0]["expression"]
        mapping[pattern] = result
        seen_inputs.add(pattern)
        seen_outputs.add(result)

        elifs = if_node.get("elif", [])
        for elif_branch in elifs:
            pattern = elif_branch["condition"]["rhe"]
            result = elif_branch["block"][0]["expression"]
            mapping[pattern] = result
            seen_inputs.add(pattern)
            seen_outputs.add(result)

        else_branch = if_node.get("else")
        if else_branch:
            else_result = else_branch["block"][0]["expression"]
            seen_outputs.add(else_result)

            unmapped_inputs = seen_outputs - seen_inputs
            for unseen_input in unmapped_inputs:
                mapping[unseen_input] = else_result
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
        return cycles
    
    def is_mutually_exclusive(self, mapping):
        seen = set()
        for key, value in mapping.items():
            if key in seen or value in seen:
                return False
            seen.add(key)
            seen.add(value)
        return True
    
    def is_idempotent(self, mapping):
        for key, value in mapping.items():
            if mapping.get(value) != value:
                return False
        return True
    
    def has_fixed_point(self, mapping):
        return [k for k, v in mapping.items() if k == v]
        
    def is_exhaustive(self, mapping, domain):
        return all(value in mapping for value in domain)
    
    def write_exhaustiveness_theorem(self, function_name, input_domain=None):
      domain_cases = ""
      if input_domain:
          domain_cases = " (* x ∈ {" + ", ".join(sorted(input_domain)) + "} *)"

      return f"""
        Theorem {function_name}_exhaustive :
          forall x, exists y, {function_name} x = y.{domain_cases}
        Proof.
          intros x.
          destruct x; simpl; eexists; reflexivity.
        Qed.
        """
    
    def write_mutually_exclusive_theorem(self, function_name, mapping):
        pairs = []
        for i in range (len(mapping)):
            for j in range(i + 1, len(mapping)):
                pairs.append(f"( x = {mapping[i]} /\\ x =  {mapping[j]})")

        disjunction = " \\/\n ".join(pairs)

        num_cases = len(pairs)

        if num_cases == 1:
            intros = "intros [H _]; congruence."
        else:
            open_brackets = "[" * (num_cases - 1)
            close_brackets = "]" * (num_cases - 1)
            intros = f"intros {open_brackets}[H _]{close_brackets}; congruence." 

        return f"""
        Theorem {function_name}_mutually_exclusive :
          forall x, {disjunction}.
        Proof.
          intros x.
          destruct x; simpl; auto.
          {intros}
        Qed.
        """
    
    def write_cycle_theorem(self, function_name, cycles):
      theorems = []
      for start, length in cycles:
          print(start, length)
          theorems.append(f"""
          Theorem {function_name}_cycle_{start} :
            forall x, {function_name} x = {function_name} (x + {length}).
          Proof.
            intros x.
            induction x; simpl; auto.
            rewrite IHx.
            reflexivity.
          Qed.
          """)
      return "\n".join(theorems)
    
    def write_idempotency_theorem(self, function_name):
        return f"""
        Theorem {function_name}_idempotent :
          forall x, {function_name} ({function_name} x) = {function_name} x.
        Proof.
          intros x.
          induction x; simpl; auto.
          rewrite IHx.
          reflexivity.
        Qed.
        """
    
    def write_fixed_point_theorem(self, function_name, fixed_points):
        theorems = ""
        for val in fixed_points:
          theorems += f"""
        Theorem {function_name}_fixed_point_{val} :
        {function_name} {val} = {val}.
        Proof.
         simpl. reflexivity.
        Qed.
        """
        return theorems
        