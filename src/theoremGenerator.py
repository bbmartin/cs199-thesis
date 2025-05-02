class TheoremGenerator:
    def __init__(self):
        self.theorem = "No recognizable theorem pattern found."

    def generate(self, parsed_ast):
        for node in parsed_ast:
            if node["type"] == "for":
                self.analyze_for(node)

            elif node["type"] == "if":
                self.analyze_conditional(node)

            elif node["type"] == "while":
                self.analyze_while(node)

        return self.theorem

    def analyze_while(self, node):
        theorems = []
        z_assignment = node["block"][0]
        if (
            z_assignment.get("type") == "assignment"
            and isinstance(z_assignment.get("value"), dict)
            and z_assignment["value"].get("operator") == "+"
        ):
            theorems.append(self.generate_while_loop_length_theorem())

        if self.is_string_append(node):
            theorems.append(self.write_string_append_theorem())

    def write_string_append_theorem(self):
        theorem = """
        Lemma append_a_increases_length :
          forall s, String.length (s ++ "a"%char) = S (String.length s).
        Proof.
          intros s. rewrite String.append_length. simpl. lia.
        Qed.

        Lemma {func_name}_length_invariant :
          forall z count max_count,
            count <= max_count ->
            String.length ({func_name} z count max_count) = String.length z + (max_count - count).
        Proof.
          intros z count max_count Hle.
          revert z.
          induction count using lt_wf_ind.
          intros z.
          destruct (count <? max_count) eqn:Hlt.
          - apply Nat.ltb_lt in Hlt.
            rewrite <- Nat.add_1_r.
            simpl.
            rewrite <- append_a_increases_length.
            specialize (H (count + 1)).
            assert (count + 1 <= max_count) by lia.
            specialize (H H0 (z ++ "a"%char)).
            rewrite String.append_length.
            simpl in H.
            lia.
          - apply Nat.ltb_ge in Hlt.
            simpl. lia.
        Qed.

        Theorem {func_name}_final_length :
          forall max_count,
            String.length ({func_name} EmptyString 0 max_count) = max_count.
        Proof.
          intros. apply {func_name}_length_invariant. lia.
        Qed.
        """
        return theorem
    
    def write_while_loop_termination_theorem(func_name="while_loop_str", target=10):
      return f"""
      Theorem {func_name}_terminates :
        forall z,
          exists result, {func_name} z 0 = result.
      Proof.
        exists ({func_name} z 0).
        reflexivity.
      Qed.
      """

    def is_string_append(self, node):
      condition = node["condition"]
      lhe = condition["lhe"]
      rhe = condition["rhe"]
      op = condition["operator"]

      block = node["block"][0]
      
      if (block["type"] == "assignment"
          and block["data_type"] == "str"
          and isinstance(block["value"], dict)):
          value = block["value"]
          if (
              value["type"] == "arith_expr"
              and value["operator"] == "+"
              and value["lhe"] == block["variable"]
          ):
              if (lhe == block["variable"] 
                  and isinstance(rhe, int)
                  and (op == "<" or op == "<=")
                ):
                  return True
      return False
    
    def is_while_terminating(node):
      condition = node["condition"]
      lhe = condition["lhe"]
      rhe = condition["rhe"]
      op = condition["operator"]

      if op not in ["<", ">", "<=", ">="] or not isinstance(rhe, int):
          return False
      
      for stmt in node.get("block", []):
          if (
              stmt.get("type") == "assignment"
              and stmt.get("variable") == lhe
              and isinstance(stmt.get("value"), dict)
              and stmt["value"].get("type") == "arith_expr"
              and stmt["value"].get("lhe") == lhe
              and stmt["value"].get("operator") in ["+", "-"]
              and stmt["value"].get("rhe") == 1
          ):
              return True

      return False

      
    def analyze_for(self, node):
        theorems = []
        loop_var = node["iterable"]
        loop_range = node["range"]
        if ("name" in loop_range and loop_range["name"] == "range"):
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
        else:
            block = node["block"]
            if len(block) == 1:
                assign = block[0]
                if (
                    assign.get("type") == "assignment"
                    and isinstance(assign["value"], dict)
                    and assign["value"].get("type") == "arith_expr"
                ):
                    op = assign["value"].get("operator")
                    if op == "+":
                        theorems.append(self.write_for_loop_sum_theorem())
                    elif op == "*":
                        theorems.append(self.write_arithmetic_product_theorem())

    def write_for_loop_sum_theorem(self):
        theorem = """
        Theorem {func_name}_correct :
        forall l,
        {func_name} l = fold_left Nat.add l 0.
        Proof.
          intros l. induction l as [|h t IH].
          - reflexivity.
          - simpl. rewrite <- IH. reflexivity.
        Qed.
        """
        return theorem

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
        