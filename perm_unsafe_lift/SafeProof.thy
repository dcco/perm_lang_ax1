theory SafeProof
  imports ProcLangX
begin
  
type_synonym state = "string \<Rightarrow> p_exp option"  
  
definition invalid_state where
  "invalid_state e S = (\<exists> a. a \<in> free_vars e \<and> a \<notin> dom S)"  
  
definition valid_perm_env where
  "valid_perm_env r_s S = (use_env_vars r_s \<subseteq> dom S)"  
  
lemma soundness: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; valid_perm_env r_s1 S \<rbrakk> \<Longrightarrow> \<not> (invalid_state e S)"  
  apply (induct e arbitrary: env r_s1 tau r_s2 rx S)
       apply (auto)
    (* const + op case *)
       apply (simp add: valid_perm_env_def)
       apply (simp add: invalid_state_def)
      apply (simp add: valid_perm_env_def)
      apply (simp add: invalid_state_def)
    (* var case *)
     apply (simp add: valid_perm_env_def)
     apply (simp add: invalid_state_def)
     apply (case_tac "x1a \<in> use_env_vars r_s1")
      apply (auto)
     apply (simp add: use_env_vars_def)
     apply (cut_tac r_x="req_use_env x1a tau" and r_s="r_s1" and x="x1a" in leq_use_none)
       apply (auto)
     apply (simp add: req_use_env_def)
     apply (simp add: one_use_env_def)
     apply (case_tac tau)
         apply (auto)
     apply (case_tac x54)
      apply (auto)
    (* if case *)
    apply (simp add: invalid_state_def)
    apply (auto)
      apply (simp add: dom_def)
    
    
  
end