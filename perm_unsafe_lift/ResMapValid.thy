theory ResMapValid
  imports GenSubEnv NormEnv ResMapDisj
begin
 
definition super_drop_use_env where
  "super_drop_use_env r_s = (\<lambda> x. if r_s x = OwnPerm then NoPerm else r_s x)"  
  
lemma self_sdrop_leq_use_env: "leq_use_env (super_drop_use_env r_s) r_s"  
  apply (simp add: super_drop_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma sdrop_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (super_drop_use_env r_x) r_s"    
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_sdrop_leq_use_env)
  done
    
lemma diff_sdrop_leq_use_env: "leq_use_env (diff_use_env r_s r_s) (super_drop_use_env r_s)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: super_drop_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
  

  
  (* basically, we want a static way of describing a recursive structure that will be maintained inductively and wont have any unpleasant
      properties (cyclic dependencies, etc). *)
    
    
  (*
definition valid_use_env where
  "valid_use_env s rs_map r_s r_x = (sub_use_env s r_c \<and> leq_use_env r_s r_c \<and> (\<forall> x. r_s x \<noteq> NoPerm \<longrightarrow>
    leq_use_env (lookup_res rs_map x) r_s \<and> disj_use_env (lookup_res rs_map x) r_x
  ))"*)
  
definition valid_use_entry where
  "valid_use_entry r_c r_s r_x = (leq_use_env r_x r_c \<and> strong_disj_use_env r_x r_s)"

definition valid_use_env where
  "valid_use_env s rs_map r_c r_s = (sub_use_env s r_c \<and> leq_use_env r_s r_c \<and>
    (\<forall> x. r_c x \<noteq> NoPerm \<longrightarrow> valid_use_entry r_c r_s (lookup_res rs_map x)))"
  


    (* - valid res map lemmas *)  
    (*
lemma add_valid_res_map_rev: "\<lbrakk> valid_res_map s (add_mem rs_map x v); fresh_var s x \<rbrakk> \<Longrightarrow> valid_res_map s rs_map"
  apply (simp add: valid_res_map_def)
  apply (auto)
    apply (simp add: disj_res_map_def)
    apply (auto)
    apply (erule_tac x="xa" in allE)
    apply (erule_tac x="y" in allE)
    apply (auto)
    apply (case_tac "x = xa")
     apply (auto)
     apply (case_tac "x = y")
      apply (auto)
     apply (simp add: add_mem_def)
    apply (simp add: lookup_res_def)
    apply (simp add: add_mem_def)
    apply (case_tac "x = xa")
     apply (auto)
     apply (case_tac "x = y")
    apply (auto)
  
  apply (induct rs_map arbitrary: x v)
   apply (simp add: valid_res_map_def)
   apply (auto)
    apply (simp add: disj_res_map_def)
    apply (simp add: lookup_res_def)
    apply (auto)
    apply (rule_tac empty_strong_disj_use_env1)
   apply (simp add: sub_res_map_def)
  apply (simp add: add_mem_def)
  apply (simp add: valid_res_map_def)
  apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x1" and r_s="x2" in disj_add_res_map)
    
  done*)
    (*
lemma add_valid_res_map: "\<lbrakk> valid_res_map s rs_map \<rbrakk> \<Longrightarrow> valid_res_map (add_mem s x v) rs_map"    
  apply (simp add: valid_res_map_def)
  apply (auto)
   apply (simp add: sub_res_map_def)
   apply (simp add: add_mem_def)
  apply (erule_tac x="xa" in allE)
  apply (rule_tac add_sub_use_env)
  apply (auto)
  done
 
lemma add_set_valid_res_map: "\<lbrakk> valid_res_map s rs_map; sep_res_map r_s rs_map; sub_use_env s r_s \<rbrakk> \<Longrightarrow> valid_res_map (add_mem s x v) (set_res_map rs_map x r_s)"    
  apply (simp add: valid_res_map_def)
  apply (auto)
     apply (simp add: set_res_map_def)
     apply (simp add: disj_res_map_def)
     apply (auto)
     apply (simp add: sep_res_map_def)
    apply (simp add: sep_res_map_def)
    apply (rule_tac comm_strong_disj_use_env)
    apply (simp)
   apply (simp add: sub_res_map_def)
   apply (simp add: add_mem_def)
   apply (auto)
   apply (simp add: set_res_map_def)
  apply (simp add: sub_res_map_def)
  apply (simp add: set_res_map_def)
  apply (auto)
   apply (rule_tac add_sub_use_env)
   apply (simp)
  apply (rule_tac add_sub_use_env)
  apply (simp)
  done    *)
(*
lemma add_rem_valid_res_map: "\<lbrakk> valid_res_map (add_mem s x v) rs_map \<rbrakk> \<Longrightarrow> valid_res_map s (rem_res_map rs_map x)"        
  apply (simp add: valid_res_map_def)
  apply (auto)
    apply (rule_tac disj_rem_res_map)
    apply (simp)
   apply (rule_tac add_rem_sub_res_map)
   apply (simp)
  apply (simp add: rem_res_map_def)
  apply (simp add: set_res_map_def)
  apply (auto)
   apply (rule_tac empty_sub_use_env)
  *)
(*
lemma valid_lookup_res_map: "\<lbrakk> valid_res_map s rs_map; lookup_mem rs_map x = Some (r_s, rs_map') \<rbrakk> \<Longrightarrow> scope_use_env rs_map' r_s"  
  apply (induct rs_map)
   apply (auto)
  apply (simp add: valid_res_map_def)    *)
    
    (* valid use env lemmas *)
    
lemma contain_valid_use_env: "\<lbrakk> contain_env s' s; valid_use_env s rs_map r_c r_s \<rbrakk> \<Longrightarrow> valid_use_env s' rs_map r_c r_s"    
  apply (simp add: valid_use_env_def)
  apply (simp add: sub_use_env_def)
  apply (simp add: contain_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "s x")
   apply (auto)
  done
    
    (* ######### NRES map validity *)
  
definition valid_nres_map where
  "valid_nres_map s s_map = (full_nres_map s s_map \<and> disj_nres_map s_map \<and> sub_nres_map s s_map)"
    
definition valid_exp_use_env where
  "valid_exp_use_env s s_map r_s = (sub_use_env s r_s \<and> sep_nres_map r_s s_map)"
  
end