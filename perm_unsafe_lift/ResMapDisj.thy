theory ResMapDisj
  imports ResMap NormEnv
begin
  
lemma lift_sub_use_env: "\<lbrakk> sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_use_env s (lift_use_env r_s r)"   
  apply (simp add: sub_use_env_def)
  apply (case_tac r)
    apply (auto)
  done
  
    (* strong disjointness *)
  
definition strong_disj_use_env where
  "strong_disj_use_env r_x r_s = (\<forall> x. r_x x = NoPerm \<or> r_s x = NoPerm)"  
    
lemma empty_strong_disj_use_env1: "strong_disj_use_env empty_use_env r_s"
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: empty_use_env_def)
  done

lemma empty_strong_disj_use_env2: "strong_disj_use_env r_s empty_use_env"
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: empty_use_env_def)
  done    
  
lemma comm_strong_disj_use_env: "\<lbrakk> strong_disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> strong_disj_use_env r_x r_s"    
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  done        
    
lemma strong_disj_leq_use_env1: "\<lbrakk> strong_disj_use_env r_s r_ex; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> strong_disj_use_env r_x r_ex"
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done        

lemma strong_disj_leq_use_env2: "\<lbrakk> strong_disj_use_env r_ex r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> strong_disj_use_env r_ex r_x"
  apply (rule_tac comm_strong_disj_use_env)  
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env1)
   apply (rule_tac comm_strong_disj_use_env)
   apply (auto)
  done
    
lemma reduce_strong_disj_use_env: "\<lbrakk> disj_use_env r_s r_x; strong_use_env r_x \<rbrakk> \<Longrightarrow> strong_disj_use_env r_s r_x"
  apply (simp add: disj_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma add_strong_disj_use_env: "\<lbrakk> strong_disj_use_env r_x r_s; r_s x = NoPerm \<rbrakk> \<Longrightarrow> strong_disj_use_env (add_use_env r_x x r) r_s"
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  apply (simp add: add_use_env_def)
  apply (auto)
  done
    
lemma diff_strong_disj_use_env: "\<lbrakk> strong_use_env r_x \<rbrakk> \<Longrightarrow> strong_disj_use_env (diff_use_env r_s r_x) r_x"    
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
 
lemma strong_disj_comp_use_env1: "\<lbrakk> strong_disj_use_env r_ex r_x; strong_disj_use_env r_ex r_s \<rbrakk> \<Longrightarrow> strong_disj_use_env r_ex (comp_use_env r_x r_s)"    
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
 
lemma strong_disj_comp_use_env2: "\<lbrakk> strong_disj_use_env r_x r_ex; strong_disj_use_env r_s r_ex \<rbrakk> \<Longrightarrow> strong_disj_use_env (comp_use_env r_x r_s) r_ex"     
  apply (rule_tac comm_strong_disj_use_env)
  apply (rule_tac strong_disj_comp_use_env1)
   apply (simp_all add: comm_strong_disj_use_env)
  done 
    
    (* map disjointness *) 
    
definition disj_res_map where
  "disj_res_map rs_map = (\<forall> x y. x \<noteq> y \<longrightarrow> strong_disj_use_env (lookup_res rs_map x) (lookup_res rs_map y))"    
  
definition sep_res_map where
  "sep_res_map r_s rs_map = (\<forall> x. strong_disj_use_env r_s (lookup_res rs_map x))"

    (* scoping definition (explored more deeply later *)
  
definition scope_use_env where
  "scope_use_env rs_map r_s = (\<forall> x. lookup_mem rs_map x = None \<longrightarrow> r_s x = NoPerm)"  
  
definition fresh_map_var where
  "fresh_map_var rs_map x = (lookup_mem rs_map x = None)"  
  
fun scope_res_rec where
  "scope_res_rec rs_map = (case rs_map of
    NilStack \<Rightarrow> True
    | ConsStack x r_s rs_map' \<Rightarrow> fresh_map_var rs_map' x \<and>
      strong_use_env r_s \<and> scope_use_env rs_map' r_s \<and> scope_res_rec rs_map'
  )"
  
definition scope_res_map where
  "scope_res_map rs_map = scope_res_rec rs_map"  
  
definition valid_res_map where
  "valid_res_map s rs_map = (disj_res_map rs_map \<and> sub_res_map s rs_map \<and> scope_res_map rs_map)"      
  
    (* - scope use env lemmas *)
    
lemma dist_add_scope_use_env: "\<lbrakk> scope_use_env rs_map r_s \<rbrakk> \<Longrightarrow> scope_use_env (add_mem rs_map x r_c) (add_use_env r_s x r)"    
  apply (simp add: scope_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
   apply (simp add: add_mem_def)
   apply (simp add: add_use_env_def)
   apply (auto)
  apply (simp add: add_mem_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  done

lemma add_scope_use_env: "\<lbrakk> scope_use_env rs_map r_s; lookup_mem rs_map x \<noteq> None \<rbrakk> \<Longrightarrow> scope_use_env rs_map (add_use_env r_s x r)"     
  apply (simp add: scope_use_env_def) 
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  apply (simp add: add_use_env_def)
  apply (auto)
  done
  
    (* - scope res map USAGE lemmas *)
  
lemma add_scope_res_map_rev: "\<lbrakk> scope_res_map (add_mem rs_map x r_s) \<rbrakk> \<Longrightarrow> scope_res_map rs_map"    
  apply (simp add: scope_res_map_def)
  apply (simp add: add_mem_def)
  done
  
lemma self_scope_use_env_ih1: "\<lbrakk> scope_res_map rs_map; lookup_mem rs_map x = Some (r_s, rs_map') \<rbrakk> \<Longrightarrow> scope_use_env rs_map' r_s"    
  apply (induct rs_map)
   apply (auto)
   apply (case_tac "x1 = x")
   apply (simp add: scope_res_map_def)
  apply (cut_tac rs_map="rs_map" and x="x1" and r_s="x2" in add_scope_res_map_rev)
   apply (simp add: add_mem_def)
  apply (simp)
  done

definition sub_scope_use_env where
  "sub_scope_use_env rs_map rs_map' = (\<forall> y. lookup_mem rs_map y = None \<longrightarrow> lookup_mem rs_map' y = None)"

lemma self_scope_use_env_ih2: "\<lbrakk> scope_res_map rs_map; lookup_mem rs_map x = Some (r_s, rs_map') \<rbrakk> \<Longrightarrow> sub_scope_use_env rs_map rs_map'"
  apply (induct rs_map)
   apply (auto)
  apply (case_tac "x1 = x")
   apply (simp add: scope_res_map_def)
   apply (simp add: sub_scope_use_env_def)
  apply (cut_tac rs_map="rs_map" and x="x1" and r_s="x2" in add_scope_res_map_rev)
   apply (simp add: add_mem_def)
  apply (simp add: sub_scope_use_env_def)
  done
    
lemma empty_scope_use_env: "scope_use_env rs_map empty_use_env"    
  apply (simp add: scope_use_env_def)
  apply (simp add: empty_use_env_def)
  done
  
lemma trans_scope_use_env: "\<lbrakk> sub_scope_use_env rs_map rs_map'; scope_use_env rs_map' r_s \<rbrakk> \<Longrightarrow> scope_use_env rs_map r_s"    
  apply (simp add: sub_scope_use_env_def)
  apply (simp add: scope_use_env_def)
  done

lemma trans_scope_use_env2: "\<lbrakk> scope_use_env rs_map r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> scope_use_env rs_map r_x"       
  apply (simp add: scope_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma self_scope_use_env: "\<lbrakk> scope_res_map rs_map \<rbrakk> \<Longrightarrow> scope_use_env rs_map (lookup_res rs_map x)"  
  apply (simp add: lookup_res_def)
  apply (case_tac "lookup_mem rs_map x")
   apply (auto)
   apply (rule_tac empty_scope_use_env)
  apply (rule_tac trans_scope_use_env)
   apply (rule_tac self_scope_use_env_ih2)
    apply (auto)
  apply (rule_tac self_scope_use_env_ih1)
   apply (auto)
  done
    
lemma add_scope_res_map: "\<lbrakk> scope_res_map rs_map; fresh_map_var rs_map x; strong_use_env r_s; scope_use_env rs_map r_s \<rbrakk>
    \<Longrightarrow> scope_res_map (add_mem rs_map x r_s)"
  apply (simp add: scope_res_map_def)
  apply (simp add: add_mem_def)
  done
  
lemma scope_res_map_strong: "\<lbrakk> scope_res_map rs_map; lookup_mem rs_map x = Some (r_s, rs_map') \<rbrakk> \<Longrightarrow> strong_use_env r_s"        
  apply (induct rs_map)
   apply (auto)
  apply (case_tac "x1 = x")
   apply (auto)
   apply (simp add: scope_res_map_def)
  apply (cut_tac rs_map="rs_map" and x="x1" and r_s="x2" in add_scope_res_map_rev)
   apply (simp add: add_mem_def)
  apply (auto)
  done    
    
lemma scope_res_map_fresh_lookup: "\<lbrakk> scope_res_map rs_map; lookup_mem rs_map x = Some (r_s, rs_map') \<rbrakk> \<Longrightarrow> fresh_map_var rs_map' x"        
  apply (induct rs_map)
   apply (auto)
  apply (case_tac "x1 = x")
   apply (auto)
   apply (simp add: scope_res_map_def)
  apply (cut_tac rs_map="rs_map" and x="x1" and r_s="x2" in add_scope_res_map_rev)
   apply (simp add: add_mem_def)
  apply (auto)
  done
    
lemma self_scope_res_map: "\<lbrakk> scope_res_map rs_map; lookup_mem rs_map x = Some (r_s, rs_map') \<rbrakk> \<Longrightarrow> scope_res_map rs_map'"
  apply (induct rs_map)
   apply (auto)
  apply (case_tac "x1 = x")
   apply (auto)
   apply (rule_tac add_scope_res_map_rev)
   apply (simp add: add_mem_def)
  apply (cut_tac rs_map="rs_map" and x="x1" and r_s="x2" in add_scope_res_map_rev)
   apply (simp add: add_mem_def)
  apply (auto)
  done      
  
   (* - sep res map lemmas *)
    
    (* - to prove this we must show that x is separate from every part of rs_map, which is true because of the structure of scope_res_map *)
lemma add_sep_res_map: "\<lbrakk> sep_res_map r_s rs_map; fresh_var s x; valid_res_map s rs_map \<rbrakk> \<Longrightarrow> sep_res_map (add_use_env r_s x r) rs_map"    
  apply (simp add: sep_res_map_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="xaa" in allE)
  apply (auto)
  apply (case_tac "x \<noteq> xaa")
   apply (simp add: add_use_env_def)
    (* in the case where xaa = x, we must show that rs_map does not have x, since s does not have x, s scopes rs_map, and rs_map scopes all rs_map xa *)
  apply (cut_tac rs_map="rs_map" and x="xa" in self_scope_use_env)
   apply (simp add: valid_res_map_def)
  apply (simp add: fresh_var_def)
  apply (simp add: valid_res_map_def)
  apply (simp add: sub_res_map_def)
  apply (simp add: scope_use_env_def)
  done  
 
lemma add_mem_sep_res_map: "\<lbrakk> sep_res_map r_s rs_map; strong_disj_use_env r_s r_x  \<rbrakk> \<Longrightarrow> sep_res_map r_s (add_mem rs_map x r_x)"
  apply (simp add: sep_res_map_def)
  apply (simp add: add_mem_def)
  apply (simp add: lookup_res_def)
  done    
    
    (*
lemma add_mem_sep_res_map: "\<lbrakk> sep_res_map r_s rs_map; strong_disj_use_env r_s r_x  \<rbrakk> \<Longrightarrow> sep_res_map r_s (add_mem rs_map x r_x)"    
  apply (simp add: sep_res_map_def)
  apply (simp add: add_mem_def)
  apply (simp add: lookup_res_def)
  done
    
lemma add_sep_res_map: "\<lbrakk> sep_res_map r_s rs_map; fresh_var s x; valid_res_map s rs_map \<rbrakk> \<Longrightarrow> sep_res_map (add_use_env r_s x r) rs_map"    
  apply (simp add: sep_res_map_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: valid_res_map_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (simp add: fresh_var_def)
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
    
  done  
 
lemma empty_sep_res_map: "sep_res_map empty_use_env rs_map"      
  apply (simp add: sep_res_map_def)
  apply (auto)
  apply (rule_tac empty_strong_disj_use_env1)
  done*)
  
    (* - disj res map lemmas *)
    
lemma disj_add_res_map: "\<lbrakk> disj_res_map rs_map;
  sep_res_map r_s (rem_mem rs_map x) \<rbrakk> \<Longrightarrow> disj_res_map (add_mem rs_map x r_s)"
  apply (simp add: disj_res_map_def)
  apply (auto)
  apply (case_tac "x = xa")
   apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="y" in lookup_add_mem_diff)
    apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in lookup_add_mem_same)
   apply (auto)
   apply (simp add: sep_res_map_def)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="y" in allE)
   apply (cut_tac rs_map="rs_map" and x="x" and y="y" in lookup_rem_mem_diff)   
    apply (auto)
  apply (case_tac "x = y")
   apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="xa" in lookup_add_mem_diff)
    apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in lookup_add_mem_same)
   apply (auto)
   apply (rule_tac comm_strong_disj_use_env)
   apply (simp add: sep_res_map_def)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="xa" in allE)
   apply (cut_tac rs_map="rs_map" and x="x" and y="xa" in lookup_rem_mem_diff)  
    apply (auto)
  apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="xa" in lookup_add_mem_diff)
  apply (auto)
  apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="y" in lookup_add_mem_diff)
  apply (auto)
  done
    
lemma disj_add_res_map_rev: "\<lbrakk> disj_res_map (add_mem rs_map x r_s); lookup_res rs_map x = empty_use_env \<rbrakk> \<Longrightarrow> disj_res_map rs_map"    
  apply (simp add: disj_res_map_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (erule_tac x="y" in allE)
  apply (auto)
  apply (case_tac "x = xa")
   apply (auto)
   apply (rule_tac empty_strong_disj_use_env1)
  apply (case_tac "x = y")
   apply (auto)
   apply (rule_tac empty_strong_disj_use_env2)
  apply (simp add: add_mem_def)
  apply (simp add: lookup_res_def)
  done
  
lemma disj_rem_res_map: "\<lbrakk> disj_res_map rs_map \<rbrakk> \<Longrightarrow> disj_res_map (rem_mem rs_map x)"  
  apply (simp add: disj_res_map_def)
  apply (auto)
  apply (case_tac "x = xa")
   apply (simp add: lookup_rem_mem_same)
   apply (rule_tac empty_strong_disj_use_env1)
  apply (case_tac "x = y")
   apply (simp add: lookup_rem_mem_same)
   apply (rule_tac empty_strong_disj_use_env2)
  apply (simp add: lookup_rem_mem_diff)
  done
    
    (* ### NEW DISJOINTNESS *)

    
definition disj_nres_map where
  "disj_nres_map rs_map = (\<forall> x y. x \<noteq> y \<longrightarrow> strong_disj_use_env (nres_lookup rs_map x) (nres_lookup rs_map y))"  
  
  
  
definition sep_nres_map where
  "sep_nres_map r_s rs_map = (\<forall> x. strong_disj_use_env r_s (nres_lookup rs_map x))"     
    
lemma add_sep_nres_map: "\<lbrakk> sep_nres_map r_x rs_map; strong_disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> sep_nres_map r_x (add_env rs_map x r_s)"    
  apply (simp add: sep_nres_map_def)
  apply (simp add: nres_lookup_def)
  apply (simp add: add_env_def)
  done  
  
lemma leq_sep_nres_map: "\<lbrakk> leq_use_env r_x r_s; sep_nres_map r_s rs_map \<rbrakk> \<Longrightarrow> sep_nres_map r_x rs_map"      
  apply (simp add: sep_nres_map_def)
  apply (auto)
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env1)
   apply (auto)
  done
    
lemma comp_sep_nres_map: "\<lbrakk> sep_nres_map r_s rs_map; sep_nres_map r_x rs_map \<rbrakk> \<Longrightarrow> sep_nres_map (comp_use_env r_s r_x) rs_map"    
  apply (simp add: sep_nres_map_def)
  apply (auto)
  apply (rule_tac strong_disj_comp_use_env2)
   apply (auto)
  done    
    
lemma disj_add_nres_map: "\<lbrakk> disj_nres_map rs_map;
  sep_nres_map r_s (rem_env rs_map x) \<rbrakk> \<Longrightarrow> disj_nres_map (add_env rs_map x r_s)"
  apply (simp add: disj_nres_map_def)
  apply (auto)
  apply (case_tac "x = xa")
   apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="y" in nres_add_diff)
    apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_same)
   apply (auto)
    apply (simp add: sep_nres_map_def)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="y" in allE)
   apply (cut_tac rs_map="rs_map" and x="x" and y="y" in nres_rem_diff)
    apply (auto)
  apply (case_tac "x = y")
   apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="xa" in nres_add_diff)
    apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_same)
   apply (auto)
   apply (rule_tac comm_strong_disj_use_env)
   apply (simp add: sep_nres_map_def)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="xa" in allE)
   apply (cut_tac rs_map="rs_map" and x="x" and y="xa" in nres_rem_diff)  
    apply (auto)
  apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="xa" in nres_add_diff)
  apply (auto)
  apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="y" in nres_add_diff)
  apply (auto)
  done    
    
end