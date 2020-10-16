theory ReduceRestrX
  imports GenSubEnv WTLemma ResMapDisj
begin
  
    
definition restr_env where
  "restr_env s rs_map = (\<lambda> x. if rs_map x = None then None else s x)"  
  
definition np_restr_env where
  "np_restr_env env rs_map = (\<lambda> x. if rs_map x = None \<and> non_prim_entry env x then None else env x)"     
  
lemma restr_env_eq: "\<lbrakk> full_nres_map s rs_map; sub_env s env \<rbrakk> \<Longrightarrow> restr_env env rs_map = env"    
  apply (case_tac "\<forall> x. restr_env env rs_map x = env x")  
   apply (auto)
  apply (simp add: restr_env_def)
  apply (case_tac "rs_map x")
   apply (auto)
  apply (simp add: sub_env_def)
  apply (simp add: full_nres_map_def)
  done  
  
lemma well_typed_restr: "\<lbrakk> 
  full_nres_map s rs_map; sub_env s env; well_typed env r_s1 v tau r_s2 rx \<rbrakk> \<Longrightarrow>
  well_typed (restr_env env rs_map) r_s1 v tau r_s2 rx"  
  apply (simp add: restr_env_eq)
  done                            
  
end