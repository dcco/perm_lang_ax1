theory OldSafeRedLemma
  imports SafeRedLemma
begin


definition disj_trap where
  "disj_trap c1 c2 = (c1 \<or> c2)"
    
fun c_red_exp :: "p_state \<times> p_exp \<Rightarrow> p_act \<Rightarrow> p_state \<times> p_exp \<Rightarrow> bool" where
  "c_red_exp (s, e) a (s', e') = disj_trap (app_red_exp (s, e) a (s', e')) (case e of
    AppExp e1 e2 \<Rightarrow> (\<exists> e2'. AppExp e1 e2' = e' \<and> is_sexp e1 \<and> c_red_exp (s, e2) a (s', e2')) \<or>
      (\<exists> e1'. AppExp e1' e2 = e' \<and> c_red_exp (s, e1) a (s', e1'))
    | other \<Rightarrow> False
  )"    
   
fun f_red_exp :: "p_state \<times> p_exp \<Rightarrow> p_act \<Rightarrow> p_state \<times> p_exp \<Rightarrow> bool" where
  "f_red_exp (s, AppExp e1 e2) a (s', e') = disj_trap (app_red_exp (s, AppExp e1 e2) a (s', e')) (
      (\<exists> e2'. AppExp e1 e2' = e' \<and> is_sexp e1 \<and> f_red_exp (s, e2) a (s', e2')) \<or>
      (\<exists> e1'. AppExp e1' e2 = e' \<and> f_red_exp (s, e1) a (s', e1'))
  )"
| "f_red_exp (s, other) a (s', e') = False"
      
  

    

    


    
(*well_typed (red_env env (AppExp e11 e2') tau' ax) (red_use_env r_s1 (AppExp e11 e2') ax) e11 (FunTy t1 tau r a) (red_use_env r_s1 e2 ax)
            (comp_use_env rx1 (infl_use_env r_s1 r_s2a))*)  
  
lemma well_typed_red_vars: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; free_vars e \<subseteq> free_vars e'; safe_act s ax; sub_env s env \<rbrakk> \<Longrightarrow>
  well_typed (red_env env t ax) r_s1 e tau r_s2 rx"    
  apply (case_tac ax)
    apply (auto)
   apply (rule_tac x="x2" and t="t" in well_typed_add_vars)
    apply (auto)
   apply (cut_tac env="env" and x="x2" and e="e" in well_typed_fv_env_use)
     apply (auto)
   apply (simp add: sub_env_def)(*
  apply (rule_tac well_typed_rem_vars)
   apply (auto)*)
  done    
    
   (*
lemma red_leq_use_env: "leq_use_env r_s (red_use_env r_s ax)"
  apply (case_tac ax)
   apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac rhs_add_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (case_tac "r_s x2")
    apply (auto)
  done
     *)

    
lemma well_typed_add_permsx: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; x \<notin> free_vars e; r = OwnPerm \<rbrakk> \<Longrightarrow>
  well_typed env (add_use_env r_s1 x r) e tau (add_use_env r_s2 x r) rx"
  apply (rule_tac rx="rem_use_env rx x" in well_typed_incr_req)
    apply (cut_tac r_s="r_s1" and x="x" and r="r" in partial_add_rem_use_env)
    apply (cut_tac r_s="r_s2" and x="x" and r="r" in partial_add_rem_use_env)
  (*apply (cut_tac r_s="rx" and x="x" in ignore_rem_use_env)
   apply (simp)*)
    apply (cut_tac r_s="rem_use_env r_s1 x" and x="x" and r="r" in add_comp_use_env)
     apply (auto)
    apply (cut_tac r_s="rem_use_env r_s2 x" and x="x" and r="r" in add_comp_use_env)
     apply (auto)
    apply (rule_tac well_typed_comp_perms_gen)
     apply (rule_tac well_typed_rem_perms)
      apply (auto)
    apply (simp add: mini_disj_use_env_def)
    apply (simp add: one_use_env_def)
    apply (simp add: rem_use_env_def)
   apply (rule_tac self_rem_leq_use_env)
    apply (rule_tac rhs_add_leq_use_env)
   apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and tau="tau" and ?r_s2.0="r_s2" and rx="rx" and x="x" in well_typed_rem_perms)
     apply (auto)
  apply (rule_tac well_typed_perm_leqx)
  apply (auto)
  done    

lemma well_typed_red_permsx: "\<lbrakk> well_typed env r_s e tau r_s rx; safe_act s ax; sub_env s env \<rbrakk> \<Longrightarrow>
  well_typed env (red_use_env r_s ax) e tau (red_use_env r_s ax) rx"     
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac well_typed_add_permsx)
    apply (simp)
   apply (case_tac "x2 \<in> free_vars e")
    apply (cut_tac env="env" and x="x2" and e="e" in well_typed_fv_env_use)
      apply (auto)
  apply (simp add: sub_env_def)
  done
    
lemma well_typed_red_perms: "\<lbrakk> well_typed env r_s e tau r_s rx; safe_act s ax; sub_env s env \<rbrakk> \<Longrightarrow>
  well_typed env (red_use_env r_s ax) e tau (red_use_env r_s ax) (red_use_env rx ax)"    
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac rx="rx" in well_typed_incr_req)
    apply (rule_tac well_typed_add_permsx)
      apply (simp)
     apply (case_tac "x2 \<in> free_vars e")
      apply (cut_tac env="env" and x="x2" and e="e" in well_typed_fv_env_use)
        apply (auto)
    apply (simp add: sub_env_def)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (case_tac "rx x2")
     apply (auto)
  apply (rule_tac dist_add_leq_use_env)
  apply (rule_tac well_typed_perm_leqx)
  apply (auto)(*
  apply (rule_tac well_typed_rem_perms)
   apply (auto)*)
  done

lemma mini_disj_infl_use_env: "mini_disj_use_env (infl_use_env r_s r_x) r_x"
  apply (simp add: infl_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  done

lemma mini_disj_infl_use_env2: "mini_disj_use_env r_x (infl_use_env r_s r_x)"
  apply (simp add: infl_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  done

lemma disj_infl_use_env: "disj_use_env (infl_use_env r_s r_x) r_x"
  apply (simp add: disj_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  done    
    

    
  (*
lemma exp_red_leq_use_env: "\<lbrakk> free_vars e \<subseteq> free_vars e' \<rbrakk> \<Longrightarrow> leq_use_env (red_use_env r_s ax) (red_use_env r_s ax)"    
  apply (case_tac ax)
    apply (auto)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac id_leq_use_env)(*
   apply (rule_tac self_rem_leq_use_env)
  apply (rule_tac id_leq_use_env)*)
  done*)
    
    (*
lemma exp_contain_env: "\<lbrakk> free_vars e \<subseteq> free_vars e' \<rbrakk> \<Longrightarrow> contain_env (red_env env tau ax) (red_env env tau ax)"    
  apply (case_tac ax)
    apply (auto)
      apply (rule_tac id_contain_env)
     apply (rule_tac id_contain_env)
    apply (rule_tac id_contain_env)
   apply (rule_tac self_rem_contain_env)
  apply (rule_tac id_contain_env)
  done*)
    

    
lemma comp_red_leq_use_env: "leq_use_env (red_use_env (comp_use_env r_s r_x) ax) (comp_use_env (red_use_env r_s ax) r_x)"    
  apply (case_tac ax)
    apply (auto)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac add_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac comp_leq_use_env1)
     apply (rule_tac self_add_leq_use_env)
     apply (case_tac "r_s x2")
       apply (auto)
    apply (rule_tac self_comp_leq_use_env2)
   apply (simp add: comp_use_env_def)
   apply (simp add: add_use_env_def)
  apply (rule_tac id_leq_use_env)(*
  apply (rule_tac t="rem_use_env (comp_use_env r_s r_x) x3" and s="comp_use_env (rem_use_env r_s x3) (rem_use_env r_x x3)" in subst)
   apply (cut_tac r_s="r_s" and r_x="r_x" and x="x3" in dist_rem_comp_use_env)
   apply (simp)
  apply (rule_tac id_leq_use_env)*)
  done
  
lemma rhs_unroll_add_use_env: "leq_use_env r_x (rem_use_env (diff_use_env r_sa r_sb) x) \<Longrightarrow> leq_use_env r_x (diff_use_env r_sa (add_use_env r_sb x OwnPerm))"    
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done(*
  
lemma end_red_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (end_red_use_env r_x e ax) r_s"        
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac rem_leq_use_env)
  apply (simp)
  done

lemma end_red_leq_use_env2: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (end_red_use_env r_x e ax) (red_use_env r_s e ax)"        
  apply (case_tac ax)
    apply (auto)
   apply (rule_tac rhs_add_leq_use_env)
    apply (simp)
   apply (case_tac "r_x x2")
     apply (auto)
  apply (rule_tac dist_rem_leq_use_env)
  apply (simp)
  done    
    
lemma diff_end_red_leq_use_env_ex: "\<lbrakk> leq_use_env r_x (diff_use_env r_sa r_sb); sub_use_env s r_x; safe_act s ax \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env r_sa (end_red_use_env r_sb e ax))"    
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac r_sb="diff_use_env r_sa r_sb" in trans_leq_use_env)
   apply (rule_tac dist_diff_leq_use_env_gen)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac self_rem_leq_use_env)
  apply (simp)
  done*)
    
lemma diff_red_leq_use_env_ex: "\<lbrakk> leq_use_env r_x (diff_use_env r_sa r_sb); sub_use_env s r_x; safe_act s ax \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env r_sa (red_use_env r_sb ax))"    
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac rhs_unroll_add_use_env)
  apply (rule_tac rhs_rem_leq_use_env)
   apply (simp add: sub_use_env_def)
  apply (simp)(*
  apply (rule_tac r_sb="diff_use_env r_sa r_sb" in trans_leq_use_env)
   apply (rule_tac dist_diff_leq_use_env_gen)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac self_rem_leq_use_env)
  apply (simp)*)
  done
  
lemma trans_sub_use_env: "\<lbrakk> sub_use_env s r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> sub_use_env s r_x"    
  apply (simp add: sub_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
(*
lemma dist_end_red_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (end_red_use_env r_x e ax) (end_red_use_env r_s e ax)"    
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac dist_rem_leq_use_env)
  apply (simp)
  done    *)
    
lemma dist_red_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (red_use_env r_x ax) (red_use_env r_s ax)"    
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
(*
  apply (rule_tac dist_rem_leq_use_env)
  apply (simp)*)
  done
  
lemma disj_red_use_env: "\<lbrakk> disj_use_env r_s r_x; sub_use_env s r_x; safe_act s ax \<rbrakk> \<Longrightarrow> disj_use_env (red_use_env r_s ax) r_x"
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac disj_add_use_env)
   apply (simp add: sub_use_env_def)
  apply (simp)(*
  apply (rule_tac disj_rem_use_envx)
  apply (simp)*)
  done
   (*
lemma diff_end_red_leq_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (end_red_use_env r_x e ax) (diff_use_env (end_red_use_env r_s e ax) r_ex)"    
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac rhs_fold_rem_use_env)
  apply (rule_tac rhs_fold_dcl_use_env)
  apply (rule_tac rhs_flip_use_env)
  apply (rule_tac rhs_unroll_dcl_use_env)
  apply (rule_tac rhs_unroll_rem_use_env)
  apply (rule_tac dist_rem_leq_use_env)
  apply (simp)
  done
    
lemma diff_end_red_leq_use_env2: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (end_red_use_env r_x e ax) (diff_use_env (red_use_env r_s e ax) r_ex)"    
  apply (case_tac ax)
    apply (auto)
   apply (rule_tac r_sb="diff_use_env r_s r_ex" in trans_leq_use_env)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac rhs_add_leq_use_env)
     apply (rule_tac id_leq_use_env)
    apply (case_tac "r_s x2")
      apply (auto)
  apply (rule_tac rhs_fold_rem_use_env)
  apply (rule_tac rhs_fold_dcl_use_env)
  apply (rule_tac rhs_flip_use_env)
  apply (rule_tac rhs_unroll_dcl_use_env)
  apply (rule_tac rhs_unroll_rem_use_env)
  apply (rule_tac dist_rem_leq_use_env)
  apply (simp)
  done
    
lemma dist_diff_end_red_leq_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (end_red_use_env r_x e ax) (end_red_use_env r_ex e ax)) (end_red_use_env r_s e ax)"    
  apply (case_tac ax)
    apply (auto)
  apply (case_tac "\<not> diff_use_env (rem_use_env r_x x3) (rem_use_env r_ex x3) = rem_use_env (diff_use_env r_x r_ex) x3")
   apply (cut_tac r_s="r_x" and r_x="r_ex" and x="x3" in dist_diff_rem_use_env)
   apply (auto)
  apply (rule_tac dist_rem_leq_use_env)
  apply (simp)
  done
  
lemma lhs_unroll_ercl_use_env: "\<lbrakk> leq_use_env (comp_use_env (end_red_use_env r_x e ax) (end_red_use_env r_s e ax)) r_ex \<rbrakk> \<Longrightarrow>
  leq_use_env (end_red_use_env (comp_use_env r_x r_s) e ax) r_ex"    
  apply (case_tac ax)
    apply (auto)
  apply (cut_tac r_s="r_x" and r_x="r_s" and x="x3" in dist_rem_comp_use_env)
  apply (auto)
  done
  
lemma lift_end_red_leq_use_env: "leq_use_env (lift_use_env (end_red_use_env r_s e ax) r) (end_red_use_env (lift_use_env r_s r) e ax)"    
  apply (case_tac ax)
    apply (auto)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (cut_tac r_s="r_s" and x="x3" and r="r" in lift_rem_use_env)
   apply (simp)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac id_leq_use_env)
  done
    
lemma lift_end_red_leq_use_envx: "leq_use_env (end_red_use_env (lift_use_env r_s r) e ax) (lift_use_env (end_red_use_env r_s e ax) r)"     
  apply (case_tac ax)
    apply (auto)
    apply (rule_tac id_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (cut_tac r_s="r_s" and x="x3" and r="r" in lift_rem_use_env)
   apply (simp)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac id_leq_use_env)
  done
    
lemma safe_lift_end_red_use_env: "\<lbrakk> safe_use_lift r_s r \<rbrakk> \<Longrightarrow> safe_use_lift (end_red_use_env r_s e ax) r"    
  apply (case_tac ax)
    apply (auto)
  apply (rule_tac safe_lift_rem_use_env)
  apply (simp)
  done
  
lemma well_typed_red_simul_permx: "\<lbrakk> well_typed env (end_red_use_env r_s1 ex ax) e tau (end_red_use_env r_s2 ex ax) (end_red_use_env rx ex ax); leq_use_env r_s2 r_s1;
  leq_use_env rx r_s2; free_vars ex \<subseteq> free_vars ex' \<rbrakk> \<Longrightarrow> well_typed env (end_red_use_env r_s1 ex' ax) e tau (end_red_use_env r_s2 ex' ax) (end_red_use_env rx ex' ax)"    
  apply (case_tac ax)
    apply (auto)
   apply (case_tac "x3 \<notin> free_vars ex")
    apply (auto)
  apply (case_tac "x3 \<notin> free_vars ex")
   apply (auto)
  apply (rule_tac t="r_s1" and s="add_use_env (rem_use_env r_s1 x3) x3 (r_s1 x3)" in subst)
   apply (cut_tac r_s="r_s1" and x="x3" and r="r_s1 x3" in cancel_add_rem_use_env)
    apply (auto)
  apply (rule_tac t="r_s2" and s="add_use_env (rem_use_env r_s2 x3) x3 (r_s2 x3)" in subst)
   apply (cut_tac r_s="r_s2" and x="x3" and r="r_s2 x3" in cancel_add_rem_use_env)
    apply (auto)
  apply (rule_tac rx="rem_use_env rx x3" in well_typed_incr_req)
    apply (rule_tac ?r_s1.0="add_use_env (rem_use_env r_s1 x3) x3 (r_s2 x3)" in well_typed_incr_start_perm)
     apply (cut_tac r_s="rem_use_env r_s1 x3" and x="x3" and r="r_s2 x3" in add_comp_use_env)
      apply (simp add: rem_use_env_def)
     apply (cut_tac r_s="rem_use_env r_s2 x3" and x="x3" and r="r_s2 x3" in add_comp_use_env)
      apply (simp add: rem_use_env_def)
     apply (auto)
     apply (rule_tac well_typed_comp_perms_gen)
      apply (simp)
     apply (simp add: mini_disj_use_env_def)
     apply (simp add: rem_use_env_def)
     apply (simp add: one_use_env_def)
    apply (rule_tac dist_add_leq_use_env_gen)
     apply (rule_tac id_leq_use_env)
    apply (simp add: leq_use_env_def)
   apply (rule_tac self_rem_leq_use_env)
  apply (cut_tac r_s="r_s2" and x="x3" in cancel_add_rem_use_env)
   apply (auto)
  done*)
    

lemma safe_act_well_typed: "\<lbrakk> well_typed env r_s1 e1 tau r_s2 rx; f_red_exp (s1, e1) ax (s2, e2) \<rbrakk> \<Longrightarrow> safe_act s1 ax"
  apply (case_tac "app_red_exp (s1, e1) ax (s2, e2)")
   apply (rule_tac safe_act_well_typed_app)
    apply (auto)
  apply (induct e1 arbitrary: env r_s1 tau r_s2 rx e2)
       apply (auto)
  apply (simp add: disj_trap_def)
  apply (auto)
   apply (cut_tac ?r_s1.0="r_s2a" and r_c="r_s1" and e="e12" in well_typed_incr_start_perm)
     apply (auto)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (case_tac "app_red_exp (s1, e12) ax (s2, e2')")
    apply (rule_tac safe_act_well_typed_app)
      apply (auto)
  apply (case_tac "app_red_exp (s1, e11) ax (s2, e1')")
   apply (auto)
  apply (rule_tac safe_act_well_typed_app)
   apply (auto)
  done      
    
  (*
lemma well_typed_red_simul_perm: "\<lbrakk> well_typed env (red_use_env r_s1 ax) e tau r_s2 rx; (*leq_use_env r_s2 r_s1;
  leq_use_env rx r_s2;*) free_vars ex \<subseteq> free_vars ex' \<rbrakk> \<Longrightarrow> well_typed env (red_use_env r_s1 ax) e tau r_s2 rx"    
  apply (case_tac ax)
    apply (auto)(*
   apply (case_tac "x3 \<notin> free_vars ex")
    apply (auto)
  apply (case_tac "x3 \<notin> free_vars ex")
   apply (auto)
  apply (rule_tac t="r_s1" and s="add_use_env (rem_use_env r_s1 x3) x3 (r_s1 x3)" in subst)
   apply (cut_tac r_s="r_s1" and x="x3" and r="r_s1 x3" in cancel_add_rem_use_env)
    apply (auto)
  apply (rule_tac t="r_s2" and s="add_use_env (rem_use_env r_s2 x3) x3 (r_s2 x3)" in subst)
   apply (cut_tac r_s="r_s2" and x="x3" and r="r_s2 x3" in cancel_add_rem_use_env)
    apply (auto)
  apply (rule_tac rx="rem_use_env rx x3" in well_typed_incr_req)
    apply (rule_tac ?r_s1.0="add_use_env (rem_use_env r_s1 x3) x3 (r_s2 x3)" in well_typed_incr_start_perm)
     apply (cut_tac r_s="rem_use_env r_s1 x3" and x="x3" and r="r_s2 x3" in add_comp_use_env)
      apply (simp add: rem_use_env_def)
     apply (cut_tac r_s="rem_use_env r_s2 x3" and x="x3" and r="r_s2 x3" in add_comp_use_env)
      apply (simp add: rem_use_env_def)
     apply (auto)
     apply (rule_tac well_typed_comp_perms_gen)
      apply (simp)
     apply (simp add: mini_disj_use_env_def)
     apply (simp add: rem_use_env_def)
     apply (simp add: one_use_env_def)
    apply (rule_tac dist_add_leq_use_env_gen)
     apply (rule_tac id_leq_use_env)
    apply (simp add: leq_use_env_def)
   apply (rule_tac self_rem_leq_use_env)
  apply (cut_tac r_s="r_s2" and x="x3" in cancel_add_rem_use_env)
   apply (auto)*)
  done*)
  
lemma sre_coerce: "\<lbrakk> (\<And>env r_s1 e2 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e tau r_s2 rx; well_typed_state s1 env rs_map; valid_use_env s1 rs_map r_s1; 
            f_red_exp (s1, e) ax (s2, e2); \<not> app_red_exp (s1, e) ax (s2, e2)(*; safe_act env ax*)\<rbrakk>
           \<Longrightarrow> \<exists>tau'. well_typed (red_env env tau' ax) (red_use_env r_s1 ax) e2 tau r_s2 rx \<and>
                      (\<exists>rs_map'. well_typed_state s2 (red_env env tau' ax) rs_map' \<and> valid_use_env s2 rs_map' (red_use_env r_s1 ax)));
  well_typed env r_s1 e tau r_s2 rx; well_typed_state s1 env rs_map; valid_use_env s1 rs_map r_s1;
  f_red_exp (s1, e) ax (s2, e2); \<not> app_red_exp (s1, e) ax (s2, e2)(*; safe_act env ax*) \<rbrakk>
  \<Longrightarrow> (\<exists>tau'. well_typed (red_env env tau' ax) (red_use_env r_s1 ax) e2 tau r_s2 rx \<and>
                      (\<exists>rs_map'. well_typed_state s2 (red_env env tau' ax) rs_map' \<and> valid_use_env s2 rs_map' (red_use_env r_s1 ax)))"
  apply (auto)
  done
    
    (* 
      reduction system: global state, thread local sets of expressions
      type system: global env + perm mapping, thread local perm set

      the main statement we are making is that given e1 \<rightarrow> e2, where e1 is well-typed, e2 is also well-typed.
      e2 may be well-typed under a new env, perm mapping + local perm set.

      the main property is that s2 is also well-typed (getting this involves various constraints on env + rs_map).
      the hard property is ensuring that rs_map remains consistent with all extraneous maps.

      e1 well-typed, s1 well-typed, e1 reduces to e2, "valid" perm set (disjoint from main perm map, subset of s1)
    *)
    (* futures map validity:
        
      no action - r_s1 + rs_map will remain unchanged
      make action - r_s1 will gain 'x', the new resource. rs_map will gain an entry at 'x'
        the resources will be removed from the old r_s1.
      use action - uses include read / write / array ext. if a resource is never used again, it is deleted.
        then, r_s1 will delete 'x'. rs_map will lose permissions at 'x'. if a resource is written to, it may gain permissions.
        then, r_s1 starts unchanged, rs_map will gain permissions at 'x', again removed from the old r_s1.

      the important invariants are, all permissions "added to" rs_map come from r_s1.
      meanwhile r_s1 will only gain permissions if they are completely fresh.
      the easiest way of stating this is that rs_map + r_s1 \<le> their old selves + fresh x
    *)
    
lemma safe_red_exp: "\<lbrakk> well_typed env r_s1 e1 tau r_s2 rx; well_typed_state s1 env rs_map; valid_use_env s1 rs_map r_s1;
  f_red_exp (s1, e1) ax (s2, e2) \<rbrakk> \<Longrightarrow> (\<exists> tau' rs_map'.
  well_typed (red_env env tau' ax) (red_use_env r_s1 ax) e2 tau r_s2 rx \<and>
  (*red_env env ax env' \<and>*) well_typed_state s2 (red_env env tau' ax) rs_map' \<and> valid_use_env s2 rs_map' (red_use_env r_s1 ax))"
    (* first we eliminate the case where the reduction is a simple application. (we do this before induction to remove most cases.) *)
  apply (case_tac "app_red_exp (s1, e1) ax (s2, e2)")
   apply (rule_tac safe_app_red_exp_strict)
       apply (auto)
    (* - prelim: one helpful fact is that reduction always produces safe actions *)
  apply (cut_tac ax="ax" and env="env" and ?s1.0="s1" in safe_act_well_typed)
    apply (auto)
    (* if the application is nested, we induct. *)
  apply (induct e1 arbitrary: env r_s1 e2 tau r_s2 rx)
       apply (auto)
  apply (simp add: disj_trap_def)
  apply (auto)
    (* rhs case. within this there are two cases, one where a reduction is performed on e2, and one where we have to induct on e2 *)
    (* - we start by assuming that we are able that the lemma holds on e2
          (which we will prove later either through safe_app or induction)
       - assuming flat permissions (changing r_s2a to (red r_s1)), and increasing the end perms accordingly
          to contain the new reqs (changing r_s3 to r_s3 + (infl r_s1 r_s2a)).
    *)
   apply (case_tac "\<exists>tau'. well_typed (red_env env tau' ax) (red_use_env r_s1 ax) e2' t1
        (comp_use_env r_s3 (infl_use_env r_s1 r_s2a)) rx2 \<and>
        (\<exists>rs_map'. well_typed_state s2 (red_env env tau' ax) rs_map' \<and> valid_use_env s2 rs_map' (red_use_env r_s1 ax))")
    apply (auto)
    (* - we fill in env'. again, e1 needs flat perms to call safe_app, which we are able to do by calling the s-exp lemma. *)
    apply (rule_tac x="tau'" in exI)
    apply (auto)
    apply (rule_tac x="t1" in exI)
    apply (rule_tac x="r" in exI)
    apply (rule_tac x="a" in exI)
    apply (rule_tac x="red_use_env r_s1 ax" in exI)
    apply (rule_tac x="comp_use_env rx1 (infl_use_env r_s1 r_s2a)" in exI)
    apply (auto)
      apply (rule_tac s="s1" in well_typed_red_vars)
         apply (rule_tac well_typed_red_permsx)
          apply (rule_tac infl_full_sexp_wp)
           apply (auto)
      apply (simp add: well_typed_state_def)
     apply (simp add: well_typed_state_def)
    (* - here we type e2 based on our earlier assumption *)
     apply (rule_tac x="rx2" in exI)
     apply (rule_tac x="comp_use_env r_s3 (infl_use_env r_s1 r_s2a)" in exI)
     apply (auto)(*
       (*apply (rule_tac r_c="red_use_env (comp_use_env r_s3 (infl_use_env r_s1 r_s2a)) e2' ax" in well_typed_decr_end_perm)*)
      apply (rule_tac env'="red_env env tau' ax" in well_typed_contain_env)
       apply (rule_tac ex="e2'" in well_typed_red_simul_perm)
        apply (auto)(*
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
          apply (rule_tac well_typed_perm_leq)
          apply (auto)
         apply (rule_tac well_typed_perm_leq)
         apply (auto)
        apply (rule_tac self_infl_leq_use_env)
       apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
        apply (rule_tac comp_leq_use_env1)
        apply (simp)
       apply (rule_tac comp_leq_use_env2)
       apply (rule_tac self_lift_leq_use_env)*)
      apply (rule_tac exp_contain_env)
      apply (auto)*)
    (* - lastly we prove the various bounds *)
     apply (rule_tac x="r_ex" in exI)
     apply (auto)
    (* - end perm bound *)
         apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
          apply (rule_tac unroll_dcl_use_env)
          apply (rule_tac dist_diff_leq_use_env)
          apply (rule_tac unroll_dcl_use_env)
          apply (rule_tac dist_diff_leq_use_env)
          apply (rule_tac rhs_unroll_dcl_use_env)
          apply (rule_tac mini_disj_diff_leq_use_env2)
           apply (rule_tac dist_diff_leq_use_env)
           apply (rule_tac self_comp_leq_use_env1)
          apply (rule_tac gen_mini_disj_use_env1)
          apply (rule_tac comm_disj_use_env)
          apply (rule_tac r_s="r_s3" in disj_leq_use_env1)
           apply (rule_tac infl_disj_use_env)
           apply (rule_tac well_typed_perm_leq)
           apply (auto)
         apply (rule_tac self_diff_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac comp_leq_use_env1)
          apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
           apply (simp)
          apply (rule_tac self_comp_leq_use_env1)
         apply (rule_tac self_comp_leq_use_env2)
        apply (rule_tac comp_leq_use_env1)
        apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
         apply (simp)
        apply (rule_tac self_comp_leq_use_env2)
(*
    (* - result used for diff_end_red_leq_use_env_ex lemma *)
           apply (cut_tac s="s1" and r_s="r_s1" and r_x="end_red_use_env r_s2 (AppExp e11 e2') ax" in trans_sub_use_env)
             apply (simp add: valid_use_env_def)
            apply (rule_tac end_red_leq_use_env)
            apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
             apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
              apply (rule_tac well_typed_perm_leq)
              apply (auto)
            apply (rule_tac diff_leq_use_env)
            apply (rule_tac well_typed_perm_leq)
            apply (auto)
    (* - end perm bound *)
           apply (rule_tac rhs_unroll_dcl_use_env)
           apply (rule_tac s="s1" in diff_end_red_leq_use_env_ex)
             apply (auto)
           apply (rule_tac rhs_fold_dcl_use_env)
           apply (rule_tac rhs_flip_use_env)
           apply (rule_tac rhs_unroll_dcl_use_env)
           apply (rule_tac rhs_flip_use_env)
           apply (rule_tac rhs_unroll_dcl_use_env)
           apply (rule_tac s="s1" in diff_end_red_leq_use_env_ex)
             apply (auto)
           apply (rule_tac r_sb="diff_use_env (end_red_use_env r_s3 (AppExp e11 e2') ax) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
            apply (rule_tac r_sb="diff_use_env (end_red_use_env r_s3 (AppExp e11 e2') ax)
                (comp_use_env (comp_use_env (comp_use_env rx1 (infl_use_env r_s1 r_s2a)) (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
             apply (rule_tac lhs_flip_use_env)
             apply (rule_tac lhs_unroll_dcl_use_env)
             apply (rule_tac lhs_flip_use_env)
             apply (rule_tac lhs_unroll_dcl_use_env)
             apply (rule_tac dist_diff_leq_use_env)
             apply (rule_tac dist_diff_leq_use_env_gen)
              apply (rule_tac dist_diff_leq_use_env)
              apply (rule_tac dist_end_red_leq_use_env)
              apply (rule_tac self_comp_leq_use_env1)
             apply (rule_tac dist_lift_leq_use_env)
             apply (rule_tac end_red_leq_use_env)
             apply (rule_tac id_leq_use_env)
            apply (rule_tac unroll_dcl_use_env)
            apply (rule_tac dist_diff_leq_use_env)
            apply (rule_tac unroll_dcl_use_env)
            apply (rule_tac dist_diff_leq_use_env)
            apply (rule_tac rhs_unroll_dcl_use_env)
            apply (rule_tac mini_disj_diff_leq_use_env)
             apply (rule_tac id_leq_use_env)
            apply (rule_tac gen_mini_disj_use_env1)
            apply (rule_tac comm_disj_use_env)
            apply (rule_tac r_s="r_s3" in disj_leq_use_env1)
             apply (rule_tac infl_disj_use_env)
             apply (rule_tac well_typed_perm_leq)
             apply (auto)
            apply (rule_tac diff_leq_use_env)
            apply (rule_tac end_red_leq_use_env)
            apply (rule_tac id_leq_use_env)
           apply (rule_tac diff_end_red_leq_use_env)
           apply (simp)
          apply (rule_tac safe_lift_end_red_use_env)
          apply (simp)*)
    (* - containment bound *)(*
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac dist_end_red_leq_use_env)
          apply (rule_tac dist_comp_leq_use_env)
           apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
            apply (rule_tac comp_leq_use_env1)
            apply (simp)
           apply (rule_tac self_comp_leq_use_env1)
          apply (rule_tac self_comp_leq_use_env2)
         apply (rule_tac r_sb="end_red_use_env (lift_use_env rx2 r) (AppExp e11 e2') ax" in trans_leq_use_env)
          apply (rule_tac dist_end_red_leq_use_env)
          apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
           apply (rule_tac comp_leq_use_env1)
           apply (simp)
          apply (rule_tac self_comp_leq_use_env2)
         apply (rule_tac lift_end_red_leq_use_env)*)
    (* - disjointness *)
       apply (rule_tac disj_comp_use_env1)
        apply (simp)
       apply (rule_tac comm_disj_use_env)
       apply (rule_tac infl_disj_use_env)
       apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
        apply (simp)
       apply (rule_tac self_comp_leq_use_env2)
(*
        apply (rule_tac r_s="comp_use_env rx1 (infl_use_env r_s1 r_s2a)" in disj_leq_use_env1)
         apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
          apply (rule_tac disj_comp_use_env1)
           apply (simp)
          apply (rule_tac comm_disj_use_env)
          apply (rule_tac infl_disj_use_env)
          apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
           apply (rule_tac well_typed_perm_leq)
           apply (auto)
          apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
           apply (simp)
          apply (rule_tac self_comp_leq_use_env2)
         apply (rule_tac dist_lift_leq_use_env)
         apply (rule_tac end_red_leq_use_env)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac end_red_leq_use_env)
        apply (rule_tac id_leq_use_env)*)
    (* - in-between bound *)(*
       apply (rule_tac dist_end_red_leq_use_env)
       apply (simp)*)
    (* - subtractibility bound *)
      apply (rule_tac red_leq_use_env)
      apply (auto)
    (*
      apply (rule_tac end_red_leq_use_env2)
      apply (simp)*)
    (* - requirements bound *)
     apply (simp add: app_req_def)
     apply (auto)
     apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
      apply (simp)
     apply (rule_tac lhs_dist_dcl_use_env)
     apply (rule_tac rhs_dist_dcl_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac lhs_dist_dcl_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac lhs_unroll_dcl_use_env)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac r_sb="diff_use_env (infl_use_env r_s1 r_s2a) (infl_use_env r_s1 r_s2a)" in trans_leq_use_env)
       apply (rule_tac r_sb="empty_use_env" in trans_leq_use_env)
        apply (rule_tac leq_empty_use_env)
       apply (rule_tac diff_infl_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env_gen)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac self_comp_leq_use_env2)
     apply (rule_tac comp_leq_use_env2)
     apply (rule_tac unroll_dcl_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (rule_tac unroll_dcl_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (rule_tac lhs_unroll_dcl_use_env)
     apply (rule_tac self_diff_leq_use_env)
    (*
     apply (rule_tac r_sb="diff_use_env (end_red_use_env (comp_use_env (comp_use_env rx1 (infl_use_env r_s1 r_s2a)) rx2) (AppExp e11 e2') ax)
              (end_red_use_env (comp_use_env
                (comp_use_env (comp_use_env rx1 (infl_use_env r_s1 r_s2a)) (lift_use_env rx2 r)) r_ex) (AppExp e11 e2') ax)" in trans_leq_use_env)
      apply (rule_tac dist_diff_end_red_leq_use_env)
      apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac lhs_dist_dcl_use_env)
      apply (rule_tac rhs_dist_dcl_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac lhs_dist_dcl_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac unroll_dcl_use_env)
        apply (rule_tac dist_diff_leq_use_env)
        apply (rule_tac unroll_dcl_use_env)
        apply (rule_tac dist_diff_leq_use_env)
        apply (rule_tac lhs_unroll_dcl_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac r_sb="diff_use_env (infl_use_env r_s1 r_s2a) (infl_use_env r_s1 r_s2a)" in trans_leq_use_env)
        apply (rule_tac r_sb="empty_use_env" in trans_leq_use_env)
         apply (rule_tac leq_empty_use_env)
        apply (rule_tac diff_infl_leq_use_env)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac comp_leq_use_env2)
      apply (rule_tac unroll_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac unroll_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac lhs_unroll_dcl_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (rule_tac dist_diff_leq_use_env_gen)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac dist_end_red_leq_use_env)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac dist_end_red_leq_use_env)
      apply (rule_tac self_comp_leq_use_env2)
     apply (rule_tac lhs_unroll_ercl_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac lhs_unroll_ercl_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac comp_leq_use_env2)
      apply (rule_tac lift_end_red_leq_use_envx)
     apply (rule_tac self_comp_leq_use_env2)*)
    (* proving state validity is maintained *)(*
           apply (rule_tac dist_diff_leq_use_env_gen)
            apply (rule_tac id_leq_use_env)
    
           apply (rule_tac rhs_fold_dcl_use_env)
           apply (rule_tac rhs_fold_dcl_use_env)
           apply (rule_tac rhs_flip_use_env)
           apply (rule_tac unroll_dcl_use_env)
    apply (rule_tac dist_diff_leq_use_env)
           apply (rule_tac rhs_fold_dcl_use_env)
           apply (rule_tac rhs_flip_use_env)
    
          apply (rule_tac id_leq_use_env)
         apply (rule_tac r_s="r_s2a" in mini_disj_leq_use_env2)
          apply (rule_tac mini_disj_infl_use_env)
         apply (rule_tac diff_leq_use_env)
         apply (rule_tac diff_leq_use_env)
         apply (rule_tac diff_leq_use_env)
          apply (rule_tac well_typed_perm_leq)
         apply (auto)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac comp_leq_use_env1)
         apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
          apply (simp)
         apply (rule_tac self_comp_leq_use_env1)
        apply (rule_tac self_comp_leq_use_env2)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
        apply (simp)
       apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac disj_comp_use_env1)
       apply (simp)
      apply (rule_tac r_s="r_s2a" in disj_leq_use_env2)
       apply (rule_tac disj_infl_use_env)
      apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
       apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
      apply (rule_tac self_comp_leq_use_env2)
     apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
      apply (rule_tac red_leq_use_env)
     apply (simp)
    apply (simp add: app_req_def)
    apply (auto)
    apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac lhs_dist_dcl_use_env)
    apply (rule_tac rhs_dist_dcl_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac comp_leq_use_env1)
     apply (rule_tac lhs_dist_dcl_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac unroll_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac unroll_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac lhs_unroll_dcl_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (rule_tac r_sb="diff_use_env (infl_use_env r_s1 r_s2a) (infl_use_env r_s1 r_s2a)" in trans_leq_use_env)
      apply (rule_tac r_sb="empty_use_env" in trans_leq_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac diff_infl_leq_use_env)
     apply (rule_tac dist_diff_leq_use_env_gen)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac comp_leq_use_env1)
     apply (rule_tac comp_leq_use_env1)
     apply (rule_tac self_comp_leq_use_env2)
    apply (rule_tac comp_leq_use_env2)
    apply (rule_tac unroll_dcl_use_env)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac unroll_dcl_use_env)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac lhs_unroll_dcl_use_env)
    apply (rule_tac self_diff_leq_use_env)*)
    (* - what remains is to prove the initial assumption we made about e2.
       - to start, we have to change the permissions on e12's well typed-ness statement.
    *)
   apply (cut_tac env="env" and ?r_s1.0="r_s2a" and ?r_s2.0="r_s3" and r_ex="infl_use_env r_s1 r_s2a" and e="e12" in well_typed_comp_perms_gen)
     apply (auto)
    apply (rule_tac mini_disj_infl_use_env2)
   apply (cut_tac env="env" and ?r_s1.0="comp_use_env r_s2a (infl_use_env r_s1 r_s2a)" and r_c="r_s1" and
      ?r_s2.0="comp_use_env r_s3 (infl_use_env r_s1 r_s2a)" and e="e12" in well_typed_incr_start_perm)
     apply (auto)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac lhs_infl_leq_use_env)
    apply (rule_tac id_leq_use_env)
    (* rhs reduct case. in this case, our goal is to apply the safe_app lemma on e2. *)
   apply (case_tac "app_red_exp (s1, e12) ax (s2, e2')")
    apply (cut_tac env="env" and ?r_s1.0="r_s1" and ?e1.0="e12" and ?e2.0="e2'" in safe_app_red_exp_strict)
        apply (auto)
    (* rhs induct case. in this case, our goal is to induct on e2, which we do with a classic coercion lemma *)
   apply (cut_tac env="env" and e="e12" and ?r_s1.0="r_s1" and ?e2.0="e2'" and tau="t1" and ?r_s2.0="comp_use_env r_s3 (infl_use_env r_s1 r_s2a)" and rx="rx2" in sre_coerce)
         apply (auto)
    (* lhs case.
      - we again start by assuming that the lemma holds for e1. this time we don't require any change of permissions beforehand.
    *)
   apply (case_tac "\<exists>tau'. well_typed (red_env env tau' ax) (red_use_env r_s1 ax) e1' (FunTy t1 tau r a) r_s2a rx1 \<and>
                      (\<exists> rs_map'. well_typed_state s2 (red_env env tau' ax) rs_map' \<and> valid_use_env s2 rs_map' (red_use_env r_s1 ax))")
   apply (auto)
    (* - this makes typing e1 straightforward *)
   apply (rule_tac x="tau'" in exI)
   apply (auto)
   apply (rule_tac x="t1" in exI)
   apply (rule_tac x="r" in exI)
   apply (rule_tac x="a" in exI)
   apply (rule_tac x="r_s2a" in exI)
   apply (rule_tac x="rx1" in exI)
   apply (auto)
    (* - this also makes typing e2 straightforward *)
   apply (rule_tac x="rx2" in exI)
   apply (rule_tac x="r_s3" in exI)
   apply (auto)
    apply (rule_tac well_typed_red_vars)
       apply (auto)
    apply (simp add: well_typed_state_def)
    (* - lastly, filling in the existentials is also straightforward *)
   apply (rule_tac x="r_ex" in exI)
   apply (auto)
   apply (rule_tac red_leq_use_env)
   apply (simp)
    (* lhs reduct case. our goal is to again apply the safe app lemma, which we can do without change of permissions *)
  apply (case_tac "app_red_exp (s1, e11) ax (s2, e1')")
   apply (cut_tac env="env" and ?r_s1.0="r_s1" and ?e1.0="e11" and ?e2.0="e1'" in safe_app_red_exp_strict)
       apply (auto)
    (* lhs induct case. lastly we can perform another coercion for the inductive case *)
  apply (cut_tac env="env" and e="e11" and ?r_s1.0="r_s1" and ?e2.0="e1'" and tau="FunTy t1 tau r a" and ?r_s2.0="r_s2a" and rx="rx1" in sre_coerce)
        apply (auto)
  done
    
end