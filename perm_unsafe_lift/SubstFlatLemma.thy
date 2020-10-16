theory SubstFlatLemma
  imports SubstDropEnv
begin
  (*
definition refl_use_env where
  "refl_use_env r_s r_x r = (\<lambda> x. if r_s x = OwnPerm \<and> r_x x = NoPerm then r else NoPerm)"

lemma refl_leq_use_env: "leq_use_env (refl_use_env r_s r_x r) r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: refl_use_env_def)
  done  
  
lemma refl_disj_use_env: "\<lbrakk> leq_use_env r_ex r_x \<rbrakk> \<Longrightarrow> disj_use_env r_ex (refl_use_env r_s r_x r)"  
  apply (simp add: leq_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: refl_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
  done  
  
lemma trans_leq_perm: "\<lbrakk> leq_perm p q; leq_perm q r \<rbrakk> \<Longrightarrow> leq_perm p r"  
  apply (case_tac q)
    apply (auto)
    apply (case_tac p)
      apply (auto)
   apply (case_tac r)
     apply (auto)
  apply (case_tac r)
    apply (auto)
  done
  
lemma rswp_gen_leq_use_env: "\<lbrakk> leq_use_env r_ex r_s1; leq_use_env r_s2 (diff_use_env r_s1 r_ex);
  leq_use_env (diff_use_env r_x r_ex) rx; (\<forall> x. leq_perm (r_x x) r) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (comp_use_env rx (refl_use_env r_s1 r_s2 r))"
  apply (case_tac "(\<forall> x. leq_perm (r_x x) (comp_use_env rx (refl_use_env r_s1 r_s2 r) x))")
   apply (simp add: leq_use_env_def)
    apply (auto)
    (* in all cases, if EX \<noteq> Own, the case is trivial *)
  apply (case_tac "r_ex x \<noteq> OwnPerm")
   apply (cut_tac r_x="diff_use_env r_x r_ex" and r_s="comp_use_env rx (refl_use_env r_s1 r_s2 r)" and x="x" in spec_leq_perm)
    apply (rule_tac comp_leq_use_env1)
    apply (simp)
   apply (cut_tac r_s="r_x" and r_x="r_ex" and x="x" in diff_use_eq)
    apply (auto)
    (* otherwise, split on r_s1 x1a = Own *)
  apply (case_tac "r_s1 x \<noteq> OwnPerm")
   apply (cut_tac r_x="r_ex" and r_s="r_s1" and x="x" in leq_use_own)
     apply (auto)
    (* - if r_s1 x1a = Own, and EX = Own, r_s2 x1a = None, meaning the reflective case is guaranteed to have a value. *)
  apply (cut_tac r_x="r_s2" and r_s="diff_use_env r_s1 r_ex" and x="x" in leq_use_none)
    apply (simp)
   apply (rule_tac diff_use_none_ex)
   apply (auto)
  apply (cut_tac r_x="r_x" and r_s="comp_use_env rx (refl_use_env r_s1 r_s2 r)" and x="x" in spec_leq_perm)
   apply (cut_tac p="r_x x" and q="refl_use_env r_s1 r_s2 r x" and r="comp_use_env rx (refl_use_env r_s1 r_s2 r) x" in trans_leq_perm)
     apply (simp add: refl_use_env_def)
    apply (rule_tac r_x="refl_use_env r_s1 r_s2 r" in spec_leq_perm)
    apply (rule_tac self_comp_leq_use_env2)
   apply (auto)
  done  

lemma rswp_var_leq_use_env: "\<lbrakk> leq_use_env (ereq_use_env x1a tau) r_s1; leq_use_env r_ex r_s1; var_val_type rf tau_r tau;
  leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau) r_ex)); safe_type tau r; rf \<noteq> NoRef;
  leq_use_env (diff_use_env (ereq_use_env x1a tau) (comp_use_env (ereq_use_env x1a tau) r_ex)) rx \<rbrakk> \<Longrightarrow>
  leq_use_env (ereq_use_env x1a tau) (comp_use_env rx (refl_use_env r_s1 r_s2 r))"
  apply (rule_tac r_x="ereq_use_env x1a tau" and r_ex="comp_use_env (ereq_use_env x1a tau) r_ex" in rswp_gen_leq_use_env)    
     apply (rule_tac dist_comp_leq_use_env)
      apply (auto)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (auto)
  apply (simp add: end_req_perm_def)
  apply (case_tac r)
    apply (auto)
  apply (case_tac tau)
        apply (auto)
  done
     
lemma drop_infl_use_env: "drop_use_env (infl_use_env r_s r_x) = refl_use_env r_s r_x UsePerm"    
  apply (case_tac "\<forall> x. drop_use_env (infl_use_env r_s r_x) x = refl_use_env r_s r_x UsePerm x")
   apply (auto)
  apply (simp add: drop_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (simp add: refl_use_env_def)
  apply (case_tac "r_s x = OwnPerm \<and> r_x x = NoPerm")
   apply (auto)
   apply (simp add: infl_use_env_def)
  apply (simp add: infl_use_env_def)
  done

lemma refl_infl_use_env: "infl_use_env r_s r_x = refl_use_env r_s r_x OwnPerm"    
  apply (case_tac "\<forall> x. infl_use_env r_s r_x x = refl_use_env r_s r_x OwnPerm x")
   apply (auto) 
  apply (simp add: infl_use_env_def)
  apply (simp add: refl_use_env_def)
  done
    
lemma refl_sexp_wp: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; is_sexp e; safe_type tau r \<rbrakk> \<Longrightarrow>
  well_typed env (comp_use_env rx (refl_use_env r_s1 r_s2 r)) e tau
  (comp_use_env rx (refl_use_env r_s1 r_s2 r)) (comp_use_env rx (refl_use_env r_s1 r_s2 r))"    
  apply (case_tac r)
    apply (auto)
    (* use case *)
   apply (case_tac "\<not> leq_use_env (drop_use_env (comp_use_env rx (infl_use_env r_s1 r_s2))) (comp_use_env rx (refl_use_env r_s1 r_s2 UsePerm))")
    apply (cut_tac r_sa="rx" and r_sb="infl_use_env r_s1 r_s2" in dist_drop_comp_use_env)
    apply (cut_tac r_xa="drop_use_env rx" and r_xb="drop_use_env (infl_use_env r_s1 r_s2)" and r_s="comp_use_env rx (refl_use_env r_s1 r_s2 UsePerm)" in dist_comp_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac self_drop_leq_use_env)
     apply (cut_tac r_s="r_s1" and r_x="r_s2" in drop_infl_use_env)
     apply (auto)
    apply (rule_tac self_comp_leq_use_env2)
   apply (rule_tac rx="drop_use_env (comp_use_env rx (infl_use_env r_s1 r_s2))" in well_typed_incr_req)   
     apply (rule_tac r_s="drop_use_env (comp_use_env rx (infl_use_env r_s1 r_s2))" in well_typed_incr_simul_perm)
      apply (auto)
    apply (rule_tac wt_sexp_drop_all)
      apply (rule_tac infl_sexp_wp)
       apply (auto)
    apply (simp add: unlim_def)
   apply (rule_tac id_leq_use_env)
    (* ownership case *)
  apply (rule_tac t="refl_use_env r_s1 r_s2 OwnPerm" and s="infl_use_env r_s1 r_s2" in subst)
   apply (rule_tac refl_infl_use_env)
  apply (rule_tac infl_sexp_wp)
   apply (auto)
  done
    
    (*
  (* the goal of this is to come up with flat permissions that are still "safe." *)
lemma refl_sexp_wp: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; is_sexp e; safe_type tau r \<rbrakk> \<Longrightarrow>
  well_typed env (comp_use_env rx (refl_use_env r_s1 r_s2 r)) e tau
  (comp_use_env rx (refl_use_env r_s1 r_s2 r)) (comp_use_env rx (refl_use_env r_s1 r_s2 r))"
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
       apply (auto)
    (* const + op case *)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac id_leq_use_env)
    (* var case p1. *)
     apply (rule_tac r_ex="r_ex" in rswp_var_leq_use_env)
          apply (auto)
    (* var case p2. *)
    apply (rule_tac x="empty_use_env" in exI)
    apply (auto)
       apply (rule_tac rhs_weak_leq_use_env)
        apply (rule_tac dist_weak_comp_use_env)
         apply (rule_tac weak_ereq_use_env)
         apply (simp add: unlim_def)
         apply (case_tac tau)
               apply (auto)
        apply (simp add: weak_use_env_def)
        apply (simp add: empty_use_env_def)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac leq_empty_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (rule_tac r_ex="r_ex" in rswp_var_leq_use_env)
          apply (auto)
    (* pair case *)
    (* - prelim: new reqs for e1 \<le> rx1 *)
    apply (cut_tac r_x="comp_use_env r_xa (refl_use_env rx1 r_sa r)" and r_s="rx1" and r="ra" in dist_lift_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac r_sb="r_sa" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac well_typed_perm_leqx)
      apply (auto)
     apply (rule_tac refl_leq_use_env)
    (* - prelim: new reqs for e2 \<le> rx2 *)
    apply (cut_tac r_x="comp_use_env r_xb (refl_use_env rx2 r_sb r)" and r_s="rx2" and r="ra" in dist_lift_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac r_sb="r_sb" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac well_typed_perm_leqx)
      apply (auto)
     apply (rule_tac refl_leq_use_env)
    (* - prelim: overall inequality proving our new reqs are in rxa *)
    apply (cut_tac r_xa="lift_use_env (comp_use_env r_xa (refl_use_env rx1 r_sa r)) ra " and
      r_xb="lift_use_env (comp_use_env r_xb (refl_use_env rx2 r_sb r)) ra" and r_s="rxa" in dist_comp_leq_use_env)
      apply (rule_tac r_sb="lift_use_env rx1 ra" in trans_leq_use_env)
       apply (simp_all)
     apply (rule_tac r_sb="lift_use_env rx2 ra" in trans_leq_use_env)
      apply (simp_all)
    (* - prelim: the other half of the inequality proving rxa contained in rx + [r_s1 - r_s2] *)
    apply (cut_tac ?r_s1.0="r_s1" and r_x="rxa" and rx="rx" and ?r_s2.0="r_s2" and r_ex="r_ex" and r="r" in rswp_gen_leq_use_env)
        apply (auto)
     apply (case_tac r)
       apply (auto)
     apply (simp add: unlim_def)
     apply (simp add: aff_use_env_def)
     apply (case_tac "max_aff (req_type t1) (req_type t2)")
       apply (auto)
      apply (simp add: weak_use_env_def)
      apply (case_tac "rxa x")
        apply (auto)
     apply (simp add: null_use_env_def)
    (* - well-typedness *)
    apply (rule_tac x="comp_use_env (lift_use_env (comp_use_env r_xa (refl_use_env rx1 r_sa r)) ra)
      (lift_use_env (comp_use_env r_xb (refl_use_env rx2 r_sb r)) ra)" in exI)
    apply (rule_tac x="comp_use_env r_xa (refl_use_env rx1 r_sa r)" in exI)
    apply (auto)
     apply (rule_tac x="comp_use_env r_xa (refl_use_env rx1 r_sa r)" in exI)
     apply (rule_tac x="comp_use_env r_xa (refl_use_env rx1 r_sa r)" in exI)
     apply (cut_tac e="e1" in value_is_sexp)
      apply (auto)
     apply (case_tac "\<not> safe_type t1 r")
      apply (case_tac r)
        apply (auto)
     apply (simp add: unlim_def)
    apply (rule_tac x="comp_use_env r_xb (refl_use_env rx2 r_sb r)" in exI)
    apply (auto)
          apply (rule_tac x="comp_use_env r_xb (refl_use_env rx2 r_sb r)" in exI)
          apply (rule_tac x="comp_use_env r_xb (refl_use_env rx2 r_sb r)" in exI)
          apply (cut_tac e="e2" in value_is_sexp)
           apply (auto)    
          apply (case_tac "\<not> safe_type t2 r")
           apply (case_tac r)
             apply (auto)
          apply (simp add: unlim_def)
          apply (case_tac "req_type t1")
            apply (auto)
         apply (rule_tac r_s="rxa" in aff_leq_use_env)
          apply (simp_all)
        apply (rule_tac r_sb="rxa" in trans_leq_use_env)
         apply (simp_all)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac self_comp_leq_use_env2)
     apply (rule_tac r_s="lift_use_env rx1 ra" in disj_leq_use_env1)
      apply (rule_tac r_s="lift_use_env rx2 ra" in disj_leq_use_env2)
       apply (simp_all)
    apply (rule_tac x="empty_use_env" in exI)
    apply (auto)
       apply (rule_tac rhs_weak_leq_use_env)
        apply (simp add: weak_use_env_def)
        apply (simp add: empty_use_env_def)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac leq_empty_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (rule_tac r_sb="rxa" in trans_leq_use_env)
     apply (simp_all)
    (* lam case. prelim: this inequality is used twice *)
   apply (cut_tac r_x="rxa" and r_ex="r_ex" and ?r_s1.0="r_s1" and ?r_s2.0="r_s2" and r="r" in rswp_gen_leq_use_env)
       apply (auto)
    apply (case_tac r)
      apply (auto)
    apply (simp add: unlim_def)
    apply (simp add: aff_use_env_def)
    apply (case_tac a)
      apply (auto)
     apply (simp add: weak_use_env_def)
     apply (case_tac "rxa x")
       apply (auto)
    apply (simp add: null_use_env_def)(*
   apply (cut_tac r_x="rxa" and r_s="rx" and r_ex="infl_use_env r_s1 r_s2" in st_diff_comp_leq_use_env)
    apply (rule_tac r_sb="diff_use_env rxa r_ex" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac dist_diff_leq_use_env_cut)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac infl_leq_use_env)
     apply (simp_all)*)
    (* - existentials *)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="empty_use_env" in exI)
   apply (auto)
      apply (rule_tac rhs_weak_leq_use_env)
       apply (simp add: weak_use_env_def)
       apply (simp add: empty_use_env_def)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac leq_empty_use_env)
   apply (rule_tac diff_leq_use_env)
   apply (simp)
    (* app case.*)
  apply (case_tac e1)
       apply (auto)
  apply (case_tac x1)
               apply (auto)
  apply (simp add: pure_fun_def)
  apply (auto)
    (* - proof for e1 *)
  apply (rule_tac x="comp_use_env rx (refl_use_env r_s1 r_s2 r)" in exI)
  apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
    (* - proof for e2. we must know that it's a lambda rather than inducting, so we know rx2 is non-affine *)
  apply (case_tac e2)
       apply (auto)
    (* - prelim: r_s3 \<le> r_s1 *)
  apply (cut_tac r_sc="r_s3" and r_sb="diff_use_env r_s2a r_exa" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (auto)
    (* - prelim: this inequality is used several times in the remainder of the proof *)
  apply (case_tac "\<not> leq_use_env rxa (comp_use_env rx (refl_use_env r_s1 r_s2 r))")
    (* - we split it based on whether it's primitive *)
   apply (simp add: app_req_def)
   apply (case_tac "req_type t = Prim")
    apply (auto)
    apply (simp add: leq_use_env_def)
    apply (simp add: aff_use_env_def)
    apply (simp add: null_use_env_def)
    (* - if it's not we use the usual lemma *)
   apply (cut_tac r_x="rxa" and r_ex="comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex)" and rx="rx" and
      ?r_s1.0="r_s1" and ?r_s2.0="r_s2" and r="r" in rswp_gen_leq_use_env)
       apply (auto)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
        apply (auto)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (auto)
     apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
      apply (rule_tac rhs_unroll_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s2a r_exa" in trans_leq_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (auto)
    apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac lhs_unroll_dcl_use_env)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac comp_leq_use_env2)
    apply (simp)
   apply (simp add: unlim_def)
   apply (case_tac "req_type t")
     apply (auto)
   apply (case_tac r)
     apply (auto)
   apply (simp add: aff_use_env_def)
   apply (simp add: weak_use_env_def)
   apply (case_tac "rxa x")
     apply (auto)
(*
  apply (cut_tac r_x="rxa" and r_s="rx" and r_ex="infl_use_env r_s1 r_s2" in st_diff_comp_leq_use_env)
    (* - we split it based on whether it's primitive or not *)
   apply (simp add: app_req_def)
   apply (case_tac "req_type t = Prim")
    apply (auto)
    apply (rule_tac diff_leq_use_env)
    apply (rule_tac r_sb="empty_use_env" in trans_leq_use_env)
     apply (rule_tac leq_empty_use_env)
    apply (simp add: leq_use_env_def)
    apply (simp add: aff_use_env_def)
    apply (simp add: null_use_env_def)
    (* - non primitive case actually uses an inequality *)
   apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac r_sb="diff_use_env (diff_use_env rxa r_exa) (infl_use_env r_s1 r_s2)" in trans_leq_use_env)
    apply (rule_tac dist_diff_leq_use_env_cut)
     apply (rule_tac comp_leq_use_env2)
     apply (simp)
    apply (rule_tac infl_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s2a r_exa" in trans_leq_use_env)
       apply (rule_tac diff_leq_use_env)
       apply (simp_all)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s2a r_exa" in trans_leq_use_env)
       apply (rule_tac diff_leq_use_env)
       apply (simp_all)
   apply (rule_tac rhs_diff_leq_use_env)
   apply (rule_tac dist_diff_leq_use_env_cut)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac infl_leq_use_env)
    apply (rule_tac r_sb="diff_use_env r_s2a r_exa" in trans_leq_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (simp)
    apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (simp_all)
   apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
    apply (simp_all)*)
    (* - completing the proof for e2 *)
  apply (rule_tac x="rxa" in exI)
  apply (rule_tac x="comp_use_env rx (refl_use_env r_s1 r_s2 r)" in exI)
  apply (auto)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="empty_use_env" in exI)
   apply (auto)
      apply (rule_tac rhs_weak_leq_use_env)
       apply (simp add: weak_use_env_def)
       apply (simp add: empty_use_env_def)
      apply (rule_tac id_leq_use_env)
    apply (rule_tac leq_empty_use_env)
   apply (rule_tac self_diff_leq_use_env)
    (* - end permissions bound *)
  apply (case_tac "\<not> weak_use_env empty_use_env")
   apply (simp add: weak_use_env_def)
   apply (simp add: empty_use_env_def)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
        apply (rule_tac rhs_weak_leq_use_env)
         apply (rule_tac dist_weak_comp_use_env)
          apply (rule_tac dist_weak_comp_use_env)
           apply (simp_all)
         apply (simp add: aff_use_env_def)
         apply (case_tac "req_type t")
           apply (auto)
          apply (simp add: unlim_def)
         apply (simp add: weak_use_env_def)
         apply (simp add: null_use_env_def)
        apply (rule_tac id_leq_use_env)
    (* - affinity *)
       apply (simp add: aff_use_env_def)
       apply (simp add: weak_use_env_def)
       apply (case_tac "req_type t")
         apply (auto)
         apply (simp add: unlim_def)
        apply (simp add: weak_use_env_def)
       apply (simp add: null_use_env_def)
    (* - requirements containment *)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (simp)
    (* - disjointness *)
    apply (rule_tac disj_empty_use_env2)
    (* - in-between bound *)
    apply (rule_tac id_leq_use_env)
    (* - subtracter containment *)
   apply (rule_tac leq_empty_use_env)
    (* - requirements bound *)
  apply (simp add: app_req_def)
  apply (case_tac "req_type t = Prim")
   apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac r_sb="rxa" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac diff_leq_use_env)
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac id_leq_use_env)
  done    *)    

lemma refl_full_sexp_wp: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; is_sexp e; safe_type tau r \<rbrakk> \<Longrightarrow>
  well_typed env r_s1 e tau r_s1 (comp_use_env rx (refl_use_env r_s1 r_s2 r))" 
  apply (rule_tac r_s="comp_use_env rx (refl_use_env r_s1 r_s2 r)" in well_typed_incr_simul_perm)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
   apply (rule_tac refl_leq_use_env)
  apply (rule_tac refl_sexp_wp)
    apply (auto)
  done    
  *)
end