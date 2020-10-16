theory OldFlatLemma
  imports WTLemma NormEnv
begin

  (*
  
    (* -we want to show that rxa is disjoint from rx1. so for all x in rxa, x not in rx1.
      again, if rx2 contains x, then again this is trivial since rx2 is already disjoint. otherwise
      it was subtracted out of rxa. but this again implies that r_s2  also had x subtracted out, and rx1 \<le> r_s2. *)
lemma swp_disj_use_env: "\<lbrakk>leq_use_env rx1 r_s2; disj_use_env rx2 rx1; leq_use_env r_s2 (diff_use_env r_s1 r_ex); leq_use_env rx1 r_s2;
        leq_use_env (diff_use_env rxa r_ex) rx2 \<rbrakk> \<Longrightarrow> disj_use_env rxa rx1"
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (case_tac "rxa x = NoPerm")
   apply (auto)
  apply (case_tac "rx2 x \<noteq> NoPerm")
   apply (erule_tac x="x" in allE)
   apply (auto)
  apply (cut_tac r_s="r_s1" and r_x="rxa" and r_ex="r_ex" and x="x" in diff_use_none)
    apply (auto)
   apply (rule_tac r_s="rx2" in leq_use_none)
    apply (auto)
  apply (cut_tac r_x="rx1" and r_s="diff_use_env r_s1 r_ex" and x="x" in leq_use_none)
    apply (auto)
  apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
   apply (auto)
  done*)
    
    (* - var ordering. if lift rx \<le> r_s2, but \<not> lift rxa \<le> r_s1, rxa x = Use + r_s1 x = Use. r_ex x \<noteq> OwnPerm, but then Use \<le> rx x.
      but in this case, lift rx x = Own, so r_s2 x = Own, so r_s1 x = Own, which is a contradiction *)
lemma swp_leq_use_env: "\<lbrakk> leq_use_env (lift_use_env rx r) r_s2; leq_use_env r_s2 r_s1; leq_use_env r_ex r_s1;
  leq_use_env (diff_use_env rxa r_ex) rx; leq_use_env rxa r_s1 \<rbrakk> \<Longrightarrow> leq_use_env (lift_use_env rxa r) r_s1"    
  apply (case_tac "leq_use_env (lift_use_env rxa r) r_s1")
   apply (auto)
  apply (case_tac "\<forall> x. leq_perm (lift_use_env rxa r x) (r_s1 x)")
   apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "\<not> leq_perm (rxa x) (r_s1 x)")
   apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "rxa x \<noteq> UsePerm")
   apply (case_tac r)
     apply (auto)
   apply (case_tac "rxa x")
     apply (auto)
  apply (case_tac "r_s1 x")
    apply (auto)
  apply (cut_tac r_x="r_ex" and r_s="r_s1" and x="x" in leq_use_no_own)
    apply (auto)
  apply (cut_tac r_s="rxa" and r_x="r_ex" and x="x" in diff_use_eq)
   apply (auto)
  apply (case_tac "rx x = NoPerm")
   apply (cut_tac r_x="diff_use_env rxa r_ex" and r_s="rx" and x="x" in leq_use_none)
     apply (auto)
  apply (case_tac "lift_use_env rx r x \<noteq> OwnPerm")
   apply (case_tac r)
     apply (auto)
  apply (cut_tac r_x="lift_use_env rx r" and r_s="r_s1" and x="x" in leq_use_own)
    apply (auto)
  apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
   apply (auto)
  done  
  
lemma swp_disj_use_env: "\<lbrakk>leq_use_env rx1 r_s2; disj_use_env rx2 rx1; leq_use_env r_s2 (diff_use_env r_s1 r_ex); leq_use_env rx1 r_s2;
        leq_use_env (diff_use_env rxa r_ex) rx2 \<rbrakk> \<Longrightarrow> disj_use_env rxa rx1"
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
    (* first we would like to show that rxa x = Own implies rx1 x = None.
      if we ever have r_ex x = Own, then rx1 x \<le> (r_s1 - r_ex) x = None.
    *)
  apply (case_tac "r_ex x = OwnPerm")
    apply (rule_tac r_s="diff_use_env r_s1 r_ex" in leq_use_none)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (simp_all)
    apply (cut_tac r_s="r_s1" and r_ex="r_ex" and x="x" in diff_use_none_ex)
     apply (auto)
    (* if rx2 x \<noteq> Own, since rxa x = Own, r_ex x = Own, a contradiction. otherwise, rx1 x = None follows trivially *)
   apply (case_tac "rx2 x \<noteq> OwnPerm")
    apply (cut_tac r_x="rxa" and r_s="rx2" and x="x" and r_ex="r_ex" in diff_use_leq)
      apply (auto)
   apply (case_tac "rx2 x")
     apply (auto)
    (* next we would like to show that rx1 x = Own implies rxa x = None.
      if rx1 x = Own, we know that rx2 x = None. if rxa x \<noteq> None, then r_ex x = Own *)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "rxa x = NoPerm")
   apply (auto)
  apply (cut_tac r_x="rxa" and r_s="rx2" and r_ex="r_ex" and x="x" in diff_use_own)
     apply (auto)
    (* then rx1 x \<le> (r_s1 - r_ex) x = None, a contradiction *)
  apply (cut_tac r_s="diff_use_env r_s1 r_ex" and r_x="rx1" and x="x" in leq_use_none)
    apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
     apply (simp_all)
  apply (rule_tac diff_use_none_ex)
  apply (simp)
  done    
    
lemma swp_mini_disj_use_env: "\<lbrakk> leq_use_env rx_p (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow> mini_disj_use_env r_ex rx_p"    
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (rule_tac r_s="diff_use_env r_s r_ex" in leq_use_none)
   apply (auto)
  apply (rule_tac diff_use_none_ex)
  apply (auto)
  done
  
    (* this notorious lemma allows us to re-write s-expressions so that they have uniform permissions.
        simple enough by itself, but we want to ensure that the permissions meet certain conditions, and aren't
        just totally random.
        - given lift rx r \<le> r_s2, we want lift rx' r \<le> r_s2
            (as a corollary, we want rx' to be liftable)
        - given rx *disjoint from* rx_p, we want to ensure rx' *disjoint from* rx_p
            (as part of this, we assume rx_p is subtractible from rs_2)
       ideally, we would find an exact formulation of rx', from which we could prove these facts as lemmas. however we would
        have to derive it from rx, which is challenging because rx may have extra requirements + may have requirements
        subtracted from the end perms.
       so we accomplish this in parts. first we assume the existence of an rx such that no end perms are removed
     *)
    
    
    (* - this lemma is notably not true because of pair functions. the argument being passed in may be a pair or an affine function.
      the implication is that an s_expression may have uneven permissions (it will use a resource at some point). in principle this
      isn't insurmountable, but it's obviously problematic for us.
    *)
lemma minor_app_lemma: "\<lbrakk> is_sexp (AppExp e1 e2); well_typed env r_s1 e1 (FunTy tau t r a) r_s2 rx1; well_typed env r_s2 e2 tau r_s3 rx2 \<rbrakk> \<Longrightarrow> unlim tau"    
  apply (case_tac e1)
       apply (auto)
  apply (case_tac x1)
              apply (auto)
  apply (simp add: pure_fun_def)
  done

  (*
lemma sexp_wild_perm_pre: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; is_sexp e \<rbrakk> \<Longrightarrow> (\<exists> rx'. well_typed env r_s1 e tau r_s1 rx' \<and> weak_use_env rx')"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
       apply (auto)
    (* const case *)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac x="empty_use_env" in exI)
       apply (auto)
        apply (rule_tac leq_empty_use_env)
       apply (simp add: weak_use_env_def)
       apply (simp add: empty_use_env_def)
    (* op case *)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
      apply (rule_tac leq_empty_use_env)
     apply (simp add: weak_use_env_def)
     apply (simp add: empty_use_env_def)
    (* var case *)
    apply (case_tac "\<not> weak_use_env (req_use_env x1a tau)")
     apply (simp add: req_use_env_def)
     apply (simp add: one_use_env_def)
     apply (simp add: weak_use_env_def)
     apply (auto)
     apply (case_tac "x1a = x")
      apply (auto)
     apply (simp add: start_req_perm_def)
     apply (case_tac "tau")
           apply (auto)    
    apply (rule_tac x="req_use_env x1a tau" in exI)
    apply (auto)
    apply (rule_tac x="empty_use_env" in exI)
    apply (auto)
      apply (rule_tac rhs_weak_leq_use_env)
       apply (rule_tac dist_weak_comp_use_env)
        apply (simp)
       apply (simp add: weak_use_env_def)
       apply (simp add: empty_use_env_def)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac leq_empty_use_env)
    apply (rule_tac self_diff_leq_use_env)
   apply (simp add: weak_use_env_def)
    (* lambda case *)
   apply (rule_tac x="rxa" in exI)
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
    (* app case *)
  apply (case_tac e1)
       apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s2a" and r_c="r_s1" and e="e2" and ?r_s2.0="r_s3" and rx="rx2" in well_typed_incr_start_perm)
    apply (auto)
  apply (cut_tac ?e1.0="ConstExp x1" and ?e2.0="e2" in e2_sexp)
   apply (auto)
  apply (case_tac "\<exists>rx'. well_typed env r_s1 e2 t1 r_s1 rx' \<and> filler rx'")
   apply (erule_tac exE)
   apply (auto)
  apply (simp add: filler_def)
  apply (rule_tac x="rx'" in exI)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (auto)
  apply (rule_tac x="r_s1" in exI)
  apply (auto)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac x="rx'" in exI)
  apply (rule_tac x="r_s1" in exI)
  apply (auto)
  apply (case_tac "\<not> weak_use_env empty_use_env")
   apply (simp add: weak_use_env_def)
   apply (simp add: empty_use_env_def)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
        apply (rule_tac rhs_weak_leq_use_env)
         apply (rule_tac dist_weak_comp_use_env)
          apply (rule_tac dist_weak_comp_use_env)
           apply (simp_all)
    *)
 
  
    (* if the value being passed into an application is being passed in as a use, not only do we require that its requirements be unlim,
        but we require that the type be unlimited, since otherwise it could be hiding affine values. 
    *)    

lemma sexp_wild_perm: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; leq_use_env (lift_use_env rx r) r_s2; safe_use_lift rx r; safe_type tau r;
  leq_use_env rx_p r_s2; disj_use_env rx rx_p; is_sexp e \<rbrakk> \<Longrightarrow>
  (\<exists> rx' r_ex. well_typed env rx' e tau rx' rx' \<and> leq_use_env rx rx' \<and> leq_use_env (lift_use_env rx' r) r_s1 \<and> safe_use_lift rx' r \<and>
    leq_use_env (diff_use_env rx' r_ex) rx \<and> leq_use_env r_ex r_s1 \<and> disj_use_env r_ex rx_p \<and> mini_disj_use_env r_ex r_s2)"
  apply (induct e arbitrary: env r_s1 tau r_s2 rx r rx_p)
       apply (auto)
    (* - const case *)
      apply (rule_tac x="rx" in exI)
      apply (auto)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
      apply (rule_tac x="empty_use_env" in exI)
      apply (auto)
         apply (simp add: diff_empty_use_env2)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac leq_empty_use_env)
       apply (rule_tac disj_empty_use_env2)
      apply (rule_tac mini_disj_empty_use_env)
    (* - op case *)
     apply (rule_tac x="rx" in exI)
     apply (auto)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (auto)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
        apply (simp add: diff_empty_use_env2)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac disj_empty_use_env2)
     apply (rule_tac mini_disj_empty_use_env)
    (* var case *)
    apply (case_tac "\<not> weak_use_env (req_use_env x1a tau)")
     apply (simp add: weak_use_env_def)
     apply (simp add: req_use_env_def)
     apply (simp add: start_req_perm_def)
     apply (simp add: one_use_env_def)
     apply (auto)
      apply (case_tac "x1a = x")
       apply (auto)
      apply (simp add: aff_fun_ty_def)
      apply (case_tac tau)
            apply (auto)
     apply (case_tac "x1a = x")
      apply (auto)
    apply (rule_tac x="comp_use_env (req_use_env x1a tau) rx" in exI)
    apply (auto)
    (* - initial req that [[ true reqs ]] \<le> rx' (start perm cond.) *)
         apply (rule_tac self_comp_leq_use_env1)
    (* - normal var bounds *)
        apply (rule_tac x="empty_use_env" in exI)
        apply (auto)
           apply (rule_tac rhs_weak_leq_use_env)
            apply (rule_tac dist_weak_comp_use_env)
             apply (simp)
            apply (simp add: weak_use_env_def)
            apply (simp add: empty_use_env_def)
           apply (rule_tac id_leq_use_env)
          apply (rule_tac id_leq_use_env)
         apply (rule_tac leq_empty_use_env)
        apply (rule_tac diff_leq_use_env)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac self_comp_leq_use_env2)
    (* - lift req. special lemma *)
      apply (rule_tac rx="rx" and ?r_s2.0="r_s2" and r_ex="comp_use_env (req_use_env x1a tau) r_ex" in swp_leq_use_env)
          apply (auto)
         apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (req_use_env x1a tau) r_ex)" in trans_leq_use_env)
          apply (rule_tac self_diff_leq_use_env)
         apply (auto)
        apply (rule_tac dist_comp_leq_use_env)
         apply (auto)
       apply (rule_tac lhs_dist_dcl_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (simp)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (simp)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (req_use_env x1a tau) r_ex)" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (auto)
    (* - safety lemma *)
     apply (rule_tac safe_lift_comp_use_env)
      apply (case_tac r)
        apply (auto)
     apply (simp add: weak_use_env_def)
    (* - main rx inequality *)
    apply (rule_tac x="norm_use_env (comp_use_env (req_use_env x1a tau) r_ex) (req_use_env x1a tau)" in exI)
    apply (auto)
        apply (rule_tac lhs_dist_dcl_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac r_sb="diff_use_env (req_use_env x1a tau) (comp_use_env (req_use_env x1a tau) r_ex)" in trans_leq_use_env)
         apply (simp)
        apply (rule_tac diff_norm_leq_use_env_ex)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac self_diff_leq_use_env)
    (* - containment *)
      apply (rule_tac norm_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (auto)
    (* - disj req. special lemma *)
     apply (cut_tac ?rx1.0="rx_p" and rxa="req_use_env x1a tau" and ?r_s2.0="r_s2" and ?rx2.0="rx" and r_ex="comp_use_env (req_use_env x1a tau) r_ex" in swp_disj_use_env)
          apply (auto)
     apply (rule_tac disj_norm_use_env1)
      apply (rule_tac r_s="diff_use_env r_s1 (comp_use_env (req_use_env x1a tau) r_ex)" in mini_disj_leq_use_env2)
      apply (rule_tac mini_disj_diff_use_env)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (auto)
    (* - semi-disjointness *)
    apply (rule_tac r_s="comp_use_env (req_use_env x1a tau) r_ex" in mini_disj_leq_use_env1)
     apply (rule_tac r_s="diff_use_env r_s1 (comp_use_env (req_use_env x1a tau) r_ex)" in mini_disj_leq_use_env2)
      apply (rule_tac mini_disj_diff_use_env)
     apply (auto)
    apply (rule_tac self_norm_leq_use_env)
    (* lambda case *)
   apply (rule_tac x="comp_use_env rxa rx" in exI)
   apply (auto)
      apply (rule_tac x="rxa" in exI)
      apply (auto)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac x="empty_use_env" in exI)
       apply (auto)
          apply (simp add: diff_empty_use_env2)
          apply (rule_tac id_leq_use_env)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac leq_empty_use_env)
       apply (rule_tac diff_leq_use_env)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac self_comp_leq_use_env2)
     apply (rule_tac rx="rx" and ?r_s2.0="r_s2" and r_ex="r_ex" in swp_leq_use_env)
         apply (auto)
       apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (auto)
      apply (rule_tac lhs_dist_dcl_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (simp)
      apply (rule_tac self_diff_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (auto)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
       apply (rule_tac self_diff_leq_use_env)
      apply (auto)
    (* to prove that rxa is safe, we exploit the safe type property *)
    apply (rule_tac safe_lift_comp_use_env)
     apply (case_tac r)
       apply (auto)
    apply (simp add: aff_use_env_def)
    apply (simp add: weak_use_env_def)
    (* - main rx inequality *)
   apply (rule_tac x="norm_use_env r_ex rxa" in exI)
   apply (auto)
      apply (rule_tac lhs_dist_dcl_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac r_sb="diff_use_env rxa r_ex" in trans_leq_use_env)
        apply (simp)
       apply (rule_tac diff_norm_leq_use_env_ex)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac self_diff_leq_use_env)
    (* - minor inequality *)
     apply (rule_tac norm_leq_use_env)
     apply (simp)
    (* - disjointness *)
    apply (rule_tac disj_norm_use_env1)
     apply (rule_tac r_s="diff_use_env r_s1 r_ex" in mini_disj_leq_use_env2)
      apply (rule_tac mini_disj_diff_use_env)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac ?r_s2.0="r_s2" in swp_disj_use_env)
        apply (auto)
    (* - semi-disjointness *)
   apply (rule_tac r_s="r_ex" in mini_disj_leq_use_env1)
    apply (rule_tac r_s="diff_use_env r_s1 r_ex" in mini_disj_leq_use_env2)
     apply (rule_tac mini_disj_diff_use_env)
    apply (auto)
   apply (rule_tac self_norm_leq_use_env)
    (* app case *)
  apply (case_tac e1)
       apply (auto)
  apply (case_tac x1)
              apply (auto)
  apply (case_tac e2)
       apply (auto)
  apply (simp add: pure_fun_def)
  apply (simp add: aff_use_env_def)
  apply (auto)
  apply (simp add: app_req_def)
  apply (case_tac t)
      apply (auto)
  apply (case_tac "\<not> weak_use_env empty_use_env")
   apply (simp add: weak_use_env_def)
   apply (simp add: empty_use_env_def)
    (* - we'll have to prove this twice *)
  apply (cut_tac r_sc="r_s2" and r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 rx2) r_ex)" and
      r_sa="diff_use_env r_s1 (comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex))" in trans_leq_use_env)
    apply (rule_tac rhs_unroll_dcl_use_env)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac r_sb="diff_use_env r_s2a r_exa" in trans_leq_use_env)
  apply (rule_tac dist_diff_leq_use_env)
     apply (auto)
    (* - same here *)
  apply (cut_tac r_sc="diff_use_env rxa (comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex))" and r_sa="rx" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac lhs_unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac comp_leq_use_env2)
   apply (simp)
    (* - instantiation. our selection of rx should be such that it is consistent, from beginning to end. it minimally must contain
        rx, the original permission set, but it must also include anything subtracted out that would have been necessary. since e1 is a
        constant, it requires no permissions. which means that we must simply include the permissions required for e2. in order to get
        this we induct on e2. *)
  apply (rule_tac x="comp_use_env rxa rx" in exI)
  apply (auto)
     apply (rule_tac x="comp_use_env rxa rx" in exI)
     apply (auto)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
      apply (rule_tac leq_empty_use_env)
     apply (rule_tac x="rxa" in exI)
     apply (rule_tac x="comp_use_env rxa rx" in exI)
     apply (auto)
      apply (rule_tac x="rxa" in exI)
      apply (auto)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac x="empty_use_env" in exI)
      apply (auto)
         apply (rule_tac rhs_weak_leq_use_env)
          apply (simp)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (rule_tac x="empty_use_env" in exI)
      apply (auto)
            apply (rule_tac rhs_weak_leq_use_env)
             apply (rule_tac dist_weak_comp_use_env)
              apply (rule_tac dist_weak_comp_use_env)
               apply (auto)
            apply (rule_tac id_leq_use_env)
           apply (simp add: weak_use_env_def)
          apply (rule_tac dist_comp_leq_use_env)
           apply (rule_tac leq_empty_use_env)
          apply (rule_tac self_comp_leq_use_env1)
         apply (rule_tac disj_empty_use_env2)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac diff_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac self_comp_leq_use_env1)
    (* - basic inequalities *)
     apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac rx="rx" and ?r_s2.0="r_s2" and r_ex="comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex)" in swp_leq_use_env)
        apply (auto)
       apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex))" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (auto)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
        apply (auto)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s2a r_exa" in trans_leq_use_env)
         apply (rule_tac diff_leq_use_env)
         apply (auto)
     apply (rule_tac lhs_dist_dcl_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (simp)
     apply (rule_tac self_diff_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex))" in trans_leq_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (auto)
    (* - safe lift *)
   apply (rule_tac safe_lift_comp_use_env)
    apply (case_tac r)
      apply (auto)
   apply (simp add: weak_use_env_def)
    (* - main inequality *)
  apply (rule_tac x="norm_use_env (comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex)) rxa" in exI)
  apply (auto)
     apply (rule_tac lhs_dist_dcl_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac r_sb="diff_use_env rxa (comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex))" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac diff_norm_leq_use_env_ex)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac self_diff_leq_use_env)
    (* - minor inequality *)
    apply (rule_tac norm_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
      apply (simp_all)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s2a r_exa" in trans_leq_use_env)
       apply (rule_tac diff_leq_use_env)
       apply (simp_all)
    (* - disjointness *)
   apply (rule_tac disj_norm_use_env1)
    apply (rule_tac r_s="diff_use_env r_s1 (comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex))" in mini_disj_leq_use_env2)
     apply (rule_tac mini_disj_diff_use_env)
    apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
     apply (auto)
   apply (rule_tac ?r_s2.0="r_s2" and ?rx2.0="rx" and r_ex="comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex)" and ?r_s1.0="r_s1" in swp_disj_use_env)
       apply (auto)
    (* - semi-disjointness *)
  apply (rule_tac r_s="comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex)" in mini_disj_leq_use_env1)
   apply (rule_tac r_s="diff_use_env r_s1 (comp_use_env r_exa (comp_use_env (comp_use_env rx1 rx2) r_ex))" in mini_disj_leq_use_env2)
    apply (rule_tac mini_disj_diff_use_env)
   apply (auto)
  apply (rule_tac self_norm_leq_use_env)
  done


end