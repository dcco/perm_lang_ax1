theory SafeRedUnpack
    imports FlatLemma SRUseEnv
begin
  
    (*
lemma sum_comp_diff_use_env2: "comp_use_env r_s r_x = comp_use_env r_s (diff_use_env r_x r_s)"  
  apply (rule_tac t="comp_use_env r_s r_x" and s="comp_use_env r_x r_s" in subst)
   apply (rule_tac comm_comp_use_env)
  apply (rule_tac t="comp_use_env r_s (diff_use_env r_x r_s)" and s="comp_use_env (diff_use_env r_x r_s) r_s" in subst)
   apply (rule_tac comm_comp_use_env)   
  apply (simp add: sum_comp_diff_use_env)
  done
    
definition anti_norm_use_env where
  "anti_norm_use_env r_x r_s = (\<lambda> x. if r_s x = NoPerm then r_x x else NoPerm)"
    
lemma split_norm_use_env: "r_x = comp_use_env (norm_use_env r_x r_s) (anti_norm_use_env r_x r_s)"  
  apply (case_tac "\<forall> x. r_x x = comp_use_env (norm_use_env r_x r_s) (anti_norm_use_env r_x r_s) x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: anti_norm_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (case_tac "r_s x = NoPerm")
   apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma squish_norm_leq_use_env: "\<lbrakk> leq_use_env r_s1 (diff_use_env r_c r_ex); leq_use_env (diff_use_env r_x r_ex) r_s2;
  leq_use_env r_s2 r_s1 \<rbrakk> \<Longrightarrow> leq_use_env (norm_use_env r_x r_s1) r_s2 "    
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x = OwnPerm")
   apply (simp)
   apply (case_tac "r_s1 x")
     apply (auto)
    apply (case_tac "r_c x")
      apply (auto)
   apply (case_tac "r_c x")
  apply (auto)
  apply (case_tac "neg_perm (r_ex x) \<noteq> NoEP")
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
  
lemma mini_disj_anti_norm_use_env: "mini_disj_use_env r_s (anti_norm_use_env r_x r_s)"
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: anti_norm_use_env_def)
  done
    
lemma mini_disj_split_norm_use_env: "mini_disj_use_env (norm_use_env r_x r_s) (anti_norm_use_env r_x r_s)"    
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (simp add: anti_norm_use_env_def)
  done
  
    (* this lemma is based on two ideas. first, that r_x is already present in r_s2 except for what got subtracted out.
      and everything that got subtracted out wasn't present in r_s1 to start with, and is thus, add-able.
      > translating this: r_x can be split into a part that is already in r_s1, and a part that is fully-disjoint.
    *)
lemma well_typed_comp_perms_squish: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx;
  leq_use_env r_s1 (diff_use_env r_c r_ex); leq_use_env (diff_use_env r_x r_ex) r_s2 \<rbrakk> \<Longrightarrow>
  well_typed env (comp_use_env r_s1 r_x) e tau (comp_use_env r_s2 r_x) rx"    
  apply (rule_tac t="r_x" and s="comp_use_env (norm_use_env r_x r_s1) (anti_norm_use_env r_x r_s1)" in subst)
   apply (cut_tac r_x="r_x" and r_s="r_s1" in split_norm_use_env)
   apply (auto)
  apply (simp add: assoc_comp_use_env)
  apply (rule_tac well_typed_comp_perms_gen)
   apply (rule_tac ?r_s1.0="r_s1" in well_typed_incr_start_perm)
    apply (rule_tac r_c="r_s2" in well_typed_decr_end_perm)
      apply (simp)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac r_c="r_c" and r_ex="r_ex" in squish_norm_leq_use_env)
       apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac comp_leq_use_env1)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
   apply (rule_tac self_comp_leq_use_env1)
  apply (rule_tac mini_disj_comp_use_env)
   apply (rule_tac mini_disj_anti_norm_use_env)
  apply (rule_tac mini_disj_split_norm_use_env)
  done
    
lemma reverse_disj_use_env1: "\<lbrakk> disj_use_env (diff_use_env r_x r_ex) r_s; leq_use_env r_s (diff_use_env r_c r_ex) \<rbrakk> \<Longrightarrow> disj_use_env r_x r_s"    
  apply (simp add: disj_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
    apply (case_tac "neg_perm (r_ex x) \<noteq> NoEP")
     apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
    apply (case_tac "minus_ep (r_c x) OwnEP \<noteq> NoPerm")
     apply (case_tac "r_c x")
       apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "neg_perm (r_ex x) \<noteq> OwnEP")
    apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "minus_ep (r_c x) OwnEP \<noteq> NoPerm")
    apply (case_tac "r_c x")
      apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "neg_perm (r_ex x) = OwnEP")
   apply (case_tac "r_c x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
  apply (auto)
  done
    
lemma reverse_disj_use_env2: "\<lbrakk> disj_use_env r_s (diff_use_env r_x r_ex); leq_use_env r_s (diff_use_env r_c r_ex) \<rbrakk> \<Longrightarrow> disj_use_env r_s r_x"       
  apply (rule_tac comm_disj_use_env)
  apply (rule_tac reverse_disj_use_env1)
   apply (auto)
  apply (rule_tac comm_disj_use_env)
  apply (simp)
  done
  
lemma self_pair_req_leq_use_env: "leq_use_env (pair_req r_s r_ex t) (diff_use_env r_s r_ex)"    
  apply (simp add: pair_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac id_leq_use_env)
  done

lemma pair_req_leq_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s \<rbrakk> \<Longrightarrow> leq_use_env (pair_req r_x r_ex t) r_s"    
  apply (rule_tac r_sb="diff_use_env r_x r_ex" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_pair_req_leq_use_env)
  done
    
    
definition unpack_abbrev where
  "unpack_abbrev f = (AppExp (ConstExp UnpackConst) f)"
    
definition pair_abbrev where
  "pair_abbrev v1 v2 = (PairExp v1 v2)"  
  
definition upc_abbrev where
  "upc_abbrev f v1 v2 = (AppExp (unpack_abbrev f) (pair_abbrev v1 v2))"  

definition ures_arg1_abbrev where
  "ures_arg1_abbrev f v = (AppExp f v)"  
  
definition ures_abbrev where
  "ures_abbrev f v1 v2 = (AppExp (ures_arg1_abbrev f v1) v2)"  
  
    
lemma unpack_lam_type: "\<lbrakk> well_typed env r_s1 (unpack_abbrev f) (FunTy tau tx r a) r_s2 rx; is_value f \<rbrakk> \<Longrightarrow>
  (\<exists> t1 t2 a1 a2. tau = PairTy t1 t2 r \<and> well_typed env r_s1 f (FunTy t1 (FunTy t2 tx r a2) r a1) r_s1 (comp_use_env rx (infl_use_env r_s1 r_s2)))" 
  apply (simp add: unpack_abbrev_def)
  apply (auto)
  apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (simp add: app_req_def)
  apply (simp add: pure_fun_def)
  apply (auto)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac rx="comp_use_env rx2 (infl_use_env r_s1 r_s3)" in well_typed_incr_req)
    apply (rule_tac infl_full_sexp_wp)
      apply (rule_tac ?r_s1.0="r_s2a" in well_typed_incr_start_perm)
       apply (auto)
    apply (rule_tac value_is_sexp)
    apply (auto)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac st_diff_comp_leq_use_env)
    apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac dist_diff_leq_use_env_cut)
     apply (rule_tac self_comp_leq_use_env2)
    apply (rule_tac infl_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (auto)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
   apply (rule_tac comp_leq_use_env2)
   apply (rule_tac dist_infl_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
    apply (rule_tac self_diff_leq_use_env)
   apply (simp)
  apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
    apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 rx2) r_ex)" in trans_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (auto)
  apply (rule_tac self_infl_leq_use_env)
  done

lemma unpack_pair_type: "\<lbrakk> well_typed env r_s1 (pair_abbrev v1 v2) (PairTy t1 t2 r) r_s2 rx; is_value v1; is_value v2 \<rbrakk> \<Longrightarrow>
   well_typed env r_s1 (pair_abbrev v1 v2) (PairTy t1 t2 r) r_s1 (comp_use_env rx (infl_use_env r_s1 r_s2))"
  apply (rule_tac infl_full_sexp_wp)
    apply (auto)
   apply (simp add: pair_abbrev_def)(*
  apply (simp add: pair_abbrev_def)
  apply (case_tac r)
    apply (auto)
  apply (simp add: unlim_def)
  apply (case_tac "req_type t1")
    apply (auto)
   apply (case_tac "req_type t2")
     apply (auto)
  apply (case_tac "req_type t2")
    apply (auto)*)
  done
    
lemma unpack_split_pair_type: "\<lbrakk> well_typed env r_s1 (pair_abbrev v1 v2) (PairTy t1 t2 r) r_s1 rx; is_value v1; is_value v2 \<rbrakk> \<Longrightarrow>
  (\<exists> rx1 rx2. well_typed env r_s1 v1 t1 r_s1 rx1 \<and> well_typed env r_s1 v2 t2 r_s1 rx2 \<and>
    leq_use_env (lift_use_env rx1 r) r_s1 \<and> leq_use_env (lift_use_env rx2 r) r_s1 \<and>
    (*safe_use_lift rx1 r \<and> safe_use_lift rx2 r \<and> safe_type t1 r \<and> safe_type t2 r \<and>*)
    disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
    leq_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) rx)"    
  apply (simp add: pair_abbrev_def)
  apply (auto)
  apply (rule_tac x="pair_req rx1 empty_use_env (PairTy t1 t2 r)" in exI)
  apply (auto)
   apply (rule_tac r_c="r_s2" in well_typed_decr_end_perm)
     apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
      apply (simp add: pair_req_def)
      apply (rule_tac rx="rx1" in wt_sexp_no_req)
        apply (auto)
       apply (case_tac r)
         apply (auto)
       apply (case_tac "req_type t1")
         apply (auto)
       apply (case_tac "req_type t2")
         apply (auto)
      apply (rule_tac value_is_sexp)
      apply (auto)
     apply (simp add: pair_req_def)
     apply (simp add: diff_empty_use_env2)
    apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
   apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac pair_req_leq_use_env)
   apply (rule_tac diff_leq_use_env)
   apply (rule_tac well_typed_perm_leqx)
   apply (auto)
  apply (rule_tac x="pair_req rx2 empty_use_env (PairTy t1 t2 r)" in exI)
  apply (auto)
        apply (rule_tac r_c="r_s3" in well_typed_decr_end_perm)
          apply (rule_tac ?r_s1.0="r_s2" in well_typed_incr_start_perm)
           apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
            apply (simp add: pair_req_def)
            apply (rule_tac rx="rx2" in wt_sexp_no_req)
              apply (auto)
             apply (case_tac "r")
              apply (auto)
             apply (case_tac "req_type t2")
               apply (auto)
              apply (case_tac "req_type t1")
                apply (auto)
             apply (case_tac "req_type t1")
               apply (auto)
            apply (rule_tac value_is_sexp)
            apply (auto)
           apply (simp add: pair_req_def)
           apply (simp add: diff_empty_use_env2)
          apply (rule_tac well_typed_perm_leq)
          apply (auto)
         apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
          apply (rule_tac self_diff_leq_use_env)
         apply (simp)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
          apply (rule_tac well_typed_perm_leq)
          apply (auto)
         apply (rule_tac well_typed_perm_leq)
         apply (auto)
        apply (rule_tac pair_req_leq_use_env)
        apply (rule_tac r_sb="lift_use_env rx2 r" in trans_leq_use_env)
         apply (simp)
        apply (rule_tac diff_leq_use_env)
        apply (rule_tac self_lift_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (rule_tac r_sb="lift_use_env rx1 r" in trans_leq_use_env)
        apply (simp)
       apply (rule_tac dist_lift_leq_use_env)
       apply (rule_tac pair_req_leq_use_env)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac r_sb="lift_use_env rx2 r" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac dist_lift_leq_use_env)
      apply (rule_tac pair_req_leq_use_env)
      apply (rule_tac self_diff_leq_use_env)
   apply (rule_tac r_s="lift_use_env rx1 r" in disj_leq_use_env1)
    apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
     apply (simp)
    apply (rule_tac dist_lift_leq_use_env)
    apply (rule_tac pair_req_leq_use_env)
    apply (rule_tac self_diff_leq_use_env)
   apply (rule_tac dist_lift_leq_use_env)
   apply (rule_tac pair_req_leq_use_env)
   apply (rule_tac self_diff_leq_use_env)
  apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
   apply (simp add: pair_req_def)
   apply (auto)
   apply (simp add: lift_empty_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac leq_empty_use_env)
   apply (rule_tac leq_empty_use_env)
  apply (simp add: pair_req_def)
  apply (simp add: diff_empty_use_env2)
  apply (rule_tac r_sb="diff_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac mini_disj_diff_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac r_s="diff_use_env r_s3 r_ex" in mini_disj_leq_use_env2)
   apply (rule_tac mini_disj_diff_use_env)
  apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
   apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (rule_tac dist_comp_leq_use_env)
   apply (simp_all)
  done
    
    
lemma unpack_app1_type: "\<lbrakk> well_typed env r_s1 f (FunTy t1 (FunTy t2 tau r a2) r a1) r_s1 (comp_use_env rx1 (infl_use_env r_s1 r_s2));
  well_typed env r_s1 v1 t1 r_s1 rx2a; leq_use_env r_s2 r_s1; leq_use_env rx1 r_s2; leq_use_env (lift_use_env rx2a r) r_s2;
  disj_use_env rx1 (lift_use_env rx2a r)(*; safe_use_lift rx2a r; safe_type t1 r*) \<rbrakk> \<Longrightarrow>
  well_typed env r_s1 (ures_arg1_abbrev f v1) (FunTy t2 tau r a2)
  (diff_use_env r_s2 (comp_use_env rx1 (lift_use_env rx2a r)))
  (diff_use_env (comp_use_env rx1 rx2a) (comp_use_env rx1 (lift_use_env rx2a r)))"    
  apply (simp add: ures_arg1_abbrev_def)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a1" in exI)
  apply (rule_tac x="r_s1" in exI)
  apply (rule_tac x="comp_use_env rx1 (infl_use_env r_s1 r_s2)" in exI)
  apply (auto)
  apply (rule_tac x="rx2a" in exI)
  apply (rule_tac x="r_s1" in exI)
  apply (auto)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
       apply (rule_tac rhs_unroll_dcl_use_env)
       apply (rule_tac disj_diff_leq_use_env)
        apply (rule_tac disj_empty_use_env2)
       apply (rule_tac unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac rhs_flip_use_env)
       apply (rule_tac rhs_unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac disj_diff_leq_use_env)
        apply (rule_tac comm_disj_use_env)
        apply (rule_tac infl_disj_use_env)
        apply (rule_tac id_leq_use_env)
       apply (simp)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac well_typed_perm_leqx)
       apply (auto)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (simp_all)
     apply (rule_tac disj_comp_use_env1)
      apply (simp)
     apply (rule_tac comm_disj_use_env)
     apply (rule_tac infl_disj_use_env)
     apply (simp)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (simp)
    apply (rule_tac r_sb="lift_use_env rx2a r" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac leq_empty_use_env)
  apply (simp add: app_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac lhs_unroll_dcl_use_env)
  apply (rule_tac diff_leq_use_env)
  apply (rule_tac unroll_dcl_use_env)
  apply (rule_tac dist_diff_leq_use_env)
  apply (rule_tac lhs_flip_use_env)
  apply (rule_tac lhs_unroll_dcl_use_env)
  apply (rule_tac dist_diff_leq_use_env)  
  apply (rule_tac lhs_dist_dcl_use_env)
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac lhs_dist_dcl_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac comp_leq_use_env1)
    apply (rule_tac self_diff_leq_use_env)
   apply (rule_tac diff_infl_leq_use_env)
  apply (rule_tac comp_leq_use_env2)
  apply (rule_tac self_diff_leq_use_env)
  done
       
    
lemma well_typed_simul_diff_perms: "\<lbrakk> well_typed env r_s e tau r_s rx; is_sexp e; disj_use_env rx r_x \<rbrakk> \<Longrightarrow>
  well_typed env (diff_use_env r_s r_x) e tau (diff_use_env r_s r_x) (diff_use_env rx r_x)"    
  apply (rule_tac well_typed_diff_perms)
   apply (simp)
  apply (auto)
  apply (case_tac "r_s x = NoPerm")
   apply (cut_tac ?r_s1.0="r_s" and env="env" and e="e" and x="x" in well_typed_no_npv_use)
     apply (auto)
  apply (cut_tac rx="rx" and x="x" and ?r_s2.0="r_s" and env="env" and e="e" in wt_sexp_req_use)
      apply (auto)
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: own_env_vars_def)
  done
  
lemma unpack_app2_type: "\<lbrakk> well_typed env r_s1 (ures_arg1_abbrev f v1) (FunTy t2 tau ra a2) (diff_use_env r_s2a (comp_use_env rx1 (lift_use_env rx1a ra)))
         (diff_use_env (comp_use_env rx1 rx1a) (comp_use_env rx1 (lift_use_env rx1a ra))); well_typed env r_s2a v2 t2 r_s2a rx2a;
        leq_use_env (lift_use_env rx1a ra) r_s2a; leq_use_env (lift_use_env rx2a ra) r_s2a; leq_use_env r_s3 r_s2a; leq_use_env r_s2a r_s1;
        (*safe_use_lift rx1a ra; safe_use_lift rx2a ra; safe_type t1a ra; safe_type t2 ra;*)
        disj_use_env (lift_use_env rx1a ra) (lift_use_env rx2a ra); leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3;
        disj_use_env rx1 (lift_use_env rx2 r); leq_use_env (comp_use_env (lift_use_env rx1a ra) (lift_use_env rx2a ra)) rx2; is_value v1; is_value v2
   \<rbrakk> \<Longrightarrow>
  well_typed env r_s1 (ures_abbrev f v1 v2) tau (diff_use_env r_s3 (comp_use_env rx1 (lift_use_env rx2 r)))
  (diff_use_env (comp_use_env rx1 rx2) (comp_use_env rx1 (lift_use_env rx2 r)))"
    (* main disjointness result *)
  apply (cut_tac r_ex="lift_use_env rx2a ra" and ?r_s1.0="rx1" and ?r_s2.0="lift_use_env rx1a ra" in disj_comp_use_env2)
    apply (rule_tac comm_disj_use_env)
    apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
     apply (auto)
    apply (rule_tac r_sb="comp_use_env (lift_use_env rx1a ra) (lift_use_env rx2a ra)" in trans_leq_use_env)
     apply (rule_tac lift_leq_use_env)
     apply (simp)
    apply (rule_tac self_comp_leq_use_env2)
   apply (rule_tac comm_disj_use_env)
   apply (simp)
    (* other *)
  apply (simp add: ures_abbrev_def)
  apply (rule_tac x="t2" in exI)
  apply (rule_tac x="ra" in exI)
  apply (rule_tac x="a2" in exI)
  apply (rule_tac x="diff_use_env r_s2a (comp_use_env rx1 (lift_use_env rx1a ra))" in exI)
  apply (rule_tac x="diff_use_env (comp_use_env rx1 rx1a) (comp_use_env rx1 (lift_use_env rx1a ra))" in exI)
  apply (auto)
  apply (rule_tac x="rx2a" in exI)
  apply (rule_tac x="diff_use_env r_s2a (comp_use_env rx1 (lift_use_env rx1a ra))" in exI)
  apply (auto)
   apply (rule_tac rx="diff_use_env rx2a (comp_use_env rx1 (lift_use_env rx1a ra))" in well_typed_incr_req)
     apply (rule_tac well_typed_simul_diff_perms)
       apply (simp)
      apply (rule_tac value_is_sexp)
      apply (auto)
     apply (rule_tac r_s="lift_use_env rx2a ra" in disj_leq_use_env1)
      apply (simp)
     apply (rule_tac self_lift_leq_use_env)
    apply (rule_tac self_diff_leq_use_env)
   apply (rule_tac disj_diff_leq_use_env)
    apply (rule_tac comm_disj_use_env)
    apply (rule_tac r_s="lift_use_env rx2a ra" in disj_leq_use_env1)
     apply (simp)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac well_typed_perm_leqx)
   apply (auto)
    (* existentials *)
  apply (rule_tac x="comp_use_env rx1 (lift_use_env rx2 r)" in exI)
  apply (auto)
       apply (rule_tac rhs_unroll_dcl_use_env)
       apply (rule_tac rhs_diff_leq_use_env)
       apply (rule_tac rhs_fold_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (simp)
       apply (rule_tac r_sb="comp_use_env rx1 (comp_use_env (lift_use_env rx1a ra) (lift_use_env rx2a ra))" in trans_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac self_comp_leq_use_env1)
        apply (rule_tac comp_leq_use_env2)
        apply (rule_tac lift_leq_use_env)
        apply (simp)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac self_comp_leq_use_env1)
        apply (rule_tac comp_leq_use_env2)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac diff_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac self_comp_leq_use_env1)
        apply (rule_tac comp_leq_use_env2)
        apply (rule_tac comp_leq_use_env1)
        apply (rule_tac self_lift_leq_use_env)
       apply (rule_tac comp_leq_use_env2)
       apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
         apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
          apply (auto)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac r_sb="lift_use_env rx1a ra" in trans_leq_use_env)
        apply (simp)
       apply (rule_tac self_lift_leq_use_env)
      apply (rule_tac disj_diff_leq_use_env)
       apply (rule_tac comm_disj_use_env)
       apply (auto)
     apply (rule_tac r_s="comp_use_env rx1 (lift_use_env rx1a ra)" in disj_leq_use_env1)
      apply (rule_tac comm_disj_use_env)
      apply (simp)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac self_comp_leq_use_env1)
     apply (rule_tac comp_leq_use_env2)
     apply (rule_tac self_lift_leq_use_env)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac self_comp_leq_use_env1)
    apply (rule_tac comp_leq_use_env2)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
    apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
     apply (auto)
  apply (simp add: app_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac lhs_unroll_dcl_use_env)
  apply (rule_tac dist_diff_leq_use_env)
  apply (rule_tac diff_leq_use_env)
  apply (rule_tac r_sb="comp_use_env rx1 (comp_use_env (lift_use_env rx1a ra) (lift_use_env rx2a ra))" in trans_leq_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac self_comp_leq_use_env1)
   apply (rule_tac comp_leq_use_env2)
   apply (simp)
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac diff_leq_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac self_comp_leq_use_env1)
   apply (rule_tac comp_leq_use_env2)
   apply (rule_tac comp_leq_use_env1)
   apply (rule_tac self_lift_leq_use_env)
  apply (rule_tac comp_leq_use_env2)
  apply (rule_tac comp_leq_use_env2)
  apply (rule_tac self_lift_leq_use_env)
  done
    
  
(*    
   
  apply (rule_tac x="t2" in exI)
  apply (rule_tac x="ra" in exI)
  apply (rule_tac x="a2" in exI)
  apply (rule_tac x="r_s2a" in exI)
  apply (rule_tac x="comp_use_env rx1 (infl_use_env r_s1 r_s2a)" in exI)
  apply (auto)
   apply (rule_tac x="t1a" in exI)
   apply (rule_tac x="ra" in exI)
   apply (rule_tac x="a1" in exI)
   apply (rule_tac x="r_s1" in exI)
   apply (rule_tac x="comp_use_env rx1 (infl_use_env r_s1 r_s2a)" in exI)
   apply (auto)
   apply (rule_tac x="rx1a" in exI)
   apply (rule_tac x="r_s1" in exI)
   apply (auto)
    apply (rule_tac r_s="r_s2a" in well_typed_incr_simul_perm)
     apply (auto)
   apply (rule_tac x="empty_use_env" in exI)
   apply (auto) 
 *)
    
    
lemma unpack_comb: "\<lbrakk> is_value f; is_value v1; is_value v2;
        leq_use_env r_s2 (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)); (*safe_use_lift rx2 r; safe_type (PairTy t1a t2 r) r;*)
        leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; disj_use_env rx1 (lift_use_env rx2 r); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (app_req rx1 rx2 r tau r_ex) rx; leq_use_env r_s2a r_s1; leq_use_env rx1 r_s2a; leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3;
        well_typed env r_s1 f (FunTy t1a (FunTy t2 tau r a2) r a1) r_s1 (comp_use_env rx1 (infl_use_env r_s1 r_s2a));
        well_typed env r_s2a (pair_abbrev v1 v2) (PairTy t1a t2 r) r_s2a (comp_use_env rx2 (infl_use_env r_s2a r_s3));
        leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; leq_use_env r_s3 r_s2a \<rbrakk>
       \<Longrightarrow> well_typed env r_s1 (ures_abbrev f v1 v2) tau (diff_use_env r_s2a (comp_use_env rx1 (lift_use_env (comp_use_env rx2 (infl_use_env r_s2a r_s3)) r)))
         (diff_use_env (comp_use_env rx1 (comp_use_env rx2 (infl_use_env r_s2a r_s3)))
           (comp_use_env rx1 (lift_use_env (comp_use_env rx2 (infl_use_env r_s2a r_s3)) r)))"
  apply (cut_tac env="env" and ?r_s1.0="r_s2a" and ?v1.0="v1" and ?v2.0="v2" in unpack_split_pair_type)
   apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and f="f" and ?t1.0="t1a" and ?t2.0="t2" and tau="tau" and r="r" and
      ?rx1.0="rx1" and ?r_s2.0="r_s2a" and ?v1.0="v1" and rx2a="rx1a" in unpack_app1_type)
          apply (auto)
    apply (rule_tac r_s="r_s2a" in well_typed_incr_simul_perm)
     apply (auto)
   apply (rule_tac r_s="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in disj_leq_use_env2)
    apply (rule_tac disj_comp_use_env2)
     apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
      apply (simp)
     apply (rule_tac self_lift_leq_use_env)
    apply (rule_tac infl_disj_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2  r)" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac self_comp_leq_use_env1)
   apply (rule_tac r_sb="comp_use_env (lift_use_env rx1a r) (lift_use_env rx2a r)" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac self_comp_leq_use_env1)
  apply (case_tac "\<not> leq_perm r r")
   apply (case_tac r)
     apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and r_s2a="r_s2a" and ?r_s3.0="r_s2a" and f="f" and ?v1.0="v1" and ?v2.0="v2" and
      ?rx1.0="rx1" and rx1a="rx1a" and rx2a="rx2a" and r="r" and ra="r" and ?rx2.0="comp_use_env rx2 (infl_use_env r_s2a r_s3)"
      and ?t2.0="t2" in unpack_app2_type)
                  apply (auto)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (auto)
     apply (rule_tac self_comp_leq_use_env1)
    apply (simp add: lift_comp_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (auto)
     apply (rule_tac self_comp_leq_use_env2)
    apply (simp add: infl_lift_use_env)
    apply (rule_tac self_infl_leq_use_env)
   apply (simp add: lift_comp_use_env)
   apply (rule_tac disj_comp_use_env2)
    apply (simp)
   apply (simp add: infl_lift_use_env)
   apply (rule_tac infl_disj_use_env)
   apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac self_comp_leq_use_env1)
  done
    
lemma refl_infl_leq_use_env: "leq_use_env (refl_use_env r_s r_x r) (infl_use_env r_s r_x)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: refl_use_env_def)
  apply (simp add: infl_use_env_def)
  done
    
    (*
\<exists>g_ax. (\<exists>t1 r a r_s2a rx1.
                      (\<exists>t1a ra aa r_s2 rx1a.
                          well_typed (red_env env g_ax) (exp_red_use_env r_s1 g_ax) v1 (FunTy t1a (FunTy t1 tau r a) ra aa) r_s2 rx1a \<and>
                          (\<exists>rx2 r_s3.
                              well_typed (red_env env g_ax) r_s2 v1 t1a r_s3 rx2 \<and>
                              (\<exists>r_ex. leq_use_env r_s2a (diff_use_env r_s3 (comp_use_env (comp_use_env rx1a (lift_use_env rx2 ra)) r_ex)) \<and>
                                      safe_use_lift rx2 ra \<and>
                                      safe_type t1a ra \<and>
                                      leq_use_env (comp_use_env rx1a (lift_use_env rx2 ra)) r_s3 \<and>
                                      disj_use_env rx1a (lift_use_env rx2 ra) \<and>
                                      leq_use_env rx1 r_s2a \<and>
                                      leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and> leq_use_env (app_req rx1a rx2 ra (FunTy t1 tau r a) r_ex) rx1))) \<and>
                      (\<exists>rx2 r_s3.
                          well_typed (red_env env g_ax) r_s2a v2a t1 r_s3 rx2 \<and>
                          (\<exists>r_ex. leq_use_env (end_red_use_env r_s2 g_ax) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) \<and>
                                  safe_use_lift rx2 r \<and>
                                  safe_type t1 r \<and>
                                  leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
                                  disj_use_env rx1 (lift_use_env rx2 r) \<and>
                                  leq_use_env (end_red_use_env rx g_ax) (end_red_use_env r_s2 g_ax) \<and>
                                  leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and> leq_use_env (app_req rx1 rx2 r tau r_ex) (end_red_use_env rx g_ax)))) \<and>
                  well_typed_state s1 (red_env env g_ax) (red_nres_map rs_map g_ax) \<and>
                  valid_exp_use_env s1 (red_nres_map rs_map g_ax) (exp_red_use_env r_f g_ax) \<and> safe_act s1 r_f g_ax \<and> corr_act NoAct g_ax

*)
    
lemma sares_unpack_abbrev: "\<lbrakk>well_typed_state s1 env rs_map; valid_exp_use_env s1 rs_map r_f; leq_use_env r_s1 r_f;
        proper_exp rs_map (AppExp (AppExp (ConstExp UnpackConst) f) (PairExp v1 v2));
        well_typed env r_s1 (upc_abbrev f v1 v2) tau r_s2 rx; is_value f; is_value v1; is_value v2 \<rbrakk>
       \<Longrightarrow> \<exists>g_ax. (\<exists>t1 r a r_s2a rx1.
                      (\<exists>t1a ra aa r_s2 rx1a.
                          well_typed (red_env env g_ax) (exp_red_use_env r_s1 g_ax) f (FunTy t1a (FunTy t1 tau r a) ra aa) r_s2 rx1a \<and>
                          (\<exists>rx2 r_s3.
                              well_typed (red_env env g_ax) r_s2 v1 t1a r_s3 rx2 \<and>
                              (\<exists>r_ex. leq_use_env r_s2a (diff_use_env r_s3 (comp_use_env (comp_use_env rx1a (lift_use_env rx2 ra)) r_ex)) \<and>
                                      (*safe_use_lift rx2 ra \<and>
                                      safe_type t1a ra \<and>*)
                                      leq_use_env (comp_use_env rx1a (lift_use_env rx2 ra)) r_s3 \<and>
                                      disj_use_env rx1a (lift_use_env rx2 ra) \<and>
                                      leq_use_env rx1 r_s2a \<and>
                                      leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and> leq_use_env (app_req rx1a rx2 ra (FunTy t1 tau r a) r_ex) rx1))) \<and>
                      (\<exists>rx2 r_s3.
                          well_typed (red_env env g_ax) r_s2a v2 t1 r_s3 rx2 \<and>
                          (\<exists>r_ex. leq_use_env (end_red_use_env r_s2 g_ax) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) \<and>
                                  (*safe_use_lift rx2 r \<and>
                                  safe_type t1 r \<and>*)
                                  leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
                                  disj_use_env rx1 (lift_use_env rx2 r) \<and>
                                  leq_use_env (end_red_use_env rx g_ax) (end_red_use_env r_s2 g_ax) \<and>
                                  leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and> leq_use_env (app_req rx1 rx2 r tau r_ex) (end_red_use_env rx g_ax)))) \<and>
                  proper_exp (red_nres_map rs_map g_ax) (AppExp (AppExp f v1) v2) \<and>
                  well_typed_state s1 (red_env env g_ax) (red_nres_map rs_map g_ax) \<and>
                  valid_exp_use_env s1 (red_nres_map rs_map g_ax) (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act NoAct g_ax"
  apply (rule_tac x="NoResAct" in exI)
  apply (auto)
  apply (simp add: upc_abbrev_def)
  apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and tau="t1" and tx="tau" and f="f" in unpack_lam_type)
    apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s2a" and ?v1.0="v1" and ?v2.0="v2" and ?r_s2.0="r_s3" in unpack_pair_type)
     apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and r_s2a="r_s2a" and ?r_s3.0="r_s3" and ?rx1.0="rx1" and ?rx2.0="rx2" 
      and f="f" and ?v1.0="v1" and ?v2.0="v2" and t1a="t1a" and ?t2.0="t2" and r="r" in unpack_comb)
                    apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (simp add: ures_abbrev_def)
  apply (auto)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="ra" in exI)
  apply (rule_tac x="aa" in exI)
  apply (rule_tac x="r_s2aa" in exI)
  apply (rule_tac x="rx1a" in exI)
  apply (auto)
   apply (simp add: ures_arg1_abbrev_def)
  apply (rule_tac x="rx2a" in exI)
  apply (rule_tac x="r_s3a" in exI)
  apply (auto)
  apply (case_tac "\<not> leq_perm r r")
   apply (case_tac r)
     apply (auto)
  apply (rule_tac x="comp_use_env r_exa (comp_use_env (infl_use_env r_s2a r_s3) r_ex)" in exI)
  apply (auto)
    apply (rule_tac r_sb="diff_use_env r_s2a (comp_use_env (comp_use_env rx1 (lift_use_env (comp_use_env rx2 (infl_use_env r_s2a r_s3)) r)) (comp_use_env (infl_use_env r_s2a r_s3) r_ex))" in trans_leq_use_env)
     apply (rule_tac unroll_dcl_use_env)
     apply (rule_tac rhs_unroll_dcl_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (rule_tac rhs_fold_dcl_use_env)
     apply (simp)
    apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
     apply (rule_tac unroll_dcl_use_env)
     apply (rule_tac rhs_unroll_dcl_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (rule_tac disj_diff_leq_use_env)
      apply (rule_tac comm_disj_use_env)
      apply (rule_tac infl_disj_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (simp add: lift_comp_use_env)
     apply (rule_tac rhs_unroll_dcl_use_env)
     apply (rule_tac rhs_unroll_dcl_use_env)
     apply (simp add: infl_lift_use_env)
     apply (rule_tac disj_diff_leq_use_env)
      apply (rule_tac comm_disj_use_env)
      apply (rule_tac infl_disj_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (rule_tac rhs_fold_dcl_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (auto)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac dist_comp_leq_use_env)
    apply (auto)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
   apply (rule_tac self_infl_leq_use_env)
  apply (simp add: app_req_def)
  apply (auto)
  apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
   apply (simp)
   apply (rule_tac r_sb="diff_use_env (diff_use_env (comp_use_env rx1 (comp_use_env rx2 (infl_use_env r_s2a r_s3)))
           (comp_use_env rx1 (lift_use_env (comp_use_env rx2 (infl_use_env r_s2a r_s3)) r))) (comp_use_env (infl_use_env r_s2a r_s3) r_ex)" in trans_leq_use_env)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac lhs_fold_dcl_use_env)
   apply (rule_tac lhs_flip_use_env)
   apply (rule_tac lhs_unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env_gen)
    apply (rule_tac lhs_dist_dcl_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac self_comp_leq_use_env1)
    apply (rule_tac lhs_dist_dcl_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac self_comp_leq_use_env2)
     apply (rule_tac diff_infl_leq_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac self_comp_leq_use_env1)
   apply (rule_tac comp_leq_use_env2)
   apply (rule_tac dist_lift_leq_use_env)
   apply (rule_tac self_comp_leq_use_env1)
  apply (rule_tac lhs_unroll_dcl_use_env)
  apply (rule_tac lhs_unroll_dcl_use_env)
  apply (rule_tac dist_diff_leq_use_env)
  apply (rule_tac lhs_fold_dcl_use_env)
   apply (simp)
  apply (simp add: proper_exp_def)
  done
    *)
  
definition upc_init_abbrev where
  "upc_init_abbrev v1 v2 = AppExp (ConstExp UnpackConst) (PairExp v1 v2)"  

definition pair_abbrev where
  "pair_abbrev v1 v2 = PairExp v1 v2"  
  
definition upc_res_abbrev where
  "upc_res_abbrev f v1 v2 = LamExp f (AppExp (AppExp (VarExp f NoRef) v1) v2)"
  
lemma wt_sexp_drop_dep_all: "\<lbrakk> well_typed env r_s e tau r_s r_s; is_sexp e; safe_type_x tau r \<rbrakk> \<Longrightarrow>
  well_typed env (drop_use_env_dep r_s r) e tau (drop_use_env_dep r_s r) (drop_use_env_dep r_s r)"  
  apply (case_tac r)
    apply (auto)
   apply (rule_tac wt_sexp_no_all)
     apply (auto)
  apply (rule_tac wt_sexp_drop_all)
    apply (auto)
  apply (simp add: unlim_def)
  done  
  
lemma leq_safe_type: "\<lbrakk> aff_leq (req_type tau) r \<rbrakk> \<Longrightarrow> safe_type_x tau r"    
  apply (case_tac r)
    apply (auto)
   apply (case_tac "req_type tau")
     apply (auto)
  apply (simp add: unlim_def)
  apply (case_tac "req_type tau")
    apply (auto)
  done
    
lemma lift_drop_leq_use_env: "\<lbrakk> leq_use_env (lift_use_env r_x r) r_s \<rbrakk> \<Longrightarrow> leq_use_env (lift_use_env (drop_use_env_dep r_x r) r) r_s"    
  apply (rule_tac r_sb="lift_use_env r_x r" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac dist_lift_leq_use_env)
  apply (rule_tac self_drop_dep_leq_use_env)
  done
  
lemma aff_lift_use_env: "\<lbrakk> aff_use_env r_s (as_aff r) \<rbrakk> \<Longrightarrow> aff_use_env (lift_use_env r_s r) (as_aff r)"    
  apply (case_tac "r")
    apply (auto)
  apply (simp add: aff_use_env_def)
  done
  
lemma aff_drop_dep_use_env: "aff_use_env (drop_use_env_dep r_s r) (as_aff r)"    
  apply (case_tac "r")
    apply (auto)
    apply (simp add: aff_use_env_def)
    apply (simp add: null_use_env_def)
    apply (simp add: empty_use_env_def)
   apply (simp add: aff_use_env_def)
   apply (simp add: weak_use_env_def)
   apply (simp add: drop_use_env_def)
  apply (simp add: aff_use_env_def)
  done    
    
lemma unpack_pair_type: "\<lbrakk> well_typed env r_s1 (upc_init_abbrev v1 v2) t2 r_s2 rx; is_value v1; is_value v2;
  t2 = FunTy (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')) tx r' (as_aff r); f \<notin> free_vars v1; f \<notin> free_vars v2 \<rbrakk> \<Longrightarrow>
  (\<exists> rx1 rx2 r_ex.
    well_typed env rx1 v1 t1a rx1 rx1 \<and> well_typed env rx2 v2 t2a rx2 rx2 \<and> rx1 f = NoPerm \<and> rx2 f = NoPerm \<and>
    leq_use_env r_s2 (diff_use_env r_s1 r_ex) \<and> leq_use_env r_ex r_s1 \<and>
    leq_use_env (diff_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex) rx \<and>
    leq_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_s1 \<and> disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
    aff_use_env (lift_use_env rx1 r) (as_aff r) \<and> aff_use_env (lift_use_env rx2 r) (as_aff r)
  )"
  apply (simp add: upc_init_abbrev_def)
  apply (auto)
    (* well-typedness of e1 *)
  apply (rule_tac x="rem_use_env (drop_use_env_dep (comp_use_env rx1a (infl_use_env r_s2a r_s2aa)) r) f" in exI)
  apply (auto)
   apply (rule_tac well_typed_rem_perms)
    apply (rule_tac wt_sexp_drop_dep_all)
      apply (rule_tac infl_sexp_wp)
       apply (simp)
      apply (rule_tac value_is_sexp)
      apply (simp)
     apply (rule_tac value_is_sexp)
     apply (simp)
    apply (rule_tac leq_safe_type)
    apply (case_tac "req_type t1a")
      apply (auto)
    apply (case_tac r)
      apply (auto)
    apply (case_tac "req_type t2a")
      apply (auto)
   apply (simp add: non_prim_vars_def)
    (* well-typedness of e2 *)
  apply (rule_tac x="rem_use_env (drop_use_env_dep (comp_use_env rx2a (infl_use_env r_s2aa r_s3a)) r) f" in exI)
  apply (auto)
        apply (rule_tac well_typed_rem_perms)
         apply (rule_tac wt_sexp_drop_dep_all)
           apply (rule_tac infl_sexp_wp)
            apply (simp)
           apply (rule_tac value_is_sexp)
           apply (simp)
          apply (rule_tac value_is_sexp)
          apply (simp)
         apply (rule_tac leq_safe_type)
         apply (case_tac "req_type t2a")
           apply (auto)
          apply (case_tac r)
            apply (auto)
           apply (case_tac "req_type t1a")
             apply (auto)
          apply (case_tac "req_type t1a")
            apply (auto)
         apply (case_tac r)
           apply (auto)
         apply (case_tac "req_type t1a")
           apply (auto)
        apply (simp add: non_prim_vars_def)
    (* none bounds *)
    apply (simp add: rem_use_env_def)
   apply (simp add: rem_use_env_def)
    (* existential bounds *)
  apply (cut_tac r_sc="r_s3a" and r_sb="r_s2aa" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
     apply (simp_all)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (rule_tac x="comp_use_env (comp_use_env (comp_use_env (infl_use_env r_s2a r_s2aa) (infl_use_env r_s2aa r_s3a)) r_exa)
    (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in exI)
  apply (auto)
        apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
         apply (rule_tac rhs_unroll_dcl_use_env)
         apply (rule_tac dist_diff_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s3a r_exa" in trans_leq_use_env)
          apply (rule_tac rhs_unroll_dcl_use_env)
          apply (rule_tac dist_diff_leq_use_env)
          apply (simp_all)
        apply (rule_tac disj_diff_leq_use_env)
         apply (rule_tac comm_disj_use_env)
         apply (rule_tac disj_comp_use_env2)
          apply (rule_tac infl_disj_use_env)
          apply (rule_tac well_typed_perm_leq)
          apply (auto)
        apply (rule_tac infl_disj_use_env)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
         apply (simp)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac lhs_infl_leq_use_env)
          apply (rule_tac id_leq_use_env)
         apply (rule_tac lhs_infl_leq_use_env)
         apply (rule_tac well_typed_perm_leq)
         apply (auto)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s3a r_exa" in trans_leq_use_env)
          apply (rule_tac diff_leq_use_env)
          apply (simp_all)
    (* - primitive case *)
      apply (case_tac "r = NoPerm")
       apply (simp)
       apply (rule_tac diff_leq_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac rem_leq_use_env)
        apply (rule_tac leq_empty_use_env)
       apply (rule_tac rem_leq_use_env)
       apply (rule_tac leq_empty_use_env)
    (* - non-primitive case *)
      apply (simp add: pair_req_def)
      apply (simp add: app_req_def)
      apply (case_tac "as_aff r = Prim")
       apply (case_tac r)
         apply (auto)
      apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac lhs_unroll_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac r_sb="diff_use_env (comp_use_env (lift_use_env rx1a r) (lift_use_env rx2a r)) r_exa" in trans_leq_use_env)
       apply (rule_tac comp_leq_use_env2)
       apply (simp)
      apply (rule_tac lhs_unroll_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac lhs_dist_dcl_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (simp add: lift_diff_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac dist_lift_leq_use_env)
       apply (rule_tac r_sb="diff_use_env (comp_use_env rx1a (infl_use_env r_s2a r_s2aa)) (infl_use_env r_s2a r_s2aa)" in trans_leq_use_env)
        apply (rule_tac lhs_dist_dcl_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac self_diff_leq_use_env)
        apply (rule_tac diff_infl_leq_use_env)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac rem_leq_use_env)
        apply (rule_tac self_drop_dep_leq_use_env)
       apply (rule_tac self_comp_leq_use_env1)
      apply (simp add: lift_diff_use_env)
      apply (rule_tac comp_leq_use_env2)
      apply (rule_tac dist_lift_leq_use_env)
      apply (rule_tac r_sb="diff_use_env (comp_use_env rx2a (infl_use_env r_s2aa r_s3a)) (infl_use_env r_s2aa r_s3a)" in trans_leq_use_env)
       apply (rule_tac lhs_dist_dcl_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac diff_infl_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env_gen)
       apply (rule_tac rem_leq_use_env)
       apply (rule_tac self_drop_dep_leq_use_env)
      apply (rule_tac self_comp_leq_use_env2)
    (* main bound *)
     apply (rule_tac dist_comp_leq_use_env)
      apply (simp add: lift_rem_use_env)
      apply (rule_tac rem_leq_use_env)
      apply (rule_tac lift_drop_leq_use_env)
      apply (simp add: lift_comp_use_env)
      apply (simp add: infl_lift_use_env)
      apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac r_sb="r_s2aa" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (rule_tac r_sb="r_s3a" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
      apply (rule_tac self_infl_leq_use_env)
     apply (simp add: lift_rem_use_env)
     apply (rule_tac rem_leq_use_env)
     apply (rule_tac lift_drop_leq_use_env)
     apply (simp add: lift_comp_use_env)
     apply (simp add: infl_lift_use_env)
     apply (rule_tac r_sb="r_s2aa" in trans_leq_use_env)
      apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac r_sb="r_s3a" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
     apply (rule_tac self_infl_leq_use_env)
    (* disjointness *)
    apply (simp add: lift_rem_use_env)
    apply (rule_tac r_s="lift_use_env (comp_use_env rx1a (infl_use_env r_s2a r_s2aa)) r" in disj_leq_use_env1)
     apply (rule_tac r_s="lift_use_env (comp_use_env rx2a (infl_use_env r_s2aa r_s3a)) r" in disj_leq_use_env2)
      apply (simp add: lift_comp_use_env)
      apply (simp add: infl_lift_use_env)
      apply (rule_tac disj_comp_use_env1)
       apply (rule_tac disj_comp_use_env2)
        apply (simp)
       apply (rule_tac infl_disj_use_env)
       apply (simp)
      apply (rule_tac disj_comp_use_env2)
       apply (rule_tac comm_disj_use_env)
       apply (rule_tac infl_disj_use_env)
       apply (rule_tac r_sb="r_s3a" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
      apply (rule_tac comm_disj_use_env)
      apply (rule_tac infl_disj_use_env)
      apply (rule_tac self_infl_leq_use_env)
     apply (rule_tac rem_leq_use_env)
     apply (rule_tac lift_drop_leq_use_env)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (rule_tac lift_drop_leq_use_env)
    apply (rule_tac id_leq_use_env)
    (* affinity reqs *)
   apply (rule_tac aff_lift_use_env)
   apply (rule_tac aff_rem_use_env)
   apply (rule_tac aff_drop_dep_use_env)
  apply (rule_tac aff_lift_use_env)
  apply (rule_tac aff_rem_use_env)
  apply (rule_tac aff_drop_dep_use_env)
  done
    (*
lemma well_typed_add_perms2: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; x \<notin> non_prim_vars env e \<rbrakk> \<Longrightarrow>
  well_typed env (add_use_env r_s1 x r) e tau (add_use_env r_s2 x r) rx"
  apply (rule_tac rx="rem_use_env rx x" in well_typed_incr_req)
    apply (cut_tac r_s="r_s1" and x="x" and r="r" in partial_add_rem_use_env)
    apply (cut_tac r_s="r_s2" and x="x" and r="r" in partial_add_rem_use_env)
    apply (cut_tac r_s="rem_use_env r_s1 x" and x="x" and r="r" in add_comp_use_env)
     apply (auto)
     apply (simp add: rem_use_env_def)
    apply (cut_tac r_s="rem_use_env r_s2 x" and x="x" and r="r" in add_comp_use_env)
     apply (auto)
     apply (simp add: rem_use_env_def)
    apply (rule_tac well_typed_comp_perms)
     apply (rule_tac well_typed_rem_perms)
      apply (auto)
    apply (simp add: disj_use_env_def)
    apply (simp add: one_use_env_def)
    apply (simp add: rem_use_env_def)
   apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and tau="tau" and ?r_s2.0="r_s2" and rx="rx" and x="x" in well_typed_rem_perms)
     apply (auto)
  done     *)
    
    
lemma aff_leq_perm: "\<lbrakk> aff_use_env r_s (as_aff r) \<rbrakk> \<Longrightarrow> leq_perm (r_s x) r"    
  apply (case_tac r)
    apply (auto)
   apply (simp add: aff_use_env_def)
   apply (simp add: null_use_env_def)
  apply (simp add: aff_use_env_def)
  apply (simp add: weak_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma comp_use_no_own: "\<lbrakk> r_sa x \<noteq> OwnPerm; r_sb x \<noteq> OwnPerm \<rbrakk> \<Longrightarrow> comp_use_env r_sa r_sb x \<noteq> OwnPerm"    
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_sa x")
    apply (auto)
   apply (case_tac "r_sb x")
     apply (auto)
  apply (case_tac "r_sb x")
    apply (auto)
  done
    
lemma sares_unpack_case: "\<lbrakk>well_typed_state s1 env rs_map; valid_exp_use_env s1 rs_map r_f; proper_exp rs_map (AppExp (ConstExp UnpackConst) (PairExp v1 v2));
        t2 = FunTy (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')) tx r' (as_aff r); is_value v1; is_value v2;
        f \<notin> free_vars v1; f \<notin> free_vars v2; f \<notin> ref_vars v1; f \<notin> ref_vars v2; leq_perm r r';
        well_typed env r_s1 (upc_init_abbrev v1 v2) t2 r_s3 rx \<rbrakk>
       \<Longrightarrow> \<exists>g_ax. (\<exists>rxa. (\<exists>r_end r_s' t1 ra a r_s2 rx1.
                             (\<exists>t1b rb. (\<exists>aa. add_env (red_env env g_ax) f (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')) (deref_name f NoRef) =
                                             Some (FunTy t1b (FunTy t1 tx ra a) rb aa)) \<and>
                                       (\<exists>r_s2a rx1a.
                                           (\<exists>r_ex tau_x.
                                               add_env (red_env env g_ax) f (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')) f = Some tau_x \<and>
                                               leq_use_env (ereq_use_env f tau_x) (add_use_env rxa f r') \<and>
                                               leq_use_env r_s2a (diff_use_env (add_use_env rxa f r') (comp_use_env (ereq_use_env f tau_x) r_ex)) \<and>
                                               leq_use_env rx1a r_s2a \<and>
                                               leq_use_env r_ex (add_use_env rxa f r') \<and>
                                               leq_use_env (diff_use_env (ereq_use_env f tau_x) (comp_use_env (ereq_use_env f tau_x) r_ex)) rx1a) \<and>
                                           (\<exists>rx2 r_s3.
                                               well_typed (add_env (red_env env g_ax) f (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r'))) r_s2a v1 t1b
                                                r_s3 rx2 \<and>
                                               (\<exists>r_ex. leq_use_env r_s2 (diff_use_env r_s3 (comp_use_env (comp_use_env rx1a (lift_use_env rx2 rb)) r_ex)) \<and>
                                                       leq_use_env (comp_use_env rx1a (lift_use_env rx2 rb)) r_s3 \<and>
                                                       disj_use_env rx1a (lift_use_env rx2 rb) \<and>
                                                       leq_use_env rx1 r_s2 \<and>
                                                       leq_use_env r_ex (add_use_env rxa f r') \<and>
                                                       leq_use_env (app_req rx1a rx2 rb (FunTy t1 tx ra a) r_ex) rx1)))) \<and>
                             (\<exists>rx2 r_s3.
                                 well_typed (add_env (red_env env g_ax) f (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r'))) r_s2 v2 t1 r_s3 rx2 \<and>
                                 (\<exists>r_ex. leq_use_env r_s' (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 ra)) r_ex)) \<and>
                                         leq_use_env (comp_use_env rx1 (lift_use_env rx2 ra)) r_s3 \<and>
                                         disj_use_env rx1 (lift_use_env rx2 ra) \<and>
                                         leq_use_env r_end r_s' \<and>
                                         leq_use_env r_ex (add_use_env rxa f r') \<and> leq_use_env (app_req rx1 rx2 ra tx r_ex) r_end))) \<and>
                         aff_use_env rxa (as_aff r) \<and>
                         leq_use_env rxa (exp_red_use_env r_s1 g_ax) \<and>
                         (\<exists>r_ex. leq_use_env (end_red_use_env r_s3 g_ax) (diff_use_env (exp_red_use_env r_s1 g_ax) r_ex) \<and>
                                 leq_use_env (end_red_use_env rx g_ax) (end_red_use_env r_s3 g_ax) \<and>
                                 leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and> leq_use_env (diff_use_env rxa r_ex) (end_red_use_env rx g_ax))) \<and>
                  proper_exp (red_nres_map rs_map g_ax) (LamExp f (AppExp (AppExp (VarExp f NoRef) v1) v2)) \<and>
                  well_typed_state s1 (red_env env g_ax) (red_nres_map rs_map g_ax) \<and>
                  valid_exp_use_env s1 (red_nres_map rs_map g_ax) (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s3) g_ax \<and> corr_act NoAct g_ax"  
  apply (rule_tac x="NoResAct" in exI)
  apply (auto)
    (* prelim: prepare the type of the pairs *)
   apply (cut_tac env="env" and ?v1.0="v1" and ?v2.0="v2" in unpack_pair_type)
       apply (auto)
    (* permissions given to f v1 v2 derived from the permissions of the pair *)
   apply (rule_tac x="comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)" in exI)
   apply (auto)
     apply (rule_tac x="diff_use_env (comp_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) (one_use_env f r'))
      (comp_use_env (one_use_env f r') (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)))" in exI)
     apply (rule_tac x="diff_use_env (comp_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) (one_use_env f r'))
      (comp_use_env (one_use_env f r') (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)))" in exI)
    (* typing f v1 *)
     apply (rule_tac x="t2a" in exI)
     apply (rule_tac x="r" in exI)
     apply (rule_tac x="as_aff r'" in exI)
     apply (rule_tac x="diff_use_env (comp_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) (one_use_env f r'))
      (comp_use_env (one_use_env f r') (lift_use_env rx1 r))" in exI)
     apply (rule_tac x="diff_use_env (comp_use_env (lift_use_env rx1 r) (one_use_env f r'))
      (comp_use_env (one_use_env f r') (lift_use_env rx1 r))" in exI)
     apply (auto)
    (* typing f *)
      apply (rule_tac x="t1a" in exI)
      apply (rule_tac x="r" in exI)
      apply (auto)
       apply (simp add: add_env_def)
       apply (simp add: deref_name_def)
      apply (rule_tac x="diff_use_env (comp_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) (one_use_env f r')) (one_use_env f r')" in exI)
      apply (rule_tac x="diff_use_env (one_use_env f r') (one_use_env f r')" in exI)
      apply (auto)
       apply (rule_tac x="one_use_env f r'" in exI)
       apply (rule_tac x="FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')" in exI)
       apply (auto)
            apply (simp add: add_env_def)
           apply (rule_tac ereq_leq_use_envx)
           apply (simp add: add_use_env_def)
           apply (simp add: end_req_perm_def)
           apply (case_tac "r'")
             apply (auto)
          apply (rule_tac dist_diff_leq_use_env_gen)
           apply (cut_tac r_s="comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)" and x="f" and r="r'" in add_comp_use_env)
            apply (auto)
            apply (rule_tac q="r" in trans_leq_perm)
             apply (rule_tac r_s="comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)" and x="f" in aff_leq_perm)
             apply (rule_tac aff_comp_use_env)
              apply (auto)
           apply (rule_tac id_leq_use_env)
          apply (rule_tac dist_comp_leq_use_env)
           apply (rule_tac ereq_leq_use_envx)
           apply (simp add: one_use_env_def)
           apply (simp add: end_req_perm_def)
           apply (case_tac "r'")
             apply (auto)
          apply (rule_tac id_leq_use_env)
         apply (rule_tac dist_diff_leq_use_env)
         apply (rule_tac self_comp_leq_use_env2)
        apply (simp add: leq_use_env_def)
        apply (simp add: one_use_env_def)
        apply (simp add: add_use_env_def)
        apply (case_tac "r'")
          apply (auto)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac ereq_leq_use_envx)
        apply (simp add: one_use_env_def)
        apply (simp add: end_req_perm_def)
        apply (case_tac "r'")
          apply (auto)
       apply (rule_tac self_comp_leq_use_env2)
    (* typing v1 + resolving app *)
      apply (rule_tac x="rx1" in exI)
      apply (rule_tac x="diff_use_env (comp_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) (one_use_env f r')) (one_use_env f r')" in exI)
      apply (auto)
       apply (rule_tac rx="diff_use_env rx1 (one_use_env f r')" in well_typed_incr_req)
         apply (rule_tac well_typed_diff_perms)
          apply (rule_tac r_s="rx1" in well_typed_incr_simul_perm)
           apply (rule_tac comp_leq_use_env1)
           apply (rule_tac comp_leq_use_env1)
           apply (rule_tac self_lift_leq_use_env)
          apply (rule_tac well_typed_add_vars)
            apply (auto)
         apply (simp add: own_env_vars_def)
         apply (simp add: one_use_env_def)
         apply (simp add: non_prim_vars_def)
         apply (case_tac "x = f")
          apply (auto)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac disj_diff_leq_use_env)
        apply (simp add: disj_use_env_def)
        apply (simp add: mini_disj_use_env_def)
        apply (simp add: one_use_env_def)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac self_lift_leq_use_env)
    (* first app bounds *)
      apply (rule_tac x="empty_use_env" in exI)
      apply (auto)
           apply (rule_tac rhs_fold_dcl_use_env)
           apply (rule_tac dist_diff_leq_use_env_gen)
            apply (rule_tac id_leq_use_env)
           apply (rule_tac dist_comp_leq_use_env)
            apply (rule_tac self_comp_leq_use_env1)
           apply (rule_tac dist_comp_leq_use_env)
            apply (rule_tac dist_comp_leq_use_env)
             apply (rule_tac diff_leq_use_env)
             apply (rule_tac self_comp_leq_use_env1)
            apply (rule_tac self_comp_leq_use_env2)
           apply (rule_tac leq_empty_use_env)
          apply (rule_tac dist_comp_leq_use_env)
           apply (rule_tac dist_diff_leq_use_env)
           apply (rule_tac self_comp_leq_use_env2)
          apply (rule_tac disj_diff_leq_use_env)
           apply (simp add: disj_use_env_def)
           apply (simp add: mini_disj_use_env_def)
           apply (simp add: one_use_env_def)
           apply (case_tac r)
             apply (simp_all)
          apply (rule_tac comp_leq_use_env1)
          apply (rule_tac self_comp_leq_use_env1)
         apply (rule_tac r_s="one_use_env f r'" in disj_leq_use_env1)
          apply (simp add: disj_use_env_def)
          apply (simp add: mini_disj_use_env_def)
          apply (simp add: one_use_env_def)
          apply (case_tac r)
            apply (simp_all)
         apply (rule_tac self_diff_leq_use_env)
        apply (rule_tac dist_diff_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac comp_leq_use_env1)
         apply (rule_tac self_comp_leq_use_env1)
        apply (rule_tac self_comp_leq_use_env2)
       apply (rule_tac leq_empty_use_env)
      apply (simp add: app_req_def)
      apply (auto)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac rhs_unroll_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env_gen)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac dist_diff_leq_use_env)
        apply (rule_tac self_comp_leq_use_env2)
       apply (rule_tac disj_diff_leq_use_env)
        apply (simp add: disj_use_env_def)
        apply (simp add: mini_disj_use_env_def)
        apply (simp add: one_use_env_def)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac self_lift_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac self_comp_leq_use_env2)
    (* typing v2 *)
     apply (rule_tac x="rx2" in exI)
     apply (rule_tac x="diff_use_env (comp_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) (one_use_env f r'))
      (comp_use_env (one_use_env f r') (lift_use_env rx1 r))" in exI)
     apply (auto)
      apply (rule_tac rx="diff_use_env rx2 (comp_use_env (one_use_env f r') (lift_use_env rx1 r))" in well_typed_incr_req)
        apply (rule_tac well_typed_diff_perms)
         apply (rule_tac well_typed_comp_perms_gen)
          apply (rule_tac well_typed_comp_perms2)
           apply (rule_tac well_typed_lift_perms)
           apply (rule_tac well_typed_add_vars)
             apply (auto)
          apply (rule_tac comm_disj_use_env)
          apply (simp)
         apply (simp add: mini_disj_use_env_def)
         apply (simp add: one_use_env_def)
         apply (simp add: comp_use_env_def)
         apply (case_tac r)
           apply (simp_all)
        apply (simp add: own_env_vars_def)
        apply (case_tac "f = x")
         apply (simp add: non_prim_vars_def)
        apply (case_tac "one_use_env f r' x = OwnPerm")
         apply (simp add: one_use_env_def)
        apply (case_tac "lift_use_env rx1 r x = OwnPerm")
         apply (case_tac "lift_use_env rx2 r x = NoPerm")
          apply (cut_tac x="x" and ?r_s1.0="rx2" and env="env" and e="v2" in well_typed_no_npv_use)
            apply (auto)
           apply (case_tac r)
             apply (auto)
           apply (case_tac "rx2 x")
             apply (auto)
          apply (simp add: non_prim_vars_def)
          apply (simp add: add_env_def)
          apply (simp add: non_prim_entry_def)
         apply (simp add: disj_use_env_def)
         apply (simp add: mini_disj_use_env_def)
        apply (cut_tac r_sa="one_use_env f r'" and r_sb="lift_use_env rx1 r" and x="x" in comp_use_no_own)
          apply (auto)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac disj_diff_leq_use_env)
       apply (rule_tac disj_comp_use_env1)
        apply (simp add: disj_use_env_def)
        apply (simp add: mini_disj_use_env_def)
        apply (simp add: one_use_env_def)
       apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
        apply (simp)
       apply (rule_tac self_lift_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac comp_leq_use_env2)
      apply (rule_tac self_lift_leq_use_env)
    (* (f v1) v2 bounds *)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
          apply (rule_tac rhs_fold_dcl_use_env)
          apply (rule_tac dist_diff_leq_use_env_gen)
           apply (rule_tac id_leq_use_env)
          apply (rule_tac dist_comp_leq_use_env)
           apply (rule_tac dist_comp_leq_use_env)
            apply (rule_tac self_comp_leq_use_env1)
           apply (rule_tac comp_leq_use_env2)
           apply (rule_tac self_comp_leq_use_env1)
          apply (rule_tac dist_comp_leq_use_env)
           apply (rule_tac dist_comp_leq_use_env)
            apply (rule_tac diff_leq_use_env)
            apply (rule_tac dist_comp_leq_use_env)
             apply (rule_tac comp_leq_use_env2)
             apply (rule_tac self_comp_leq_use_env1)
            apply (rule_tac self_comp_leq_use_env1)
           apply (rule_tac comp_leq_use_env2)
           apply (rule_tac self_comp_leq_use_env2)
          apply (rule_tac leq_empty_use_env)
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac dist_diff_leq_use_env)
          apply (rule_tac dist_comp_leq_use_env)
           apply (rule_tac comp_leq_use_env1)
           apply (rule_tac self_comp_leq_use_env1)
          apply (rule_tac self_comp_leq_use_env2)
         apply (rule_tac disj_diff_leq_use_env)
          apply (rule_tac disj_comp_use_env1)
           apply (simp add: disj_use_env_def)
           apply (simp add: mini_disj_use_env_def)
           apply (simp add: one_use_env_def)
           apply (case_tac r)
             apply (auto)
         apply (rule_tac comp_leq_use_env1)
         apply (rule_tac self_comp_leq_use_env2)
        apply (rule_tac r_s="comp_use_env (lift_use_env rx1 r) (one_use_env f r')" in disj_leq_use_env1)
         apply (rule_tac disj_comp_use_env1)
          apply (simp)
         apply (simp add: disj_use_env_def)
         apply (simp add: mini_disj_use_env_def)
         apply (simp add: one_use_env_def)
         apply (case_tac r)
           apply (simp_all)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac leq_empty_use_env)
     apply (simp add: app_req_def)
     apply (auto)
      apply (rule_tac leq_empty_use_env)
     apply (rule_tac lhs_unroll_dcl_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac unroll_dcl_use_env)
     apply (rule_tac rhs_unroll_dcl_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (rule_tac rhs_fold_dcl_use_env)
     apply (rule_tac lhs_dist_dcl_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac diff_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac self_comp_leq_use_env2)
     apply (rule_tac disj_diff_leq_use_env)
      apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
       apply (rule_tac disj_comp_use_env1)
        apply (simp add: disj_use_env_def)
        apply (simp add: mini_disj_use_env_def)
        apply (simp add: one_use_env_def)
        apply (case_tac r)
          apply (simp_all)
      apply (rule_tac diff_leq_use_env)
      apply (rule_tac self_lift_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac comp_leq_use_env1)
     apply (rule_tac comp_leq_use_env2)
     apply (rule_tac self_lift_leq_use_env)
    apply (rule_tac aff_comp_use_env)
     apply (simp_all)
    (* final existential *)
   apply (rule_tac x="r_ex" in exI)
   apply (auto)
   apply (rule_tac well_typed_perm_leqx)
   apply (auto)
    (* proper expression *)
  apply (simp add: proper_exp_def)
  done
    
    
    
  (*
lemma sares_unpack_case: "\<lbrakk>well_typed_state s1 env rs_map; valid_exp_use_env s1 rs_map r_f; proper_exp rs_map (AppExp (ConstExp UnpackConst) (PairExp v1 v2));
        leq_use_env r_s3 (diff_use_env r_s2 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex));
        leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s2; leq_use_env r_ex r_s1; leq_use_env rx r_s3;
        leq_use_env (app_req rx1 rx2 r (FunTy (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')) tx r' (as_aff r)) r_ex) rx; leq_use_env r_s1 r_f;
        ax = NoAct; c = UnpackConst; v = PairExp v1 v2; t1 = PairTy t1a t2a r; s2 = s1;
        t2 = FunTy (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')) tx r' (as_aff r); e2 = LamExp f (AppExp (AppExp (VarExp f NoRef) v1) v2); a = Prim;
        leq_perm r r'; is_value v1; is_value v2; f \<notin> free_vars v1; f \<notin> free_vars v2; f \<notin> ref_vars v1; f \<notin> ref_vars v2; well_typed env r_s1 v1 t1a r_s2a rx1a;
        well_typed env r_s2a v2 t2a r_s3a rx2a; leq_use_env (lift_use_env rx1a r) r_s3a; leq_use_env (lift_use_env rx2a r) r_s3a;
        aff_leq (max_aff (req_type t1a) (req_type t2a)) r; disj_use_env (lift_use_env rx1a r) (lift_use_env rx2a r);
        leq_use_env r_s2 (diff_use_env r_s3a r_exa); leq_use_env rx2 r_s2; leq_use_env r_exa r_s1;
        leq_use_env (pair_req (comp_use_env (lift_use_env rx1a r) (lift_use_env rx2a r)) r_exa (PairTy t1a t2a r)) rx2\<rbrakk>
       \<Longrightarrow> \<exists>g_ax. (\<exists>rxa. (\<exists>r_end r_s' t1 ra a r_s2 rx1.
                             (\<exists>t1b rb. (\<exists>aa. add_env (red_env env g_ax) f (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')) (deref_name f NoRef) =
                                             Some (FunTy t1b (FunTy t1 tx ra a) rb aa)) \<and>
                                       (\<exists>r_s2a rx1a.
                                           (\<exists>r_ex tau_x.
                                               add_env (red_env env g_ax) f (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r')) f = Some tau_x \<and>
                                               leq_use_env (ereq_use_env f tau_x) (add_use_env rxa f r') \<and>
                                               leq_use_env r_s2a (diff_use_env (add_use_env rxa f r') (comp_use_env (ereq_use_env f tau_x) r_ex)) \<and>
                                               leq_use_env rx1a r_s2a \<and>
                                               leq_use_env r_ex (add_use_env rxa f r') \<and>
                                               leq_use_env (diff_use_env (ereq_use_env f tau_x) (comp_use_env (ereq_use_env f tau_x) r_ex)) rx1a) \<and>
                                           (\<exists>rx2 r_s3.
                                               well_typed (add_env (red_env env g_ax) f (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r'))) r_s2a v1 t1b
                                                r_s3 rx2 \<and>
                                               (\<exists>r_ex. leq_use_env r_s2 (diff_use_env r_s3 (comp_use_env (comp_use_env rx1a (lift_use_env rx2 rb)) r_ex)) \<and>
                                                       leq_use_env (comp_use_env rx1a (lift_use_env rx2 rb)) r_s3 \<and>
                                                       disj_use_env rx1a (lift_use_env rx2 rb) \<and>
                                                       leq_use_env rx1 r_s2 \<and>
                                                       leq_use_env r_ex (add_use_env rxa f r') \<and>
                                                       leq_use_env (app_req rx1a rx2 rb (FunTy t1 tx ra a) r_ex) rx1)))) \<and>
                             (\<exists>rx2 r_s3.
                                 well_typed (add_env (red_env env g_ax) f (FunTy t1a (FunTy t2a tx r (as_aff r')) r (as_aff r'))) r_s2 v2 t1 r_s3 rx2 \<and>
                                 (\<exists>r_ex. leq_use_env r_s' (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 ra)) r_ex)) \<and>
                                         leq_use_env (comp_use_env rx1 (lift_use_env rx2 ra)) r_s3 \<and>
                                         disj_use_env rx1 (lift_use_env rx2 ra) \<and>
                                         leq_use_env r_end r_s' \<and>
                                         leq_use_env r_ex (add_use_env rxa f r') \<and> leq_use_env (app_req rx1 rx2 ra tx r_ex) r_end))) \<and>
                         aff_use_env rxa (as_aff r) \<and>
                         leq_use_env rxa (exp_red_use_env r_s1 g_ax) \<and>
                         (\<exists>r_ex. leq_use_env (end_red_use_env r_s3 g_ax) (diff_use_env (exp_red_use_env r_s1 g_ax) r_ex) \<and>
                                 leq_use_env (end_red_use_env rx g_ax) (end_red_use_env r_s3 g_ax) \<and>
                                 leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and> leq_use_env (diff_use_env rxa r_ex) (end_red_use_env rx g_ax))) \<and>
                  proper_exp (red_nres_map rs_map g_ax) (LamExp f (AppExp (AppExp (VarExp f NoRef) v1) v2)) \<and>
                  well_typed_state s1 (red_env env g_ax) (red_nres_map rs_map g_ax) \<and>
                  valid_exp_use_env s1 (red_nres_map rs_map g_ax) (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s3) g_ax \<and> corr_act NoAct g_ax"
  apply (rule_tac x="NoResAct" in exI)
    apply (auto)
   apply (rule_tac x="comp_use_env (drop_use_env_dep (lift_use_env rx1a r) r) (drop_use_env_dep (lift_use_env rx2a r) r)" in exI)
   apply (auto)
      apply (rule_tac x="empty_use_env" in exI)
      apply (rule_tac x="empty_use_env" in exI)
      apply (rule_tac x="t2a" in exI)
      apply (rule_tac x="r" in exI)
      apply (rule_tac x="as_aff r'" in exI)
      apply (rule_tac x="empty_use_env" in exI)
      apply (rule_tac x="empty_use_env" in exI)
    *)
    
    
end