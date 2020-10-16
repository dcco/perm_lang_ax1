theory SafeSubRename
  imports WTLemma SubstExp
begin
  

definition rename_use_env where
  "rename_use_env r_s x y = (add_use_env (rem_use_env r_s x) y (r_s x))"  
  
lemma rename_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (rename_use_env r_x x y) (rename_use_env r_s x y)"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: rem_use_env_def)
  done
  
lemma rename_ereq_use_env: "ereq_use_env y tau = rename_use_env (ereq_use_env x tau) x y"
  apply (case_tac "\<forall> x'. ereq_use_env y tau x' = rename_use_env (ereq_use_env x tau) x y x'")
   apply (auto)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
 
lemma rename_ereq_use_env2: "\<lbrakk> z \<noteq> x ; z \<noteq> y\<rbrakk> \<Longrightarrow> ereq_use_env z tau = rename_use_env (ereq_use_env z tau) x y"    
  apply (case_tac "\<forall> x'. ereq_use_env z tau x' = rename_use_env (ereq_use_env z tau) x y x'")
   apply (auto)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "z = x'")
   apply (auto)
   apply (simp add: rem_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done    
    
lemma rename_req_use_env: "req_use_env y tau = rename_use_env (req_use_env x tau) x y"
  apply (case_tac "\<forall> x'. req_use_env y tau x' = rename_use_env (req_use_env x tau) x y x'")
   apply (auto)
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
 
lemma rename_req_use_env2: "\<lbrakk> z \<noteq> x ; z \<noteq> y\<rbrakk> \<Longrightarrow> req_use_env z tau = rename_use_env (req_use_env z tau) x y"    
  apply (case_tac "\<forall> x'. req_use_env z tau x' = rename_use_env (req_use_env z tau) x y x'")
   apply (auto)
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "z = x'")
   apply (auto)
   apply (simp add: rem_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
    
lemma rename_add_use_env: "add_use_env (rename_use_env r_s x y) y r = rename_use_env (add_use_env r_s x r) x y"    
  apply (case_tac "\<forall> x'. add_use_env (rename_use_env r_s x y) y r x' = rename_use_env (add_use_env r_s x r) x y x'")
   apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)  
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done

lemma rename_add_use_env2: "\<lbrakk> z \<noteq> x; z \<noteq> y \<rbrakk> \<Longrightarrow> add_use_env (rename_use_env r_s x y) z r = rename_use_env (add_use_env r_s z r) x y"    
  apply (case_tac "\<forall> x'. add_use_env (rename_use_env r_s x y) z r x' = rename_use_env (add_use_env r_s z r) x y x'")    
   apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)  
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "z = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
 
lemma rename_add_use_env3: "\<lbrakk> r_s x = NoPerm \<rbrakk> \<Longrightarrow> add_use_env r_s y r = rename_use_env (add_use_env r_s x r) x y"
  apply (case_tac "\<forall> x'. add_use_env r_s y r x' = rename_use_env (add_use_env r_s x r) x y x'")
   apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
  
lemma rename_comp_use_env: "comp_use_env (rename_use_env r_x x y) (rename_use_env r_s x y) = rename_use_env (comp_use_env r_x r_s) x y"    
  apply (case_tac "\<forall> x'. comp_use_env (rename_use_env r_x x y) (rename_use_env r_s x y) x' = rename_use_env (comp_use_env r_x r_s) x y x'")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
    
lemma rename_diff_use_env: "diff_use_env (rename_use_env r_x x y) (rename_use_env r_s x y) = rename_use_env (diff_use_env r_x r_s) x y"    
  apply (case_tac "\<forall> x'. diff_use_env (rename_use_env r_x x y) (rename_use_env r_s x y) x' = rename_use_env (diff_use_env r_x r_s) x y x'")
  apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
    
lemma rename_lift_use_env: "lift_use_env (rename_use_env r_s x y) r = rename_use_env (lift_use_env r_s r) x y"  
  apply (case_tac "\<forall> x'. lift_use_env (rename_use_env r_s x y) r x' = rename_use_env (lift_use_env r_s r) x y x'")
   apply (auto)
  apply (case_tac r)
    apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
   apply (simp add: rem_use_env_def)
   apply (case_tac "x = x'")
    apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
  
lemma aff_rename_use_env: "\<lbrakk> aff_use_env r_s a \<rbrakk> \<Longrightarrow> aff_use_env (rename_use_env r_s x y) a"    
  apply (simp add: aff_use_env_def)
  apply (case_tac a)
    apply (auto)
   apply (simp add: rename_use_env_def)
   apply (simp add: add_use_env_def)
   apply (simp add: weak_use_env_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (simp add: rem_use_env_def)
   apply (case_tac "x = xa")
    apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: null_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: rem_use_env_def)
  done
  (*
lemma safe_lift_rename_use_env: "\<lbrakk> safe_use_lift r_s r \<rbrakk> \<Longrightarrow> safe_use_lift (rename_use_env r_s x y) r"
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac r)
    apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = xa")
   apply (auto)
  done*)

lemma disj_rename_use_env: "\<lbrakk> disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> disj_use_env (rename_use_env r_x x y) (rename_use_env r_s x y)"
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
   apply (simp add: rename_use_env_def)
   apply (simp add: add_use_env_def)
   apply (auto)
   apply (simp add: rem_use_env_def)
   apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  apply (simp add: rem_use_env_def)
  apply (auto)
  done
    
lemma artp_var_case1: "\<lbrakk>x \<notin> deref_vars x x2a; y \<noteq> x; y \<notin> deref_vars x x2a; add_env env x t (deref_name x x2a) = Some tau; add_env env x t x = Some tau_x;
        var_val_type x2a tau tau_x; leq_use_env (ereq_use_env x tau_x) r_s1; leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env x tau_x) r_ex));
        leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (diff_use_env (ereq_use_env x tau_x) (comp_use_env (ereq_use_env x tau_x) r_ex)) rx\<rbrakk>
       \<Longrightarrow> \<exists>r_ex tau_x.
              add_env env y t y = Some tau_x \<and>
              var_val_type x2a tau tau_x \<and>
              leq_use_env (ereq_use_env y tau_x) (rename_use_env r_s1 x y) \<and>
              leq_use_env (rename_use_env r_s2 x y) (diff_use_env (rename_use_env r_s1 x y) (comp_use_env (ereq_use_env y tau_x) r_ex)) \<and>
              leq_use_env (rename_use_env rx x y) (rename_use_env r_s2 x y) \<and>
              leq_use_env r_ex (rename_use_env r_s1 x y) \<and>
              leq_use_env (diff_use_env (ereq_use_env y tau_x) (comp_use_env (ereq_use_env y tau_x) r_ex)) (rename_use_env rx x y)"
  apply (simp add: add_env_def)
  apply (auto)
   apply (case_tac "\<not> leq_perm (end_req_perm tau_x) (r_s1 x)")
    apply (cut_tac r_x="ereq_use_env x tau_x" and r_s="r_s1" and x="x" in spec_leq_perm)
     apply (simp)
    apply (simp add: ereq_use_env_def)
    apply (simp add: one_use_env_def)
   apply (simp add: leq_use_env_def)
   apply (simp add: ereq_use_env_def)
   apply (simp add: one_use_env_def)
   apply (simp add: rename_use_env_def)
   apply (simp add: add_use_env_def)
  apply (cut_tac x="x" and y="y" and tau="tau_x" in rename_ereq_use_env)
  apply (simp)
  apply (case_tac "\<not> comp_use_env (ereq_use_env y tau_x) (rename_use_env r_ex x y) = rename_use_env (comp_use_env (ereq_use_env x tau_x) r_ex) x y")
   apply (cut_tac r_x="ereq_use_env x tau_x" and r_s="r_ex" and x="x" and y="y" in rename_comp_use_env)
   apply (simp)
  apply (rule_tac x="rename_use_env r_ex x y" in exI)
  apply (auto)
     apply (cut_tac r_x="r_s1" and r_s="comp_use_env (ereq_use_env x tau_x) r_ex" and x="x" and y="y" in rename_diff_use_env)
     apply (simp)
     apply (rule_tac rename_leq_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
  apply (cut_tac r_x="ereq_use_env x tau_x" and r_s="comp_use_env (ereq_use_env x tau_x) r_ex" and x="x" and y="y" in rename_diff_use_env)
  apply (simp)
  apply (rule_tac rename_leq_use_env)
  apply (simp)
  done
 
lemma rename_ref_vars1: "\<lbrakk> z \<notin> ref_vars e; z \<noteq> y \<rbrakk> \<Longrightarrow> z \<notin> ref_vars (deep_alpha_rename e x y)"    
  apply (induct e)
        apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done
    
lemma rename_ref_vars2: "\<lbrakk> y \<notin> ref_vars e; x \<notin> ref_vars e \<rbrakk> \<Longrightarrow> y \<notin> ref_vars (deep_alpha_rename e x y)"    
  apply (induct e)
        apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done    
  
lemma artp_var_case2: "\<lbrakk>x \<notin> deref_vars x1a x2a; y \<noteq> x1a; y \<notin> deref_vars x1a x2a; add_env env x t (deref_name x1a x2a) = Some tau; add_env env x t x1a = Some tau_x;
        var_val_type x2a tau tau_x; leq_use_env (ereq_use_env x1a tau_x) r_s1; leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau_x) r_ex));
        leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (diff_use_env (ereq_use_env x1a tau_x) (comp_use_env (ereq_use_env x1a tau_x) r_ex)) rx; x \<noteq> x1a\<rbrakk>
       \<Longrightarrow> \<exists>r_ex tau_x.
              add_env env y t x1a = Some tau_x \<and>
              var_val_type x2a tau tau_x \<and>
              leq_use_env (ereq_use_env x1a tau_x) (rename_use_env r_s1 x y) \<and>
              leq_use_env (rename_use_env r_s2 x y) (diff_use_env (rename_use_env r_s1 x y) (comp_use_env (ereq_use_env x1a tau_x) r_ex)) \<and>
              leq_use_env (rename_use_env rx x y) (rename_use_env r_s2 x y) \<and>
              leq_use_env r_ex (rename_use_env r_s1 x y) \<and>
              leq_use_env (diff_use_env (ereq_use_env x1a tau_x) (comp_use_env (ereq_use_env x1a tau_x) r_ex)) (rename_use_env rx x y)"   
  apply (simp add: add_env_def)
  apply (auto)
   apply (case_tac "\<not>  leq_use_env (ereq_use_env x1a tau_x) (rename_use_env r_s1 x y) =  leq_use_env (rename_use_env (ereq_use_env x1a tau_x) x y) (rename_use_env r_s1 x y)")
    apply (cut_tac z="x1a" and x="x" and y="y" and tau="tau_x" in rename_ereq_use_env2)
      apply (simp_all)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
  apply (case_tac "\<not> rename_use_env (ereq_use_env x1a tau_x) x y = ereq_use_env x1a tau_x")
   apply (cut_tac z="x1a" and x="x" and y="y" and tau="tau_x" in rename_ereq_use_env2)
  apply (simp_all)
  apply (cut_tac r_x="ereq_use_env x1a tau_x" and r_s="r_ex" and x="x" and y="y" in rename_comp_use_env)
  apply (simp_all)
  apply (rule_tac x="rename_use_env r_ex x y" in exI)
  apply (auto)
     apply (cut_tac r_x="r_s1" and r_s="comp_use_env (ereq_use_env x1a tau_x) r_ex" and x="x" and y="y" in rename_diff_use_env)
     apply (simp_all)
     apply (rule_tac rename_leq_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
  apply (cut_tac r_x="ereq_use_env x1a tau_x" and r_s="comp_use_env (ereq_use_env x1a tau_x) r_ex" and x="x" and y="y" in rename_diff_use_env)
  apply (simp_all)
  apply (rule_tac rename_leq_use_env)
  apply (simp)
  done
    
lemma alpha_rename_type_preserve: "\<lbrakk> well_typed (add_env env x t) r_s1 e tau r_s2 rx; (*env x = None;*)
  x \<notin> ref_vars e; y \<notin> free_vars e; y \<notin> ref_vars e; y \<notin> lam_vars e \<rbrakk> \<Longrightarrow>
  well_typed (add_env env y t) (rename_use_env r_s1 x y) (deep_alpha_rename e x y) tau (rename_use_env r_s2 x y) (rename_use_env rx x y)"
  apply (induct e arbitrary: env tau t r_s1 r_s2 rx)
        apply (auto)
    (* const + op cases *)
                apply (rule_tac x="x" in rename_leq_use_env)
                apply (simp_all)
               apply (rule_tac x="x" in rename_leq_use_env)
               apply (simp_all)
              apply (rule_tac x="x" in rename_leq_use_env)
              apply (simp_all)
             apply (rule_tac x="x" in rename_leq_use_env)
             apply (simp_all)
    (* var case. *)
            apply (case_tac "deref_name x x2a = x")
             apply (case_tac "deref_name y x2a \<noteq> y")
              apply (simp add: deref_name_def)
              apply (case_tac x2a)
                apply (auto)
             apply (simp add: add_env_def)
            apply (simp add: deref_name_def)
            apply (case_tac x2a)
              apply (auto)
           apply (rule_tac artp_var_case1)
                     apply (auto)
          apply (case_tac "x = deref_name x1a x2a \<or> y = deref_name x1a x2a")
           apply (simp add: deref_name_def)
           apply (case_tac x2a)
             apply (auto)
          apply (simp add: add_env_def)
           apply (rule_tac artp_var_case2)
                    apply (auto)
    (* pair case *)
        apply (cut_tac r_s="rx1" and x="x" and y="y" and r="r" in rename_lift_use_env)
        apply (cut_tac r_s="rx2" and x="x" and y="y" and r="r" in rename_lift_use_env)
        apply (rule_tac x="rename_use_env r_s2a x y" in exI)
        apply (rule_tac x="rename_use_env r_s3 x y" in exI)
        apply (rule_tac x="rename_use_env rx1 x y" in exI)
        apply (auto)
        apply (rule_tac x="rename_use_env rx2 x y" in exI)
        apply (auto)
             apply (rule_tac rename_leq_use_env)
             apply (simp)
            apply (rule_tac rename_leq_use_env)
            apply (simp)(*
           apply (rule_tac safe_lift_rename_use_env)
           apply (simp)
          apply (rule_tac safe_lift_rename_use_env)
          apply (simp)*)
         apply (rule_tac disj_rename_use_env)
         apply (simp)
        apply (cut_tac r_x="r_s3" and r_s="r_ex" and x="x" and y="y" in rename_diff_use_env)
        apply (rule_tac x="rename_use_env r_ex x y" in exI)
        apply (auto)
           apply (rule_tac rename_leq_use_env)
           apply (simp)
          apply (rule_tac rename_leq_use_env)
          apply (simp)
         apply (rule_tac rename_leq_use_env)
         apply (simp)
        apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
         apply (simp add: pair_req_def)
         apply (rule_tac leq_empty_use_env)
        apply (simp add: pair_req_def)
        apply (simp add: rename_comp_use_env)
        apply (simp add: rename_diff_use_env)
        apply (rule_tac rename_leq_use_env)
        apply (simp)
    (* if case *)
       apply (rule_tac x="rename_use_env rx' x y" in exI)
       apply (rule_tac x="rename_use_env r_s2a x y" in exI)
       apply (auto)
       apply (rule_tac x="rename_use_env rx1 x y" in exI)
       apply (auto)
       apply (rule_tac x="rename_use_env rx2 x y" in exI)
       apply (auto)
       apply (cut_tac r_x="rx1" and r_s="rx2" and x="x" and y="y" in rename_comp_use_env)
       apply (auto)
    (* lam case p1. *)
      apply (cut_tac y="y" and x="x" and e="e" in rename_ref_vars2)
        apply (auto)
     apply (rule_tac x="rename_use_env rxa x y" in exI)
     apply (auto)
        apply (rule_tac x="rename_use_env r_end x y" in exI)
        apply (rule_tac x="rename_use_env r_s' x y" in exI)
        apply (cut_tac env="env" and x="x" and t="t" and t'="t1" in double_add_env)
        apply (cut_tac env="env" and x="y" and t="t" and t'="t1" in double_add_env)
        apply (cut_tac r_s="rxa" and x="x" and y="y" and r="r" in rename_add_use_env)
        apply (simp)
       apply (rule_tac aff_rename_use_env)
       apply (simp)
      apply (rule_tac rename_leq_use_env)
      apply (simp)
     apply (rule_tac x="rename_use_env r_ex x y" in exI)
     apply (auto)
        apply (cut_tac r_x="r_s1" and r_s="r_ex" and x="x" and y="y" in rename_diff_use_env)
        apply (simp)
        apply (rule_tac rename_leq_use_env)
        apply (simp)
       apply (rule_tac rename_leq_use_env)
       apply (simp)
      apply (rule_tac rename_leq_use_env)
      apply (simp)
     apply (cut_tac r_x="rxa" and r_s="r_ex" and x="x" and y="y" in rename_diff_use_env)
     apply (simp)
     apply (rule_tac rename_leq_use_env)
     apply (simp)
    (* lam case p2. *)
    apply (cut_tac z="x1a" and x="x" and y="y" and e="e" in rename_ref_vars1)
      apply (auto)
   apply (rule_tac x="rename_use_env rxa x y" in exI)
   apply (auto)
      apply (rule_tac x="rename_use_env r_end x y" in exI)
      apply (rule_tac x="rename_use_env r_s' x y" in exI)
      apply (cut_tac env="env" and x="x1a" and y="x" and t="t" and t'="t1" in almost_comm_add_env)
       apply (simp_all)
      apply (cut_tac env="env" and x="x1a" and y="y" and t="t" and t'="t1" in almost_comm_add_env)
       apply (simp_all)
      apply (cut_tac r_s="rxa" and x="x" and y="y" and z="x1a" and r="r" in rename_add_use_env2)
        apply (simp_all)
     apply (rule_tac aff_rename_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (rule_tac x="rename_use_env r_ex x y" in exI)
   apply (auto)
      apply (cut_tac r_x="r_s1" and r_s="r_ex" and x="x" and y="y" in rename_diff_use_env)
      apply (simp)
      apply (rule_tac rename_leq_use_env)
      apply (simp)
     apply (rule_tac rename_leq_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (cut_tac r_x="rxa" and r_s="r_ex" and x="x" and y="y" in rename_diff_use_env)
   apply (simp)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
    (* app case *)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="rename_use_env r_s2a x y" in exI)
  apply (rule_tac x="rename_use_env rx1 x y" in exI)
  apply (auto)
  apply (rule_tac x="rename_use_env rx2 x y" in exI)
  apply (rule_tac x="rename_use_env r_s3 x y" in exI)
  apply (auto)
  apply (cut_tac r_s="rx2" and x="x" and y="y" and r="r" in rename_lift_use_env)
  apply (simp)
  apply (cut_tac r_x="rx1" and r_s="lift_use_env rx2 r" and x="x" and y="y" in rename_comp_use_env)
  apply (cut_tac r_x="comp_use_env rx1 (lift_use_env rx2 r)" and r_s="r_ex" and x="x" and y="y" in rename_comp_use_env)
  apply (rule_tac x="rename_use_env r_ex x y" in exI)
  apply (auto)
        apply (cut_tac r_x="r_s3" and r_s="comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex" and x="x" and y="y" in rename_diff_use_env)
        apply (simp)
        apply (rule_tac rename_leq_use_env)
        apply (simp)(*
       apply (rule_tac safe_lift_rename_use_env)
       apply (simp)*)
      apply (rule_tac rename_leq_use_env)
      apply (simp)
     apply (rule_tac disj_rename_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
  apply (simp add: app_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (cut_tac r_x="rx1" and r_s="rx2" and x="x" and y="y" in rename_comp_use_env)
  apply (simp)
  apply (cut_tac r_x="comp_use_env rx1 rx2" and r_s="comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex" and x="x" and y="y" in rename_diff_use_env)
  apply (simp)
  apply (rule_tac rename_leq_use_env)
  apply (simp)
  done  
    
lemma lam_var_remove_ref_vars: "\<lbrakk> z \<notin> ref_vars e; z \<noteq> y \<rbrakk> \<Longrightarrow> z \<notin> ref_vars (lam_var_remove e x y)"    
  apply (induct e)  
        apply (auto)
  apply (cut_tac z="z" and e="e" and x="x" and y="y" in rename_ref_vars1)
    apply (auto)
  done
    
lemma lam_var_remove_ref_vars2: "\<lbrakk> y \<notin> ref_vars e; x \<notin> ref_vars e \<rbrakk> \<Longrightarrow> y \<notin> ref_vars (lam_var_remove e x y)"    
  apply (induct e)
        apply (auto)
  apply (cut_tac y="y" and e="e" and x="x" in rename_ref_vars2)
    apply (auto)
  done
  
lemma lam_var_remove_type_preserve: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; y \<notin> free_vars e; y \<notin> ref_vars e; y \<notin> lam_vars e \<rbrakk> \<Longrightarrow>
  well_typed env r_s1 (lam_var_remove e x y) tau r_s2 rx"
  apply (induct e arbitrary: env tau r_s1 r_s2 rx)
        apply (auto)
    (* pair case *)
        apply (rule_tac x="r_s2a" in exI)
        apply (rule_tac x="r_s3" in exI)
        apply (rule_tac x="rx1" in exI)
        apply (auto)
        apply (rule_tac x="rx2" in exI)
        apply (auto)
    (* if case *)
       apply (rule_tac x="rx'" in exI)
       apply (rule_tac x="r_s2a" in exI)
       apply (auto)
       apply (rule_tac x="rx1" in exI)
       apply (auto)
       apply (rule_tac x="rx2" in exI)
       apply (auto)
    (* lam case p1. *)
      apply (cut_tac e="e" and x="x" and y="y" in rename_ref_vars2)
        apply (auto)
     apply (rule_tac x="rxa" in exI)
     apply (auto)
     apply (rule_tac x="rename_use_env r_end x y" in exI)
     apply (rule_tac x="rename_use_env r_s' x y" in exI)
     apply (rule_tac ?r_s1.0="rem_use_env (add_use_env rxa y r) x" in well_typed_incr_start_perm)
      apply (cut_tac r_s="rxa" and x="y" and y="x" and r="r" in almost_comm_rem_add_use_env)
       apply (simp_all)
      apply (case_tac "\<not> add_use_env (rem_use_env rxa x) y r = rename_use_env (add_use_env rxa x r) x y")
       apply (case_tac "\<not> (\<forall> x'. add_use_env (rem_use_env rxa x) y r x' = rename_use_env (add_use_env rxa x r) x y x')")
        apply (auto)
       apply (simp add: rename_use_env_def)
       apply (simp add: add_use_env_def)
       apply (case_tac "y = x'")
        apply (auto)
       apply (simp add: rem_use_env_def)
       apply (case_tac "x = x'")
        apply (auto)
      apply (rule_tac alpha_rename_type_preserve)
          apply (simp_all)
     apply (rule_tac self_rem_leq_use_env)
    (* lam case p2. *)
    apply (cut_tac e="e" and x="x" and y="y" and z="x1a" in lam_var_remove_ref_vars)
      apply (auto)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="r_end" in exI)
   apply (rule_tac x="r_s'" in exI)
   apply (auto)
    (* app case *)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="r_s2a" in exI)
  apply (rule_tac x="rx1" in exI)
  apply (auto)
  apply (rule_tac x="rx2" in exI)
  apply (rule_tac x="r_s3" in exI)
  apply (auto)
  done    

lemma alpha_rename_free_var_id: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> x \<notin> free_vars (deep_alpha_rename e x y)"
  apply (induct e)
       apply (auto)
  done       

lemma alpha_rename_free_var_none: "\<lbrakk> a \<notin> free_vars e; a \<noteq> y \<rbrakk> \<Longrightarrow> a \<notin> free_vars (deep_alpha_rename e x y)"     
  apply (induction e)
       apply (auto)
  apply (cut_tac e="e" and x="a" and y="y" in alpha_rename_free_var_id)
   apply (auto)
  done
    
lemma alpha_rename_lam_var_none: "\<lbrakk> a \<notin> lam_vars e; a \<noteq> y \<rbrakk> \<Longrightarrow> a \<notin> lam_vars (deep_alpha_rename e x y)"  
  apply (induct e)
       apply (auto)
  done
  
lemma lam_var_remove_free_var_none: "\<lbrakk> x \<notin> free_vars e \<rbrakk> \<Longrightarrow> x \<notin> free_vars (lam_var_remove e a b)"    
  apply (induct e)
       apply (auto)
   apply (case_tac "x \<noteq> b")
    apply (cut_tac e="e" and a="x" and x="a" and y="b" in alpha_rename_free_var_none)
      apply (auto)
  apply (case_tac "x \<noteq> b")
   apply (cut_tac e="e" and x="x" and y="b" in alpha_rename_free_var_id)
    apply (auto)
  done


lemma lam_var_remove_ref_var_none: "\<lbrakk> x \<notin> ref_vars e; well_typed env r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow> x \<notin> ref_vars (lam_var_remove e a b)"     
  apply (induct e arbitrary: env r_s1 tau r_s2 rx x)
        apply (auto)
  apply (case_tac "x \<noteq> b")
   apply (cut_tac z="x" and x="a" and y="b" and e="e" in rename_ref_vars1)
     apply (auto)
  apply (cut_tac x="a" and y="b" and e="e" in rename_ref_vars2)
    apply (auto)
  done
    
lemma lam_var_remove_lam_var_none: "\<lbrakk> x \<notin> lam_vars e; x \<noteq> b \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_remove e a b)"  
  apply (induct e)  
       apply (auto)
  apply (cut_tac a="x" and e="e" and x="a" and y="b" in alpha_rename_lam_var_none)
    apply (auto)
  done
 
  
    (* basically, we want to make sure that when we replace a var, we dont end up with the post_vars of vl overlapping with
      any of the ref vars of e. in other words, that we arent changing any of the ref vars. now the thing is, when we do lam var remove,
      we dont expect any of the ref vars to change actually  *)
lemma lam_var_list_remove_type_preserve: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; unique_post_vars vl;(* pre_vars vl \<subseteq> lam_vars e;*)
  post_vars vl \<inter> (free_vars e \<union> ref_vars e \<union> lam_vars e) = {} \<rbrakk> \<Longrightarrow> well_typed env r_s1 (lam_var_list_remove e vl) tau r_s2 rx"
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and tau="tau" and ?r_s2.0="r_s2" and rx="rx" and x="a" and y="b" in lam_var_remove_type_preserve)
      apply (auto)
  apply (case_tac "\<not> post_vars vl \<inter> (free_vars (lam_var_remove e a b) \<union> ref_vars (lam_var_remove e a b) \<union> lam_vars (lam_var_remove e a b)) = {}")
   apply (auto)
    apply (cut_tac e="e" and x="x" and a="a" and b="b" in lam_var_remove_free_var_none)
     apply (auto)
   apply (cut_tac e="e" and x="x" and a="a" and b="b" in lam_var_remove_ref_var_none)
     apply (auto)
  apply (cut_tac e="e" and x="x" and a="a" and b="b" in lam_var_remove_lam_var_none)
    apply (auto)
    (*
  apply (case_tac "\<not> pre_vars vl \<inter> ref_vars (lam_var_remove e a b) = {}")
   apply (auto)
  apply (cut_tac e="e" and z="x" and x="a" and y="b" in lam_var_remove_ref_vars)
    apply (auto)
  apply (cut_tac e="e" and x="a" and y="b" in lam_var_remove_ref_vars2)
    apply (auto)*)
  done     
   

definition disj_vars where
  "disj_vars s1 s2 = ((s1 \<inter> s2) = {})"
    
lemma show_disj_vars: "\<lbrakk> \<forall> x. x \<in> s1 \<longrightarrow> x \<notin> s2 \<rbrakk> \<Longrightarrow> disj_vars s1 s2"  
  apply (simp add: disj_vars_def)
  apply (auto)
  done
    
lemma union_disj_vars: "\<lbrakk> disj_vars s1 s2; \<forall> x. x \<in> s1 \<longrightarrow> x \<notin> s3 \<rbrakk> \<Longrightarrow> disj_vars s1 (s2 \<union> s3)"
  apply (simp add: disj_vars_def)
  apply (auto)
  done
  
lemma use_disj_vars: "\<lbrakk> disj_vars s1 s2; x \<in> s1 \<rbrakk> \<Longrightarrow> x \<notin> s2"    
  apply (simp add: disj_vars_def)
  apply (auto)
  done    
 
lemma alpha_rename_free_var_some: "\<lbrakk> x \<in> free_vars e; x \<noteq> a; x \<noteq> b \<rbrakk> \<Longrightarrow> x \<in> free_vars (deep_alpha_rename e a b)"    
  apply (induct e)
       apply (auto)
  done
    
lemma lam_var_remove_free_var_some: "\<lbrakk> x \<in> free_vars e; x \<noteq> b \<rbrakk> \<Longrightarrow> x \<in> free_vars (lam_var_remove e a b)"    
  apply (induct e)
       apply (auto)
  apply (rule_tac alpha_rename_free_var_some)
    apply (auto)
  done
(*
lemma lam_var_list_remove_lam_var_none: "\<lbrakk> x \<notin> lam_vars e; x \<noteq> b \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_remove e a b)"     *)
    
lemma lam_var_list_remove_free_var_some: "\<lbrakk> x \<in> free_vars e; x \<notin> post_vars vl \<rbrakk> \<Longrightarrow> x \<in> free_vars (lam_var_list_remove e vl)"    
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_free_var_some)
    apply (auto)
  done        
 
    
lemma lam_var_list_remove_lam_var_none1: "\<lbrakk> x \<notin> lam_vars e; x \<notin> post_vars vl \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_list_remove e vl)"        
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac e="e" and x="x" and a="a" and b="b" in lam_var_remove_lam_var_none)
    apply (auto)
  done
    

lemma alpha_rename_lam_var_none2: "\<lbrakk> x \<noteq> b \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (deep_alpha_rename e x b)"    
  apply (induct e)
       apply (auto)
  done
    
lemma lam_var_remove_lam_var_none2: "\<lbrakk> x \<noteq> b \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_remove e x b)"    
  apply (induct e)
       apply (auto)
  apply (cut_tac e="e" and x="x" and b="b" in alpha_rename_lam_var_none2)
   apply (auto)
  done
    
lemma lam_var_list_remove_lam_var_none2: "\<lbrakk> x \<in> pre_vars vl; x \<notin> post_vars vl \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_list_remove e vl)"    
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac e="e" and x="x" and b="b" in lam_var_remove_lam_var_none2)
   apply (auto)
  apply (cut_tac e="lam_var_remove e x b" and x="x" and vl="vl" in lam_var_list_remove_lam_var_none1)
    apply (auto)
  done
    
lemma lam_var_list_remove_free_var_some_rev: "\<lbrakk> x \<in> free_vars (lam_var_list_remove e vl) \<rbrakk> \<Longrightarrow> x \<in> free_vars e"
  apply (induction vl arbitrary: e)
   apply (auto)
  apply (case_tac "x \<notin> free_vars e")
   apply (auto)
  apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_free_var_none)
   apply (auto)
  done
 
lemma lam_var_list_remove_free_var_none: "\<lbrakk> x \<notin> free_vars e \<rbrakk> \<Longrightarrow> x \<notin> free_vars (lam_var_list_remove e vl)"    
  apply (case_tac "x \<in> free_vars (lam_var_list_remove e vl)")
   apply (auto)
  apply (cut_tac x="x" and e="e" and vl="vl" in lam_var_list_remove_free_var_some_rev)
   apply (auto)
  done    
    
    
  
lemma lam_var_list_remove_ref_var: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; x \<notin> ref_vars e; unique_post_vars vl;
  disj_vars (post_vars vl) (free_vars e \<union> ref_vars e \<union> lam_vars e) \<rbrakk> \<Longrightarrow> x \<notin> ref_vars (lam_var_list_remove e vl)"    
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac e="e" and a="a" and b="b" and x="x" in lam_var_remove_ref_var_none)
    apply (auto)
  apply (cut_tac env="env" and e="e" and x="a" and y="b" in lam_var_remove_type_preserve)
      apply (auto)
     apply (simp add: disj_vars_def)
    apply (simp add: disj_vars_def)
   apply (simp add: disj_vars_def)
  apply (case_tac "\<not> disj_vars (post_vars vl) (free_vars (lam_var_remove e a b) \<union> ref_vars (lam_var_remove e a b) \<union> lam_vars (lam_var_remove e a b))")
   apply (auto)
  apply (cut_tac ?s1.0="post_vars vl" and ?s2.0="free_vars (lam_var_remove e a b) \<union> ref_vars (lam_var_remove e a b)" and ?s3.0="lam_vars (lam_var_remove e a b)" in union_disj_vars)
    apply (rule_tac union_disj_vars)
     apply (rule_tac show_disj_vars)
     apply (auto)
    apply (cut_tac x="xa" and ?s1.0="insert b (post_vars vl)" and
        ?s2.0="free_vars e \<union> ref_vars e \<union> lam_vars e" in use_disj_vars)
      apply (auto)
    apply (cut_tac e="e" and x="xa" and a="a" and b="b" in lam_var_remove_free_var_none)
     apply (auto)
   apply (cut_tac x="xa" and ?s1.0="insert b (post_vars vl)" and
        ?s2.0="free_vars e \<union> ref_vars e \<union> lam_vars e" in use_disj_vars)
     apply (auto)
   apply (cut_tac e="e" and x="xa" and a="a" and b="b" in lam_var_remove_ref_var_none)
     apply (auto)
  apply (cut_tac x="xa" and ?s1.0="insert b (post_vars vl)" and
        ?s2.0="free_vars e \<union> ref_vars e \<union> lam_vars e" in use_disj_vars)
    apply (auto)
  apply (cut_tac e="e" and x="xa" and a="a" and b="b" in lam_var_remove_lam_var_none)
    apply (auto)
  done    
    
end