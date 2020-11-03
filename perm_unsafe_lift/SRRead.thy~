theory SRRead
  imports SubstDropEnv DerefVars
begin
  
fun ack_exp where
  "ack_exp (ConstExp c) x' = ConstExp c"
| "ack_exp (OpExp xop) x' = OpExp xop"
| "ack_exp (VarExp x v) x' = (case v of
    NoRef \<Rightarrow> VarExp x v
    | SelfRef \<Rightarrow> VarExp x' (OtherRef x)
    | OtherRef y \<Rightarrow> VarExp x' (OtherRef y))"
| "ack_exp (PairExp e1 e2) x' = (PairExp (ack_exp e1 x') (ack_exp e2 x'))"
| "ack_exp (IfExp e1 e2 e3) x' = (IfExp (ack_exp e1 x') (ack_exp e2 x') (ack_exp e3 x'))"
| "ack_exp (LamExp x e) x' = (LamExp x (ack_exp e x'))"  
| "ack_exp (AppExp e1 e2) x' = (AppExp (ack_exp e1 x') (ack_exp e2 x'))"  
  
definition array_ty where
  "array_ty tau = (\<exists> t. tau = ArrayTy t)"  
  
definition not_free_var where  
  "not_free_var x e = (x \<notin> free_vars e)"
  
lemma rhs_diff_rem_leq_use_env: "\<lbrakk> r_x x = NoPerm; leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (rem_use_env r_ex x)) (diff_use_env r_s r_ex)"  
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: rem_use_env_def)
  done
  
lemma rhs_diff_rem_leq_use_env2: "\<lbrakk> r_ex x \<noteq> OwnPerm; leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (rem_use_env r_ex x)) (diff_use_env r_s r_ex)"  
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (case_tac "\<not> neg_perm (r_ex x) = NoEP")
   apply (case_tac "r_ex x")
     apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done    
    
lemma dist_disj_add_use_env: "\<lbrakk> disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> disj_use_env (add_use_env r_x x UsePerm) (add_use_env r_s x UsePerm)"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: add_use_env_def)
  done
  
    
lemma wtae_end_leq_use_env1: "\<lbrakk> leq_use_env r_x (diff_use_env r_s (comp_use_env r_exa r_exb)); r_exa x \<noteq> OwnPerm \<rbrakk> \<Longrightarrow>
  leq_use_env (add_use_env r_x x UsePerm) (diff_use_env (add_use_env r_s x UsePerm) (comp_use_env r_exa (rem_use_env r_exb x)))"    
  apply (rule_tac r_sb="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)" in trans_leq_use_env)
   apply (simp add: dist_rem_comp_use_env)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac rhs_diff_rem_leq_use_env2)
    apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac t="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)"
      and s="add_use_env (diff_use_env r_s (comp_use_env r_exa r_exb)) x UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done

lemma wtae_end_leq_use_env2: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (add_use_env r_x x UsePerm) (diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_ex x))"  
  apply (rule_tac t="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_ex x)"
      and s="add_use_env (diff_use_env r_s r_ex) x UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)  
  done
    
lemma wtae_req_leq_use_env1: "\<lbrakk> leq_use_env (diff_use_env r_x (comp_use_env r_exa r_exb)) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (add_use_env r_x x UsePerm) (comp_use_env r_exa (rem_use_env r_exb x))) (add_use_env r_s x UsePerm)"
  apply (rule_tac r_sb="diff_use_env (add_use_env r_x x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)" in trans_leq_use_env)
   apply (rule_tac t="diff_use_env (add_use_env r_x x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)"
      and s="add_use_env (diff_use_env r_x (comp_use_env r_exa r_exb)) x UsePerm" in subst)
    apply (rule_tac diff_add_rem_use_env)
   apply (rule_tac dist_add_leq_use_env)
   apply (simp)
  apply (rule_tac dist_diff_leq_use_env_gen)
   apply (rule_tac id_leq_use_env)
  apply (simp add: dist_rem_comp_use_env)
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac comp_leq_use_env1)
   apply (rule_tac self_rem_leq_use_env)
  apply (rule_tac self_comp_leq_use_env2)
  done

lemma wtae_req_leq_use_env2: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (add_use_env r_x x UsePerm) (rem_use_env r_ex x)) (add_use_env r_s x UsePerm)"
  apply (rule_tac t="diff_use_env (add_use_env r_x x UsePerm) (rem_use_env r_ex x)"
      and s="add_use_env (diff_use_env r_x r_ex) x UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done
    
    
lemma ack_ref_vars: "\<lbrakk> x \<notin> ref_vars e; x \<noteq> y \<rbrakk> \<Longrightarrow> x \<notin> ref_vars (ack_exp e y)"    
  apply (induct e)
        apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done
    
lemma empty_ack_ref_vars: "\<lbrakk> ref_vars e = {} \<rbrakk> \<Longrightarrow> x \<notin> ref_vars (ack_exp e y)"    
  apply (induct e)
        apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done    
    
fun pre_ref_vars where
  "pre_ref_vars (ConstExp c) = {}"
| "pre_ref_vars (OpExp xop) = {}"
| "pre_ref_vars (VarExp x v) = (if v = NoRef then {} else {x})"
| "pre_ref_vars (PairExp e1 e2) = (pre_ref_vars e1 \<union> pre_ref_vars e2)"    
| "pre_ref_vars (IfExp e1 e2 e3) = (pre_ref_vars e1 \<union> pre_ref_vars e2 \<union> pre_ref_vars e3)"  
| "pre_ref_vars (LamExp x e) = (pre_ref_vars e)"  
| "pre_ref_vars (AppExp e1 e2) = (pre_ref_vars e1 \<union> pre_ref_vars e2)"  
  
lemma empty_ack_pre_ref_vars: "\<lbrakk> pre_ref_vars e = {} \<rbrakk> \<Longrightarrow> x \<notin> ref_vars (ack_exp e y)"    
  apply (induct e)
        apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done    
  
lemma sub_pre_ref_vars: "\<lbrakk> x \<notin> ref_vars e \<rbrakk> \<Longrightarrow> x \<notin> pre_ref_vars e"    
  apply (induct e)
        apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done
  
    (* one way we could deal with the issue we were having is to restor the unlim tau requirement,
        and strongly prevent us from inducting in the lam case *)  
    
lemma well_typed_ack_no_ref: "\<lbrakk> pre_ref_vars e = {}; well_typed env r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow>
   well_typed env r_s1 (ack_exp e x) tau r_s2 rx"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)  
        apply (auto)
    (* var case *)
       apply (case_tac x2a)
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
    (* lam case *)
    apply (cut_tac e="e" and x="x1a" and y="x" in empty_ack_pre_ref_vars)
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
    
definition not_pre_ref_var where
  "not_pre_ref_var x e = (x \<notin> pre_ref_vars e)"

lemma empty_leq_use_env: "\<lbrakk> leq_use_env r_x empty_use_env \<rbrakk> \<Longrightarrow> r_x = empty_use_env"  
  apply (case_tac "\<forall> x. r_x x = empty_use_env x")
   apply (auto)
  apply (simp add: leq_use_env_def)
  apply (simp add: empty_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done
  
lemma well_typed_no_pre_ref_vars_ih: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; r_s1 x = NoPerm \<rbrakk> \<Longrightarrow> not_pre_ref_var x e"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* const + op cases *)
        apply (simp add: not_pre_ref_var_def)
       apply (simp add: not_pre_ref_var_def)
    (* var case *)
      apply (simp add: not_pre_ref_var_def)
      apply (auto)
      apply (simp add: leq_use_env_def)
      apply (simp add: ereq_use_env_def)
      apply (simp add: one_use_env_def)
      apply (erule_tac x="x" in allE)
      apply (simp add: end_req_perm_def)
      apply (case_tac "x2a = NoRef")
       apply (simp add: deref_name_def)
      apply (cut_tac v="x2a" and tau="tau" and tau_x="tau_x" in var_value_unlim)
        apply (auto)
    (* pair case *)
     apply (simp add: not_pre_ref_var_def)
     apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="x" in leq_use_none)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
    (* if case *)
    apply (simp add: not_pre_ref_var_def)
    apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="x" in leq_use_none)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* lam case *)
   apply (simp add: not_pre_ref_var_def)
   apply (case_tac "x = x1a")
    apply (auto)
    apply (cut_tac x="x" and e="e" in sub_pre_ref_vars)
     apply (auto)
   apply (cut_tac r_x="rxa" and r_s="r_s1" and x="x" in leq_use_none)
     apply (auto)
   apply (case_tac "\<not> add_use_env rxa x1a r x = NoPerm")
    apply (simp add: add_use_env_def)
   apply (auto)
   apply (iprover)
    (* app case *)
  apply (simp add: not_pre_ref_var_def)
  apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="x" in leq_use_none)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  done
 
lemma well_typed_no_pre_ref_vars: "\<lbrakk> well_typed env empty_use_env e tau r_s rx \<rbrakk> \<Longrightarrow> pre_ref_vars e = {}"    
  apply (auto)
  apply (cut_tac x="x" and e="e" and ?r_s1.0="empty_use_env" and env="env" in well_typed_no_pre_ref_vars_ih)
    apply (auto)
   apply (simp add: empty_use_env_def)
  apply (simp add: not_pre_ref_var_def)
  done
  
    
    (* replacement version *)
 
fun mem_ty where
  "mem_ty (ArrayTy tau) = unlim tau"
| "mem_ty (ChanTy tau c_end) = True"
| "mem_ty tau = False"
    
definition mem_val_env where
  "mem_val_env env = (\<forall> x. case env x of
    None \<Rightarrow> True
    | Some tau \<Rightarrow> mem_ty tau
  )"        

definition semi_weak_use_env where
  "semi_weak_use_env r_s r_set = (\<forall> x. x \<in> r_set \<longrightarrow> r_s x \<noteq> OwnPerm)"
    
lemma sw_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; semi_weak_use_env r_s r_set \<rbrakk> \<Longrightarrow> semi_weak_use_env r_x r_set"  
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
    
definition set_use_none where
  "set_use_none r_s r_set = (\<forall> x. x \<in> r_set \<longrightarrow> r_s x = NoPerm)"
    
definition pwrite_use_env where
  "pwrite_use_env r_s r_set x = (if set_use_none r_s r_set then r_s else add_use_env r_s x UsePerm)"
    
lemma leq_set_use_none: "\<lbrakk> leq_use_env r_x r_s; set_use_none r_s s \<rbrakk> \<Longrightarrow> set_use_none r_x s"  
  apply (simp add: set_use_none_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
  
lemma dist_pwrite_leq_use_env: "\<lbrakk> semi_weak_use_env r_s r_set; x \<in> r_set; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (pwrite_use_env r_x r_set x) (pwrite_use_env r_s r_set x)"
  apply (case_tac "set_use_none r_s r_set")
   apply (cut_tac r_x="r_x" and r_s="r_s" and s="r_set" in leq_set_use_none)
     apply (auto)
   apply (simp add: pwrite_use_env_def)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (rule_tac rhs_add_leq_use_env)
    apply (simp)
   apply (cut_tac r_x="r_x" and r_s="r_s" and x="x" in leq_use_no_own)
     apply (simp add: semi_weak_use_env_def)
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done
 
lemma rem_pwrite_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (rem_use_env r_x x) (pwrite_use_env r_s r_set x)"       
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (rule_tac rem_leq_use_env)
   apply (simp)
  apply (rule_tac rhs_add_leq_use_env)
   apply (rule_tac rem_leq_use_env)
   apply (simp)
  apply (simp add: rem_use_env_def)
  done
  
lemma pwrite_leq_use_env: "\<lbrakk> semi_weak_use_env r_s r_set; x \<in> r_set; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (pwrite_use_env r_s r_set x)"    
  apply (simp add: pwrite_use_env_def)
  apply (auto)
  apply (rule_tac rhs_add_leq_use_env)
   apply (simp)
  apply (cut_tac r_x="r_x" and r_s="r_s" and x="x" in leq_use_no_own)
    apply (simp add: semi_weak_use_env_def)
   apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
 
lemma add_pwrite_leq_use_env: "\<lbrakk> semi_weak_use_env r_x r_set; x \<in> r_set; leq_use_env (add_use_env r_x x UsePerm) r_s \<rbrakk> \<Longrightarrow> leq_use_env (pwrite_use_env r_x r_set x) r_s"      
  apply (simp add: pwrite_use_env_def)
  apply (auto)
  apply (rule_tac r_sb="add_use_env r_x x UsePerm" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac rhs_add_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (simp add: semi_weak_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma rem_ereq_use_env: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> rem_use_env (ereq_use_env y tau) x = ereq_use_env y tau"    
  apply (case_tac "\<forall> x'. rem_use_env (ereq_use_env y tau) x x' = ereq_use_env y tau x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  done
    
lemma lift_pwrite_leq_use_env: "\<lbrakk> semi_weak_use_env r_s r_set; x \<in> r_set; leq_use_env (lift_use_env r_x r) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (lift_use_env (pwrite_use_env r_x r_set x) r) (add_use_env r_s x UsePerm)"    
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (rule_tac rhs_add_leq_use_env)
    apply (simp)
   apply (cut_tac r_x="lift_use_env r_x r" and r_s="r_s" in sw_leq_use_env)
     apply (auto)
   apply (simp add: semi_weak_use_env_def)
   apply (case_tac "lift_use_env r_x r x")
     apply (auto)
  apply (simp add: set_use_none_def)
  apply (auto)
  apply (case_tac "r = OwnPerm")
   apply (case_tac "r_s xa \<noteq> OwnPerm")
    apply (simp add: leq_use_env_def)
    apply (erule_tac x="xa" in allE)
    apply (auto)
    apply (case_tac "r_s xa")
      apply (auto)
   apply (simp add: semi_weak_use_env_def)
  apply (case_tac "lift_use_env r_x r \<noteq> r_x")
   apply (case_tac r)
     apply (auto)
  apply (case_tac "lift_use_env (add_use_env r_x x UsePerm) r \<noteq> add_use_env r_x x UsePerm")
   apply (case_tac r)
     apply (auto)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done
    (*
lemma safe_lift_pwrite_use_env: "\<lbrakk> safe_use_lift r_x r; safe_use_lift r_s r \<rbrakk> \<Longrightarrow> safe_use_lift (pwrite_use_env r_s r_set x) r"    
  apply (case_tac r)
    apply (auto)
  apply (simp add: pwrite_use_env_def)
  apply (case_tac "set_use_none r_s r_set")
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (case_tac "x = xa")
   apply (auto)
  done*)
    
lemma disj_add_use_envx: "\<lbrakk> disj_use_env r_x r_s; semi_weak_use_env r_s r_set; x \<in> r_set \<rbrakk> \<Longrightarrow> disj_use_env (add_use_env r_x x UsePerm) r_s"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  apply (simp add: semi_weak_use_env_def)
  done
  
lemma disj_pwrite_use_env: "\<lbrakk> semi_weak_use_env r_x r_set; semi_weak_use_env r_s r_set; x \<in> r_set; disj_use_env r_x r_s \<rbrakk> \<Longrightarrow>
  disj_use_env (pwrite_use_env r_x r_set x) (pwrite_use_env r_s r_set x)"   
  apply (simp add: pwrite_use_env_def)
  apply (auto)
    apply (rule_tac comm_disj_use_env)
    apply (rule_tac disj_add_use_envx)
    apply (rule_tac comm_disj_use_env)
     apply (auto)
   apply (rule_tac disj_add_use_envx)
    apply (auto)
  apply (rule_tac disj_add_use_envx)
   apply (rule_tac comm_disj_use_env)
   apply (rule_tac disj_add_use_envx)
    apply (rule_tac comm_disj_use_env)
    apply (auto)
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: add_use_env_def)
  done
    
  
lemma disj_lift_pwrite_use_env: "\<lbrakk> disj_use_env (lift_use_env r_x r) (lift_use_env r_s r);
  leq_use_env (lift_use_env r_x r) r_c; leq_use_env (lift_use_env r_s r) r_c; semi_weak_use_env r_c r_set; x \<in> r_set; r \<noteq> NoPerm (*safe_use_lift r_ex r*) \<rbrakk> \<Longrightarrow>
  disj_use_env (lift_use_env (pwrite_use_env r_x r_set x) r) (lift_use_env (pwrite_use_env r_s r_set x) r)"    
  apply (case_tac "\<not> is_own r")
   apply (simp add: is_own_def)
   apply (case_tac r)
     apply (auto)
   apply (rule_tac disj_pwrite_use_env)
     apply (auto)
    apply (rule_tac r_s="r_c" in sw_leq_use_env)
     apply (auto)
   apply (rule_tac r_s="r_c" in sw_leq_use_env)
    apply (auto)
  apply (case_tac "\<not> set_use_none r_x r_set")
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (simp add: leq_use_env_def)
   apply (erule_tac x="xa" in allE)
   apply (simp add: is_own_def)
   apply (simp add: semi_weak_use_env_def)
   apply (case_tac "r_c xa")
     apply (auto)
  apply (case_tac "\<not> set_use_none r_s r_set")
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (simp add: leq_use_env_def)
   apply (erule_tac x="xa" in allE)
   apply (erule_tac x="xa" in allE)
   apply (simp add: is_own_def)
   apply (simp add: semi_weak_use_env_def)
   apply (case_tac "r_c xa")
     apply (auto)
  apply (simp add: pwrite_use_env_def)
  done

lemma lift_pwrite_use_env: "\<lbrakk> semi_weak_use_env (lift_use_env r_s r) r_set \<rbrakk> \<Longrightarrow>
  pwrite_use_env (lift_use_env r_s r) r_set x = lift_use_env (pwrite_use_env r_s r_set x) r"
  apply (case_tac "is_own r")
   apply (case_tac "\<not> set_use_none r_s r_set")
    apply (simp add: set_use_none_def)
    apply (auto)
    apply (simp add: semi_weak_use_env_def)
    apply (simp add: is_own_def)
    apply (erule_tac x="xa" in allE)
    apply (auto)
   apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (simp add: is_own_def)
  apply (simp add: is_own_def)
  apply (case_tac r)
    apply (auto)
  done
    
lemma pwc_add_use_env1: "\<lbrakk> semi_weak_use_env r_x r_set; x \<in> r_set \<rbrakk> \<Longrightarrow> comp_use_env r_x (add_use_env r_s x UsePerm) = add_use_env (comp_use_env r_x r_s) x UsePerm"    
  apply (case_tac "\<forall> y. comp_use_env r_x (add_use_env r_s x UsePerm) y = add_use_env (comp_use_env r_x r_s) x UsePerm y")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (case_tac "x = y")
   apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done

lemma pwc_add_use_env2: "\<lbrakk> semi_weak_use_env r_s r_set; x \<in> r_set \<rbrakk> \<Longrightarrow> comp_use_env (add_use_env r_x x UsePerm) r_s = add_use_env (comp_use_env r_x r_s) x UsePerm"    
  apply (case_tac "\<forall> y. comp_use_env (add_use_env r_x x UsePerm) r_s y = add_use_env (comp_use_env r_x r_s) x UsePerm y")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (case_tac "x = y")
   apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
  
lemma pwrite_comp_use_env: "\<lbrakk> semi_weak_use_env r_x r_set; semi_weak_use_env r_s r_set; x \<in> r_set \<rbrakk> \<Longrightarrow>
  comp_use_env (pwrite_use_env r_x r_set x) (pwrite_use_env r_s r_set x) = pwrite_use_env (comp_use_env r_x r_s) r_set x"
  apply (case_tac "set_use_none r_x r_set")
   apply (case_tac "set_use_none r_s r_set")
    apply (simp add: pwrite_use_env_def)
    apply (auto)
    apply (simp add: set_use_none_def)
    apply (simp add: comp_use_env_def)
    apply (auto)
   apply (simp add: pwrite_use_env_def)
   apply (auto)
    apply (simp add: set_use_none_def)
    apply (simp add: comp_use_env_def)
    apply (auto)
    apply (erule_tac x="xa" in allE)
    apply (erule_tac x="xa" in allE)
    apply (auto)
    apply (case_tac "r_s xa")
      apply (auto)
   apply (rule_tac pwc_add_use_env1)
   apply (auto)
  apply (case_tac "set_use_none r_s r_set")
   apply (simp add: pwrite_use_env_def)
   apply (auto)
    apply (simp add: set_use_none_def)
    apply (simp add: comp_use_env_def)
    apply (auto)
    apply (erule_tac x="xa" in allE)
    apply (erule_tac x="xa" in allE)
    apply (auto)
    apply (case_tac "r_x xa")
      apply (auto)
   apply (rule_tac pwc_add_use_env2)
   apply (auto)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (simp add: set_use_none_def)
   apply (simp add: comp_use_env_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto) 
   apply (case_tac "r_x xa")
     apply (auto)
   apply (case_tac "r_s xa")
     apply (auto)
  apply (rule_tac dist_add_comp_use_env)
  done
    
lemma sw_add_use_env: "\<lbrakk> semi_weak_use_env r_s r_set; x \<notin> r_set \<rbrakk> \<Longrightarrow> semi_weak_use_env (add_use_env r_s x r) r_set"    
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: add_use_env_def)
  done
  
lemma diff_pwrite_rem_use_env: "\<lbrakk> semi_weak_use_env r_x r_set; x \<in> r_set \<rbrakk> \<Longrightarrow>
  diff_use_env (pwrite_use_env r_s r_set x) (rem_use_env r_x x) = pwrite_use_env (diff_use_env r_s r_x) r_set x"    
  apply (case_tac "set_use_none r_s r_set")
   apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (simp add: set_use_none_def)
    apply (case_tac "\<forall> y. diff_use_env r_s (rem_use_env r_x x) y = diff_use_env r_s r_x y")
     apply (auto)
    apply (simp add: diff_use_env_def)
    apply (simp add: minus_use_env_def)
    apply (simp add: neg_use_env_def)
    apply (simp add: rem_use_env_def)
    apply (case_tac "x = y")
     apply (auto)
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto)
   apply (cut_tac r_x="diff_use_env r_s r_x" and r_s="r_s" and x="xa" in leq_use_none)
     apply (auto)
   apply (rule_tac self_diff_leq_use_env)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto)
   apply (case_tac "r_x xa \<noteq> OwnPerm")
    apply (simp add: diff_use_env_def)
    apply (simp add: minus_use_env_def)
    apply (simp add: neg_use_env_def)
    apply (case_tac "neg_perm (r_x xa) \<noteq> NoEP")
     apply (case_tac "r_x xa")
       apply (auto)
    apply (case_tac "r_s xa")
      apply (auto)
   apply (simp add: semi_weak_use_env_def)
  apply (simp add: diff_add_rem_use_env)
  done
    
lemma rhs_sw_leq_use_none: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s; r_s x = NoPerm; semi_weak_use_env r_ex r_set; x \<in> r_set  \<rbrakk> \<Longrightarrow> r_x x = NoPerm"    
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma rhs_pwrite_diff_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s (pwrite_use_env r_ex r_set x))"    
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (rule_tac dist_diff_leq_use_env)
   apply (simp)
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (case_tac "neg_perm (r_ex x) = NoEP")
    apply (auto)
    apply (case_tac "minus_ep (r_x x) NoEP \<noteq> r_x x")
     apply (case_tac "r_x x")
       apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (case_tac "neg_perm (r_ex xa) = NoEP")
   apply (auto)
   apply (case_tac "minus_ep (r_x xa) NoEP \<noteq> r_x xa")
    apply (case_tac "r_x xa")
      apply (auto)
   apply (case_tac "r_s xa")
     apply (auto)
  apply (case_tac "r_ex xa")
    apply (auto)
  apply (case_tac "r_x xa")
    apply (auto)
  done
 
    



lemma wtaer_var_case: "\<lbrakk> (*not_free_var x (VarExp x1a x2a);*) (if x2a = NoRef then {} else {x1a}) \<subseteq> r_set; semi_weak_use_env r_s1 r_set; x \<in> r_set; env x = Some t; mem_ty t;
        env (deref_name x1a x2a) = Some tau; env x1a = Some tau_x; var_val_type x2a tau tau_x; leq_use_env (ereq_use_env x1a tau_x) r_s1;
        leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau_x) r_ex)); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (diff_use_env (ereq_use_env x1a tau_x) (comp_use_env (ereq_use_env x1a tau_x) r_ex)) rx\<rbrakk>
       \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm)
            (case x2a of NoRef \<Rightarrow> VarExp x1a x2a | SelfRef \<Rightarrow> VarExp x (OtherRef x1a) | OtherRef y \<Rightarrow> VarExp x (OtherRef y)) tau (add_use_env r_s2 x UsePerm)
            (pwrite_use_env rx r_set x)"
    (* var case. non-value *)
       (*apply (simp add: not_free_var_def)*)
  apply (case_tac "x2a = NoRef")
   apply (auto)
    apply (rule_tac rhs_add_leq_use_env)
     apply (auto)
    apply (simp add: ereq_use_env_def)
    apply (simp add: one_use_env_def)
    apply (auto)
    apply (simp add: end_req_perm_def)
    apply (case_tac t)
          apply (auto)
(*
        apply (rule_tac t="ereq_use_env x1a tau_x" and s="rem_use_env (ereq_use_env x1a tau_x) x" in subst)
         apply (rule_tac rem_ereq_use_env)
         apply (simp)*)
   apply (rule_tac x="rem_use_env r_ex x" in exI)
(*
        apply (rule_tac t="comp_use_env (rem_use_env (ereq_use_env x1a tau_x) x) (rem_use_env r_ex x)"
            and s="rem_use_env (comp_use_env (ereq_use_env x1a tau_x) r_ex) x" in subst)
         apply (rule_tac dist_rem_comp_use_env)*)
   apply (auto)
(*
           apply (rule_tac t="diff_use_env (add_use_env r_s1 x UsePerm) (rem_use_env (comp_use_env (ereq_use_env x1a tau_x) r_ex) x)"
           and s="add_use_env (diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau_x) r_ex)) x UsePerm" in subst)
            apply (rule_tac diff_add_rem_use_env)
           apply (rule_tac dist_add_leq_use_env)
           apply (simp)*)
      apply (rule_tac r_sb="diff_use_env (add_use_env r_s1 x UsePerm) (rem_use_env (comp_use_env (ereq_use_env x1a tau_x) r_ex) x)" in trans_leq_use_env)
       apply (simp add: dist_rem_comp_use_env)
       apply (rule_tac unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac rhs_diff_rem_leq_use_env2)
        apply (simp add: ereq_use_env_def)
        apply (simp add: one_use_env_def)
        apply (simp add: end_req_perm_def)
        apply (case_tac tau_x)
              apply (auto)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac t="diff_use_env (add_use_env r_s1 x UsePerm) (rem_use_env (comp_use_env (ereq_use_env x1a tau_x) r_ex) x)"
           and s="add_use_env (diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau_x) r_ex)) x UsePerm" in subst)
       apply (rule_tac diff_add_rem_use_env)
      apply (rule_tac dist_add_leq_use_env)
      apply (simp)
     apply (rule_tac add_pwrite_leq_use_env)
       apply (rule_tac r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau_x) r_ex)" in trans_leq_use_env)
         apply (rule_tac self_diff_leq_use_env)
        apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
         apply (auto)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac rhs_add_leq_use_env)
     apply (rule_tac rem_leq_use_env)
     apply (simp)
    apply (simp add: rem_use_env_def)
   apply (rule_tac r_sb="diff_use_env (ereq_use_env x1a tau_x) (comp_use_env (ereq_use_env x1a tau_x) r_ex)" in trans_leq_use_env)
    apply (rule_tac pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau_x) r_ex)" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac rhs_diff_rem_leq_use_env2)
    apply (cut_tac r_x="r_ex" and r_s="r_s1" in sw_leq_use_env)
      apply (simp)
     apply (auto)
    apply (simp add: semi_weak_use_env_def)
   apply (rule_tac id_leq_use_env)
    (* var case. value cases *)
  apply (case_tac "(case x2a of NoRef \<Rightarrow> VarExp x1a x2a | SelfRef \<Rightarrow> VarExp x (OtherRef x1a) | OtherRef y \<Rightarrow> VarExp x (OtherRef y))
          \<noteq> VarExp x (case x2a of SelfRef \<Rightarrow> OtherRef x1a | _ \<Rightarrow> x2a)")
   apply (case_tac x2a)
     apply (auto)
     apply (simp add: deref_name_def)
     apply (case_tac x2a)
       apply (auto)
    apply (cut_tac tau="tau" in var_value_prim1)
      apply (auto)
    apply (case_tac x2a)
      apply (auto)
     apply (case_tac t)
           apply (auto)
    apply (case_tac t)
          apply (auto)
   apply (rule_tac ereq_leq_use_envx)
   apply (simp add: add_use_env_def)
   apply (simp add: end_req_perm_def)
   apply (case_tac t)
         apply (auto)
  apply (rule_tac x="rem_use_env r_ex x" in exI)
  apply (auto)
     apply (rule_tac rhs_flip_use_env)
     apply (rule_tac rhs_unroll_dcl_use_env)
     apply (rule_tac rhs_weak_leq_use_env)
      apply (rule_tac weak_ereq_use_env)
      apply (simp add: unlim_def)
      apply (case_tac t)
            apply (auto)
          apply (rule_tac t="diff_use_env (add_use_env r_s1 x UsePerm) (rem_use_env r_ex x)" and s="add_use_env (diff_use_env r_s1 r_ex) x UsePerm" in subst)
           apply (rule_tac diff_add_rem_use_env)
          apply (rule_tac dist_add_leq_use_env)
          apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau_x) r_ex)" in trans_leq_use_env)
           apply (rule_tac dist_diff_leq_use_env_gen)
            apply (rule_tac id_leq_use_env)
           apply (rule_tac self_comp_leq_use_env2)
          apply (simp)
         apply (rule_tac add_pwrite_leq_use_env)
          apply (rule_tac r_s="r_s1" in sw_leq_use_env)
            apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau_x) r_ex)" in trans_leq_use_env)
             apply (rule_tac self_diff_leq_use_env)
            apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
             apply (auto)
         apply (rule_tac dist_add_leq_use_env)
         apply (simp)
        apply (rule_tac rhs_add_leq_use_env)
         apply (rule_tac rem_leq_use_env)
         apply (simp)
        apply (simp add: rem_use_env_def)
    (* - req bound manipulation *)
       apply (cut_tac v="x2a" and tau_x="tau_x" in var_value_unlim)
         apply (auto)
       apply (simp add: pwrite_use_env_def)
       apply (auto)
    (* - say that we do not add a perm to rx. this means x1a is not in rx, which is impossible since r_s1 is weak *)
        apply (case_tac "rx x1a \<noteq> NoPerm")
         apply (simp add: set_use_none_def)
        apply (case_tac "ereq_use_env x1a tau_x x1a \<noteq> UsePerm")
         apply (simp add: ereq_use_env_def)
         apply (simp add: one_use_env_def)
         apply (simp add: end_req_perm_def)
        apply (case_tac "comp_use_env (ereq_use_env x1a tau_x) r_ex x1a \<noteq> OwnPerm")
         apply (cut_tac r_x="ereq_use_env x1a tau_x" and r_s="rx" and r_ex="comp_use_env (ereq_use_env x1a tau_x) r_ex" and x="x1a" in diff_use_leq)
           apply (auto)
        apply (cut_tac r_x="comp_use_env (ereq_use_env x1a tau_x) r_ex" and r_s="r_s1" and x="x1a" in leq_use_own)
          apply (simp)
         apply (rule_tac dist_comp_leq_use_env)
          apply (auto)
        apply (simp add: semi_weak_use_env_def)
    (* - otherwise we know what x is *)
       apply (rule_tac diff_leq_use_env)
       apply (rule_tac ereq_leq_use_envx)
       apply (simp add: add_use_env_def)
  apply (simp add: end_req_perm_def)
  apply (case_tac t)
        apply (auto)
  done
  
lemma wtaer_pair_case: "\<lbrakk>\<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e1 tau r_s2 rx; (*not_free_var x e1;*) r_set \<inter> lam_vars e1 = {}; semi_weak_use_env r_s1 r_set; env x = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e1 x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x);
        \<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e2 tau r_s2 rx; (*not_free_var x e2;*) r_set \<inter> lam_vars e2 = {}; semi_weak_use_env r_s1 r_set; env x = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e2 x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x);
       (* not_free_var x (PairExp e1 e2);*) r_set \<inter> (lam_vars e1 \<union> lam_vars e2) = {}; semi_weak_use_env r_s1 r_set; x \<in> r_set; env x = Some t; mem_ty t;
        pre_ref_vars e1 \<subseteq> r_set; pre_ref_vars e2 \<subseteq> r_set; well_typed env r_s1 e1 t1 r_s2a rx1; well_typed env r_s2a e2 t2 r_s3 rx2; r \<noteq> NoPerm;
        leq_use_env (lift_use_env rx1 r) r_s3; leq_use_env (lift_use_env rx2 r) r_s3;
        disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r); leq_use_env r_s2 (diff_use_env r_s3 r_ex); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r)) rx\<rbrakk>
       \<Longrightarrow> \<exists>r_s2a r_s3 rx1.
              well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e1 x) t1 r_s2a rx1 \<and>
              (\<exists>rx2. well_typed env r_s2a (ack_exp e2 x) t2 r_s3 rx2 \<and>
                     leq_use_env (lift_use_env rx1 r) r_s3 \<and>
                     leq_use_env (lift_use_env rx2 r) r_s3 \<and>
                     disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
                     (\<exists>r_ex. leq_use_env (add_use_env r_s2 x UsePerm) (diff_use_env r_s3 r_ex) \<and>
                             leq_use_env (pwrite_use_env rx r_set x) (add_use_env r_s2 x UsePerm) \<and>
                             leq_use_env r_ex (add_use_env r_s1 x UsePerm) \<and>
                             leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r)) (pwrite_use_env rx r_set x)))"    
      apply (rule_tac x="add_use_env r_s2a x UsePerm" in exI)
      apply (rule_tac x="add_use_env r_s3 x UsePerm" in exI)
      apply (rule_tac x="pwrite_use_env rx1 r_set x" in exI)
      apply (auto)(*
       apply (case_tac "\<not> not_free_var x e1")
        apply (simp add: not_free_var_def)
       apply (auto)*)
       apply (case_tac "\<not> r_set \<inter> lam_vars e1 = {}")
        apply (auto)
      apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (cut_tac r_x="lift_use_env rx1 r" and r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (auto)
      apply (cut_tac r_x="lift_use_env rx2 r" and r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (auto)
      apply (rule_tac x="pwrite_use_env rx2 r_set x" in exI)
      apply (auto)(*
            apply (case_tac "\<not> not_free_var x e2")
             apply (simp add: not_free_var_def)
            apply (auto)*)
            apply (case_tac "\<not> r_set \<inter> lam_vars e2 = {}")
             apply (auto)
            apply (cut_tac r_x="r_s2a" and r_s="r_s1" in sw_leq_use_env)
              apply (rule_tac well_typed_perm_leq)
              apply (auto)
           apply (rule_tac lift_pwrite_leq_use_env)
             apply (rule_tac r_s="r_s1" in sw_leq_use_env)
              apply (auto)
          apply (rule_tac lift_pwrite_leq_use_env)
            apply (rule_tac r_s="r_s1" in sw_leq_use_env)
             apply (auto)(*
         apply (rule_tac r_x="rx1" in safe_lift_pwrite_use_env)
          apply (auto)
        apply (rule_tac r_x="rx2" in safe_lift_pwrite_use_env)
         apply (auto)*)
       apply (rule_tac r_c="r_s1" in disj_lift_pwrite_use_env)
           apply (auto)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (auto)
       apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (auto)
      apply (rule_tac x="rem_use_env r_ex x" in exI)
      apply (auto)
         apply (rule_tac t="diff_use_env (add_use_env r_s3 x UsePerm) (rem_use_env r_ex x)"
          and s="add_use_env (diff_use_env r_s3 r_ex) x UsePerm" in subst)
          apply (rule_tac diff_add_rem_use_env)
         apply (rule_tac dist_add_leq_use_env)
         apply (simp)
        apply (rule_tac add_pwrite_leq_use_env)
         apply (rule_tac r_s="r_s1" in sw_leq_use_env)
           apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
            apply (rule_tac diff_leq_use_env)
            apply (simp)
           apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
            apply (auto)
        apply (rule_tac dist_add_leq_use_env)
        apply (simp)
       apply (rule_tac rhs_add_leq_use_env)
        apply (rule_tac rem_leq_use_env)
        apply (auto)
       apply (simp add: rem_use_env_def)
      apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
       apply (simp add: pair_req_def)
       apply (rule_tac leq_empty_use_env)
      apply (simp add: pair_req_def)
      apply (rule_tac t="lift_use_env (pwrite_use_env rx1 r_set x) r" and s="pwrite_use_env (lift_use_env rx1 r) r_set x" in subst)
       apply (rule_tac lift_pwrite_use_env)
       apply (rule_tac r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (auto)
      apply (rule_tac t="lift_use_env (pwrite_use_env rx2 r_set x) r" and s="pwrite_use_env (lift_use_env rx2 r) r_set x" in subst)
       apply (rule_tac lift_pwrite_use_env)
       apply (rule_tac r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (auto)
      apply (simp add: pwrite_comp_use_env)
      apply (cut_tac r_x="r_ex" and r_s="r_s1" in sw_leq_use_env)
        apply (auto)
      apply (simp add: diff_pwrite_rem_use_env)
      apply (rule_tac dist_pwrite_leq_use_env)
        apply (rule_tac r_s="r_s1" in sw_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
          apply (rule_tac diff_leq_use_env)
          apply (simp)
         apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
  apply (auto)
  done

lemma wtaer_if_case: "\<lbrakk>\<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e1 tau r_s2 rx; (*not_free_var x e1;*) r_set \<inter> lam_vars e1 = {}; semi_weak_use_env r_s1 r_set; env x = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e1 x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x);
        \<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e2 tau r_s2 rx; (*not_free_var x e2;*) r_set \<inter> lam_vars e2 = {}; semi_weak_use_env r_s1 r_set; env x = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e2 x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x);
        \<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e3 tau r_s2 rx; (*not_free_var x e3;*) r_set \<inter> lam_vars e3 = {}; semi_weak_use_env r_s1 r_set; env x = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e3 x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x);
        (*not_free_var x (IfExp e1 e2 e3);*) r_set \<inter> (lam_vars e1 \<union> lam_vars e2 \<union> lam_vars e3) = {}; semi_weak_use_env r_s1 r_set; x \<in> r_set;
        env x = Some t; mem_ty t; pre_ref_vars e1 \<subseteq> r_set; well_typed env r_s1 e1 BoolTy r_s2a rx'; pre_ref_vars e2 \<subseteq> r_set; pre_ref_vars e3 \<subseteq> r_set;
        well_typed env r_s2a e2 tau r_s2 rx1; well_typed env r_s2a e3 tau r_s2 rx2\<rbrakk>
       \<Longrightarrow> \<exists>rx' r_s2a.
              well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e1 x) BoolTy r_s2a rx' \<and>
              (\<exists>rx1a. well_typed env r_s2a (ack_exp e2 x) tau (add_use_env r_s2 x UsePerm) rx1a \<and>
                      (\<exists>rx2a. well_typed env r_s2a (ack_exp e3 x) tau (add_use_env r_s2 x UsePerm) rx2a \<and>
                              pwrite_use_env (comp_use_env rx1 rx2) r_set x = comp_use_env rx1a rx2a))"    
  apply (rule_tac x="pwrite_use_env rx' r_set x" in exI)
     apply (rule_tac x="add_use_env r_s2a x UsePerm" in exI)
     apply (auto)(*
      apply (case_tac "\<not> not_free_var x e1")
       apply (simp add: not_free_var_def)
      apply (auto)*)
      apply (case_tac "\<not> r_set \<inter> lam_vars e1 = {}")
       apply (auto)
     apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_set="r_set" in sw_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
     apply (rule_tac x="pwrite_use_env rx1 r_set x" in exI)
     apply (auto)(*
      apply (case_tac "\<not> not_free_var x e2")
       apply (simp add: not_free_var_def)
      apply (auto)*)
      apply (case_tac "\<not> r_set \<inter> lam_vars e2 = {}")
       apply (auto)
     apply (rule_tac x="pwrite_use_env rx2 r_set x" in exI)
     apply (auto)(*
      apply (case_tac "\<not> not_free_var x e3")
       apply (simp add: not_free_var_def)
      apply (auto)*)
      apply (case_tac "\<not> r_set \<inter> lam_vars e3 = {}")
       apply (auto)
     apply (cut_tac r_x="r_s2" and r_s="r_s2a" in sw_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
     apply (cut_tac r_x="rx1" and r_s="r_s2" in sw_leq_use_env)
       apply (rule_tac well_typed_perm_leqx)
       apply (auto)
     apply (cut_tac r_x="rx2" and r_s="r_s2" in sw_leq_use_env)
       apply (rule_tac well_typed_perm_leqx)
       apply (auto)
     apply (simp add: pwrite_comp_use_env)
  done
    
lemma wtaer_lam_case: "\<lbrakk>\<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e tau r_s2 rx; (*not_free_var x e;*) semi_weak_use_env r_s1 r_set; env x = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x);
        (*not_free_var x (LamExp x1a e);*) pre_ref_vars e \<subseteq> r_set; semi_weak_use_env r_s1 r_set; x \<in> r_set; env x = Some t; mem_ty t; x1a \<notin> r_set;
        r_set \<inter> lam_vars e = {}; x1a \<notin> ref_vars e; well_typed (add_env env x1a t1) (add_use_env rxa x1a r) e t2 r_s' r_end; aff_use_env rxa a;
        leq_use_env rxa r_s1; leq_use_env r_s2 (diff_use_env r_s1 r_ex); leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (diff_use_env rxa r_ex) rx\<rbrakk>
       \<Longrightarrow> \<exists>rxa. (\<exists>r_end r_s'. well_typed (add_env env x1a t1) (add_use_env rxa x1a r) (ack_exp e x) t2 r_s' r_end) \<and>
                 aff_use_env rxa a \<and>
                 leq_use_env rxa (add_use_env r_s1 x UsePerm) \<and>
                 (\<exists>r_ex. leq_use_env (add_use_env r_s2 x UsePerm) (diff_use_env (add_use_env r_s1 x UsePerm) r_ex) \<and>
                         leq_use_env (pwrite_use_env rx r_set x) (add_use_env r_s2 x UsePerm) \<and>
                         leq_use_env r_ex (add_use_env r_s1 x UsePerm) \<and> leq_use_env (diff_use_env rxa r_ex) (pwrite_use_env rx r_set x))"
    (* lam case. rxa does not contain any members of r_set *)
   apply (case_tac "set_use_none rxa r_set")
    apply (rule_tac x="rxa" in exI)
    apply (auto)
      apply (rule_tac x="r_end" in exI)
      apply (rule_tac x="r_s'" in exI)
      apply (rule_tac well_typed_ack_no_ref)
       apply (auto)
      apply (cut_tac env="add_env env x1a t1" and ?r_s1.0="add_use_env rxa x1a r" and x="xa" and e="e" in well_typed_no_pre_ref_vars_ih)
        apply (auto)
       apply (case_tac "xa = x1a")
        apply (cut_tac x="xa" and e="e" in sub_pre_ref_vars)
         apply (auto)
       apply (simp add: add_use_env_def)
       apply (simp add: set_use_none_def)
       apply (auto)
      apply (simp add: not_pre_ref_var_def)
     apply (rule_tac rhs_add_leq_use_env)
      apply (simp)
     apply (simp add: set_use_none_def)
    apply (rule_tac x="rem_use_env r_ex x" in exI)
    apply (auto)
       apply (rule_tac wtae_end_leq_use_env2)
       apply (simp)
      apply (rule_tac add_pwrite_leq_use_env)
        apply (rule_tac r_s="r_s1" in sw_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
          apply (rule_tac self_diff_leq_use_env)
         apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
          apply (auto)
      apply (rule_tac dist_add_leq_use_env)
      apply (simp)
     apply (rule_tac rhs_add_leq_use_env)
      apply (rule_tac rem_leq_use_env)
      apply (simp)
    apply (simp add: rem_use_env_def)
    apply (rule_tac pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    apply (rule_tac r_sb="diff_use_env rxa r_ex" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac rhs_diff_rem_leq_use_env)
     apply (simp add: set_use_none_def)
    apply (rule_tac id_leq_use_env)  
    (* lam case. rxa contains at least one member of r_set *)
    (* - prelim: rxa is not primitive *)
   apply (case_tac "a = Prim")
    apply (simp add: set_use_none_def)
    apply (auto)
    apply (simp add: aff_use_env_def)
    apply (simp add: null_use_env_def)
    (* - prelim: rx has at least one value as well *)
   apply (case_tac "set_use_none rx r_set")
    apply (simp add: set_use_none_def)
    apply (auto)
    apply (erule_tac x="xa" in allE)
    apply (cut_tac r_ex="r_ex" and r_x="rxa" and r_s="rx" and x="xa" in rhs_sw_leq_use_none)
        apply (auto)
    apply (rule_tac r_s="r_s1" in sw_leq_use_env)
     apply (auto)
    (* - prelim: x \<noteq> x1a *)
   apply (case_tac "x = x1a")
    apply (auto)
   apply (rule_tac x="add_use_env rxa x UsePerm" in exI)
   apply (auto)
      apply (rule_tac x="pwrite_use_env r_end r_set x" in exI)
     apply (rule_tac x="add_use_env r_s' x UsePerm" in exI)
     apply (rule_tac t="add_use_env (add_use_env rxa x UsePerm) x1a r" and s="add_use_env (add_use_env rxa x1a r) x UsePerm" in subst)
      apply (simp add: almost_comm_add_use_env)
      (*apply (case_tac "\<not> not_free_var x e")
       apply (simp add: not_free_var_def)*)
      apply (cut_tac r_s="rxa" and x="x1a" and r="r" and r_set="r_set" in sw_add_use_env)
        apply (rule_tac r_s="r_s1" in sw_leq_use_env)
         apply (auto)
      apply (case_tac "\<not> add_env env x1a t1 x = Some t")
       apply (simp add: add_env_def)
      apply (auto)
     apply (simp add: aff_use_env_def)
     apply (case_tac a)
       apply (auto)
     apply (simp add: weak_use_env_def)
     apply (simp add: add_use_env_def)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac x="rem_use_env r_ex x" in exI)
   apply (auto)
      apply (rule_tac t="diff_use_env (add_use_env r_s1 x UsePerm) (rem_use_env r_ex x)" and
        s="add_use_env (diff_use_env r_s1 r_ex) x UsePerm" in subst)
       apply (rule_tac diff_add_rem_use_env)
      apply (rule_tac dist_add_leq_use_env)
      apply (simp)
     apply (rule_tac add_pwrite_leq_use_env)
       apply (rule_tac r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
         apply (rule_tac self_diff_leq_use_env)
        apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
         apply (auto)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac rhs_add_leq_use_env)
     apply (rule_tac rem_leq_use_env)
     apply (simp)
    apply (simp add: rem_use_env_def)
   apply (simp add: pwrite_use_env_def)
   apply (rule_tac t="diff_use_env (add_use_env rxa x UsePerm) (rem_use_env r_ex x)" and
      s="add_use_env (diff_use_env rxa r_ex) x UsePerm" in subst)
    apply (rule_tac diff_add_rem_use_env)
   apply (rule_tac dist_add_leq_use_env)
   apply (simp)
  done
  
lemma wtaer_app_case: "\<lbrakk>\<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e1 tau r_s2 rx; (*not_free_var x e1;*) r_set \<inter> lam_vars e1 = {}; semi_weak_use_env r_s1 r_set; env x = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e1 x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x);
        \<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e2 tau r_s2 rx; (*not_free_var x e2;*) r_set \<inter> lam_vars e2 = {}; semi_weak_use_env r_s1 r_set; env x = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e2 x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x);
        (*not_free_var x (AppExp e1 e2);*) r_set \<inter> (lam_vars e1 \<union> lam_vars e2) = {}; semi_weak_use_env r_s1 r_set; x \<in> r_set; env x = Some t; mem_ty t;
        pre_ref_vars e1 \<subseteq> r_set; pre_ref_vars e2 \<subseteq> r_set; well_typed env r_s1 e1 (FunTy t1 tau r a) r_s2a rx1; well_typed env r_s2a e2 t1 r_s3 rx2;
        leq_use_env r_s2 (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)); r \<noteq> NoPerm;
        leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; disj_use_env rx1 (lift_use_env rx2 r); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (app_req rx1 rx2 r tau r_ex) rx\<rbrakk>
       \<Longrightarrow> \<exists>t1 r a r_s2a rx1.
              well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e1 x) (FunTy t1 tau r a) r_s2a rx1 \<and>
              (\<exists>rx2 r_s3. well_typed env r_s2a (ack_exp e2 x) t1 r_s3 rx2 \<and>
                          (\<exists>r_ex. leq_use_env (add_use_env r_s2 x UsePerm) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) \<and>
                                  r \<noteq> NoPerm \<and>
                                  leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
                                  disj_use_env rx1 (lift_use_env rx2 r) \<and>
                                  leq_use_env (pwrite_use_env rx r_set x) (add_use_env r_s2 x UsePerm) \<and>
                                  leq_use_env r_ex (add_use_env r_s1 x UsePerm) \<and> leq_use_env (app_req rx1 rx2 r tau r_ex) (pwrite_use_env rx r_set x)))"    
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="add_use_env r_s2a x UsePerm" in exI)
  apply (rule_tac x="pwrite_use_env rx1 r_set x" in exI)
  apply (auto)
   (*apply (case_tac "\<not> not_free_var x e1")
    apply (simp add: not_free_var_def)*)
   apply (case_tac "\<not> r_set \<inter> lam_vars e1 = {}")
    apply (auto)
  apply (rule_tac x="pwrite_use_env rx2 r_set x" in exI)
  apply (rule_tac x="add_use_env r_s3 x UsePerm" in exI)
  apply (auto)
   (*apply (case_tac "\<not> not_free_var x e2")
    apply (simp add: not_free_var_def)*)
   apply (case_tac "\<not> r_set \<inter> lam_vars e2 = {}")
    apply (auto)
   apply (cut_tac r_x="r_s2a" and r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (cut_tac r_sc="r_s2" and r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (auto)
  apply (cut_tac r_x="lift_use_env rx2 r" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac self_comp_leq_use_env2)
  apply (cut_tac r_x="rx1" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac self_comp_leq_use_env1)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx2 r_set x) r" and s="pwrite_use_env (lift_use_env rx2 r) r_set x" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (simp)
  apply (simp add: pwrite_comp_use_env)
  apply (rule_tac x="rem_use_env r_ex x" in exI)
  apply (auto)
        apply (rule_tac wtae_end_leq_use_env1)
         apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
          apply (rule_tac unroll_dcl_use_env)
          apply (rule_tac dist_diff_leq_use_env)
          apply (rule_tac rhs_pwrite_diff_leq_use_env)
          apply (rule_tac id_leq_use_env)
         apply (simp)
        apply (simp add: pwrite_use_env_def)
        apply (auto)
         apply (cut_tac r_x="comp_use_env rx1 (lift_use_env rx2 r)" and r_s="r_s1" and x="x" in leq_use_no_own)
           apply (simp add: semi_weak_use_env_def)
          apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
           apply (auto)
        apply (simp add: add_use_env_def)(*
       apply (rule_tac r_x="rx2" in safe_lift_pwrite_use_env)
        apply (auto)*)
      apply (rule_tac add_pwrite_leq_use_env)
        apply (rule_tac r_s="r_s1" in sw_leq_use_env)
         apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
          apply (auto)
      apply (rule_tac dist_add_leq_use_env)
      apply (simp)
     apply (rule_tac disj_pwrite_use_env)
        apply (auto)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (simp)
   apply (simp add: rem_use_env_def)
  apply (simp add: app_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx2 r_set x) r" and s="pwrite_use_env (lift_use_env rx2 r) r_set x" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (simp)
  apply (cut_tac r_x="rx2" and r_s="lift_use_env rx2 r" in sw_leq_use_env)
    apply (rule_tac self_lift_leq_use_env)
   apply (simp)
  apply (simp add: pwrite_comp_use_env)
  apply (case_tac "\<not> set_use_none (comp_use_env rx1 rx2) r_set")
   apply (case_tac "pwrite_use_env (comp_use_env rx1 rx2) r_set x \<noteq> add_use_env (comp_use_env rx1 rx2) x UsePerm")
    apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (case_tac "set_use_none rx r_set")
    apply (simp add: set_use_none_def)
    apply (auto)
    apply (cut_tac r_x="comp_use_env rx1 rx2" and r_s="rx" and r_ex="comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex" and x="xa" in rhs_sw_leq_use_none)
        apply (auto)
    apply (rule_tac r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (auto)
   apply (case_tac "pwrite_use_env rx r_set x \<noteq> add_use_env rx x UsePerm")
    apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (rule_tac wtae_req_leq_use_env1)
   apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac dist_diff_leq_use_env_gen)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (case_tac "pwrite_use_env (comp_use_env rx1 rx2) r_set x \<noteq> comp_use_env rx1 rx2")
   apply (simp add: pwrite_use_env_def)
  apply (auto)
  apply (rule_tac pwrite_leq_use_env)
    apply (rule_tac sw_leq_use_env)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (auto)
  apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac unroll_dcl_use_env)
  apply (rule_tac rhs_diff_rem_leq_use_env2)
   apply (rule_tac r_s="r_s1" in leq_use_no_own)
    apply (simp add: semi_weak_use_env_def)
   apply (simp)
  apply (rule_tac dist_diff_leq_use_env)
  apply (rule_tac dist_diff_leq_use_env_gen)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac pwrite_leq_use_env)
    apply (rule_tac r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
  apply (rule_tac id_leq_use_env) 
  done
    
(*
lemma well_typed_ack_exp_rep: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; not_free_var x e; r_set \<inter> lam_vars e = {};
  pre_ref_vars e \<subseteq> r_set; semi_weak_use_env r_s1 r_set; x \<in> r_set; env x = Some (ArrayTy t); unlim t \<rbrakk> \<Longrightarrow>
  well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x)"      
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)  *)  
    
lemma well_typed_ack_exp_rep: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; (*not_free_var x e;*) r_set \<inter> lam_vars e = {};
  pre_ref_vars e \<subseteq> r_set; semi_weak_use_env r_s1 r_set; x \<in> r_set; env x = Some t; mem_ty t \<rbrakk> \<Longrightarrow>
  well_typed env (add_use_env r_s1 x UsePerm) (ack_exp e x) tau (add_use_env r_s2 x UsePerm) (pwrite_use_env rx r_set x)"      
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* const + op cases *)
           apply (rule_tac dist_add_leq_use_env)
            apply (auto)
          apply (rule_tac add_pwrite_leq_use_env)
           apply (rule_tac r_s="r_s1" in sw_leq_use_env)
           apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
            apply (auto)
          apply (rule_tac dist_add_leq_use_env)
          apply (auto)
         apply (rule_tac dist_add_leq_use_env)
         apply (auto)
        apply (rule_tac add_pwrite_leq_use_env)
         apply (rule_tac r_s="r_s1" in sw_leq_use_env)
           apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
            apply (auto)
        apply (rule_tac dist_add_leq_use_env)
        apply (auto)
    (* var case. *)
       apply (rule_tac wtaer_var_case)
                    apply (auto)
    (* pair case. *)
      apply (rule_tac wtaer_pair_case)
                      apply (auto)
    (* if case *)
     apply (rule_tac wtaer_if_case)
                   apply (auto)
    (* lam case *) 
    apply (cut_tac e="e" and x="x1a" and y="x" in ack_ref_vars)
      apply (auto)
   apply (rule_tac wtaer_lam_case)
                   apply (auto)
    (* app case *)
  apply (rule_tac wtaer_app_case)
                     apply (auto)
  done
    
    (* ########### *)
    
fun finish_value where    
  "finish_value s (ConstExp c) = ConstExp c"
| "finish_value s (OpExp xop) = OpExp xop"  
| "finish_value s (VarExp x v) = (case v of
    NoRef \<Rightarrow> if x \<in> s then VarExp x SelfRef else VarExp x v
    | v \<Rightarrow> VarExp x v 
  )"  
| "finish_value s (PairExp e1 e2) = PairExp (finish_value s e1) (finish_value s e2)"
| "finish_value s (IfExp e1 e2 e3) = IfExp (finish_value s e1) (finish_value s e2) (finish_value s e3)"
| "finish_value s (LamExp x e) = LamExp x (finish_value (s - {x}) e)"
| "finish_value s (AppExp e1 e2) = AppExp (finish_value s e1) (finish_value s e2)"    

lemma finish_free_vars: "\<lbrakk> x \<notin> free_vars e \<rbrakk> \<Longrightarrow> x \<notin> free_vars (finish_value s e)"
  apply (induct e arbitrary: s)
        apply (auto)
   apply (case_tac x2a)
     apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done
  
lemma finish_lam_vars: "\<lbrakk> x \<notin> lam_vars e \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (finish_value s e)"    
  apply (induct e arbitrary: s)
        apply (auto)
   apply (case_tac x2a)
     apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done
    
  
    (* "finishing" an expression involves valuating all array variables with real ones. one thing
        we want to say is that if x was not a ref var in the original version, it wont be a ref var
        in the new expression if env x = None. *)
lemma finish_rem_ref_vars: "\<lbrakk> x \<notin> ref_vars e \<rbrakk> \<Longrightarrow> x \<notin> ref_vars (finish_value (s - {x}) e)"  
  apply (induct e arbitrary: s)
        apply (auto)
     apply (case_tac x2a)
       apply (auto)
    apply (case_tac x2a)
      apply (auto)
   apply (case_tac x2a)
     apply (auto)
  apply (case_tac "x = x1a")
   apply (auto)
  apply (case_tac "\<not> (s - {x} - {x1a}) = (s - {x1a} - {x})")
   apply (auto)
  done

lemma finish_ref_vars: "\<lbrakk> x \<notin> free_vars e; x \<notin> ref_vars e \<rbrakk> \<Longrightarrow> x \<notin> ref_vars (finish_value s e)"      
  apply (induct e arbitrary: s)
        apply (auto)
    apply (case_tac x2a)
      apply (auto)
   apply (case_tac x2a)
     apply (auto)
  apply (cut_tac x="x" and s="s" and e="e" in finish_rem_ref_vars)
   apply (auto)
  done
  
    
definition mem_val_subset where
  "mem_val_subset env s = (\<forall> x. x \<in> s \<longrightarrow> (\<exists> t. env x = Some t \<and> mem_ty t))"
    
lemma well_typed_finish_value: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; mem_val_subset env s \<rbrakk> \<Longrightarrow>
  well_typed env r_s1 (finish_value s e) tau r_s2 rx"
  apply (induct e arbitrary: env r_s1 r_s2 tau rx s)
        apply (auto)
    (* var case p1. *)
       apply (case_tac x2a)
         apply (auto)
        apply (simp add: deref_name_def)
        apply (simp add: deref_name_def)
        apply (simp add: mem_val_subset_def)
        apply (erule_tac x="x1a" in allE)
        apply (auto)
        apply (case_tac tau)
              apply (auto)
    (* var case p2. *)
       apply (case_tac x2a)
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
    (* lam case *)
    apply (cut_tac x="x1a" and s="s" and e="e" in finish_rem_ref_vars)
     apply (auto)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="r_end" in exI)
   apply (rule_tac x="r_s'" in exI)
   apply (case_tac "\<not> mem_val_subset (add_env env x1a t1) (s - {x1a})")
    apply (simp add: mem_val_subset_def)
    apply (auto)
   apply (simp add: add_env_def)
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
    
definition ack_full_exp where
  "ack_full_exp x e e' = (\<exists> vl. pre_vars vl = lam_vars e \<and> unique_post_vars vl \<and>
    post_vars vl \<inter> (free_vars e \<union> ref_vars e \<union> lam_vars e) = {} \<and> x \<notin> post_vars vl \<and>
    e' = ack_exp (finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl)) x)"
    
    (* the point of this lemma is that, given an arbitrary expression, if we replace every ref variable with a single source,
        it should still type properly. now, the three difficult parts of this rule are:
        - var case: for the non-value case, we need to make sure the source var doesn't overlap, which we can get by having x \<notin> fv e.
        - pair case: we run into a problem if the pair is affine since we might be adding perms to an empty req set. for this
            reason we only add x to the reqs if it already had a value.
        - lam case: ...
     *)
    
    (* the full statement of the lemma. *)

lemma wtae_diff_use_env: "\<lbrakk> strong_use_env r_s \<rbrakk> \<Longrightarrow> diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_s x) = one_use_env x UsePerm"    
  apply (case_tac "\<forall> y. diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_s x) y = one_use_env x UsePerm y")
   apply (auto)
  apply (simp add: one_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (case_tac "x = y")
   apply (auto)
  apply (erule_tac x="y" in allE)
  apply (case_tac "r_s y")
    apply (auto)
  done
    
lemma strong_lift_use_env: "\<lbrakk> is_own r \<rbrakk> \<Longrightarrow> strong_use_env (lift_use_env r_s r)"    
  apply (simp add: is_own_def)
  apply (simp add: strong_use_env_def)
  done
    
lemma semi_weak_drop_use_env: "semi_weak_use_env (drop_use_env r_s) r_set"    
  apply (simp add: semi_weak_use_env_def)
  apply (auto)
  apply (simp add: drop_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done
  
fun free_nv_vars where
  "free_nv_vars (ConstExp c) = {}"
| "free_nv_vars (OpExp xop) = {}"
| "free_nv_vars (VarExp x v) = (case v of
    NoRef \<Rightarrow> {x}
    | v \<Rightarrow> {}
  )"  
| "free_nv_vars (PairExp e1 e2) = free_nv_vars e1 \<union> free_nv_vars e2"
| "free_nv_vars (IfExp e1 e2 e3) = free_nv_vars e1 \<union> free_nv_vars e2 \<union> free_nv_vars e3"
| "free_nv_vars (LamExp x e) = (free_nv_vars e) - {x}"  
| "free_nv_vars (AppExp e1 e2) = free_nv_vars e1 \<union> free_nv_vars e2"  
  
lemma free_fnv_vars: "\<lbrakk> x \<notin> free_vars e \<rbrakk> \<Longrightarrow> x \<notin> free_nv_vars e"  
  apply (induct e)
        apply (auto)
  apply (case_tac x2a)
    apply (auto)
  done
  
lemma finish_add_fnv_vars: "\<lbrakk> y \<in> free_nv_vars (finish_value s e); x \<noteq> y \<rbrakk> \<Longrightarrow> y \<in> free_nv_vars (finish_value (s \<union> {x}) e)"  
  apply (induct e arbitrary: s)
        apply (auto)
     apply (case_tac x2a)
       apply (auto)
     apply (case_tac "x \<in> s")
      apply (auto)
    apply (case_tac x2a)
      apply (auto)
   apply (case_tac x2a)
     apply (auto)
  apply (case_tac "\<not> (insert x s - {x1a}) = (insert x (s - {x1a}))")
   apply (auto)
  done
    
    (* in a "finished" expression, none of the vars in the env will be free non-variables *)
  
lemma finish_exp_nvv: "\<lbrakk> well_typed env r_s1 (finish_value s e) tau r_s2 rx; mem_val_subset env s; y \<in> s \<rbrakk> \<Longrightarrow>
  y \<notin> free_nv_vars (finish_value s e)"  
  apply (induct e arbitrary: env s r_s1 tau r_s2 rx)
        apply (auto)
    (* var case. *)
    apply (case_tac x2a)
      apply (auto)
   apply (case_tac x2a)
     apply (auto)
    (* lam case. *)
  apply (case_tac "y = x1a")
   apply (auto)
  apply (case_tac "\<not> mem_val_subset (add_env env x1a t1) (s - {x1a})")
   apply (auto)
  apply (simp add: mem_val_subset_def)
  apply (simp add: add_env_def)
  done
    
    (* in an ack-ed expression, if y is not a variable in the expression, and y isn't x, it will not be a non-prim var *)
    
lemma ack_exp_npv: "\<lbrakk> well_typed env r_s1 (ack_exp e x) tau r_s2 rx; y \<notin> free_nv_vars e; env y = Some t; mem_ty t; x \<noteq> y \<rbrakk> \<Longrightarrow>
    y \<notin> non_prim_vars env (ack_exp e x)"
  apply (induct e arbitrary: env r_s1 r_s2 tau rx)
        apply (auto)
    (* const + op cases *)
         apply (simp add: non_prim_vars_def)
        apply (simp add: non_prim_vars_def)
    (* var case *)
       apply (simp add: non_prim_vars_def)
       apply (simp add: non_prim_entry_def)
       apply (auto)
       apply (case_tac "x2a")
         apply (auto)
    (* pair case *)
      apply (simp add: non_prim_vars_def)
      apply (auto)
    (* if case *)
     apply (simp add: non_prim_vars_def)
     apply (auto)
    (* lam case. non-scope. in this case we just use induction *)
    apply (case_tac "y \<notin> non_prim_vars (add_env env x1a t1) (ack_exp e x)")
     apply (simp add: non_prim_vars_def)
     apply (auto)
     apply (simp add: non_prim_entry_def)
     apply (simp add: add_env_def)
    (* - we have to check the off possibility that y = x1a anyway *)
    apply (case_tac "x1a = y")
     apply (simp add: non_prim_vars_def)
    apply (case_tac "\<not> add_env env x1a t1 y = Some t")
     apply (simp add: add_env_def)
    apply (auto)
    (* lam case. var capture. trivial because y is no longer free *)
   apply (simp add: non_prim_vars_def)
    (* app case. *)
  apply (simp add: non_prim_vars_def)
  apply (auto)
  done
    
    
lemma free_vars_subset: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; mem_val_env env \<rbrakk> \<Longrightarrow>
  mem_val_subset env (free_vars e)"    
  apply (simp add: mem_val_subset_def)
  apply (auto)
  apply (cut_tac env="env" and x="x" and e="e" in well_typed_fv_env_use)
    apply (auto)
  apply (simp add: mem_val_env_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done    
    
lemma ref_vars_subset: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; mem_val_env env \<rbrakk> \<Longrightarrow>
  mem_val_subset env (ref_vars e)"    
  apply (simp add: mem_val_subset_def)
  apply (auto)
  apply (cut_tac env="env" and x="x" and e="e" in well_typed_rv_env_use)
    apply (auto)
  apply (simp add: mem_val_env_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done

    (* for x to avoid being turned into a ref var, x \<noteq> b, simple as that *)(*
lemma lam_var_remove_ref_var_none2: "\<lbrakk> x \<notin> ref_vars e; well_typed env r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow> x \<notin> ref_vars (lam_var_remove e a b)"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)  
        apply (auto)
      apply (iprover)
     apply (iprover)
    apply (iprover)
    
  apply (case_tac "a = x1a")
   apply (auto)
  apply (case_tac "x \<in> ref_vars e")
   apply (auto)
  apply (cut_tac z="x" and x="a" and y="b" and e="e" in rename_ref_vars1)
    apply (auto)
  done*)(*
    thm lam_var_remove_type_preserve
    (* post_vars vl \<inter> (free_vars e \<union> ref_vars e \<union> lam_vars e) = {} *)
lemma lam_var_list_remove_ref_none: "\<lbrakk> x \<in> ref_vars (lam_var_list_remove e vl); well_typed env r_s1 e tau r_s2 rx;
  post_vars vl \<inter> (free_vars e \<union> ref_vars e \<union> lam_vars e) = {}  \<rbrakk> \<Longrightarrow> x \<in> ref_vars e"    
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and x="a" and y="b" in lam_var_remove_type_preserve)
    apply (auto)
  apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_ref_var_none2)
    apply (auto)
  done*)
    
lemma well_typed_ack_exp: "\<lbrakk> well_typed env r_x e tau r_x r_x; is_value e; (*x \<notin> lam_vars e;*)
  (*(free_vars e \<union> ref_vars e) \<inter> lam_vars e = {}*)ack_full_exp x e e';
  env x = Some t; mem_ty t; unlim tau; r_s x \<noteq> NoPerm; mem_val_env env \<rbrakk> \<Longrightarrow>
  well_typed env r_s e' tau r_s (one_use_env x UsePerm)"    
    (* prelim: x \<notin> free_vars e, because r_x x = NoPerm *)
 (*apply (case_tac "x \<in> free_vars e")
   apply (cut_tac env="env" and e="e" and ?r_s1.0="r_x" and x="x" in well_typed_no_npv_use)
     apply (auto)
   apply (simp add: non_prim_vars_def)
   apply (simp add: non_prim_entry_def)*)
    (* to prove that ack_exp works with arbitrary permissions, we want to prove that it works with just x. *)
  apply (simp add: ack_full_exp_def)
  apply (auto)
  apply (rule_tac r_s="one_use_env x UsePerm" in well_typed_incr_simul_perm)
   apply (simp add: leq_use_env_def)
   apply (simp add: one_use_env_def)
   apply (case_tac "r_s x")
     apply (auto)
    (* we predict what the lam-var-list removal proof will look like, because we will need it later *)
  apply (cut_tac env="env" and ?r_s1.0="drop_use_env r_x" and  e="e" and vl="vl" and tau="tau" and
      ?r_s2.0="drop_use_env r_x" and rx="drop_use_env r_x" in lam_var_list_remove_type_preserve)
    (* we can "un-drop" the permissions by the drop lemma *)
     apply (rule_tac wt_sexp_drop_all)
       apply (simp)
      apply (simp add: unlim_def)
     apply (rule_tac value_is_sexp)
     apply (simp)
    (* proving lam var list removal was fine *)
    apply (auto)
    (* we prove that every lambda after removal is in vl, since it's useful in proving finish correctness *)
  apply (case_tac "\<not> lam_vars (lam_var_list_remove e vl) \<subseteq> post_vars vl")
   apply (auto)
   apply (case_tac "xa \<in> post_vars vl")
    apply (auto)
   apply (case_tac "xa \<notin> lam_vars e")
    apply (cut_tac x="xa" and e="e" and vl="vl" in lam_var_list_remove_lam_var_none1)
      apply (auto)
   apply (cut_tac x="xa" and e="e" and vl="vl" in lam_var_list_remove_lam_var_none2)
     apply (auto)
    (* we predict what the ack proof will look like, because we will need to use it again later *)
  apply (cut_tac env="env" and ?r_s1.0="drop_use_env r_x" and e="finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl)" and tau="tau" and
        ?r_s2.0="drop_use_env r_x" and rx="drop_use_env r_x" and x="x" and r_set="{x} \<union> ref_vars (finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl))" and
        t="t" in well_typed_ack_exp_rep)
         apply (rule_tac well_typed_finish_value)
          apply (simp)
    (* proving finish was fine *)
         apply (rule_tac ?r_s1.0="drop_use_env r_x" in free_vars_subset)
          apply (auto)
(*
       apply (simp add: not_free_var_def)
       apply (auto)*)
    (* x is not free in the finished exp *)(*
       apply (cut_tac s="free_vars (lam_var_list_remove e vl)" and x="x" and e="lam_var_list_remove e vl" in finish_free_vars)
        apply (auto)
       apply (cut_tac x="x" and e="e" and vl="vl" in lam_var_list_remove_free_var_none)
        apply (auto)*)
    (* x is not a lambda var in the finished exp, since it is not in the post vars *)
      apply (cut_tac s="free_vars (lam_var_list_remove e vl)" and x="x" and e="lam_var_list_remove e vl" in finish_lam_vars)
       apply (auto)
    (* if xa is in the finished lam vars, it is in vl, which means it is not a free var or ref var in the original. *)
     apply (cut_tac s="free_vars (lam_var_list_remove e vl)" and x="xa" and e="lam_var_list_remove e vl" in finish_lam_vars)
      apply (auto)
     apply (case_tac "xa \<in> ref_vars e")
      apply (auto)
     apply (case_tac "xa \<in> free_vars e")
      apply (auto)
    (* - from this we know it's not a ref var in the finished *)
     apply (cut_tac s="free_vars (lam_var_list_remove e vl)" and x="xa" and e="lam_var_list_remove e vl" in finish_ref_vars)
       apply (auto)
      apply (cut_tac x="xa" and e="e" and vl="vl" in lam_var_list_remove_free_var_none)
       apply (auto)
    (* - to confirm this we have to show that removing vl doesnt add xa to the ref vars. *)
      apply (cut_tac x="xa" and e="e" and vl="vl" and env="env" and ?r_s1.0="r_x" in lam_var_list_remove_ref_var)
         apply (auto)
     apply (simp add: disj_vars_def)
    (* remaining manip reqs *)
    apply (case_tac "xa \<notin> ref_vars (finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl))")
     apply (cut_tac x="xa" and e="finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl)" in sub_pre_ref_vars)
      apply (auto)
     apply (rule_tac semi_weak_drop_use_env)
    (* to push the permissions back to r_x, we manipulate it to invoke the diff perms lemma *)
  apply (cut_tac eq_own)
  apply (auto)
  apply (rule_tac t="one_use_env x UsePerm" and s="diff_use_env (add_use_env (lift_use_env r_x r) x UsePerm) (rem_use_env (lift_use_env r_x r) x)" in subst)
   apply (rule_tac wtae_diff_use_env)
   apply (rule_tac strong_lift_use_env)
   apply (simp)
  apply (rule_tac well_typed_diff_perms)
    (* after this we have to drop permissions on everything to activate ack *)
   apply (rule_tac rx="pwrite_use_env (drop_use_env r_x) ({x} \<union> ref_vars (finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl))) x" in well_typed_incr_req)
     apply (rule_tac r_s="add_use_env (drop_use_env r_x) x UsePerm" in well_typed_incr_simul_perm)
      apply (rule_tac dist_add_leq_use_env)
      apply (rule_tac drop_leq_use_env)
      apply (rule_tac self_lift_leq_use_env)
     apply (simp)
    (* proving requirements change was valid *)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac semi_weak_drop_use_env)
     apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (rule_tac drop_leq_use_env)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac id_leq_use_env)
    (* proving that the diff was valid, which is true since x should be the only non-prim var *)
  apply (case_tac "x \<noteq> xa")
   apply (auto)
    (* we know xa in the finished version is not a free non-value *)
   apply (cut_tac env="env" and ?r_s1.0="drop_use_env r_x" and e="lam_var_list_remove e vl" and tau="tau" and s="free_vars (lam_var_list_remove e vl)" in well_typed_finish_value)
       apply (auto)
    apply (rule_tac free_vars_subset)
     apply (auto)
   apply (simp add: non_prim_vars_def)
   apply (simp add: non_prim_entry_def)
   apply (auto)
   apply (case_tac "\<not> mem_ty taua")
    apply (simp add: mem_val_env_def)
    apply (erule_tac x="xa" in allE)
    apply (auto)
   apply (case_tac "xa \<in> free_nv_vars (finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl))")
    apply (cut_tac env="env" and s="free_vars (lam_var_list_remove e vl)" and e="lam_var_list_remove e vl" and ?r_s1.0="drop_use_env r_x" and y="xa" in finish_exp_nvv)
       apply (auto)
     apply (rule_tac free_vars_subset)
      apply (auto)
    apply (case_tac "xa \<in> free_vars (lam_var_list_remove e vl)")
     apply (simp)
    apply (cut_tac x="xa" and s="free_vars (lam_var_list_remove e vl)" and e="lam_var_list_remove e vl" in finish_free_vars)
     apply (simp)
    apply (cut_tac x="xa" and e="finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl)" in free_fnv_vars)
     apply (auto)
    (* we already proved that ack_exp is well-typed to some capacity, which we can use to prove xa is non-primitive *)
   apply (cut_tac y="xa" and env="env" and t="taua" and ?r_s1.0="add_use_env (drop_use_env r_x) x UsePerm" and e="finish_value (free_vars (lam_var_list_remove e vl)) (lam_var_list_remove e vl)" in ack_exp_npv)
        apply (auto)
   apply (simp add: non_prim_vars_def)
   apply (simp add: non_prim_entry_def)
  apply (simp add: own_env_vars_def)
  apply (simp add: rem_use_env_def)
  done
    
lemma path_lookup_append: "\<lbrakk> path_lookup rs_map x l y; path_lookup rs_map y m z \<rbrakk> \<Longrightarrow> path_lookup rs_map x (l @ m) z"    
  apply (induct l arbitrary: x)
   apply (auto)
  apply (case_tac "rs_map x")
   apply (auto)
  done
  
definition proper_use_env where
  "proper_use_env rs_map x e r_s = (\<forall> y. (y \<in> ref_vars e \<and> r_s y \<noteq> NoPerm) \<longrightarrow> (\<exists> l. path_lookup rs_map x l y))"
  
lemma leq_proper_use_env: "\<lbrakk> proper_use_env rs_map x e r_s; leq_use_env r_x r_s; ref_vars e' \<subseteq> ref_vars e \<rbrakk> \<Longrightarrow> proper_use_env rs_map x e' r_x"
  apply (simp add: proper_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="y" in allE)
  apply (auto)
  apply (case_tac "r_x y")
    apply (auto)
  done
  
lemma add_proper_use_env: "\<lbrakk> proper_use_env rs_map x e r_s; y \<notin> ref_vars e \<rbrakk> \<Longrightarrow>
  proper_use_env rs_map x e (add_use_env r_s y r)"    
  apply (simp add: proper_use_env_def)
  apply (simp add: add_use_env_def)
  done
    
    (* an "acked" expression will be proper if the only variables used for x *)
lemma proper_ack_exp: "\<lbrakk> proper_use_env rs_map x e r_s; proper_exp rs_map e;
   well_typed env r_s e tau r_se r_xe \<rbrakk> \<Longrightarrow> proper_exp rs_map (ack_exp e x)"    
  apply (induct e arbitrary: env r_s tau r_se r_xe)
        apply (auto)
    (* var case. we first posit that there is a path between x \<leadsto> x1a *)
      apply (case_tac "x2a = NoRef")
       apply (auto)
      apply (simp add: proper_exp_def)
      apply (case_tac "\<not> (\<exists> l. path_lookup rs_map x l x1a)")
       apply (simp add: proper_use_env_def)
       apply (erule_tac x="x1a" in allE)
       apply (auto)
        apply (case_tac x2a)
          apply (auto)
       apply (cut_tac r_x="ereq_use_env x1a tau_x" and r_s="r_s" and x="x1a" in leq_use_none)
         apply (simp_all)
       apply (cut_tac v="x2a" and tau_x="tau_x" in var_value_unlim)
         apply (auto)
       apply (simp add: ereq_use_env_def)
       apply (simp add: one_use_env_def)
       apply (simp add: end_req_perm_def)
    (* - we split over x2a *)
      apply (case_tac x2a)
        apply (auto)
      apply (rule_tac x="l @ la" in exI)
      apply (rule_tac path_lookup_append)
       apply (auto)
    (* pair case *)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
      apply (auto)
     apply (cut_tac r_x="r_s" and r_s="r_s" and rs_map="rs_map" and e="PairExp e1 e2" and e'="e1" and x="x" in leq_proper_use_env)
        apply (auto)
      apply (rule_tac id_leq_use_env)
     apply (cut_tac r_x="r_s2" and r_s="r_s" and rs_map="rs_map" and e="PairExp e1 e2" and e'="e2" and x="x" in leq_proper_use_env)
        apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (simp add: proper_exp_def)
    (* if case *)
    apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
     apply (auto)
    apply (cut_tac r_x="r_s" and r_s="r_s" and rs_map="rs_map" and x="x" and e="IfExp e1 e2 e3" and e'="e1"  in leq_proper_use_env)
      apply (auto)
     apply (rule_tac id_leq_use_env)
    apply (cut_tac r_x="r_s2" and r_s="r_s" and rs_map="rs_map" and x="x" and e="IfExp e1 e2 e3" and e'="e2" in leq_proper_use_env)
       apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (cut_tac r_x="r_s2" and r_s="r_s" and rs_map="rs_map" and x="x" and e="IfExp e1 e2 e3" and e'="e3"  in leq_proper_use_env)
      apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (simp add: proper_exp_def)
    (* lam case *)
   apply (cut_tac r_s="rx" and rs_map="rs_map" and e="e" and x="x" and y="x1a" and r="r" in add_proper_use_env)
     apply (rule_tac r_s="r_s" and e="e" in leq_proper_use_env)
       apply (simp add: proper_use_env_def)
      apply (auto)
   apply (simp add: proper_exp_def)
    (* app case *)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (cut_tac r_x="r_s" and r_s="r_s" and rs_map="rs_map" and e="AppExp e1 e2" and e'="e1" and x="x" in leq_proper_use_env)
     apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (cut_tac r_x="r_s2" and r_s="r_s" and rs_map="rs_map" and e="AppExp e1 e2" and e'="e2" and x="x" in leq_proper_use_env)
     apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (simp add: proper_exp_def)
  done

    
definition free_ref_vars where
  "free_ref_vars e = (free_vars e \<inter> ref_vars e)"  
    
lemma free_ref_pair: "\<lbrakk> free_ref_vars (PairExp e1 e2) \<subseteq> s \<rbrakk> \<Longrightarrow> free_ref_vars e1 \<subseteq> s \<and> free_ref_vars e2 \<subseteq> s"  
  apply (simp add: free_ref_vars_def)
  apply (auto)
  done

lemma free_ref_if: "\<lbrakk> free_ref_vars (IfExp e1 e2 e3) \<subseteq> s \<rbrakk> \<Longrightarrow> free_ref_vars e1 \<subseteq> s \<and> free_ref_vars e2 \<subseteq> s \<and> free_ref_vars e3 \<subseteq> s"  
  apply (simp add: free_ref_vars_def)
  apply (auto)
  done
 
  
lemma free_ref_lam: "\<lbrakk> free_ref_vars (LamExp x e) \<subseteq> s; x \<notin> ref_vars e \<rbrakk> \<Longrightarrow> free_ref_vars e \<subseteq> (s - {x})"  
  apply (simp add: free_ref_vars_def)
  apply (auto)
  done    
    
lemma free_ref_app: "\<lbrakk> free_ref_vars (AppExp e1 e2) \<subseteq> s \<rbrakk> \<Longrightarrow> free_ref_vars e1 \<subseteq> s \<and> free_ref_vars e2 \<subseteq> s"  
  apply (simp add: free_ref_vars_def)
  apply (auto)
  done    
    
lemma proper_finish_value: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; proper_exp rs_map e; (free_ref_vars e) \<subseteq> s \<rbrakk> \<Longrightarrow> proper_exp rs_map (finish_value s e)"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx s)
        apply (auto)
       apply (simp add: proper_exp_def)
       apply (case_tac x2a)
         apply (auto)
      apply (case_tac x2a)
        apply (auto)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
      apply (auto)
     apply (cut_tac s="s" and ?e1.0="e1" and ?e2.0="e2" in free_ref_pair)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
     apply (auto)
    apply (cut_tac s="s" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in free_ref_if)
     apply (auto)
    apply (simp add: proper_exp_def)
   apply (cut_tac s="s" and e="e" and x="x1a" in free_ref_lam)
     apply (auto)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (cut_tac s="s" and ?e1.0="e1" and ?e2.0="e2" in free_ref_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
  
lemma proper_ack_full_exp: "\<lbrakk> path_lookup rs_map x l y; rs_map y = Some r_s;
  proper_exp rs_map e; mem_val_env env;
  well_typed env r_s e tau r_se r_xe; ack_full_exp x e e' \<rbrakk> \<Longrightarrow> proper_exp rs_map e'"    
  apply (simp add: ack_full_exp_def)
  apply (auto)
    (* we need this well-typedness statement more than once *)(*
  apply (cut_tac env="env" and s="free_vars e" and e="lam_var_list_remove e vl" and ?r_s1.0="r_s" and
      tau="tau" and ?r_s2.0="r_se" and rx="r_xe" in well_typed_finish_value)
    apply (rule_tac lam_var_list_remove_type_preserve)
      apply (auto)
   apply (simp add: mem_val_subset_def)
   apply (auto)
   apply (cut_tac env="env" and e="e" and x="xa" in well_typed_fv_env_use)
     apply (auto)
   apply (simp add: mem_val_env_def)
   apply (erule_tac x="xa" in allE)
   apply (auto)*)
  apply (rule_tac env="env" and r_s="r_s" and r_se="r_se" and tau="tau" and r_xe="r_xe" in proper_ack_exp)
    (* we expect everything from r_s1 to be contained in the completion of rs_map since
        r_s1 is derived from some resource y, where there is a path from x to y *)
    apply (simp add: proper_use_env_def)
    apply (auto)
    apply (rule_tac x="l @ [ya]" in exI)
    apply (rule_tac y="y" in path_lookup_append)
     apply (auto)
    (* we prove that the finished exp is still proper *)
   apply (rule_tac env="env" and ?r_s1.0="r_s" and tau="tau" and ?r_s2.0="r_se" and rx="r_xe" in proper_finish_value)
     apply (rule_tac lam_var_list_remove_type_preserve)
       apply (auto)
    apply (rule_tac proper_lvlr_ex)
       apply (auto)
   apply (simp add: free_ref_vars_def)
    (* lastly we prove the finished value is well_typed *)
  apply (rule_tac well_typed_finish_value)
   apply (rule_tac lam_var_list_remove_type_preserve)
     apply (auto)
  apply (simp add: mem_val_subset_def)
  apply (auto)
  apply (case_tac "xa \<notin> free_vars e")
   apply (cut_tac x="xa" and e="e" and vl="vl" in lam_var_list_remove_free_var_none)
    apply (auto)
  apply (cut_tac env="env" and e="e" and x="xa" in well_typed_fv_env_use)
    apply (auto)
  apply (simp add: mem_val_env_def)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done
    
end