theory WTBreak
  imports PermEnvMisc
begin

    (* - define the notion of "environment completion" *)
  
definition complete_use_env where
  "complete_use_env r_x r_s = (\<lambda> x. if r_x x = NoPerm then NoPerm else r_s x)"
    
lemma self_compl_leq_use_env: "leq_use_env (complete_use_env r_x r_s) r_s"
  apply (simp add: leq_use_env_def)
  apply (simp add: complete_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma compl_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (complete_use_env r_ex r_x) r_s"    
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_compl_leq_use_env)
  done
    
lemma dist_compl_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (complete_use_env r_x r_ex) (complete_use_env r_s r_ex)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: complete_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done
  
lemma diff_compl_leq_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow> leq_use_env (complete_use_env r_x r_s) (diff_use_env r_s r_ex)"
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: complete_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done

lemma spec_compl_leq_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow> leq_use_env (complete_use_env r_x r_c) (diff_use_env (complete_use_env r_s r_c) r_ex)"    
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: complete_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (case_tac "r_x x")
     apply (auto)
   apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
    apply (case_tac "r_c x")
      apply (auto)
   apply (case_tac "r_c x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
  
lemma rhs_self_compl_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (complete_use_env r_x r_s)"
  apply (simp add: leq_use_env_def)
  apply (simp add: complete_use_env_def)
  done
    
lemma rhs_compl_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; leq_use_env r_s r_ex \<rbrakk> \<Longrightarrow> leq_use_env r_x (complete_use_env r_s r_ex)"    
  apply (rule_tac r_sb="r_s" in trans_leq_use_env)
   apply (rule_tac rhs_self_compl_leq_use_env)
   apply (auto)
  done
    
lemma sub_complete_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> complete_use_env r_x (complete_use_env r_s r_c) = complete_use_env r_x r_c"    
  apply (case_tac "\<forall> x. complete_use_env r_x (complete_use_env r_s r_c) x = complete_use_env r_x r_c x")
   apply (auto)
  apply (simp add: leq_use_env_def)
  apply (simp add: complete_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
  
lemma dist_comp_compl_use_env: "complete_use_env (comp_use_env r_x r_s) r_c = comp_use_env (complete_use_env r_x r_c) (complete_use_env r_s r_c)"    
  apply (case_tac "\<forall> x. complete_use_env (comp_use_env r_x r_s) r_c x = comp_use_env (complete_use_env r_x r_c) (complete_use_env r_s r_c) x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: complete_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
     apply (case_tac "r_c x")
       apply (auto)
    apply (case_tac "r_c x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
     apply (case_tac "r_c x")
       apply (auto)
    apply (case_tac "r_c x")
      apply (auto)
   apply (case_tac "r_c x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
    apply (case_tac "r_c x")
      apply (auto)
   apply (case_tac "r_c x")
     apply (auto)   
  apply (case_tac "r_c x")
    apply (auto)
  done

    
definition strong_use_env where
  "strong_use_env r_s = (\<forall> x. r_s x \<noteq> UsePerm)"    
    
  (* the issue is that if r_s contains a use, then there is no way to remove it using r_ex, if it is not present in r_x
    in practice, this is describing if the original permissions had a use, but the end permissions + reqs do not have one.
  *)
    
lemma ex_complete_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> (\<exists> r_ex. strong_use_env r_ex \<and> complete_use_env r_x r_s = diff_use_env r_s r_ex)"
  apply (rule_tac x="\<lambda> x. if r_s x \<noteq> NoPerm \<and> r_x x = NoPerm then OwnPerm else NoPerm" in exI)
  apply (auto)
   apply (simp add: strong_use_env_def)
  apply (case_tac "\<forall> x. complete_use_env r_x r_s x = diff_use_env r_s (\<lambda>x. if r_s x \<noteq> NoPerm \<and> r_x x = NoPerm then OwnPerm else NoPerm) x")
   apply (auto)
  apply (simp add: leq_use_env_def)
  apply (simp add: complete_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done

end