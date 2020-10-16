theory PermEnvEq
  imports PermEnv
begin
      
    (* #### machinery for diff lemmas #### *)
  
fun comp_ep where
  "comp_ep OwnEP p = OwnEP"
| "comp_ep p OwnEP = OwnEP"
| "comp_ep NoEP NoEP = NoEP"
| "comp_ep p1 p2 = DiffEP"

definition comp_ep_use_env where
  "comp_ep_use_env r_s1 r_s2 = (\<lambda> x. comp_ep (r_s1 x) (r_s2 x))"

lemma minus_comp_ep_use_env: "minus_use_env (minus_use_env r_s r_x) r_ex = minus_use_env r_s (comp_ep_use_env r_x r_ex)"  
  apply (case_tac "\<forall> x. minus_use_env (minus_use_env r_s r_x) r_ex x = minus_use_env r_s (comp_ep_use_env r_x r_ex) x")
   apply (auto)
  apply (simp add: minus_use_env_def)
  apply (simp add: comp_ep_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done

lemma dist_neg_comp_use_env: "neg_use_env (comp_use_env r_x r_ex) = comp_ep_use_env (neg_use_env r_x) (neg_use_env r_ex)"
  apply (case_tac "\<forall> x. neg_use_env (comp_use_env r_x r_ex) x = comp_ep_use_env (neg_use_env r_x) (neg_use_env r_ex) x")
   apply (auto)
  apply (simp add: neg_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (simp add: comp_ep_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done  
    
    (* 
      ####################################
        P1. main equality lemmas
      ####################################
    *)  
    
    (* - add / rem lemmas *)
    
lemma ignore_add_use_env: "\<lbrakk> r = r_s x \<rbrakk> \<Longrightarrow> r_s = add_use_env r_s x r"
  apply (simp add: add_use_env_def)
  apply (auto)
  done    

lemma self_add_use_env: "add_use_env r_s x (r_s x) = r_s"  
  apply (case_tac "\<forall> x'. add_use_env r_s x (r_s x) x' = r_s x'")
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (auto)
  done    
    
lemma almost_comm_add_use_env: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> add_use_env (add_use_env r_s x r) y r' = add_use_env (add_use_env r_s y r') x r"    
  apply (simp add: add_use_env_def)
  apply (auto)
  done    
    
lemma ignore_rem_use_env: "\<lbrakk> r_s x = NoPerm \<rbrakk> \<Longrightarrow> r_s = rem_use_env r_s x"    
  apply (case_tac "\<forall> x'. r_s x' = rem_use_env r_s x x'")  
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (auto)
  done
    
lemma almost_comm_rem_add_use_env: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> rem_use_env (add_use_env r_s x r) y = add_use_env (rem_use_env r_s y) x r"
  apply (case_tac "\<forall> x'. rem_use_env (add_use_env r_s x r) y x' = add_use_env (rem_use_env r_s y) x r x'")
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
   apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  done    
    
lemma partial_add_rem_use_env: "add_use_env r_s x r = add_use_env (rem_use_env r_s x) x r"    
  apply (case_tac "\<forall> x'. add_use_env r_s x r x' = add_use_env (rem_use_env r_s x) x r x'")
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  done    
 
lemma partial_rem_add_use_env: "rem_use_env r_s x = rem_use_env (add_use_env r_s x r) x"    
  apply (case_tac "\<forall> x'. rem_use_env r_s x x' = rem_use_env (add_use_env r_s x r) x x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: add_use_env_def)
  done        
    
lemma cancel_rem_add_use_env: "\<lbrakk> r_s x = NoPerm \<rbrakk> \<Longrightarrow> r_s = rem_use_env (add_use_env r_s x r) x"    
  apply (case_tac "\<forall> x'. r_s x' = rem_use_env (add_use_env r_s x r) x x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: add_use_env_def)
  done    
  
lemma cancel_add_rem_use_env: "\<lbrakk> r_s x = r \<rbrakk> \<Longrightarrow> r_s = add_use_env (rem_use_env r_s x) x r"       
  apply (case_tac "\<forall> x'. r_s x' = add_use_env (rem_use_env r_s x) x r x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (simp add: add_use_env_def)
   apply (auto)
  done
    
    (* - minus lemmas *)
    
lemma double_minus_use_env: "minus_use_env (minus_use_env r_s r_x) r_x = minus_use_env r_s r_x"    
  apply (case_tac "\<forall> x. minus_use_env (minus_use_env r_s r_x) r_x x = minus_use_env r_s r_x x")
   apply (auto)
  apply (simp add: minus_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done    
    
    (* - diff lemmas *)

lemma double_diff_use_env: "diff_use_env r_s r_x = diff_use_env (diff_use_env r_s r_x) r_x"    
  apply (simp add: diff_use_env_def)
  apply (cut_tac r_s="r_s" and r_x="neg_use_env r_x" in double_minus_use_env)
  apply (auto)
  done

lemma cancel_diff_use_env2: "\<lbrakk> leq_use_env r_x r_c \<rbrakk> \<Longrightarrow> diff_use_env r_s r_c = diff_use_env (diff_use_env r_s r_c) r_x"
  apply (case_tac "\<forall> x. diff_use_env r_s r_c x = diff_use_env (diff_use_env r_s r_c) r_x x")
   apply (auto)
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_c x")
     apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_c x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done       
    
lemma cancel_diff_use_env: "\<lbrakk> leq_use_env r_x r_c \<rbrakk> \<Longrightarrow> diff_use_env r_s r_c = diff_use_env (diff_use_env r_s r_x) r_c"
  apply (case_tac "\<forall> x. diff_use_env r_s r_c x = diff_use_env (diff_use_env r_s r_x) r_c x")
   apply (auto)
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
   apply (case_tac "r_c x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  apply (case_tac "r_c x")
    apply (auto)
  done    
    
lemma weak_diff_use_env: "\<lbrakk> weak_use_env r_x \<rbrakk> \<Longrightarrow> diff_use_env r_s r_x = r_s"
  apply (case_tac "\<forall> x. diff_use_env r_s r_x x = r_s x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: minus_use_env_def)    
  apply (simp add: weak_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done

lemma dist_sq_diff_use_env: "diff_use_env (diff_use_env r_s r_x) r_ex = diff_use_env (diff_use_env r_s r_ex) (diff_use_env r_x r_ex)"
  apply (case_tac "\<forall> x. diff_use_env (diff_use_env r_s r_x) r_ex x = diff_use_env (diff_use_env r_s r_ex) (diff_use_env r_x r_ex) x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
     apply (case_tac "r_ex x")
       apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done

lemma neg_diff_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> neg_use_env r_x = neg_use_env (diff_use_env r_s (diff_use_env r_s r_x))"    
  apply (case_tac "\<forall> x.  neg_use_env r_x x = neg_use_env (diff_use_env r_s (diff_use_env r_s r_x)) x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma inv_diff_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> diff_use_env r_ex r_x = diff_use_env r_ex (diff_use_env r_s (diff_use_env r_s r_x))"       
  apply (cut_tac r_s="r_s" and r_x="r_x" in neg_diff_use_env)  
   apply (simp)
  apply (simp add: diff_use_env_def)
  done    

    (* - diff / add / rem lemmas *)

lemma diff_rem_use_env: "rem_use_env r_s x = diff_use_env r_s (one_use_env x OwnPerm)"    
  apply (case_tac "\<forall> x'. rem_use_env r_s x x' = diff_use_env r_s (one_use_env x OwnPerm) x'")  
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: one_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x'")
    apply (auto)
  done
    
lemma diff_add_rem_use_env: "add_use_env (diff_use_env r_s r_x) x r = diff_use_env (add_use_env r_s x r) (rem_use_env r_x x)"
  apply (case_tac "\<forall> x'. add_use_env (diff_use_env r_s r_x) x r x' = diff_use_env (add_use_env r_s x r) (rem_use_env r_x x) x'")
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
   apply (simp add: diff_use_env_def)
   apply (simp add: minus_use_env_def)
   apply (simp add: neg_use_env_def)
   apply (case_tac r)
     apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  done    
    
lemma comm_diff_rem_use_env: "rem_use_env (diff_use_env r_s r_x) x = diff_use_env (rem_use_env r_s x) r_x"
  apply (case_tac "\<forall> x'. rem_use_env (diff_use_env r_s r_x) x x' = diff_use_env (rem_use_env r_s x) r_x x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  done    
    
lemma dist_diff_rem_use_env: "rem_use_env (diff_use_env r_s r_x) x = diff_use_env (rem_use_env r_s x) (rem_use_env r_x x)" 
  apply (case_tac "\<forall> x'. rem_use_env (diff_use_env r_s r_x) x x' = diff_use_env (rem_use_env r_s x) (rem_use_env r_x x) x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  done    
    
    
    (* - comp lemmas *)  

lemma comm_comp_use_env: "comp_use_env r_s r_x = comp_use_env r_x r_s"
  apply (case_tac "\<forall> x. comp_use_env r_s r_x x = comp_use_env r_x r_s x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    

lemma cancel_comp_use_env1: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> comp_use_env r_x r_s = r_s"    
  apply (case_tac "\<forall> x. comp_use_env r_x r_s x = r_s x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma cancel_comp_use_env2: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> comp_use_env r_s r_x = r_s"    
  apply (cut_tac r_s="r_s" and r_x="r_x" in comm_comp_use_env)
  apply (simp)
  apply (rule_tac cancel_comp_use_env1)
  apply (simp)
  done    
    
lemma double_comp_use_env: "comp_use_env (comp_use_env r_s r_x) r_s = comp_use_env r_s r_x"
  apply (case_tac "\<forall> x. comp_use_env (comp_use_env r_s r_x) r_s x = comp_use_env r_s r_x x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done    
    
lemma assoc_comp_use_env: "comp_use_env r_ex (comp_use_env r_s r_x) = comp_use_env (comp_use_env r_ex r_s) r_x"
  apply (case_tac "\<forall> x. comp_use_env r_ex (comp_use_env r_s r_x) x = comp_use_env (comp_use_env r_ex r_s) r_x x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_ex x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done    

lemma shuffle_comp_use_env: "comp_use_env (comp_use_env r_s r_x) r_ex = comp_use_env (comp_use_env r_s r_ex) r_x"
  apply (case_tac "\<forall> x. comp_use_env (comp_use_env r_s r_x) r_ex x = comp_use_env (comp_use_env r_s r_ex) r_x x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
     apply (case_tac "r_ex x")
       apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done
    
lemma dist_sq_comp_use_env: "comp_use_env r_ex (comp_use_env r_s r_x) = comp_use_env (comp_use_env r_ex r_s) (comp_use_env r_ex r_x)"
  apply (case_tac "\<forall> x. comp_use_env r_ex (comp_use_env r_s r_x) x = comp_use_env (comp_use_env r_ex r_s) (comp_use_env r_ex r_x) x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_ex x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done

lemma dist_sq_comp_use_env2: "comp_use_env (comp_use_env r_s r_x) r_ex = comp_use_env (comp_use_env r_s r_ex) (comp_use_env r_x r_ex)"    
  apply (cut_tac r_s="comp_use_env r_s r_x" and r_x="r_ex" in comm_comp_use_env)  
  apply (cut_tac r_s="r_s" and r_x="r_ex" in comm_comp_use_env)  
  apply (cut_tac r_s="r_x" and r_x="r_ex" in comm_comp_use_env)
  apply (auto)
  apply (rule_tac dist_sq_comp_use_env)
  done
    
    (* - comp / add / rem lemmas *)
   
lemma add_comp_use_env: "\<lbrakk> leq_perm (r_s x) r \<rbrakk> \<Longrightarrow> add_use_env r_s x r = comp_use_env r_s (one_use_env x r)"
  apply (case_tac "\<forall> x'. add_use_env r_s x r x' = comp_use_env r_s (one_use_env x r) x'")  
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (simp add: one_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
     apply (case_tac r)
       apply (auto)
    apply (case_tac r)
      apply (auto)
   apply (case_tac r)
     apply (auto)
  apply (case_tac "r_s x'")
    apply (auto)
  done    
    
lemma dist_add_comp_use_env: "comp_use_env (add_use_env r_ex x r) (add_use_env r_s x r) = add_use_env (comp_use_env r_ex r_s) x r"    
  apply (case_tac "\<forall> xa. comp_use_env (add_use_env r_ex x r) (add_use_env r_s x r) xa = add_use_env (comp_use_env r_ex r_s) x r xa")  
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "x = xa")
   apply (auto)
  apply (case_tac r)
    apply (auto)
  done    

lemma dist_rem_comp_use_env: "rem_use_env (comp_use_env r_s r_x) x = comp_use_env (rem_use_env r_s x) (rem_use_env r_x x)"  
  apply (case_tac "\<forall> x'. rem_use_env (comp_use_env r_s r_x) x x' = comp_use_env (rem_use_env r_s x) (rem_use_env r_x x) x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
   apply (simp add: comp_use_env_def)
  apply (simp add: comp_use_env_def)
  done    
    
lemma rem_add_comp_use_env: "comp_use_env (rem_use_env r_ex x) (add_use_env r_s x r) = add_use_env (comp_use_env r_ex r_s) x r"
  apply (case_tac "\<forall> xa. comp_use_env (rem_use_env r_ex x) (add_use_env r_s x r) xa = add_use_env (comp_use_env r_ex r_s) x r xa")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = xa")
   apply (auto)
  apply (case_tac "r")
    apply (auto)
  done    
    
    (* - comp / minus lemmas *)
    
lemma dist_minus_comp_use_env: "minus_use_env (comp_use_env r_s r_x) r_ex = comp_use_env (minus_use_env r_s r_ex) (minus_use_env r_x r_ex)"
  apply (case_tac "\<forall> x. minus_use_env (comp_use_env r_s r_x) r_ex x = comp_use_env (minus_use_env r_s r_ex) (minus_use_env r_x r_ex) x")
   apply (auto)
  apply (simp add: minus_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_ex x")
    apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
     apply (case_tac "r_x x")
       apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
     apply (case_tac "r_x x")
       apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done

    (* - comp / diff lemmas *)
    
lemma diff_comp_use_env: "diff_use_env (diff_use_env r_s r_x) r_ex = diff_use_env r_s (comp_use_env r_x r_ex)"
  apply (simp add: diff_use_env_def)
  apply (cut_tac r_x="r_x" and r_ex="r_ex" in dist_neg_comp_use_env)
  apply (auto)
  apply (rule_tac minus_comp_ep_use_env)
  done    
    
lemma sum_comp_diff_use_env: "comp_use_env (diff_use_env r_ex r_x) r_x = comp_use_env r_ex r_x"    
  apply (case_tac "\<forall> x. comp_use_env (diff_use_env r_ex r_x) r_x x = comp_use_env r_ex r_x x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_ex x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done

lemma dist_diff_comp_use_env: "comp_use_env (diff_use_env r_s r_ex) (diff_use_env r_x r_ex) = diff_use_env (comp_use_env r_s r_x) r_ex"
  apply (case_tac "\<forall> x. comp_use_env (diff_use_env r_s r_ex) (diff_use_env r_x r_ex) x = diff_use_env (comp_use_env r_s r_x) r_ex x")
   apply (auto)
   apply (simp add: diff_use_env_def)
   apply (simp add: minus_use_env_def)
   apply (simp add: neg_use_env_def)
   apply (simp add: comp_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
     apply (case_tac "r_ex x")
       apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
     apply (case_tac "r_ex x")
       apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
   
lemma msum_diff_comp_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> comp_use_env r_x (diff_use_env r_s r_x) = r_s" 
  apply (case_tac "\<forall> x. comp_use_env r_x (diff_use_env r_s r_x) x = r_s x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done      
    
    (* - empty lemmas *)

lemma empty_eq_use_env: "neg_use_env empty_use_env = empty_ep_use_env"
  apply (case_tac "\<forall> x. neg_use_env empty_use_env x = empty_ep_use_env x")
   apply (auto)
  apply (simp add: neg_use_env_def)
  apply (simp add: empty_use_env_def)
  apply (simp add: empty_ep_use_env_def)
  done
    
lemma minus_empty_use_env: "minus_use_env empty_use_env r = empty_use_env"
  apply (case_tac "\<forall> x. minus_use_env empty_use_env r x = empty_use_env x")
   apply (auto)
  apply (simp add: minus_use_env_def)
  apply (simp add: empty_use_env_def)
  done
   
lemma minus_empty_ep_use_env: "minus_use_env r_s empty_ep_use_env = r_s"
  apply (case_tac "\<forall> x. minus_use_env r_s empty_ep_use_env x = r_s x")
   apply (auto)
  apply (simp add: minus_use_env_def)
  apply (simp add: empty_ep_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done      

lemma diff_empty_use_env1: "diff_use_env empty_use_env r_s = empty_use_env"
  apply (simp add: diff_use_env_def)
  apply (rule_tac minus_empty_use_env)
  done    
    
lemma diff_empty_use_env2: "diff_use_env r_s empty_use_env = r_s"    
  apply (case_tac "\<forall> x. diff_use_env r_s empty_use_env x = r_s x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: empty_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma comp_empty_use_env1: "comp_use_env empty_use_env r = r"
  apply (case_tac "\<forall> x. comp_use_env empty_use_env r x = r x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: empty_use_env_def)
  apply (case_tac "r x")
    apply (auto)
  done

lemma comp_empty_use_env2: "comp_use_env r empty_use_env = r"
  apply (case_tac "\<forall> x. comp_use_env r empty_use_env x = r x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: empty_use_env_def)
  apply (case_tac "r x")
    apply (auto)
  done

lemma comp_empty_use_env: "empty_use_env = comp_use_env empty_use_env empty_use_env" 
  apply (case_tac "\<forall> x. empty_use_env x = comp_use_env empty_use_env empty_use_env x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: empty_use_env_def)
  done  
    
end