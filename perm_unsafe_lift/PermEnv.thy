theory PermEnv
  imports Main
begin
  
    (* 
      ####################################
        P1. permission definitions
      ####################################
    *)  
  
datatype p_perm = NoPerm | UsePerm | OwnPerm  

datatype ext_perm = NoEP | DiffEP | OwnEP    
  
fun leq_perm where
  "leq_perm UsePerm NoPerm = False"
| "leq_perm OwnPerm NoPerm = False"
| "leq_perm OwnPerm UsePerm = False"
| "leq_perm p1 p2 = True"
 
fun minus_ep where
  "minus_ep NoPerm p = NoPerm"
| "minus_ep UsePerm OwnEP = NoPerm"
| "minus_ep UsePerm p = UsePerm"
| "minus_ep OwnPerm OwnEP = NoPerm"
| "minus_ep OwnPerm DiffEP = UsePerm"
| "minus_ep OwnPerm p = OwnPerm"
  
fun union_ep where
  "union_ep OwnPerm p = OwnPerm"
| "union_ep UsePerm OwnEP = OwnPerm"
| "union_ep UsePerm DiffEP = OwnPerm"
| "union_ep UsePerm p = UsePerm"
| "union_ep NoPerm OwnEP = OwnPerm"
| "union_ep NoPerm DiffEP = UsePerm"
| "union_ep NoPerm NoEP = NoPerm"
  
fun union_perm where
  "union_perm OwnPerm p = OwnPerm"
| "union_perm p OwnPerm = OwnPerm"
| "union_perm NoPerm NoPerm = NoPerm"
| "union_perm p1 p2 = UsePerm"      
  
    (* 
      ####################################
        P2.
      ####################################
    *)    
  
type_synonym perm_use_env = "string \<Rightarrow> p_perm"  

type_synonym ep_use_env = "string \<Rightarrow> ext_perm"  
  
definition empty_use_env where
  "empty_use_env x = NoPerm"
  
definition add_use_env where
  "add_use_env env x p = (\<lambda> x'. if x = x' then p else env x')"

definition rem_use_env where
  "rem_use_env env x = (\<lambda> x'. if x = x' then NoPerm else env x')"  
  
definition leq_use_env where
  "leq_use_env env1 env2 = (\<forall> x. leq_perm (env1 x) (env2 x))"  

   (* shift related functions *)
  
definition one_use_env where
  "one_use_env x r = (\<lambda> x'. if x = x' then r else NoPerm)"    
  
fun neg_perm where
  "neg_perm OwnPerm = OwnEP"
| "neg_perm p = NoEP"
  
definition neg_use_env where
  "neg_use_env env = (\<lambda> x. neg_perm (env x))"
  
definition empty_ep_use_env where
  "empty_ep_use_env x = NoEP"
  
definition minus_use_env where
  "minus_use_env env1 env2 = (\<lambda> x. minus_ep (env1 x) (env2 x))"  
  
definition diff_use_env where
  "diff_use_env env1 env2 = minus_use_env env1 (neg_use_env env2)"  
  
definition comp_use_env where
  "comp_use_env r_s1 r_s2 = (\<lambda> x. union_perm (r_s1 x) (r_s2 x))"  

definition mini_disj_use_env where     
  "mini_disj_use_env r_s r_ex = (\<forall> x. r_s x = OwnPerm \<longrightarrow> r_ex x = NoPerm)"    
  
definition disj_use_env where
  "disj_use_env r_s1 r_s2 = (mini_disj_use_env r_s1 r_s2 \<and> mini_disj_use_env r_s2 r_s1)"
 
definition weak_use_env where
  "weak_use_env r_s = (\<forall> x. r_s x \<noteq> OwnPerm)"   
 
definition is_own where
  "is_own r = (r = OwnPerm)"  
  
    (* #### no perm lemmas #### *)
    
    (* - none lemmas *)
  
lemma leq_use_none: "\<lbrakk> leq_use_env r_x r_s; r_s x = NoPerm \<rbrakk> \<Longrightarrow> r_x x = NoPerm"    
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done  
  
lemma add_use_none_rev: "\<lbrakk> r_s x = NoPerm ; x \<noteq> y \<rbrakk> \<Longrightarrow> add_use_env r_s y r x = NoPerm"
  apply (simp add: add_use_env_def)
  done    

lemma minus_use_none_infer: "\<lbrakk> minus_use_env r_s r_ex x = NoPerm; r_s x \<noteq> NoPerm \<rbrakk> \<Longrightarrow> minus_use_env r_x r_ex x = NoPerm"
  apply (simp add: minus_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done

lemma diff_use_none_infer: "\<lbrakk> r_x x = OwnPerm; diff_use_env r_x r_ex x \<noteq> OwnPerm \<rbrakk> \<Longrightarrow> diff_use_env r_s r_ex x = NoPerm"    
  apply (simp add: diff_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (case_tac "r_ex x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done

lemma diff_use_none: "\<lbrakk> r_x x \<noteq> NoPerm; diff_use_env r_x r_ex x = NoPerm \<rbrakk> \<Longrightarrow> diff_use_env r_s r_ex x = NoPerm"    
  apply (simp add: diff_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma diff_use_none_ex: "\<lbrakk> r_ex x = OwnPerm \<rbrakk> \<Longrightarrow> diff_use_env r_s r_ex x = NoPerm"    
  apply (simp add: diff_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done        
    
lemma comp_use_none: "\<lbrakk> r_sa x = NoPerm; r_sb x = NoPerm \<rbrakk> \<Longrightarrow> comp_use_env r_sa r_sb x = NoPerm"    
  apply (simp add: comp_use_env_def)
  done       
    
lemma comp_use_none_both: "\<lbrakk> comp_use_env r_sa r_sb x = NoPerm \<rbrakk> \<Longrightarrow> r_sa x = NoPerm \<and> r_sb x = NoPerm"    
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_sa x")
    apply (auto)
   apply (case_tac "r_sb x")
     apply (auto)
  apply (case_tac "r_sb x")
    apply (auto)
  done  
    
    (* - no own lemmas *)
  
lemma leq_use_no_own: "\<lbrakk> r_s x \<noteq> OwnPerm; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> r_x x \<noteq> OwnPerm"
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma comp_use_no_own_both: "\<lbrakk> comp_use_env r_sa r_sb x \<noteq> OwnPerm \<rbrakk> \<Longrightarrow> r_sa x \<noteq> OwnPerm \<and> r_sb x \<noteq> OwnPerm"   
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (case_tac "r_sa x")
    apply (auto)
  done    
    
lemma diff_use_no_own: "\<lbrakk> diff_use_env r_s r_ex x \<noteq> NoPerm \<rbrakk> \<Longrightarrow> r_ex x \<noteq> OwnPerm"    
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (case_tac "r_ex x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
    (* - own lemmas *)

lemma leq_use_own: "\<lbrakk> r_x x = OwnPerm; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> r_s x = OwnPerm"
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
 
lemma diff_use_own: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s; r_x x \<noteq> NoPerm; r_s x = NoPerm \<rbrakk> \<Longrightarrow> r_ex x = OwnPerm"    
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done    
    
   (* - eq lemmas *) 
    
lemma diff_use_eq: "\<lbrakk> r_x x \<noteq> OwnPerm \<rbrakk> \<Longrightarrow> diff_use_env r_s r_x x = r_s x"  
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done

    (* - fundamental lemmas *)

lemma spec_leq_perm: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_perm (r_x x) (r_s x)"    
  apply (simp add: leq_use_env_def)
  done    

    (* - leq lemmas *)
    
lemma diff_use_leq: "\<lbrakk> r_ex x \<noteq> OwnPerm; leq_use_env (diff_use_env r_x r_ex) r_s \<rbrakk> \<Longrightarrow> leq_perm (r_x x) (r_s x)"
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done

lemma diff_use_leq2: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex); r_ex x \<noteq> OwnPerm \<rbrakk> \<Longrightarrow> leq_perm (r_x x) (r_s x)"    
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (case_tac "r_ex x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
end
  