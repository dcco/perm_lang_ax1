theory DerefVars
  imports SafeSubRename
begin

fun deref_pairs where
  "deref_pairs (ConstExp c) = {}"
| "deref_pairs (OpExp xop) = {}"
| "deref_pairs (VarExp x a) = (case a of
    OtherRef y \<Rightarrow> {(x, y)}
    | r \<Rightarrow> {}
  )"  
| "deref_pairs (PairExp e1 e2) = (deref_pairs e1 \<union> deref_pairs e2)"
| "deref_pairs (IfExp e1 e2 e3) = (deref_pairs e1 \<union> deref_pairs e2 \<union> deref_pairs e3)"
| "deref_pairs (LamExp x e) = deref_pairs e"  
| "deref_pairs (AppExp e1 e2) = (deref_pairs e1 \<union> deref_pairs e2)"  
  
    (* ##### given a perm set, we derive its "resource completion" by taking all of the resources that are reachable from it.
        in other words, for each permission z in s, we lookup its resource map, and take all of the resources in it, as well
        as recursing on each resource. #####
     *)  
  
fun path_lookup where
  "path_lookup rs_map z Nil x = (z = x)"
| "path_lookup rs_map z (y # t) x = (case rs_map z of
    None \<Rightarrow> False
    | Some r_s \<Rightarrow> r_s y \<noteq> NoPerm \<and> path_lookup rs_map y t x
  )"    

fun complete_vars where
  "complete_vars rs_map s = { x | x. \<exists> l z. z \<in> s \<and> path_lookup rs_map z l x}"

lemma path_lookup_parent: "\<lbrakk> l \<noteq> Nil; path_lookup rs_map z l x; valid_nres_map s rs_map \<rbrakk> \<Longrightarrow>
  (\<exists> l' y r_s. path_lookup rs_map z l' y \<and> rs_map y = Some r_s \<and> r_s x \<noteq> NoPerm )"
  apply (induct l arbitrary: z)
   apply (auto)
  apply (case_tac "rs_map z")
   apply (auto)
    (* case where we have reached x *)
  apply (case_tac "a = x")
   apply (rule_tac x="Nil" in exI)
   apply (auto)
    (* otherwise, induct *)
  apply (case_tac "l = []")
   apply (auto)
  apply (case_tac "\<exists>l' y. path_lookup rs_map a l' y \<and> (\<exists>r_s. rs_map y = Some r_s \<and> r_s x \<noteq> NoPerm)")
   apply (erule_tac exE)
   apply (auto)
  apply (rule_tac x="a # l'" in exI)
  apply (auto)
  done
    
    (* ##### proper expressions ##### *)
  
definition proper_exp where
  "proper_exp rs_map e = (\<forall> x y. (x, y) \<in> deref_pairs e \<longrightarrow> (\<exists> l. path_lookup rs_map x l y))"

lemma proper_pair: "\<lbrakk> proper_exp rs_map (PairExp e1 e2) \<rbrakk> \<Longrightarrow> proper_exp rs_map e1 \<and> proper_exp rs_map e2"  
  apply (simp add: proper_exp_def)
  done

lemma proper_if: "\<lbrakk> proper_exp rs_map (IfExp e1 e2 e3) \<rbrakk> \<Longrightarrow> proper_exp rs_map e1 \<and> proper_exp rs_map e2 \<and> proper_exp rs_map e3"  
  apply (simp add: proper_exp_def)
  done    

lemma proper_app: "\<lbrakk> proper_exp rs_map (AppExp e1 e2) \<rbrakk> \<Longrightarrow> proper_exp rs_map e1 \<and> proper_exp rs_map e2"  
  apply (simp add: proper_exp_def)
  done
    
lemma proper_subst_exp: "\<lbrakk> proper_exp rs_map e; proper_exp rs_map e'; x \<notin> ref_vars e \<rbrakk> \<Longrightarrow> proper_exp rs_map (subst_exp e x e')"
  apply (induct e)
        apply (auto)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
     apply (auto)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
 
lemma proper_alpha_rename: "\<lbrakk> proper_exp rs_map e; a \<notin> ref_vars e \<rbrakk> \<Longrightarrow> proper_exp rs_map (deep_alpha_rename e a b)"    
  apply (induct e)
        apply (auto)
       apply (simp add: proper_exp_def)
       apply (auto)
       apply (case_tac x2a)
         apply (auto)
      apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
       apply (auto)
      apply (simp add: proper_exp_def)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
    
lemma proper_lam_var_remove_ex: "\<lbrakk> proper_exp rs_map e; well_typed env r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow> proper_exp rs_map (lam_var_remove e a b)"      
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
      apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
       apply (auto)
      apply (simp add: proper_exp_def)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (cut_tac rs_map="rs_map" and e="e" and a="a" and b="b" in proper_alpha_rename)
      apply (simp add: proper_exp_def)
     apply (simp)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
    
  
lemma proper_lam_var_remove: "\<lbrakk> proper_exp rs_map e; a \<notin> ref_vars e \<rbrakk> \<Longrightarrow> proper_exp rs_map (lam_var_remove e a b)"   
  apply (induct e)
        apply (auto)
      apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
       apply (auto)
      apply (simp add: proper_exp_def)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (cut_tac rs_map="rs_map" and e="e" and a="a" and b="b" in proper_alpha_rename)
      apply (simp add: proper_exp_def)
     apply (simp)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
      
lemma lam_var_remove_eq: "\<lbrakk> a \<notin> lam_vars e \<rbrakk> \<Longrightarrow> lam_var_remove e a b = e"    
  apply (induct e)
        apply (auto)
  done
  
lemma proper_lvlr_ex: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; proper_exp rs_map e; unique_post_vars vl;
  post_vars vl \<inter> (free_vars e \<union> lam_vars e \<union> ref_vars e) = {} \<rbrakk> \<Longrightarrow> proper_exp rs_map (lam_var_list_remove e vl)"   
  apply (induct vl arbitrary: e)
   apply (auto)
  (*apply (case_tac "a \<notin> lam_vars e")
   apply (simp add: lam_var_remove_eq)*)
  apply (cut_tac rs_map="rs_map" and e="e" and a="a" and b="b" in proper_lam_var_remove_ex)
    apply (auto)
    (* we have to prove that the post vars are still disjoint from the lam_vars / ref_vars, which is true since
        the only new lam_var is b, which must be disjoint from the rest of the post_var list *)
  apply (case_tac "post_vars vl \<inter> (free_vars (lam_var_remove e a b) \<union> lam_vars (lam_var_remove e a b) \<union> ref_vars (lam_var_remove e a b)) \<noteq> {}")
   apply (auto)
     apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_free_var_none)
      apply (auto)
    apply (case_tac "x = b")
     apply (auto)
    apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_lam_var_none)
      apply (auto)
   apply (case_tac "x = b")
    apply (auto)
   apply (cut_tac z="x" and e="e" and x="a" and y="b" in lam_var_remove_ref_vars)
     apply (auto)
    (* the last part of the induction is to prove that e is still well-typed *)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and x="a" and y="b" in lam_var_remove_type_preserve)
      apply (auto)
  done
    
    (* this lemma is predicated on the idea that after a lam_var_list removal, no new deref_pairs will be introduced.
        the intuition is that lvlr only changes lam_vars, and lam_vars don't overlap with ref_vars or free_vars,
        meaning they will not affect any deref_pairs.
    *)(*
lemma proper_lvlr: "\<lbrakk> proper_exp rs_map e; unique_post_vars vl; post_vars vl \<inter> (lam_vars e \<union> ref_vars e) = {};
  lam_vars e \<inter> ref_vars e = {} \<rbrakk> \<Longrightarrow> proper_exp rs_map (lam_var_list_remove e vl)"    
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (case_tac "a \<notin> lam_vars e")
   apply (simp add: lam_var_remove_eq)
  apply (cut_tac rs_map="rs_map" and e="e" and a="a" and b="b" in proper_lam_var_remove)
    apply (auto)
    (* we have to prove that the post vars are still disjoint from the lam_vars / ref_vars, which is true since
        the only new lam_var is b, which must be disjoint from the rest of the post_var list *)
  apply (case_tac "post_vars vl \<inter> (lam_vars (lam_var_remove e a b) \<union> ref_vars (lam_var_remove e a b)) \<noteq> {}")
   apply (auto)
    apply (case_tac "x = b")
     apply (auto)
    apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_lam_var_none)
      apply (auto)
   apply (case_tac "x = b")
    apply (auto)
   apply (cut_tac z="x" and e="e" and x="a" and y="b" in lam_var_remove_ref_vars)
     apply (auto)
  apply (case_tac "lam_vars (lam_var_remove e a b) \<inter> ref_vars (lam_var_remove e a b) = {}")
   apply (auto)
    (* the main challenge of this lemma is proving that after each renaming, the lam_vars and ref_vars remain disjoint.
        - say that such an x was in the lam_vars e, but not in the ref_vars e. *)
  apply (case_tac "x \<in> lam_vars e")
    (* - we know that x \<noteq> b by post_var disjointness.
      then we can know that x \<in> ref_vars e, since otherwise x \<notin> ref_vars (lam_var_remove e a b) *)
   apply (case_tac "x \<noteq> b")
    apply (case_tac "x \<notin> ref_vars e")
     apply (cut_tac z="x" and e="e" and x="a" and y="b" in lam_var_remove_ref_vars)
       apply (auto)
    (* otherwise, x \<notin> lam_vars e. say that x \<noteq> b. then x \<notin> lam_vars (lam_var_remove e a b) either *)
  apply (case_tac "x \<noteq> b")
   apply (cut_tac e="e" and x="x" and a="a" and b="b" in lam_var_remove_lam_var_none)
     apply (auto)
  apply (case_tac "a \<notin> ref_vars e")
   apply (cut_tac y="b" and e="e" and x="a" in lam_var_remove_ref_vars2)
     apply (auto)
  done*)
  
lemma proper_safe_subst_exp: "\<lbrakk> proper_exp rs_map e; well_typed env r_s1 e tau r_s2 rx;
  proper_exp rs_map e'; safe_subst_exp e x e' e_f \<rbrakk> \<Longrightarrow> proper_exp rs_map e_f"    
  apply (simp add: safe_subst_exp_def)
  apply (auto)
  apply (rule_tac proper_subst_exp)
    apply (rule_tac proper_lvlr_ex)
       apply (auto)
    (* we have to prove that x is not a ref var of the final result *)
  apply (cut_tac x="x" and e="e" and vl="vl" in lam_var_list_remove_ref_var)
      apply (auto)
  apply (simp add: disj_vars_def)
  apply (auto)
  done

end