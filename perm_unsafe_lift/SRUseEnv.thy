theory SRUseEnv
  imports ReduceWTS DerefVars
begin
  (*
fun safe_act where
  "safe_act s NoAct = True"
| "safe_act s (MakeAct x) = (s x = None)"
| "safe_act s (UseAct x) = True"  

lemma safe_act_well_typed_app: "\<lbrakk> well_typed env r_s1 e1 tau r_s2 rx; app_red_exp (s1, e1) ax (s2, e2) \<rbrakk> \<Longrightarrow> safe_act s1 ax"    
  apply (case_tac e1)
       apply (auto)
   apply (case_tac ax)
     apply (auto)
   apply (case_tac ax)
     apply (auto)
    (* if case *)
   apply (case_tac x41)
        apply (auto)
   apply (case_tac x1)
                apply (auto)
   apply (case_tac x3)
    apply (auto)
    (* case analysis on constants for make action *)
  apply (case_tac x61)
       apply (auto)
    apply (case_tac x1)
                 apply (auto)
     apply (case_tac x62)
          apply (auto)
    apply (simp add: fresh_var_def)
    (* case analysis for op *)
   apply (case_tac x62)
        apply (auto)
    (* case analysis for pair creation *)
  apply (case_tac x61a)
       apply (auto)
  apply (case_tac x1)
               apply (auto)
  apply (simp add: fresh_var_def)
  done
    *)

  
  (* ###### constructive permission definitions.
      the idea here is that i want to constructively state which permissions are being consumed.
      the difficult part is that because the "permissions consumed" involves 
  *)
  (*
definition intro_use_env where
  "intro_use_env r_s trs = (\<lambda> x. if x \<in> trs then UsePerm else r_s x)"  
  
definition elim_use_env where  
  "elim_use_env r_s cs = (\<lambda> x. if x \<in> cs then NoPerm else r_s x)"*)
(*
fun red_env where
  "red_env env e tau NoAct = env"
| "red_env env e tau (MakeAct x) = add_env env x tau"  
| "red_env env e tau (UseAct x) = (if x \<notin> free_vars e then rem_env env x else env)" 
  *)
    
datatype gen_act =
  NoResAct
  | AddResAct string p_type perm_use_env
  | Add2ResAct string string p_type
  | ReadResAct
  | WriteResAct string perm_use_env
    
fun red_env where
  "red_env env NoResAct = env"
| "red_env env (AddResAct x tau r_s) = add_env env x tau"
| "red_env env (Add2ResAct x1 x2 tau) = add_env (add_env env x1 (ChanTy tau SEnd)) x2 (ChanTy tau REnd)"
| "red_env env ReadResAct = env"
| "red_env env (WriteResAct x r_s) = env"
  (*
fun full_red_use_env where
  "full_red_use_env r_s NoResAct = r_s"
  (* remove resources used to create the value, add the new perm *)
| "full_red_use_env r_s (AddResAct x tau r_s') = add_use_env r_s x OwnPerm"  
| "full_red_use_env r_s ReadResAct = r_s"*)

fun exp_red_use_env where
  "exp_red_use_env r_s NoResAct = r_s"
  (* remove resources used to create the value, add the new perm *)
| "exp_red_use_env r_s (AddResAct x tau r_s') = add_use_env r_s x OwnPerm"
| "exp_red_use_env r_s (Add2ResAct x1 x2 tau) = add_use_env (add_use_env r_s x1 OwnPerm) x2 OwnPerm"
| "exp_red_use_env r_s ReadResAct = r_s"  
| "exp_red_use_env r_s (WriteResAct x r_s') = (diff_use_env r_s r_s')"
  
fun end_red_use_env where  
  "end_red_use_env r_s (WriteResAct x r_s') = (diff_use_env r_s r_s')"
| "end_red_use_env r_s r_ax = r_s"
    
  (* if this is the resource's last use, remove it. otherwise add the resources given *)
(*| "red_use_env r_s (UseAct x) = r_s"*) (*
  (*let r_s' = elim_use_env r_s trs in*)
  (if x \<notin> free_vars e then rem_use_env r_s x else r_s))"*)
  
  (*
fun red_res_map where
  "red_res_map rs_map NoResAct = rs_map"  
| "red_res_map rs_map (AddResAct x tau r_s) = add_mem rs_map x r_s"
| "red_res_map rs_map ReadResAct = rs_map"
  *)
  
fun red_nres_map where
  "red_nres_map rs_map NoResAct = rs_map"  
| "red_nres_map rs_map (AddResAct x tau r_s) = add_env rs_map x r_s"
| "red_nres_map rs_map (Add2ResAct x1 x2 tau) = add_env (add_env rs_map x1 empty_use_env) x2 empty_use_env"
| "red_nres_map rs_map ReadResAct = rs_map"
| "red_nres_map rs_map (WriteResAct x r_s) = add_env rs_map x (comp_use_env (nres_lookup rs_map x) r_s)"
  
fun safe_act where
  "safe_act s r_s NoResAct = True"
| "safe_act s r_s (AddResAct x tau r_x) = (s x = None \<and> leq_use_env r_x r_s)"
| "safe_act s r_s (Add2ResAct x1 x2 tau) = (s x1 = None \<and> s x2 = None \<and> x1 \<noteq> x2)"
| "safe_act s r_s ReadResAct = True"
| "safe_act s r_s (WriteResAct x r_x) = (s x \<noteq> None \<and> leq_use_env r_x r_s)"
  
fun corr_act where
  "corr_act ax NoResAct = (ax = NoAct)"
| "corr_act ax (AddResAct x tau r_s) = (ax = MakeAct x)"
| "corr_act ax (Add2ResAct x1 x2 tau) = (ax = Mk2Act x1 x2)"
| "corr_act ax ReadResAct = (\<exists> x. ax = UseAct x)"
| "corr_act ax (WriteResAct x r_s) = (\<exists> x. ax = UseAct x)"  
  
    
lemma leq_safe_act: "\<lbrakk> safe_act s r_x g_ax; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> safe_act s r_s g_ax"    
  apply (case_tac g_ax)
      apply (auto)
   apply (rule_tac r_sb="r_x" in trans_leq_use_env)
    apply (auto)
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (auto)
  done  
  
  (*
definition valid_reduct where
  "valid_reduct r_exp = (\<forall> are s1 rs_map env r_c r_s1 e1 tau r_s2 rx ax s2 e2. (
    r_exp are (s1, e1) ax (s2, e2) \<and> well_typed env r_s1 e1 tau r_s2 rx \<and>
    well_typed_state s1 env rs_map \<and> valid_use_env s1 rs_map r_c r_s1) \<longrightarrow>
    (\<exists> g_ax. well_typed (red_env env g_ax) (exp_red_use_env r_s1 g_ax) e2 tau r_s2 rx \<and>
      well_typed_state s2 (red_env env g_ax) (red_res_map rs_map g_ax) \<and>
      valid_use_env s2 (red_res_map rs_map g_ax) (full_red_use_env r_c g_ax) (exp_red_use_env r_s1 g_ax) \<and> safe_act s1 g_ax \<and> corr_act ax g_ax)
  )"   *)
  
definition valid_reduct where
  "valid_reduct r_exp = (\<forall> are s1 rs_map env r_f r_s1 e1 tau r_s2 rx ax s2 e2. (
    r_exp are (s1, e1) ax (s2, e2) \<and> well_typed env r_s1 e1 tau r_s2 rx \<and> proper_exp rs_map e1 \<and>
    well_typed_state s1 env rs_map \<and> valid_exp_use_env s1 rs_map r_f \<and> leq_use_env r_s1 r_f) \<longrightarrow>
    (\<exists> g_ax. well_typed (red_env env g_ax) (exp_red_use_env r_s1 g_ax) e2 tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
      proper_exp (red_nres_map rs_map g_ax) e2 \<and> well_typed_state s2 (red_env env g_ax) (red_nres_map rs_map g_ax) \<and>
      valid_exp_use_env s2 (red_nres_map rs_map g_ax) (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax)
  )"  
  

  (*
lemma wtddp2_np_var: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; x \<in> non_prim_vars env e; rx x = NoPerm \<rbrakk> \<Longrightarrow> r_s2 x \<noteq> OwnPerm"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
       apply (auto)
    (* const + op cases *)
       apply (simp add: non_prim_vars_def)
      apply (simp add: non_prim_vars_def)
    (* var case *)
     apply (cut_tac r_s="diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau) r_ex)" and r_x="r_s2" and x="x" in leq_use_no_own)
       apply (cut_tac r_s="r_s1" and r_x="ereq_use_env x1a tau" and r_ex="comp_use_env (ereq_use_env x1a tau) r_ex" and x="x" in diff_use_none)
         apply (simp add: ereq_use_env_def)
         apply (simp add: one_use_env_def)
         apply (simp add: non_prim_vars_def)
         apply (simp add: non_prim_entry_def)
         apply (simp add: end_req_perm_def)
         apply (case_tac "req_type tau")
           apply (auto)
     apply (rule_tac r_s="rx" in leq_use_none)
      apply (simp_all)
    (* if case *)
    apply (case_tac "x \<notin> free_vars (IfExp e1 e2 e3)")
     apply (simp add: non_prim_vars_def)
    apply (auto)
      apply (case_tac "x \<notin> non_prim_vars env e1")
       apply (simp add: non_prim_vars_def)
      apply (rule_tac r_s="r_s2a" in leq_use_none)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
    *)
    
    (*
    **** right now the issue is that vars from rx1 might still appear within e, even if they're owned - for instance, if a
      var is used in a location that doesn't contribute to the reqs of the final result ()

    (* - the idea is that if rx1 has an ownership, it means rx2 is None. if rx2 is None, but x is a non-prim var, it must have been
        subtracted out, meaning it cannot be in r_s2, which is a contradiction. *)
lemma well_typed_disj_diff_perms2: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx2; disj_use_env rx1 rx2; leq_use_env rx1 r_s2 \<rbrakk> \<Longrightarrow>
  well_typed env (diff_use_env r_s1 rx1) e tau (diff_use_env r_s2 rx1) (diff_use_env rx2 rx1)"      
  apply (rule_tac well_typed_diff_perms)
   apply (auto)
    *)
    
    

     
  
lemma red_contain_env: "\<lbrakk> safe_act s r_s g_ax; sub_env s env \<rbrakk> \<Longrightarrow> contain_env (red_env env g_ax) env"
  apply (case_tac g_ax)
      apply (auto)
      apply (rule_tac id_contain_env)
     apply (rule_tac add_contain_env)
     apply (simp add: sub_env_def)
    apply (rule_tac env_b="add_env env x31 (ChanTy x33 SEnd)" in trans_contain_env)
     apply (rule_tac add_contain_env)
     apply (simp add: add_env_def)
     apply (simp add: sub_env_def)
    apply (rule_tac add_contain_env)
    apply (simp add: sub_env_def)
   apply (rule_tac id_contain_env)
  apply (rule_tac id_contain_env)
  done  
(*
lemma exp_red_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (exp_red_use_env r_s g_ax)"    
  apply (case_tac g_ax)
     apply (auto)
   apply (rule_tac rhs_add_leq_use_env)
    apply (simp)
   apply (case_tac "r_x x21")
     apply (auto)
  done       *)
    
    
  (*
fun end_red_use_env where
  "end_red_use_env r_s e (UseAct x) = (if x \<notin> free_vars e then rem_use_env r_s x else r_s)"
| "end_red_use_env r_s e ax = r_s"    *)
  
  (*
fun red_res_map where
  "red_res_map rs_map e NoAct = rs_map"
| "red_res_map rs_map e (MakeAct x cs) = (add_mem rs_map x (intro_use_env empty_use_env cs))"  
| "red_res_map rs_map e (UseAct x trs) = (add_mem rs_map x (intro_use_env (lookup_res rs_map x) trs))"    
  *)
  (*
lemma ignore_elim_use_env: "elim_use_env r_s {} = r_s"    
  apply (simp add: elim_use_env_def)
  done

lemma elim_sub_use_env: "\<lbrakk> sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_use_env s (elim_use_env r_s cs)"
  apply (simp add: sub_use_env_def)
  apply (simp add: elim_use_env_def)
  done        
 
lemma add_elim_leq_use_env: "leq_use_env (elim_use_env (add_use_env r_s x r) cs) (add_use_env (elim_use_env r_s cs) x r)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: elim_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
   apply (case_tac r)
     apply (auto)
  apply (case_tac "r_s xa")
    apply (auto)
  done
 
lemma diff_elim_leq_use_env: "leq_use_env (diff_use_env (elim_use_env r_s cs) r_x) (elim_use_env (diff_use_env r_s r_x) cs)"      
  apply (simp add: leq_use_env_def)
  apply (simp add: elim_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma self_elim_leq_use_env: "leq_use_env (elim_use_env r_s cs) r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: elim_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma elim_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (elim_use_env r_x cs) r_s"    
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_elim_leq_use_env)
  done 
  
lemma dist_elim_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (elim_use_env r_x cs) (elim_use_env r_s cs)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: elim_use_env_def)
  done    
    (*
lemma diff_elim_use_env: "elim_use_env r_s cs = diff_use_env r_s (intro_use_env empty_use_env cs)"    
  apply (case_tac "\<forall> x. elim_use_env r_s cs x = diff_use_env r_s (intro_use_env empty_use_env cs) x")
   apply (auto)
  apply (simp add: elim_use_env_def)
  apply (simp add: intro_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (case_tac "x \<in> cs")
   apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (simp add: empty_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done
  
lemma rhs_unroll_elim_use_env: "\<lbrakk> leq_use_env r_x (elim_use_env r_s cs) \<rbrakk> \<Longrightarrow> leq_use_env r_x (diff_use_env r_s (intro_use_env empty_use_env cs))"    
  apply (cut_tac r_s="r_s" and cs="cs" in diff_elim_use_env)  
  apply (auto)
  done
 
lemma lhs_unroll_elim_use_env: "\<lbrakk> leq_use_env (elim_use_env r_x cs) r_s \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x (intro_use_env empty_use_env cs)) r_s"    
  apply (cut_tac r_s="r_x" and cs="cs" in diff_elim_use_env)  
  apply (auto)
  done 
 
lemma rhs_fold_elim_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env (diff_use_env r_s (intro_use_env empty_use_env cs)) r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env (elim_use_env r_s cs) r_ex)"    
  apply (cut_tac r_s="r_s" and cs="cs" in diff_elim_use_env)  
  apply (auto)
  done
 
lemma lhs_fold_elim_use_env: "\<lbrakk> leq_use_env (diff_use_env (diff_use_env r_x (intro_use_env empty_use_env cs)) r_ex) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (elim_use_env r_x cs) r_ex) r_s"    
  apply (cut_tac r_s="r_x" and cs="cs" in diff_elim_use_env)  
  apply (auto)
  done     *)
   
lemma mini_disj_intro_union_env: "\<lbrakk> mini_disj_use_env (intro_use_env r_x s1) r_s; mini_disj_use_env (intro_use_env empty_use_env s2) r_s \<rbrakk> \<Longrightarrow>
  mini_disj_use_env (intro_use_env r_x (s1 \<union> s2)) r_s"    
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: intro_use_env_def)
  done
    *)  
    
    
    (* ##### safe-reduction specific validity lemmas ##### *)
  
lemma red_sep_nres_map: "\<lbrakk> p_map u = Some r_s; disj_nres_map p_map; sub_nres_map s1 p_map;
  safe_act s1 r_s g_ax; sub_use_env s1 r_s \<rbrakk> \<Longrightarrow> sep_nres_map (exp_red_use_env r_s g_ax) (rem_env p_map u)"
  apply (simp add: sep_nres_map_def)
  apply (auto)
    (* we dont have to check x = u, since u has been removed from the map *)
  apply (case_tac "u = x")
   apply (auto)
   apply (simp add: nres_lookup_def)
   apply (simp add: rem_env_def)
   apply (rule_tac empty_strong_disj_use_env2)
    (* otherwise, the lookup is the same as it was in p_map *)
  apply (cut_tac rs_map="p_map" and x="u" and y="x" in nres_rem_diff)
   apply (auto)
    (* from here we do case analysis on the possible ways that r_s has been modified *)
    (* if it has not been modified the case is simple *)
  apply (case_tac "exp_red_use_env r_s g_ax = r_s")
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="u" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (simp add: nres_lookup_def)
    (* make case: if x21 has been added, the rest of r_s is disjoint from p_map x *)
  apply (case_tac g_ax)
     apply (auto)
    apply (rule_tac add_strong_disj_use_env)
     apply (simp add: disj_nres_map_def)
     apply (erule_tac x="u" in allE)
     apply (erule_tac x="x" in allE)
     apply (auto)
     apply (simp add: nres_lookup_def)
    (* now we have to prove that x21 was not in p_map, which should be true since p_map is sub-ordinate to s *)
    apply (case_tac "p_map x")
     apply (simp add: nres_lookup_def)
     apply (simp add: empty_use_env_def)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="x" in allE)
    apply (simp add: sub_use_env_def)
    (* make 2 case: start by assuming we have p_map x *)
   apply (case_tac "p_map x")
    apply (simp add: nres_lookup_def)
    apply (rule_tac empty_strong_disj_use_env2)
    (* otherwise, prove r_s disjoint from p_map x *)
   apply (rule_tac add_strong_disj_use_env)
    apply (rule_tac add_strong_disj_use_env)
     apply (simp add: disj_nres_map_def)
     apply (erule_tac x="u" in allE)
     apply (erule_tac x="x" in allE)
     apply (auto)
     apply (simp add: nres_lookup_def)
    (* after this, prove x31 / x32 do not appear in p_map x *)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="x" in allE)
    apply (simp add: sub_use_env_def)
   apply (simp add: sub_nres_map_def)
   apply (erule_tac x="x" in allE)
   apply (simp add: sub_use_env_def)
    (* write case: otherwise, x42 was removed from r_s, so disjointness should be simple *)
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env1)
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="u" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (simp add: nres_lookup_def)
  apply (rule_tac self_diff_leq_use_env)
  done  


    
lemma red_sep_nres_map2: "\<lbrakk> p_map v = Some r_p; p_map u = Some r_s; u \<noteq> v; disj_nres_map p_map;
  safe_act s1 r_s g_ax; sep_nres_map r_p rs_map \<rbrakk> \<Longrightarrow> sep_nres_map r_p (red_nres_map rs_map g_ax)"    
  apply (case_tac g_ax)
      apply (auto)
    (* make case *)
    apply (rule_tac add_sep_nres_map)
     apply (simp)
    apply (rule_tac r_s="r_s" in strong_disj_leq_use_env2)
     apply (simp add: disj_nres_map_def)
     apply (auto)
    apply (erule_tac x="v" in allE)
    apply (erule_tac x="u" in allE)
    apply (simp add: nres_lookup_def)
    (* make 2 case *)
   apply (rule_tac add_sep_nres_map)
    apply (rule_tac add_sep_nres_map)
     apply (simp)
    apply (rule_tac empty_strong_disj_use_env2)
   apply (rule_tac empty_strong_disj_use_env2)
    (* write case *)
  apply (rule_tac add_sep_nres_map)
   apply (simp)
  apply (rule_tac strong_disj_comp_use_env1)
   apply (simp add: sep_nres_map_def)
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env2)
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="v" in allE)
   apply (erule_tac x="u" in allE)
   apply (simp add: nres_lookup_def)
  apply (simp)
  done    
  
end