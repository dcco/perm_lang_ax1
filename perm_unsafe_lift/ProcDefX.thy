theory ProcDefX
  imports ResMapValid ProcHoleVars
begin
  
    (*
      ###### 1. defining well-typed process set ######
    *)
  
type_synonym proc_set = "p_exp gen_env"

definition well_typed_proc_set where
  "well_typed_proc_set env p_map p_set = (full_nres_map p_set p_map \<and> disj_nres_map p_map \<and> (\<forall> u. case p_set u of
    None \<Rightarrow> True
    | Some e \<Rightarrow> (case p_map u of
      None \<Rightarrow> False
      | Some r_s \<Rightarrow> (\<exists> rx r_s2. well_typed env r_s e UnitTy r_s2 rx))
  ))"  

    (*
      ###### 2. defining system reduction / well-typed system  ######
    *)
  
datatype red_act =
  ThreadAct
  | HoleAct
  | ForkAct
  | SendAct
  (*
fun red_proc_set :: "p_state \<times> proc_set \<Rightarrow> red_act \<Rightarrow> p_state \<times> proc_set \<Rightarrow> bool" where
  "red_proc_set (s1, ps1) ThreadAct (s2, ps2) = (\<exists> are u h e1 e2 ax. ps1 u = Some (app_hole h e1) \<and> wf_hole h \<and>
    app_red_exp are (s1, e1) ax (s2, e2) \<and> ps2 = add_env ps1 u (app_hole h e2))"
| "red_proc_set (s1, ps1) HoleAct (s2, ps2) = ()"
| "red_proc_set (s1, ps1) ForkAct (s2, ps2) = (\<exists> u h e v. ps1 u = Some (app_hole h (AppExp (ConstExp ForkConst) e)) \<and>
    wf_hole h \<and> is_value e \<and> ps2 = add_env (add_env ps1 u (app_hole h (ConstExp UnitConst))) v (AppExp e (ConstExp UnitConst)) \<and>
  fresh_var ps1 v \<and> s1 = s2)"
| "red_proc_set (s1, ps1) SendAct (s2, ps2) = False"

definition well_typed_system where
  "well_typed_system env rs_map p_map s p_set = (well_typed_state s env rs_map \<and> well_typed_proc_set env p_map p_set \<and> sub_nres_map s p_map \<and>
  (\<forall> u. case p_map u of
    None \<Rightarrow> True
    | Some r_s \<Rightarrow> sep_nres_map r_s rs_map
  ))"  *)
  
end