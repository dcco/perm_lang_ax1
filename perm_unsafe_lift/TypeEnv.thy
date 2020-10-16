theory TypeEnv
  imports PermEnv GenEnv
begin

    (* 
      ####################################
        P2. type definitions
      ####################################
    *)

datatype p_aff = Aff | Ref | Prim
  
datatype c_end = SEnd | REnd  
  
datatype p_type =
   IntTy | UnitTy | BoolTy
  | ArrayTy p_type  
  | PairTy p_type p_type p_perm
  | FunTy p_type p_type p_perm p_aff
  | ChanTy p_type c_end

fun as_perm where
  "as_perm Aff = OwnPerm"
| "as_perm Ref = UsePerm"
| "as_perm Prim = NoPerm"
  
    (* pairs are unlimited just like arrays because any destructive uses of a pair
        will be filtered out at the level of primitive functions. *)
    (*
fun aff_type where
  "aff_type (FunTy t1 t2 r a) = (a = Aff)"
| "aff_type (ArrayTy tau) = aff_type tau"    
| "aff_type (PairTy t1 t2) = (aff_type t1 \<or> aff_type t2)"  
| "aff_type tau = False"  
  
fun unlim where
  "unlim (FunTy t1 t2 r a) = (a \<noteq> Aff)"
| "unlim (ChanTy tau) = False"
| "unlim tau = True"  
  
fun prim_type where
  "prim_type (FunTy t1 t2 r a) = (a = Prim)"
| "prim_type (ArrayTy t) = False"
| "prim_type (PairTy t1 t2) = False"
| "prim_type (ChanTy c) = False"
| "prim_type tau = True"  *)
  
type_synonym pt_env = "p_type gen_env" 
  
end