theory AnnExp
  imports WTLemma
begin
  
datatype ann_exp =
  ConstAExp p_const
  | OpAExp p_op
  | VarAExp string var_val_ref
  | PairAExp ann_exp ann_exp
  | IfAExp ann_exp ann_exp ann_exp
  | LamAExp string p_type ann_exp
  | AppAExp ann_exp ann_exp    
  
    
    
end
  