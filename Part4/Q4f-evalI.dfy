include "WFFSupport.dfy"
include "Q4a-names.dfy"
include "Q4b-eval.dfy"

method evalI(expr :WFF, env : Env) returns (r : bool) 
  requires forall n : string :: n in names(expr) ==> n in env
  ensures r == eval(expr, env) { }