include "WFFSupport.dfy"
include "Q4a-names.dfy"
function method eval(expr :WFF, env : Env) : bool 
  requires forall n : string :: n in names(expr) ==> n in env { 
    match expr
        case Implies(left,right) => eval(left,env) ==> eval(right,env)
        case Var(name) => env[name]
        case Lit(val) => val
        case Not(e) => !eval(e,env)
        case And(left,right) => eval(left,env) && eval(right,env)
        case Or(left,right) => eval(left,env) || eval(right,env)
        case Equals(left,right) => eval(left,env) == eval(right,env)

   }