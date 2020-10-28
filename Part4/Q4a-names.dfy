include "WFFSupport.dfy"
function method names(expr : WFF) : set<string> { 
    match expr
        case Implies(left,right) => names(left) + names(right)
        case Var(name) => {name}
        case Lit(val) => {}
        case Not(e) => names(e)
        case And(left,right) => names(left) + names(right)
        case Or(left,right) => names(left) + names(right)
        case Equals(left,right) => names(left) + names(right)

 }