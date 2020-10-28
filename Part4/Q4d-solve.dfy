
include "WFFSupport.dfy"
include "Q4a-names.dfy"
include "Q4b-eval.dfy"
include "Q4c-assignments.dfy"

function method solve(expr : WFF) : (r : set<Env>)
  ensures forall e :: e in r ==> (e.Keys == names(expr)) && eval(expr, e) { {} }