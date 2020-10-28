
include "WFFSupport.dfy"
include "Q4a-names.dfy"

function method assignments(expr : WFF) : (r : set<Env>)
  ensures forall e :: e in r ==> e.Keys == names(expr) { 
      {}
      
   }