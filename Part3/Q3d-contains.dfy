include "Tweesupport.dfy"
include "Q3b-toSet.dfy"
include "Q3c-tweeOK.dfy"

predicate method contains(t : Twee, s : int)
  requires tweeOK(t)
  ensures contains(t,s) <==> (s in toSet(t))
{ 
  match t
  case Empty => false
  case Node(value,l,r) => value == s || contains(l,s) || contains(r,s)
 }

