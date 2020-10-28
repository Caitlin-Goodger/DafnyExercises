include "Tweesupport.dfy"

function method tweeSize(t:Twee) : nat
{ 
    match t 
    case Empty => 1
    case Node(value,l,r) => 1 + tweeSize(l) + tweeSize(r)

 }

 