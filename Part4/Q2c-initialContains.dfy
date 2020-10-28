include "TrieSupport.dfy"
include "Q2a-containsL.dfy"
include "Q2b-initialiseL.dfy"

lemma initialContains(x:string,s : string) 
   ensures containsL(initialiseL(x),s) ==> x ==s 
   ensures x ==s ==> containsL(initialiseL(x),s)
   ensures s ==x ==> containsL(initialiseL(s),x)
{  
   //assert |x| == |s|;
}


