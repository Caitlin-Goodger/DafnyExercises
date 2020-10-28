include "TrieSupport.dfy"
include "Q2a-containsL.dfy"
include "Q2e-insertL.dfy"

lemma stillInInsert(t:Trie, s:string, r:string) 
ensures containsL(insertL(insertL(t,s),r),s)
{ 

    
}
