include "TrieSupport.dfy"
include "Q2a-containsL.dfy"
include "Q2e-insertL.dfy"

lemma containsInsertL(t:Trie, s:string)
   ensures  containsL(insertL(t,s),s) { 
      
   }
