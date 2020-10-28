
include "TrieSupport.dfy"


predicate method  containsL(t : Trie, s : string)   
 { 
    if |s| == 0 then t.word else if  s[0] in t.letters.Keys then containsL(t.letters[s[0]],s[1..]) else false
 
  }