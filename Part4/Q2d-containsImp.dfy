include "TrieSupport.dfy"
include "Q2a-containsL.dfy"

 method  containsImp(t' : Trie, s' : string) returns (r : bool)  
   ensures r == containsL(t',s') 
 {  
   var i := 0;
    
    var t := t';
    var s := s';
    r := containsL(t,s);

    while(|s| > 0 ) 
    decreases |s|
    invariant r == containsL(t,s)
    {

      if(s[0] !in t.letters.Keys) {
        r := false;
        return r;
      }
      t := t.letters[s[0]];
      s := s[1..];
    }

    return r;

 }
