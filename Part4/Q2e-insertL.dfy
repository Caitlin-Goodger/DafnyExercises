include "TrieSupport.dfy"
include "Q2a-containsL.dfy"

function method  insertL (t : Trie, s : string)  : (r : Trie) 
decreases s  
ensures containsL(r,s)
//ensures |s| > 0 ==> r.letters.Keys == t.letters.Keys + {s[0]}
//ensures (set x | x in t.letters.Keys && x in r.letters.Keys) == t.letters.Keys
{ 
    if |s| == 0 then Trie(t.letters, true) else if  s[0] in t.letters.Keys then Trie(t.letters[s[0] := insertL(t.letters[s[0]],s[1..])],t.word) else Trie(t.letters[s[0] := insertL(Trie(map[], false), s[1..])], t.word) 

 }

//  method Main() {
//      var t:= Trie(map[], true);
//      var r := insertL(t,"wring");
//      print(r);
//      print("\n");
//      var h := insertL(r,"wrong");
//      print(h);
//      print("\n");

//  }
