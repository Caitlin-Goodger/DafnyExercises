include "TrieSupport.dfy"
include "Q2a-containsL.dfy"

function method initialiseL(s:string) : (r :Trie) 
ensures containsL(r,s)
{  
    if |s| ==0 then Trie(map[], true)  else Trie(map[s[0] := initialiseL(s[1..])], false) 
}
