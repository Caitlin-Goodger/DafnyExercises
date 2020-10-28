include "TrieSupport.dfy"
include "Q2b-initialiseL.dfy"
include "Q2e-insertL.dfy"
include "Q2h-langL.dfy"

method Main() {
    var t_anew:= Trie(map[], true);
    var t_and:= Trie(map[], true);
    var t_ane := Trie(map['w':=t_anew],false);
    var t_an := Trie(map['d':=t_and,'e':=t_ane],false);  

    print "t_an \n", t_an,"\n";
    print "t_an ",langL(t_an),"\n";
    var t:Trie := insertL(initialiseL("ew"), "d");
    assert t == t_an;
    print " t ", t,"\n";
    print " langL(t) ", langL(t),"\n";
    print "langL(insertL(t, \"d\")) ", langL(insertL(t, "d")),"\n";
    print "langL(insertL(t, \"e\")) ", langL(insertL(t, "e")),"\n";

    print"insertL(t, \"ewxx\")\n";
    print insertL(t, "ewxx"),"\n";
    print "langL(insertL(t, \"ewxx\"))", langL(insertL(t, "ewxx")),"\n";
}
/* OUTPUT from Main (don't worry about the order of sets or maps)
t_an 
Trie.Trie(map[d := Trie.Trie(map[], true), e := Trie.Trie(map[w := Trie.Trie(map[], true)], false)], false)
t_an {d, ew}
 t Trie.Trie(map[e := Trie.Trie(map[w := Trie.Trie(map[], true)], false), d := Trie.Trie(map[], true)], false)
 langL(t) {ew, d}
langL(insertL(t, "d")) {ew, d}
langL(insertL(t, "e")) {e, ew, d}
insertL(t, "ewxx")
Trie.Trie(map[e := Trie.Trie(map[w := Trie.Trie(map[x := Trie.Trie(map[x := Trie.Trie(map[], true)], false)], true)], false), d := Trie.Trie(map[], true)], false)
langL(insertL(t, "ewxx")){ew, ewxx, d}
    */