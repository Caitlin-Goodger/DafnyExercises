include "Tweesupport.dfy"
include "Q3c-tweeOK.dfy"
include "Q3d-contains.dfy"

method containsI(t : Twee, s : int) returns (r : bool)
    decreases 0
    requires tweeOK(t)
    ensures r == contains(t,s)
{ 

    var twee := t;
    r := contains(twee,s);

    while (twee.Node?) 
    decreases twee 
    invariant tweeOK(twee)
    invariant contains(twee,s) == r{

        if (twee.value == s) {
            r := true;
            return r;
        } else if (twee.value < s) {
            twee := twee.right;
        } else {
            twee:= twee.left;
        }



    }

    return r;


}


