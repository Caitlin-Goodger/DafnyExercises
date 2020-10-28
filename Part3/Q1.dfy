include "Trisupport.dfy"

method triangular(n : nat, tri : Trisupport)
 decreases 0
 modifies tri
 requires tri.printed() == 0 && tri.col() == 0 && tri.row() == 1
 //ensures  tri.printed() == ...
 ensures tri.printed() == (n*(n+1))/2
 ensures tri.col() ==0;
 ensures tri.row() == n+1;
{
    var row := 0;

    while (row < n) 
    decreases n -row
    invariant row <= n
    invariant tri.col() ==0
    invariant tri.row() == row +1
    invariant tri.test_printed == (row * (row + 1)) /2 
    {
        
        var oldRow := row;
        var spacing := ((n) + 1) - (row);
        var countspacing := 0;
        oldRow := tri.test_row;

        while (countspacing < spacing) 
        decreases spacing - countspacing
        invariant tri.test_printed == (row * (row +1)) /2
        invariant tri.row() == oldRow
        invariant tri.col() ==0
        {
            tri.space();
            countspacing := countspacing +1;
        }


        row := row +1;
        var newMax := row + tri.test_printed;

        while (tri.test_printed < newMax) 
        decreases newMax - tri.test_printed
        invariant tri.row() == oldRow
        invariant tri.col() == row -(newMax - tri.test_printed)
        invariant tri.test_printed <= newMax
        {
            tri.star();
        }

        countspacing := 0;
        while (countspacing < spacing) 
        decreases spacing - countspacing
        invariant tri.test_printed == (row * (row +1)) /2
        invariant tri.row() == oldRow
        invariant tri.col() == row
        {
            tri.space();
            countspacing := countspacing +1;
        }


        tri.cr();

    }


}
