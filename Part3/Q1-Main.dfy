// Do not modify or submit this file
include "Q1.dfy"

method Main () {
    var tri := new Trisupport();
    triangular(10,tri);
    assert tri.printed() == 55;
}