function method incomeTax(income: nat): real { 
    var come := income as real;
    var tax14 :=14000.0*0.105;
    var tax48 := (48000.0-14000.0)*0.175;
    var tax70 := (70000.0-48000.0)*0.30;
    if income > 70000 then ((come-70000.0)*0.33)+tax70 +tax48+tax14 else 
    if income > 48000 then ((come-48000.0)*0.30)+ tax48 +tax14 else 
    if income > 14000 then ((come-14000.0)*0.175) + tax14 else (come*0.105) 

}



