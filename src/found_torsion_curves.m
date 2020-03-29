

// Genus 2
intrinsic TorsionCurvesGenus2Qt() -> SeqEnum
{ Returns some of the genus 2 curves we found over Q(t). }
    K<t> := FunctionField(Rationals());
    P<x> := PolynomialRing(K);
    curves := [
        -t*x^5 + (1/4*t^2 + 5/2*t + 1/4)*x^4 + (-2*t - 1)*x^3 + (1/2*t + 3/2)*x^2 - x + 1/4, // 13
        -t*x^5 + (t^2 + 3*t + 1/4)*x^4 + (-4*t^2 - 7/2*t - 1/4)*x^3 + (6*t^2 + 2*t + 1/16)*x^2 + (-4*t^2 - 1/2*t)*x + t^2, // 14
        -t*x^5 + (1/4*t^2 + 5/2*t + 9/4)*x^4 + (-1/2*t^2 - 3*t - 9/2)*x^3 + (1/4*t^2 + 2*t + 15/4)*x^2 + (-1/2*t - 3/2)*x + 1/4, // 15
        -t*x^5 + (4*t^2 + 3*t + 1/4)*x^4 + (-8*t^2 - 5*t - 3/4)*x^3 + (8*t^2 + 5*t + 13/16)*x^2 + (-4*t^2 - 5/2*t - 3/8)*x + t^2 + 1/2*t + 1/16 // 20
    ];
    return curves;
end intrinsic;

intrinsic TorsionCurvesGenus2() -> SeqEnum
{ Returns some of the genus 2 curves we found over Q. }
    P<x> := PolynomialRing(Rationals());
    curves := [
        x^6 - 2*x^5 + 3*x^4 + 6*x^3 + 9*x^2 - 8*x + 16, // 6
        x^6 + 6*x^4 - 18*x^3 + 49*x^2 - 14*x + 1, // 7
        625/4*x^6 - 250*x^5 + 250*x^4 - 455/2*x^3 + 126*x^2 - 42*x + 49/4, // 8
        x^6 - 6*x^5 + 16*x^4 - 19*x^3 + 25/4*x^2 + 2*x + 6, // 9
        x^6 - 4*x^5 + 11/2*x^4 - 2*x^3 - 39/16*x^2 + 11/4*x - 3/4, // 10
        x^6 - 5/2*x^5 + 17/16*x^4 + 1/8*x^3 - 5/16*x^2 + 1/8*x + 1/16, // 11
        x^5 - 11/4*x^4 + 5/2*x^3 + 1/4*x^2 - 3/2*x + 9/16, // 12
        x^6 - 2*x^5 + 3*x^4 - x^2 - 2*x + 1, // 13
        x^6 - 6*x^4 + 4*x^3 + x^2 - 4*x + 4, // 14
        x^6 - 6*x^5 + 15*x^4 - 20*x^3 + 3*x^2 + 6*x + 1, // 15
        x^6 - 4*x^5 + 6*x^4 + 4*x^3 - 31*x^2 + 40*x, // 18
        1/2*x^5 - 7/16*x^4 + 9/8*x^3 - 3/16*x^2 - 1/4*x + 1/4, // 19
        1/4*x^5 - 5/4*x^4 + 5/2*x^3 - 39/16*x^2 + x, // 20
        x^6 - 2*x^5 + x^4 + 6*x^3 - 6*x^2 + 1, // 21
        x^6 - 3*x^5 + 17/4*x^4 - 4*x^3 + 7/2*x^2 - x + 1/4, // 22
        x^6 - 10*x^5 + 33*x^4 - 36*x^3 + 28*x^2 - 16*x + 4, // 23
        x^6 - 2*x^5 + x^4 + 28*x^3 - 28*x^2 + 4, // 24
        x^5 + 25/9*x^4 - 25/3*x^3 + 55/12*x^2 + 5/2*x + 1/4, // 25
        x^6 - 11*x^5 + 193/4*x^4 - 111*x^3 + 120*x^2 - 54*x + 9, // 26
        x^6 - 4*x^5 + 4*x^4 + 6*x^3 - 4*x^2 + 1, // 27
        x^6 - 2/3*x^5 - 32/9*x^4 + 17/9*x^3 + 433/36*x^2 - 19*x + 9, // 28
        x^6 - 2*x^5 + 2*x^3 - 3/4*x^2 + 1/2*x + 1/4, // 29
        x^6 + 3/4*x^5 + 393/64*x^4 + 315/32*x^2 - 27/4*x + 81/64, // 30
        -1718857/910141920 * x^5 + 377186051369/436868121600 * x^4 - 400896630191/109217030400 * x^3 + 71260492321/12135225600 * x^2 - 950527921/227535480 * x + 19018321/17065161, // 32
        x^6 - 6*x^5 + 29/3*x^4 - 10/3*x^3 + 37/9*x^2 + 28/9*x + 4/9, // 33
        x^6 - 13/3*x^5 + 265/36*x^4 - 67/9*x^3 + 89/18*x^2 - 4/3*x + 1/4, // 34
        x^6 + 4*x^5 + 4*x^4 - 10*x^3 + 4*x^2 + 1, // 39
        -3*x^5 + 19*x^4 - 44*x^3 + 185/4*x^2 - 22*x + 4 // 40
    ];
    return curves;
end intrinsic;

// Genus 3

intrinsic TorsionCurvesGenus3Qt() -> SeqEnum
{ Returns some of the genus 3 curves we found over Q(t). }
    K<t> := FunctionField(Rationals());
    P<x> := PolynomialRing(K);
    curves := [
        -t*x^7 + (1/4*t^2 + 7/2*t + 1/4)*x^6 + (-9/2*t - 3/2)*x^5 + (5/2*t + 15/4)*x^4 + (-1/2*t - 5)*x^3 + 15/4*x^2 - 3/2*x + 1/4, // 25
        -t*x^7 + (t^2 + 3*t + 1/4)*x^6 + (-7/2*t - 5/4)*x^5 + (2*t + 41/16)*x^4 + (-1/2*t - 11/4)*x^3 + 13/8*x^2 - 1/2*x + 1/16, // 26
        -t*x^7 + (1/4*t^2 + 5/2*t + 9/4)*x^6 + (-3*t - 9)*x^5 + (2*t + 15)*x^4 + (-1/2*t - 27/2)*x^3 + 7*x^2 - 2*x + 1/4, // 27
        -t*x^7 + (1/4*t^2 + 2*t + 4)*x^6 + (-3*t - 12)*x^5 + (2*t + 17)*x^4 + (-1/2*t - 14)*x^3 + 7*x^2 - 2*x + 1/4, // 28
        -t*x^7 + (4*t^2 + 3*t + 1/4)*x^6 + (-4*t^2 - 5*t - 1)*x^5 + (t^2 + 5*t + 7/4)*x^4 + (-5/2*t - 7/4)*x^3 + (1/2*t + 17/16)*x^2 - 3/8*x + 1/16, // 32
        -t*x^7 + (9*t^2 + 4*t + 1/4)*x^6 + (-27*t^2 - 21/2*t - 1)*x^5 + (141/4*t^2 + 35/2*t + 2)*x^4 + (-51/2*t^2 - 35/2*t - 5/2)*x^3 + (43/4*t^2 + 21/2*t + 2)*x^2 + (-5/2*t^2 - 7/2*t - 1)*x + 1/4*t^2 + 1/2*t + 1/4 // 42
    ];
    return curves;
end intrinsic;


intrinsic TorsionCurvesGenus3() -> SeqEnum
{ Returns some of the genus 3 curves we found over Q. }
    P<x> := PolynomialRing(Rationals());
    curves := [
        2*x^7 - 23/4*x^6 + 15/2*x^5 - 5/4*x^4 - 4*x^3 + 15/4*x^2 - 3/2*x + 1/4, // 25
        2*x^7 - 7/4*x^6 + 23/4*x^5 - 23/16*x^4 - 7/4*x^3 + 13/8*x^2 - 1/2*x + 1/16, // 26
        2*x^7 - 7/4*x^6 - 3*x^5 + 11*x^4 - 25/2*x^3 + 7*x^2 - 2*x + 1/4, // 27
        x^8 - 8*x^7 + 18*x^6 - 6*x^5 - 7*x^4 + 2*x^3 - 19*x^2 + 20*x, // 28
        192*x^7 - 575*x^6 + 612*x^5 + 84*x^4 - 846*x^3 + 900*x^2 - 432*x + 81, // 29
        2000*x^7 + 9129*x^6 - 150*x^5 - 1129*x^4 + 196*x^3 - 49*x^2 + 2*x + 1, // 30
        -648*x^7 + 8521*x^6 - 35304*x^5 + 71928*x^4 - 82404*x^3 + 54432*x^2 - 19440*x + 2916, // 31
        16*x^7 - 48*x^6 + 32*x^5 + 28*x^4 - 48*x^3 + 28*x^2 - 8*x + 1, // 32
        -32*x^7 + 113*x^6 - 558*x^5 + 1285*x^4 - 1188*x^3 + 572*x^2 - 144*x + 16, // 33
        -12*x^7 + 60*x^6 - 124*x^5 + 145*x^4 - 102*x^3 + 43*x^2 - 10*x + 1, // 34
        128*x^7 + 625*x^6 - 800*x^5 + 556*x^4 - 242*x^3 + 68*x^2 - 12*x + 1, // 35
        -1008*x^7 + 222916*x^6 - 180548*x^5 + 17681*x^4 + 1060*x^3 + 3074*x^2 + 280*x + 49, // 36
        4*x^7 - 16*x^6 + 16*x^5 + 12*x^4 - 32*x^3 + 24*x^2 - 8*x + 1, // 37
        61*x^7 - 112778711/518400*x^6 + 196766153/259200*x^5 - 51613919/51840*x^4 + 228689/1280*x^3 + 3762053/5120*x^2 - 2109807/3200*x + 301401/1600, // 38
        336468610464*x^7 + 1387158244945*x^6 - 3746988201228*x^5 + 2957749220766*x^4 - 626966305196*x^3 - 197416827111*x^2 + 44268024528*x + 18078415936, // 39
        5*x^7 + 4523081161/138384*x^6 - 1452727141/11532*x^5 + 842494611/3844*x^4 - 212383050/961*x^3 + 130569435/961*x^2 - 1509300/31*x + 8100, // 40
        32*x^7 - 23*x^6 - 196*x^5 + 504*x^4 - 560*x^3 + 340*x^2 - 112*x + 16, // 41
        -21*x^7 + 3109/25*x^6 - 12777/50*x^5 + 458049/1600*x^4 - 5575/32*x^3 + 4197/64*x^2 - 225/16*x + 25/16, // 42
        64*x^7 - 39*x^6 - 10*x^5 - 9*x^4 + 12*x^3 - x^2 - 2*x + 1, // 43
        48/25*x^7 + 217/100*x^6 - 41/5*x^5 + 183/25*x^4 - 71/50*x^3 - 17/25*x^2 + 6/25*x + 9/100, // 44
        1152*x^7 + 2692*x^6 - 9768*x^5 + 7764*x^4 - 848*x^3 - 1104*x^2 + 192*x + 64, // 48
        2*x^7 + 1/4*x^6 - 5*x^5 + 5/2*x^4 + 3/2*x^3 - 3/4*x^2 - 1/2*x + 1/4, // 49
        768*x^7 + 34177*x^6 + 3450*x^5 - 1905*x^4 + 364*x^3 + 15*x^2 - 6*x + 1, // 50
        36*x^7 - 11/25*x^6 + 19452/25*x^5 - 26366/25*x^4 - 510*x^3 + 1657*x^2 - 1050*x + 225, // 52
        1512*x^7 + 3514057*x^6 - 4215586*x^5 - 178365*x^4 + 2297474*x^3 - 718955*x^2 - 285012*x + 142884, // 54
        102*x^7 + 1797601/16*x^6 - 2190009/8*x^5 + 4838871/16*x^4 - 751187/4*x^3 + 1092687/16*x^2 - 108129/8*x + 17689/16, // 56
        1632*x^7 + 1797601*x^6 - 4380018*x^5 + 4838871*x^4 - 3004748*x^3 + 1092687*x^2 - 216258*x + 17689, // 56
        x^8 - 8*x^7 + 24*x^6 - 32*x^5 + 18*x^4 + 8*x^3 - 8*x^2 + 1, // 64
        x^8 - 14*x^7 + 55*x^6 - 48*x^5 + 23*x^4 - 14*x^3 + 21*x^2 - 12*x + 4, // 65
        1600*x^8 - 4800*x^7 + 10800*x^6 - 15920*x^5 + 14580*x^4 - 9720*x^3 + 4636*x^2 - 1320*x + 225, // 72
        x^8 - 6*x^6 + 10*x^5 - x^4 - 6*x^3 + 7*x^2 - 2*x + 1 // 91
    ];
    return curves;
end intrinsic;


// Genus 4
intrinsic TorsionCurvesGenus4Qt() -> SeqEnum
{ Returns some of the genus 4 curves we found over Q(t). }
    K<t> := FunctionField(Rationals());
    P<x> := PolynomialRing(K);
    curves := [
        -t*x^9 + (9*t^2 + 3*t + 1/4)*x^8 + (-36*t^2 - 15/2*t - 1/4)*x^7 + (78*t^2 + 10*t + 1/16)*x^6 + (-108*t^2 - 15/2*t)*x^5 + (103*t^2 + 3*t)*x^4 + (-68*t^2 - 1/2*t)*x^3 + 30*t^2*x^2 - 8*t^2*x + t^2, // 18
        -t*x^9 + (1/4*t^2 + 9/2*t + 1/4)*x^8 + (-2*t^2 - 8*t)*x^7 + (7*t^2 + 7*t)*x^6 + (-14*t^2 - 3*t)*x^5 + (35/2*t^2 + 1/2*t)*x^4 - 14*t^2*x^3 + 7*t^2*x^2 - 2*t^2*x + 1/4*t^2, // 41
        -t*x^9 + (1/4*t^2 + 4*t + 1)*x^8 + (-13/2*t - 7)*x^7 + (11/2*t + 85/4)*x^6 + (-5/2*t - 73/2)*x^5 + (1/2*t + 155/4)*x^4 - 26*x^3 + 43/4*x^2 - 5/2*x + 1/4, // 42
        -t*x^9 + (1/4*t^2 + 7/2*t + 9/4)*x^8 + (-11/2*t - 27/2)*x^7 + (5*t + 141/4)*x^6 + (-5/2*t - 105/2)*x^5 + (1/2*t + 49)*x^4 - 59/2*x^3 + 45/4*x^2 - 5/2*x + 1/4, // 43
        -t*x^9 + (1/4*t^2 + 3*t + 4)*x^8 + (-5*t - 20)*x^7 + (5*t + 45)*x^6 + (-5/2*t - 60)*x^5 + (1/2*t + 52)*x^4 - 30*x^3 + 45/4*x^2 - 5/2*x + 1/4, // 44
        -t*x^9 + (25/4*t^2 + 5/2*t + 1/4)*x^8 + (-25*t^2 - 5*t)*x^7 + (50*t^2 + 5*t)*x^6 + (-125/2*t^2 - 5/2*t)*x^5 + (105/2*t^2 + 1/2*t)*x^4 - 30*t^2*x^3 + 45/4*t^2*x^2 - 5/2*t^2*x + 1/4*t^2, // 45
        -t*x^9 + (4*t^2 + 4*t + 1/4)*x^8 + (-4*t^2 - 8*t - 3/2)*x^7 + (t^2 + 10*t + 4)*x^6 + (-15/2*t - 25/4)*x^5 + (3*t + 101/16)*x^4 + (-1/2*t - 17/4)*x^3 + 15/8*x^2 - 1/2*x + 1/16, // 48
        -t*x^9 + (9*t^2 + 4*t + 1/4)*x^8 + (-36*t^2 - 21/2*t - 3/4)*x^7 + (78*t^2 + 35/2*t + 13/16)*x^6 + (-108*t^2 - 35/2*t - 3/8)*x^5 + (103*t^2 + 21/2*t + 1/16)*x^4 + (-68*t^2 - 7/2*t)*x^3 + (30*t^2 + 1/2*t)*x^2 - 8*t^2*x + t^2, // 54
        -t*x^9 + (9*t^2 + 4*t + 1/4)*x^8 + (-18*t^2 - 21/2*t - 5/4)*x^7 + (27*t^2 + 35/2*t + 131/48)*x^6 + (-18*t^2 - 35/2*t - 41/12)*x^5 + (9*t^2 + 21/2*t + 97/36)*x^4 + (-7/2*t - 11/8)*x^3 + (1/2*t + 4/9)*x^2 - 1/12*x + 1/144, // 58
        -t*x^9 + (16*t^2 + 4*t + 1/4)*x^8 + (-48*t^2 - 14*t - 1)*x^7 + (68*t^2 + 28*t + 5/2)*x^6 + (-56*t^2 - 35*t - 4)*x^5 + (28*t^2 + 28*t + 9/2)*x^4 + (-8*t^2 - 14*t - 7/2)*x^3 + (t^2 + 4*t + 7/4)*x^2 + (-1/2*t - 1/2)*x + 1/16 // 72
    ];
    return curves;
end intrinsic;


intrinsic TorsionCurvesGenus4(: check := false) -> SeqEnum
{ Returns some of the genus 4 curves we found over Q. }
    P<x> := PolynomialRing(Rationals());
    curves := [
        12*x^9 - 27*x^8 + 16*x^7 + 34*x^6 - 88*x^5 + 99*x^4 - 68*x^3 + 30*x^2 - 8*x + 1, // 28
        -12*x^9 + 72*x^8 - 184*x^7 + 296*x^6 - 328*x^5 + 253*x^4 - 134*x^3 + 47*x^2 - 10*x + 1, // 29
        -100*x^10 + 500*x^9 - 975*x^8 + 700*x^7 + 800*x^6 - 2530*x^5 + 3030*x^4 - 2140*x^3 + 929*x^2 - 230*x + 25, // 30
        -3500*x^10 + 14000*x^9 - 17400*x^8 + 10400*x^7 - 1400*x^6 - 1680*x^5 + 1120*x^4 - 420*x^3 + 161*x^2 - 72*x + 16, // 31
        -122500*x^10 + 367500*x^9 - 70475*x^8 - 515150*x^7 + 827275*x^6 - 725570*x^5 + 448505*x^4 - 200080*x^3 + 60264*x^2 - 10528*x + 784, // 32
        121*x^10 + 242*x^8 + 2200*x^7 + 363*x^6 + 10242*x^4 - 19879*x^2 + 2200*x + 10000, // 33
        121*x^10 + 2200*x^8 - 242*x^7 + 10000*x^6 + 121*x^4 + 20000*x^3 + 2200*x^2 + 10000, // 34
         -5252187500*x^10 + 65055603600*x^8 - 144761853600*x^7 + 174015679600*x^6 - 136905623680*x^5 + 75081959120*x^4 - 29085521920*x^3 + 7678244336*x^2 - 1238608672*x + 92236816, // 35
        x^9 - 19/4*x^8 + 9*x^7 - 9/2*x^6 - 10*x^5 + 43/2*x^4 - 41/2*x^3 + 23/2*x^2 - 15/4*x + 9/16, // 40
        x^9 - 4*x^8 + 6*x^7 - 11*x^5 + 17*x^4 - 14*x^3 + 7*x^2 - 2*x + 1/4, // 41
        x^9 - 11/4*x^8 - 1/2*x^7 + 63/4*x^6 - 34*x^5 + 153/4*x^4 - 26*x^3 + 43/4*x^2 - 5/2*x + 1/4, // 42
        -4*x^9 + 24*x^8 - 76*x^7 + 161*x^6 - 220*x^5 + 198*x^4 - 118*x^3 + 45*x^2 - 10*x + 1, // 43
        14*x^9 - 31*x^8 - 166*x^7 + 969*x^6 - 2261*x^5 + 3045*x^4 - 2550*x^3 + 5265/4*x^2 - 385*x + 49, // 44
        368*x^9 + 9*x^8 + 240*x^7 + 1360*x^6 - 3080*x^5 + 3176*x^4 - 1920*x^3 + 720*x^2 - 160*x + 16, // 45
        -22032*x^9 + 158560*x^8 - 143760*x^7 + 173156*x^6 - 132248*x^5 + 76060*x^4 - 37592*x^3 + 14257*x^2 - 3204*x + 324, // 46
        18101600*x^9 + 44730929*x^8 + 32956830*x^7 - 39627675*x^6 + 13084550*x^5 - 2327500*x^4 + 1016250*x^3 - 231875*x^2 - 18750*x + 15625, // 47
        105456*x^9 + 4190761*x^8 - 27656280*x^7 + 72593688*x^6 - 101920032*x^5 + 82373616*x^4 - 37666944*x^3 + 8705664*x^2 - 746496*x + 20736, // 48
        114688*x^9 + 1358307329*x^8 - 343595896*x^7 + 69229804*x^6 - 11773160*x^5 + 1619926*x^4 - 176008*x^3 + 16268*x^2 - 1176*x + 49, // 49
        3*x^9 - 4*x^8 + 35/4*x^6 - 29/2*x^5 + 13*x^4 - 15/2*x^3 + 45/16*x^2 - 5/8*x + 1/16, // 50
        12939264*x^9 + 13931336779777*x^8 - 1714477822592*x^7 + 63564540820*x^6 + 289626064*x^5 - 26171522*x^4 + 7275424*x^3 + 49348*x^2 + 2704*x + 169, // 51
        -81000*x^9 + 352561*x^8 - 702320*x^7 + 893812*x^6 - 751940*x^5 + 476326*x^4 - 212120*x^3 + 59800*x^2 - 9500*x + 625, // 52
        1316551511808*x^9 + 648204624757665*x^8 - 1367676767024550*x^7 + 1411951052218683*x^6 - 821802862194162*x^5 + 276730856522437*x^4 - 42969861545628*x^3 - 46817938620*x^2 + 578238694272*x + 21828289536, // 53
        -x^9 + 53/4*x^8 - 189/4*x^7 + 1541/16*x^6 - 1007/8*x^5 + 1817/16*x^4 - 143/2*x^3 + 61/2*x^2 - 8*x + 1, // 54
        36*x^9 - 8*x^8 - 412*x^7 + 1488*x^6 - 2752*x^5 + 2992*x^4 - 1752*x^3 + 588*x^2 - 108*x + 9, // 55
        -32*x^9 + 217*x^8 - 316*x^7 + 176*x^6 + 4*x^5 - 58*x^4 + 28*x^3 - 4*x + 1, // 57
        -144*x^9 + 1908*x^8 - 4284*x^7 + 6801*x^6 - 5604*x^5 + 3196*x^4 - 702*x^3 + 136*x^2 - 12*x + 1, // 58
        32*x^9 - 31*x^8 - 94*x^7 + 167*x^6 - 34*x^5 - 99*x^4 + 68*x^3 + 4*x^2 - 16*x + 4, // 59
        64*x^9 - 124*x^8 - 4*x^7 + 357*x^6 - 606*x^5 + 531*x^4 - 272*x^3 + 83*x^2 - 14*x + 1, // 60
        42875000*x^9 - 198879975*x^8 + 379237950*x^7 - 317077325*x^6 - 56637680*x^5 + 423452755*x^4 - 473231690*x^3 + 275449309*x^2 - 86799580*x + 11764900, // 61
        285768*x^9 - 281655*x^8 - 464724*x^7 + 560274*x^6 + 288312*x^5 - 406811*x^4 - 157780*x^3 + 289296*x^2 - 96040*x + 9604, // 62
        -1500625000*x^9 + 7061881225*x^8 - 13627115600*x^7 + 15374111600*x^6 - 11587219280*x^5 + 6190389520*x^4 - 2374328320*x^3 + 626795456*x^2 - 101110912*x + 7529536, // 63
        4608*x^9 + 9769*x^8 - 30332*x^7 + 8620*x^6 + 23440*x^5 - 18128*x^4 - 704*x^3 + 5248*x^2 - 2048*x + 256, // 65
        4608*x^9 - 5180*x^8 - 81372*x^7 + 345417*x^6 - 655244*x^5 + 721812*x^4 - 493008*x^3 + 207328*x^2 - 49536*x + 5184, // 66
        16*x^9 + 57*x^8 - 158*x^7 + 87*x^6 + 38*x^5 - 37*x^4 - 14*x^3 + 22*x^2 - 8*x + 1, // 67
        105840*x^9 + 61070164*x^8 - 198101120*x^7 + 390170548*x^6 - 479406200*x^5 + 404864209*x^4 - 226283960*x^3 + 75818680*x^2 - 13445600*x + 960400, // 68
        -61560*x^9 + 798804*x^8 - 3997296*x^7 + 10541580*x^6 - 16695984*x^5 + 16978552*x^4 - 11290636*x^3 + 4782528*x^2 - 1179748*x + 130321, // 72
        33012672*x^9 - 33274127*x^8 - 39094086*x^7 + 120073119*x^6 - 91425812*x^5 + 16264575*x^4 + 18739482*x^3 - 9702767*x^2 - 2870304*x + 1937664, // 74
        -840*x^9 + 7345*x^8 - 26592*x^7 + 54392*x^6 - 70856*x^5 + 61780*x^4 - 36320*x^3 + 13936*x^2 - 3168*x + 324, // 82
        -696*x^9 + 4777*x^8 - 11360*x^7 + 14184*x^6 - 10104*x^5 + 3868*x^4 - 480*x^3 - 144*x^2 + 32*x + 4, // 82
        104448*x^9 - 45884*x^8 + 153912*x^7 - 331572*x^6 - 352236*x^5 + 1012380*x^4 - 892728*x^3 + 462645*x^2 - 131418*x + 21609 // 88
    ];
    if check then
        assert { Genus(HyperellipticCurve(f)) : f in curves } eq { 4 };
        assert { IsGeometricallySimple(curve) : curve in curves } eq { true };
        // [HeuristicTorsionOrder(curve) : curve in curves];
    end if;
    return curves;
end intrinsic;