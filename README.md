This repository contains the code that accompanies the torsion paper.

To load the code, attach the packages:

	> Attach("helper_functions.m");
	> Attach("zeta_function.m");
	> Attach("found_torsion_curves.m");

You can then inspect the curves as follows:
	
	> curves := TorsionCurvesGenus2();
	> TorsionSubgroup(curves2[19]);
	Abelian Group isomorphic to Z/26
	Defined on 1 generator
	Relations:
	    26*P[1] = 0
	Mapping from: Abelian Group isomorphic to Z/26
	Defined on 1 generator
	Relations:
	    26*P[1] = 0 to Jacobian of Hyperelliptic Curve defined by y^2 = 4*x^6 - 
	    44*x^5 + 193*x^4 - 444*x^3 + 480*x^2 - 216*x + 36 over Rational Field given 
	by a rule [no inverse]
