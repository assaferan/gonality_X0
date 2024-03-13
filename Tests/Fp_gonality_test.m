// this code gives a lower bound on the gonality of X_0(116)

procedure test_LB_Fq_gonality(datum)
    N, q, d := Explode(datum);
    printf " %o", N;
    X:= X0NQuotientEquations(N,[]);
    assert not ExistsFqDegreeUpTo(X, q, d-1);
    return;
end procedure;

data := [<38,  5, 4>,
	 <44,  5, 4>,
	 <53,  7, 4>, // different than paper (5->7)
	 <61,  3, 4>,
	 <76,  5, 6>,
	 <82,  5, 6>,
	 <84,  5, 6>, // should take more than 1 hour
	 <86,  3, 6>,
	 <93,  5, 6>,
	 <99,  5, 6>,
	 <102, 5, 8>, // 3.3 hrs
	 <106, 7, 8>, // 35 hrs
	 <108, 5, 6>, // 27 min
	 <109, 3, 5>,
	 <112, 3, 6>, // more than 10 hrs
	 <113, 3, 6>,
	 <114, 5, 8>, // more than 53 hrs
	 <115, 3, 6>, 
	 <116, 3, 6>,
	 <117, 5, 6>,
	 <118, 3, 6>,
	 <122, 3, 6>,
	 <127, 3, 6>,
	 <128, 3, 6>,
	 <130, 3, 8>, // 20 min
	 <132, 5, 8>, // different than paper (6 -> 5)
	 <134, 3, 8>, // over 1 hr
	 <136, 5, 8>, // over 13 hrs
	 <137, 3, 6>,
	 <140, 3, 8>,
	 <144, 5, 6>,
	 <147, 5, 6>, 
	 <148, 5, 8>, // different than paper (6 -> 5), 3 hrs
	 <150, 7, 8>, // more than 34 hrs
	 <151, 5, 6>,
	 <152, 3, 8>,
	 <153, 5, 8>, // 2 hrs
	 <154, 5, 8>, // 2 days
	 <157, 3, 8>,
	 <160, 7, 8>,
	 <162, 5, 6>,
	 <163, 5, 7>,
	 <169, 5, 6>,
	 <170, 3, 8>, // > 100 hrs
	 <172, 3, 8>,
	 <175, 2, 2>,
	 <176, 3, 8>,
	 <178, 3, 8>, // 4.5 hrs
	 <179, 5, 6>,
	 <180, 7, 7>, // 9 days
	 <181, 3, 6>,
	 <187, 2, 8>, // 1.5 hrs
	 <189, 2, 8>,
	 <192, 5, 8>, // 4 days
	 <193, 3, 6>,
	 <196, 5, 8>, // 3 hrs
	 <197, 3, 6>, // 36 min
	 <198, 5, 8>, // 7 days
	 <200, 3, 8>, // 1.6 hrs
	 <201, 2, 8>, // 4 hrs
	 <217, 2, 8>,
	 <229, 3, 8>, 
	 <233, 2, 8>, // 2 hrs 
	 <241, 2, 8>,
	 <247, 2, 8>, // 4 hrs
	 <277, 5, 8> //  different than paper (6 -> 5), 7 days
	]; 

printf "lower bounds for level";
for datum in data do
    test_LB_Fq_gonality(datum);
end for;

