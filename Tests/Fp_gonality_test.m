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
//	 <53,  5, 4>,
	 <116, 3, 6>,
	 <137, 3, 6>,
	 <162, 5, 6>,
	 <169, 5, 6>,
	 <181, 3, 6>];

printf "lower bounds for level";
for datum in data do
    test_LB_Fq_gonality(datum);
end for;

