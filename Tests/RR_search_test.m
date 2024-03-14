
procedure test_RR_search(datum)
    N, ws, d := Explode(datum);
    printf "%o ", N;
    X, _, pairs := X0NQuotientEquations(N,ws);
    Xw := pairs[1,1];
    f := pairs[1,2];
    if Type(Xw) in [CrvEll, CrvHyp] then
	ptsXw := RationalPoints(Xw:Bound:=200);
	// Converting to SeqEnum
	ptsXw := [pt : pt in ptsXw];
    else
	ptsXw := PointSearch(Xw, 200);
    end if;
    assert RRSearch(f, ptsXw, d);
    return;
end procedure;

data := [<54,  [[54]],   3>,
	 <85,  [[5,17]], 4>,
	 <88,  [[88]],   4>,
	 <109, [[109]],  5>,
	 <112, [[7]],    6> // should take more than 10 hours
	];

printf "Riemann-Roch search for level ";
for datum in data do
    test_RR_search(datum);
end for;
