
intrinsic RRSearch(f::MapSch[Crv[FldRat], Crv[FldRat]], 
		      ptsXw::SeqEnum[Pt], d::RngIntElt) -> BoolElt
{Perform a Riemann roch search.}
    X := Domain(f);
    Xw := Codomain(f);
    deg := Degree(f);
    // If Xw is in regular projective space we simply try to pullback points
    if Set(Gradings(Xw)[1]) eq {1} then
	pb:=[Pullback(f,p):p in ptsXw];
	pts := &cat [[Place(X!pt) : pt in Points(p)] : p in pb];
	for D in CartesianPower(pts, d) do
	    divisor := &+[DivisorGroup(X) | 
			 x : x in TupleToList(D)];
	    RR, RRmap := RiemannRochSpace(divisor);
	    dim := Dimension(RR);
	    if dim gt 1 then
		return true;
	    end if;
	end for;
    end if;
    pb:=[Pullback(f,Place(p)):p in ptsXw];
    pls := AssociativeArray([1..deg]);
    for i in [1..deg] do
	pls[i] := {};
    end for;
    for i:=1 to #pb do
	dec:=Decomposition(pb[i]);
	for j:=1 to #dec do
	    Include(~pls[Degree(dec[j,1])], dec[j,1]);
	end for;
    end for;
    for pi in RestrictedPartitions(d, {1..deg}) do
	divs := CartesianProduct([PowerSet(Places(X)) | 
				     pls[i] : i in pi]);
	for D in divs do
	    divisor := &+[DivisorGroup(X) | 
			 x : x in TupleToList(D)];
	    RR, RRmap := RiemannRochSpace(divisor);
	    dim := Dimension(RR);
	    if dim gt 1 then
		return true;
	    end if;
	end for;
    end for;
end intrinsic;
