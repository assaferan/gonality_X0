intrinsic GonalityBounds(label::MonStgElt) -> SeqEnum
{Return an upper bound for the gonality of this curve.}
    // Some of these checks could be also done on the data without a model
    split_label := Split(label, ".");
    level := StringToInteger(split_label[1]);
    g := StringToInteger(Split(split_label[3], "-")[1]);
    input := Read("input_data/" * label);
    pointless, q_bounds, qbar_bounds, models, model_types := eval(input);
    if g le 1 then
	qbar_bounds := [g+1,g+1];
    else
	qbar_bounds[1] := Maximum(qbar_bounds[1], 2);
	qbar_bounds[2] := Minimum(qbar_bounds[2], (g+3) div 2); 
    end if;
    if not pointless then
	// Proposition A.1 (iv), (v) in [Poonen]
	if g in [0,1] then
	    q_bounds := [g+1,g+1];
	    return [q_bounds, qbar_bounds];
	end if;
	q_bounds[2] := Minimum(q_bounds[2], g ge 2 select g else g+1);	
	// Corollary 4.6 in [Najman-Orlic]
	if (g ge 5) and (qbar_bounds eq [3,3]) then
	    q_bounds := [3,3];
	    return [q_bounds, qbar_bounds];
	end if;
	if (g ge 10) and (qbar_bounds eq [4,4]) then
	    q_bounds := [4,4];
	    return [q_bounds, qbar_bounds];
	end if;
	// This is [Poonen, Thm 2.5 (i)]
	if q_bounds[1] ge 3 then
	    qbar_bounds[1] := Maximum(qbar_bounds[1], 3);
	end if;
	if qbar_bounds[2] ge 3 then
	    q_bounds[2] := Minimum(q_bounds[2], (qbar_bounds[2]-1)^2);
	end if;
    else
	// Bjorn's observation that a genus 3 curve is trigonal 
	// if and only if it has a rational point
	if g eq 3 then
	    q_bounds[1] := Maximum(q_bounds[1], 4);
	end if;
    end if;
    for i->X in models do
	if model_types[i] eq 0 then
	    // canonical model
	    // Since we have a canonical model, the curve is not hyperelliptic
	    qbar_bounds[1] := Maximum(qbar_bounds[1],3);
	    // Here we use the fact that when we produce a canonical model,
	    // we only include cubic relations if they are essential
	    has_cubic := exists(f){f :  f in DefiningEquations(X) | 
				     Degree(f) eq 3};
	    has_quintic := exists(f){f :  f in DefiningEquations(X) | 
				     Degree(f) eq 5};
	    if (has_cubic) and (not has_quintic) then
		qbar_bounds := [3, 3];
	    else
		 qbar_bounds[1] := Maximum(qbar_bounds[1],4);
	    end if;
	    q_bounds[1] := Maximum(q_bounds[1],qbar_bounds[1]);
	end if;
	// Q : do we want to try that with every model ?
	LB := FqGonalityLB(X : BadPrimes := PrimeDivisors(level), 
			       LowerBound := q_bounds[1],
			       UpperBound := q_bounds[2]);
	q_bounds[1] := Maximum(q_bounds[1], LB);
    end for;
    return [q_bounds, qbar_bounds];
end intrinsic;

/*
intrinsic GonalityBoundsOverQ(X::Crv[FldRat]) -> RngIntElt, RngIntElt
{Return lower and upper bounds for the gonality of this curve.}
    // Some of these checks could be also done on the data without a model
    
end intrinsic;
*/
