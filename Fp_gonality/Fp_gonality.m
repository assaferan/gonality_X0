/// this code is used to determine lower bounds for the F_p-gonality and hence the Q-gonality

// some functions for handling partitions
function get_covered_partitions(pi)
    parts := {pi};
    for i in [1..#pi-1] do
	covered := pi[1..i-1] cat [pi[i]+pi[i+1]] cat pi[i+2..#pi];
	Include(~parts, Reverse(Sort(covered)));
    end for;
    return parts;
end function;

// Here what we really should do is solve a set cover problem
// For now, we do a trivial greedy approach
function minimal_cover(parts)
    if #parts eq 0 then 
	return parts;
    end if;
    covered := [get_covered_partitions(pi) : pi in parts];
    _, max_idx := Maximum([#cov : cov in covered]);
    min_cov := [parts[max_idx]];
    coverage := covered[max_idx];
    while (#coverage ne #parts) do
	covered := [{x : x in cov | x notin coverage} : cov in covered];
	_, max_idx := Maximum([#cov : cov in covered]);
	Append(~min_cov, parts[max_idx]);
	coverage join:= covered[max_idx];
    end while;
    return min_cov;
end function;

function get_integral_model(X)
    D:=DefiningEquations(X);
    D2:=[];
    for i:=1 to #D do
	p:=D[i];
	l:=LCM([Denominator(a):a in Coefficients(p)]);
	p:=p*l;
	D2:=D2 cat [p];
    end for;
    num_vars := Rank(Universe(D)); 
    C:=Scheme(ProjectiveSpace(Rationals(),num_vars-1),D2);
    return C;
end function;

// Here we could use the level to determine a priori the bad primes,
// but we try not to, in case we have non-canonical models.
// Can feed lower bound from other sources (e.g. if we already know the point counts)
function choose_Fq(C : NumReductions := 3, 
		       LowerBound := 0, 
		       PrimePowerBound := 100,
		       BadPrimes := [])
    prime_powers := [i : i in [2..PrimePowerBound] | IsPrimePower(i)];
    Cred := AssociativeArray();
    for q in prime_powers do
	Cq := ChangeRing(C, GF(q));
	p := PrimeDivisors(q)[1];
	if (p ne q) then
	    is_good := p in Keys(Cred);
	elif IsEmpty(BadPrimes) or p in [2,3] then
	    vprintf ModularGonality, 1 : "Checking for good reduction at %o...\n", p;
	    is_good := IsEmpty(SingularSubscheme(Cq));
	else
	    is_good := p notin BadPrimes;
	end if;
	if is_good then
	    Cred[q] := Cq;
	end if;
    end for;
    prime_powers := Sort([k : k in Keys(Cred)]);
    if LowerBound eq 0 then
	vprintf ModularGonality, 1 : "Computing trivial lower bound...\n";
	LowerBound := Max([Ceiling(#Points(Cred[q])/(q+1)) 
			   : q in prime_powers]);
	vprintf ModularGonality, 1 : "LowerBound = %o\n", LowerBound;
    end if;
    
    // we will measure the amount of work needed at the first degree we check
    d := LowerBound;
    work := AssociativeArray(prime_powers);
    
    vprintf ModularGonality, 1 : "Choosing a finite field F_q, checking q =";
    for q in prime_powers do
	vprintf ModularGonality,1 : " %o", q;
	work[q] := 0;
	// Instead of computing the number of pls (of large degree) 
	// we estimate them using Hasse-Weil
	npls := [(q^i + 1) div i : i in [1..d]];
	for i in [1..d] do
	    if q^i in prime_powers then
		npls[i] := #Points(Cred[q^i]) div i;
	    end if;
	end for;
	B := Floor(npls[1]/(q+1));
	parts := Partitions(d);
	for pi in parts do
	    one_idx := Index(pi, 1);
	    if one_idx eq 0 then one_idx := #pi + 1; end if;
	    num_ones := 1 + #pi - one_idx;
	    num_big_divs := &*[Integers() | npls[i] : i in pi[1..one_idx-1]];
	    num_pts := Min(num_ones, B);
	    all_exps := &cat[Partitions(num_ones,k) : k in [0..num_pts]];
	    all_exps := minimal_cover(all_exps);
	    for exps in all_exps do
		work[q] +:= npls[1]^(#exps) * num_big_divs;
	    end for;
	end for;
    end for;	
    
    sorted_work := Sort([<work[q],q> : q in prime_powers]);
    reductions := [Cred[tup[2]] : tup in sorted_work[1..NumReductions]];
    
    vprintf ModularGonality, 1 : "\n";
    return reductions, LowerBound;
end function; 

//this function takes a model X of a curve and a prime p of good reduction of the model as input and checks whether there are any degree d functions over F_p. It assumes that #X(F_p)/(p+1)< B+1 (and checks this) which can be used so that only the R-R spaces of divisors supported on at most B F_p-rational points need be checked.
// This generalizes the following functions

intrinsic ExistsFqDegree(X::Crv[FldRat], q::RngIntElt, 
			 d::RngIntElt) -> BoolElt
{Returns true if there is a degree d function over F_q.}
  
    C:=get_integral_model(X);
    C2:=ChangeRing(C,GF(q));
    FF := FunctionField(C2);
    AFF, FFtoAFF := AlgorithmicFunctionField(FF);
    return ExistsDivisorOfDegree(AFF, d);

end intrinsic;

intrinsic ExistsFqDegreeUpTo(X::Crv[FldRat], q::RngIntElt, 
			     d::RngIntElt) -> BoolElt
{Returns true if there is a degree at most d function over F_q.}
    for deg in [1..d] do
	if ExistsFqDegree(X, q, deg) then
	    return true;
	end if;
    end for;
    return false;
end intrinsic;

intrinsic ExistsDivisorOfDegree(AFF::FldFun, d::RngIntElt) -> BoolElt
{Returns true if there is a degree d function on X.}
  
    pls := [Places(AFF, i) : i in [1..d]];
    q := #BaseField(BaseField(BaseField(AFF)));

    // We know such a function is supported on at most B F_p rational points.
    B := Floor((#pls[1])/(q+1));
   
    parts := Partitions(d);
    
    for pi in parts do
	vprintf ModularGonality, 1 : "pi = %o\n", pi;
	one_idx := Index(pi, 1);
	if one_idx eq 0 then one_idx := #pi + 1; end if;
	num_ones := 1 + #pi - one_idx;
	big_divs := CartesianProduct([PowerSequence(Places(AFF)) | 
				     pls[i] : i in pi[1..one_idx-1]]);
	num_pts := Min(num_ones, B);
	all_exps := &cat[Partitions(num_ones,k) : k in [0..num_pts]];
	all_exps := minimal_cover(all_exps);
	for big_div in big_divs do
	    big_divisor := &+[DivisorGroup(AFF) | 
			 x : x in TupleToList(big_div)];
	    for exps in all_exps do
		vprintf ModularGonality, 2 : "exps = %o\n", exps;
		small_divs := CartesianPower(pls[1], #exps);
		for small_div in small_divs do
		    divisor := big_divisor;
		    divisor +:= &+[DivisorGroup(AFF) | 
				  exps[i]*small_div[i] : i in [1..#exps]];
		    vprintf ModularGonality, 3 : "divisor = %o\n", divisor;
		    RR, RRmap := RiemannRochSpace(divisor);
		    dim := Dimension(RR);
		    if dim gt 1 then
			return true;
		    end if;
		end for;
	    end for;
	end for;
    end for;
   
    return false;
end intrinsic;

intrinsic FqGonalityLB(X::Crv[FldRat] : BadPrimes := [],
					LowerBound := 1,
					UpperBound := Infinity()) -> RngIntElt
{Find a lower bound on gonality by using Fq gonality.}
    C := get_integral_model(X);
    Cqs, LB := choose_Fq(C : BadPrimes := BadPrimes, 
			     LowerBound := LowerBound);
    g := Genus(Curve(C));
    for Cq in Cqs do
	q := #BaseField(Cq);
	vprintf ModularGonality, 1 : "q = %o\n", q;
	FF := FunctionField(Cq);
	AFF, FFtoAFF := AlgorithmicFunctionField(FF);
	d := LB-1;
	found_gonal_map := false;
	while not found_gonal_map do
	    d +:= 1;
	    if (d ge UpperBound) then
		found_gonal_map := true;
	    elif (#Points(Cq) ne 0) and 
		 (((g ge 2) and (d ge g)) or (d ge g+1)) then
		    found_gonal_map := true;
	    else
		vprintf ModularGonality, 1 : 
		    "Looking for functions of degree %o...\n", d;
		found_gonal_map := ExistsDivisorOfDegree(AFF, d);
	    end if;
	end while;
	LB := d;
    end for;
    return LB;
end intrinsic;
