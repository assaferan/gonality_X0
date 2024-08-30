// AttachSpec("gonality.spec");
// import "new_models.m" : eqs_quos;
eqs_quos := X0NQuotientEquations;
// Some useful functions

// Construct a hyperelliptic curve, given Taylor expansions of differential forms at a rational cusp
function X0Hyperelliptic(forms, prec)
    fs := [qExpansion(f, prec) : f in forms];
    QQ := Rationals();
    // The following assumes X_0(N) is hyperelliptic
    g := #fs;
    x<q> := fs[g-1] / fs[g];
    y := q * Derivative(x) / fs[g];
    mons := [x^i : i in [0..2*g+2]] cat [-y^2];
    denom := q^(-(2*g+2)*Valuation(x));
    f_mons := [denom*m + O(q^AbsolutePrecision(y)) : m in mons];
    ker := Kernel(Matrix([AbsEltseq(f : FixedLength) : f in f_mons]));
    assert Dimension(ker) eq 1;
    ker_b := Basis(ker)[1];
    ker_b /:= -ker_b[2*g+4];
    R<x> := PolynomialRing(QQ);
    poly := &+[ker_b[i+1]*x^i : i in [0..2*g+2]];
    X0N<X,Y,Z> := HyperellipticCurve(-poly); // This is the curve X_0(N)
    return X0N;
end function;

forward FindCurveSimple;

function X0Elliptic(fs, prec)
    // creating an embedded model
    // TODO - check the degrees are correct here
    X0N<[x]> := FindCurveSimple(fs, prec, 2);
    qexps := [qExpansion(f, prec) : f in fs];
    cusp_seq := [];
    min_v := Minimum([Valuation(f) : f in qexps]);
    for f in qexps do
	Append(~cusp_seq, Coefficient(f,min_v));
    end for;
    cusp := X0N ! cusp_seq;
    RR, mRR := RiemannRochSpace(2*Place(cusp));
    assert (Dimension(RR) eq 2) and (mRR(RR.2) eq 1);
    x_coord := mRR(RR.1);
    RR, mRR := RiemannRochSpace(3*Place(cusp));
    assert (Dimension(RR) eq 3) and (mRR(RR.3) eq 1)
	   and (mRR(RR.2) eq x_coord);
    y_coord := mRR(RR.1);
    QQ := Rationals();
    P2<X,Y,Z> := ProjectiveSpace(QQ,2);
    phi := map<X0N -> P2 | [x_coord, y_coord, 1]>;
    X0N := Image(phi);
    return X0N, x, x_coord, y_coord;
end function;

// Find (quadratic) relations between such Taylor expansions, and return the quotient ring
// Assume forms[d] has the forms of degree d (weight 2d)
function FindRelations(forms, prec : n_rel := 2)
    grading := &cat[[d : f in forms[d]] : d in [1..#forms]];
    vprintf ModularGonality, 3: "\n\tComputing q-expansions of modular forms...";
    fs := &cat[[qExpansion(f, prec) : f in forms_d] : forms_d in forms];
    vprintf ModularGonality, 3: "Done!";
    QQ := Rationals();
    g := #fs;
    _<q> := Universe(fs);
    R<[x]> := PolynomialRing(QQ,grading);
    degmons := [MonomialsOfWeightedDegree(R, d) : d in [1..n_rel]];
    prods := [[Evaluate(m, fs) + O(q^prec) : m in degmons[d]] :
	      d in [1..n_rel]];
    vprintf ModularGonality, 3: "\n\tDoing linear algebra to find relations...";
    kers := [Kernel(Matrix([&cat[Eltseq(x) : x in AbsEltseq(f : FixedLength)]
			    : f in prod])) : prod in prods];
    vprintf ModularGonality, 3: "Done!\n";
    rels := [[&+[Eltseq(kers[d].i)[j]*degmons[d][j] : j in [1..#degmons[d]]] :
	      i in [1..Dimension(kers[d])]] : d in [1..n_rel]];
    I := ideal<R | &cat rels>;
    A<[x]> := R / I;
    // A<[x]> := FieldOfFractions(R / I);
    return A, I;
end function;

function precisionForCurve(PG : Proof := false)
    genus := Genus(PG);
    max_deg := Maximum(7-genus, 3);
    // This is the precision needed for linearly independent equations
    prec := Binomial(max_deg + genus - 1, max_deg);
    // This is not needed for Gamma0(N)
    // prec *:= Level(PG);
    prec +:= 2;
    if Proof then
	k := 2*max_deg;
	m := Index(PG);
	N := Level(PG);
	// This is the Sturm bound for weight k modular forms
	sturm := Ceiling(k*m/12 - (m-1)/N);
	// we multiply by the level since our q-expansions are in q^{1/N}
	// should replace that by the K that we are using
	// In general, should be the cusp width, but only if this is the
	// uniformizer we are actually using.

	// For Gamma0(N) we don't have to multpily by the level

	// prec := Maximum(prec, sturm * N);
	prec := Maximum(prec, sturm);
    end if;
   
    return prec, max_deg;
end function;

// function: FindCurveSimple
// input: qexps - a list of q-expansions
//        prec - precision
//        n_rel - maximal degree in which we expect to find a relation.
// output: X - a curve describing the image of the canonical embedding using these q-expansions 

function FindCurveSimple(qexps, prec, n_rel)
    R<q> := Universe(qexps);
    K := FieldOfFractions(BaseRing(R));
    _<q> := PowerSeriesRing(K);
    zeta := K.1;
    fs := [f + O(q^prec) : f in qexps];
    g := #fs;
    R<[x]> := PolynomialRing(K,g);
    degmons := [MonomialsOfDegree(R, d) : d in [1..n_rel]];
    prods := [[Evaluate(m, fs) + O(q^prec) : m in degmons[d]] :
	      d in [1..n_rel]];
    // kers := [Kernel(Matrix([AbsEltseq(f) : f in prod])) : prod in prods];
    kers := [Kernel(Matrix([&cat[Eltseq(x) : x in AbsEltseq(f)] : f in prod])) : prod in prods];
    rels := [[&+[Eltseq(kers[d].i)[j]*degmons[d][j] : j in [1..#degmons[d]]] :
	      i in [1..Dimension(kers[d])]] : d in [1..n_rel]];
    // We want to generate the ideal with the lowest possible degree
    is_all := false;
    d := 1;
    not_in_I := rels;
    I := ideal<R | 0>;
    while not is_all do
	I +:= ideal<R | &cat not_in_I[1..d]>;
	not_in_I := [[x : x in r | x notin I] : r in rels];
	is_all := &and[IsEmpty(x) : x in not_in_I];
	d +:= 1;
    end while;
    // This might throw an error in the hyperelliptic case. 
    X := Curve(ProjectiveSpace(R),I);
    return X;
end function;

function FindFormAsRationalFunction(form, R, fs, wt_diff : min_k := 0)
     prec := AbsolutePrecision(form);
     _<q> := Universe(fs);
     degmons := AssociativeArray();
     found := false;
     if min_k eq 0 then min_k := wt_diff; end if;
     k := min_k;
     while (not found) do
 	printf "Trying to find form with weight %o\n", k;
 	for d in {k-wt_diff, k} do
 	    degmons[d] := MonomialsOfWeightedDegree(R, d div 2);
 	end for;
 	prods := [Evaluate(m, fs) + O(q^prec) : m in degmons[k]];
	prods cat:= [form*Evaluate(m, fs) + O(q^prec)
		     : m in degmons[k-wt_diff]];
	mat := Matrix([&cat[Eltseq(x)
			    :  x in AbsEltseq(f)] : f in prods]);
	ker := Kernel(mat);
 	found :=  exists(v){v : v in Basis(ker)
 			| not &and[v[i] eq 0 :
 				   i in [1..#degmons[k]]] and
 			not &and[v[#degmons[k]+i] eq 0 :
 				 i in [1..#degmons[k-wt_diff]]]};
 	k +:= 2;
     end while;
     k -:= 2;
     num := &+[v[i]*degmons[k][i] : i in [1..#degmons[k]]];
     denom := -&+[v[#degmons[k]+i]*degmons[k-wt_diff][i]
 		: i in [1..#degmons[k-wt_diff]]];
     return num / denom;
end function;

function JMap(X, fs : K := 1)
    assert &and[IsWeaklyZero(Evaluate(b, fs)) : b in Basis(Ideal(X))];
    R := CoordinateRing(AmbientSpace(X));
    _<q> := Universe(fs);
    prec := AbsolutePrecision(fs[1]);
    E4 := 240*qExpansion(EisensteinSeries(ModularForms(1,4))[1],prec);
    E4 := Evaluate(E4, q^K) + O(q^prec);
    E4 := FindFormAsRationalFunction(E4, R, fs, 4 : min_k := 4);
    E6 := -504*qExpansion(EisensteinSeries(ModularForms(1,6))[1],prec);
    E6 := Evaluate(E6, q^K) + O(q^prec);
    E6 := FindFormAsRationalFunction(E6, R, fs, 6 : min_k := 6);
    j := 1728*E4^3/(E4^3-E6^2);
    _<[x]> := Parent(j);
    num_j := Numerator(j);
    den_j := Denominator(j);
    P1<s,t> := ProjectiveSpace(Rationals(),1);
    j_map := map<X -> P1 | [num_j, den_j]>;
    return j_map;
end function;

// Given the level N, the cusp space cs, and a vector variable x,
// compute the action of all Atkin-Lehner operators on x (and the genus of the quotient).
// This assumes that the hyperelliptic involution is not AL,
// so the action on x-coordinate and the genus is enough to differentiate between them.

/* Old version
function AtkinLehnerActionInCoordinates(N, cs, x : hyperelliptic := false)
    al_Q := [Q : Q in Divisors(N) | GCD(Q, N div Q) eq 1 and Q ne 1];
    ws := AssociativeArray(al_Q);
    w_x_action := AssociativeArray();
    gs := AssociativeArray(al_Q); // genera
    for Q in al_Q do
	ws[Q] := AtkinLehnerOperator(cs, Q);
	x_w := Vector(x)*ChangeRing(Transpose(ws[Q]),Universe(x));
	// should be a function of x[g-1]/x[g]
	if hyperelliptic then
	    func := x_w[#x-1]/x_w[#x];
	else
	    func := x_w;
	end if;
	// Here we assume the hyperelliptic involution is not Atkin-Lehner,
	// hence each acts differently on the x-coordinate
	assert not IsDefined(w_x_action, func);
	w_x_action[func] := Q;
	gs[Q] := Dimension(Kernel(ws[Q]-1));
    end for;
    return w_x_action, gs;
end function;
*/

function AtkinLehnerActionInCoordinates(N, cs, x : hyperelliptic := false)
    al_Q := [Q : Q in Divisors(N) | GCD(Q, N div Q) eq 1 and Q ne 1];
    ws := AssociativeArray(al_Q);
    w_action := AssociativeArray();
    QQ := Rationals();
    // This is a roundabout way to get from the affine algebra back to the ring
    A := Parent(Numerator(x[1]));
    // I := Ideal(Proj(A));
    // R := Parent(Basis(I)[1]);
    // CC := Curve(ProjectiveSpace(R), I);
    C := Curve(Proj(A));
    FFC := FunctionField(C);
    xx := FFC!(x[#x-1]/x[#x]);
    // assert xx eq b;
    for Q in al_Q do
	ws[Q] := AtkinLehnerOperator(cs, Q);
	x_w := Vector(x)*ChangeRing(Transpose(ws[Q]),Universe(x));
	// should be a function of x[g-1]/x[g]
	if hyperelliptic then
	    func_x := x_w[#x-1]/x_w[#x];
	    wx := FFC!func_x;
	    // Needs to check that wx is a function of b!!!
	    // How do we invert if this is not the case?
	    
	    _<t> := FunctionField(QQ);
	    if (Genus(C) eq 0) then
		func_t := Parent(t)!wx;
	    else
		func_t := Evaluate(wx, [t]);
	    end if;
	    func_y_div_y := Evaluate(Derivative(func_t), x[#x-1]/x[#x])
			    / x_w[#x] * x[#x];
	    func := [func_x, func_y_div_y];
	else
	    func := x_w;
	end if;
	assert not IsDefined(w_action, func);
	w_action[func] := Q;
    end for;
    return w_action;
end function;

// Given the curve X0N, the vector of variables x, the action of the ALs on x-coordinates
// and the genus of the quotients, identify the ALs as automorphisms of the curve.

/* Old version
function IdentifyAtkinLehnerAsAutomorphisms(X0N, x, w_x_action, gs : hyperelliptic := false)
    ws := AssociativeArray();
    if hyperelliptic then
	_<X,Y,Z> := X0N;	
	id_map := IdentityMap(X0N);
	auts := Automorphisms(X0N);
	involutions := [a : a in auts | a*a eq id_map and a ne id_map];
	alg_maps := [AlgebraMap(inv) : inv in involutions];
	inv_x_action := [alg_map(X)/alg_map(Z) : alg_map in alg_maps];
	for j->act in inv_x_action do
	    func := Evaluate(act, [x[#x-1],1,x[#x]]);
	    if IsDefined(w_x_action, func) then
		Q := w_x_action[func];
		g := Genus(CurveQuotient(AutomorphismGroup(X0N, [id_map, involutions[j]])));
		if gs[Q] eq g then
		    ws[Q] := involutions[j];
		end if;
	    end if;
	end for;
    else
	for func in Keys(w_x_action) do
	    Q := w_x_action[func];
	    ws[Q] := Automorphism(X0N, Eltseq(func));
	end for;
    end if;
    return ws;
end function;
*/

// TODO - we should be able to directly define the automorphisms
// from what we know
function IdentifyAtkinLehnerAsAutomorphisms(X0N, x, w_action : hyperelliptic := false)
    ws := AssociativeArray();
    if hyperelliptic then
	_<X,Y,Z> := X0N;	
	id_map := IdentityMap(X0N);
	auts := Automorphisms(X0N);
	involutions := [a : a in auts | a*a eq id_map and a ne id_map];
	alg_maps := [AlgebraMap(inv) : inv in involutions];
	inv_x_action := [alg_map(X)/alg_map(Z) : alg_map in alg_maps];
	g := #x;
	inv_y_action := [alg_map(Y)/alg_map(Z^(g+1)) : alg_map in alg_maps];
	for j->act_x in inv_x_action do
	    func_x := Evaluate(act_x, [x[#x-1],1,x[#x]]);
	    act_y := inv_y_action[j];
	    func_y_div_y := Evaluate(act_y / Y, [x[#x-1]/x[#x],1,1]);
	    func := [func_x, func_y_div_y];
	    if IsDefined(w_action, func) then
		Q := w_action[func];
		ws[Q] := involutions[j];
	    end if;
	end for;
    else
	for func in Keys(w_action) do
	    Q := w_action[func];
	    ws[Q] := Automorphism(X0N, Eltseq(func));
	end for;
    end if;
    return ws;
end function;

function exp_to_Q(e, N, ps)
    ZZ := Integers();
    return &*[ZZ | ps[i]^Valuation(N,ps[i]) : i in [1..#ps] | e[i] eq 1];
end function;

function ALSubgroups(N)
    ZZ := Integers();
    Qs_in_grp := AssociativeArray();
    ps := PrimeDivisors(N);
    W := AbelianGroup([2 : i in [1..#ps]]);
    subs_W := Subgroups(W);
    for H in subs_W do
	exps := {Eltseq(W!h) : h in H`subgroup};
	// Should check that this construction actually takes less time
	// than the two below it
	// we generate all subsets that generate the group
	// For hat we need matrices
	n := Ngens(H`subgroup);
	if (n eq 0) then
	    gens_exps := {{}};
	else
	    G := GL(n,GF(2));
	    Sn := sub<G | [PermutationMatrix(GF(2),s)
			   : s in Generators(Sym(n))]>;
	    gens := {{Eltseq(x) : x in Rows(M)} : M in Transversal(G,Sn)};
	    gens_exps := {{Eltseq(W!(H`subgroup!y)) : y in S} : S in gens};
	end if;
	subsets := &join{{S join T : S in Subsets(exps diff T)}
			 : T in gens_exps};
	assert &and[sub<W | S> eq H`subgroup : S in subsets];
	assert subsets eq {S : S in Subsets(exps) | sub<W | S>
						    eq H`subgroup};
	Qs := {exp_to_Q(e,N,ps) : e in exps};
	Qs_in_grp[Qs] := {{exp_to_Q(e,N,ps) : e in S} : S in subsets};
	/*
	for S in subsets do
	    S_Qs := {exp_to_Q(e,N,ps) : e in S};
	    Qs_in_grp[S_Qs] := Qs;
	end for;
	*/
    end for;
    return Qs_in_grp;
end function;

// Given the AL as automorphisms of the curve,
// constructs the quotients and the quotient maps for all subsets 
function ALQuotients(ws, X0N, Qs_in_grp)
    quots := AssociativeArray();
    maps := AssociativeArray();
    ZZ := Integers();
    
    quots[{1}] := X0N;
    maps[{1}] := IdentityMap(X0N);
    ws[1] := IdentityMap(X0N);

    for S in Keys(Qs_in_grp) do
	H := AutomorphismGroup(X0N, [ws[s] : s in S]);
	quoH, mapH := CurveQuotient(H);
	quots[S] := quoH;
	maps[S] := Extend(mapH);
	if IsHyperelliptic(quoH) and not IsSimplifiedModel(quoH) then
	    quots[S], isom := SimplifiedModel(quoH);
	    maps[S] := maps[S] * isom;
	end if;
    end for;
    
    return quots, maps;
end function;

function precision_for_j(X0N, N)
    is_hyp := IsHyperelliptic(X0N);
    h := Index(Gamma0(N));
    if is_hyp then
	d_y := Degree(X0N.2);
	t := h div 2 + 3;
	num_mons := ((t + (t mod (d_y))) div 2 + 1)*(t div (d_y) + 1);
    else
	g := Rank(CoordinateRing(X0N));
	assert g eq Genus(Gamma0(N));
	h := Index(Gamma0(N));
	maxd := Floor(h/(2*g-2) + 3/2);
        maxprec := Floor(N*(1 + maxd/6)+1);
	return maxprec;
    end if;
    return 2*num_mons+t+2;
end function;

// Find the map to the j-line for a hyperelliptic modular curve
// N is not necessary, but helpful for debugging assertions
function jInvariantHyperelliptic(X0N, cs, N, prec)
    QQ := Rationals();
    
    fs := [qExpansion(f, prec) : f in Basis(cs)];
    g := #fs;
    x<q> := fs[g-1] / fs[g];
    y := q * Derivative(x) / fs[g];
    E4 := qExpansion(Basis(ModularForms(1,4))[1], prec);
    E6 := qExpansion(Basis(ModularForms(1,6))[1], prec);
    j_inv := 1728*E4^3/(E4^3-E6^2) + O(q^prec);
    
    // Evaluate all monomials in x,y up to degree n_rel
    // R<[z]> := PolynomialRing(QQ,2);
    // degmons := &join [MonomialsOfDegree(R, d) : d in [0..n_rel]];
    R<[z]> := PolynomialRing(QQ,[2,-2*Valuation(y)]);
    degmons := &join [MonomialsOfWeightedDegree(R, d) :
		      d in [0..Index(Gamma0(N))+6]];
    
    prods := [Evaluate(m, [x,y]) + O(q^prec) : m in degmons];
    prods_j := prods cat [j_inv*m +O(q^prec) : m in prods];

    // Find relations
    min_v := Minimum([Valuation(f) : f in prods_j]);

    assert prec gt -min_v;
    
    mat := Matrix([&cat[Eltseq(x) :
			x in AbsEltseq(q^(-min_v)*f + O(q^(prec+min_v))
				       : FixedLength)] : f in prods_j]);
    // assert Ncols(mat) gt Nrows(mat);
    ker := Kernel(mat);
    rels_nums := [&+[Eltseq(ker.i)[j]*degmons[j] : j in [1..#degmons]] : i in [1..Dimension(ker)]];
    rels_denoms := [&+[Eltseq(ker.i)[j+#degmons]*degmons[j] : j in [1..#degmons]]
		    : i in [1..Dimension(ker)]];

    assert exists(true_rel){i : i in [1..Dimension(ker)] | rels_nums[i]*rels_denoms[i] ne 0 };

    // create the actual j-map

    F<X,Y> := FunctionField(X0N);
    num := rels_nums[true_rel];
    denom := rels_denoms[true_rel];
    num_XY := Evaluate(num, [X,Y]);
    denom_XY := Evaluate(denom, [X,Y]);
    j_XY := -num_XY/denom_XY;

    assert Degree(j_XY) eq Index(Gamma0(N));
    // assert #Poles(j_XY) eq #Cusps(Gamma0(N));
    // More accurate when there are irrational cusps
    assert &+[Degree(pole) : pole in Poles(j_XY)] eq #Cusps(Gamma0(N));

    j_map := ProjectiveMap(j_XY);
    P1<s,t> := Codomain(j_map);
    
    return j_map;
end function;

// function GetModelandAL(N)
intrinsic GetModelandAL(N::RngIntElt) -> Crv, SeqEnum, SeqEnum, SeqEnum, SeqEnum
{.}
    ZZ := Integers();
    QQ := Rationals();
    vprintf ModularGonality, 2: "Computing required precision...";
    prec, max_deg := precisionForCurve(Gamma0(N) : Proof);
    vprintf ModularGonality, 2: "Done!\nLooking for maximal degree of relations %o using precision %o.\n", max_deg, prec;
    
    cs := CuspForms(N,2);
    fs := Basis(cs);

    // Step 0 - creating the Atkin-Lehner subgroups for N
    Qs_in_grp := ALSubgroups(N);
    
    // Step 1 - look for quadratic relations
    vprintf ModularGonality, 1: "Looking for quadratic relations...";
    A<[x]>, I := FindRelations([fs], prec);
    vprintf ModularGonality, 1: "Done!\n";
    
    g := GenusX0N(N);
    
    num_quad := #[x : x in Basis(I) | Degree(x) eq 2];
    
    is_hyp := (g le 2) or (num_quad ne (g-2)*(g-3) div 2);

    vprintf ModularGonality, 1: "Constructing the curve and Atkin-Lehner involutions...\n";
    // Step 2 - consruct the curve
    if is_hyp then
	if (g eq 1) then
	    // creating an embedded model
	    // TODO - check the degrees are correct here
	    cs := ModularForms(N,2);
	    fs := Basis(cs);
	    X0N<X,Y,Z>, x, x_coord, y_coord := X0Elliptic(fs, prec);
	else
	    X0N<X,Y,Z> := X0Hyperelliptic(fs, prec);
	end if;
	// Step 3 - work out the action of Atkin-Lehners on x-coordinate
	A<[x]> := FieldOfFractions(A);
	w_action := AtkinLehnerActionInCoordinates(N, cs, x :
						     hyperelliptic := is_hyp);

	// Step 4 - create automorphisms of the curve and
	// identify Atkin-Lehners among them
	ws := IdentifyAtkinLehnerAsAutomorphisms(X0N, x, w_action :
						 hyperelliptic := is_hyp);

	// Step 5 - create quotient maps
	quots, maps := ALQuotients(ws, X0N, Qs_in_grp);
    else
	// Instead of this naive implementation - 
	// X0N<[x]> := FindCurveSimple(fs, prec, max_deg);
	// We use the code by Najman and Orlic to produce models
	grps := [S : S in Keys(Qs_in_grp) | S ne {1}];
	al_subsets := [Exclude(S,1) : S in grps];
	als_seq := [[x : x in S] : S in al_subsets];
	X0N<[x]>, ws, pairs, fs := eqs_quos(N, als_seq);
	quots := AssociativeArray(al_subsets);
	maps := AssociativeArray(al_subsets);
	vprintf ModularGonality, 1: "Extending the quotient for S = ";
	for idx->S in grps do
	    vprintf ModularGonality, 1: "%o,", S;
	    quots[S] := pairs[idx][1];
	    maps[S] := Extend(pairs[idx][2]);
	end for;
	quots[{1}] := X0N;
	maps[{1}] := IdentityMap(X0N);
    end if;
    vprintf ModularGonality, 1: "Done!\n";
    return X0N, fs, quots, maps, Qs_in_grp;
// end function;
end intrinsic;

function AbsoluteJmap(X0N, fs)
    N := Level(Universe(fs));
    prec := precision_for_j(X0N, N);

    print "Computing the map to the j-line from this model of X0(N)...";

    is_hyp := IsHyperelliptic(X0N);
    
    // Finding the map to the j-line
    if is_hyp then
	j_map := jInvariantHyperelliptic(X0N, Universe(fs), N, prec);   
    else
	QQ := Rationals();
	R<q> := PowerSeriesRing(QQ);
	fs := [R | qExpansion(f, prec) : f in fs];
	j_map := JMap(X0N, fs);
    end if;
    
    printf "Done!\n";
    return j_map;
end function;

forward CoveringMap;

// Bound is the bound for rational points search

function jRationalPointsOnALQuotients(N : Bound := 1000)

    X0N, fs, quots, maps, Qs_in_grp := GetModelandAL(N);

    // Computing j_map as composition
    N_prime := N div PrimeDivisors(N)[1];

    if N_prime gt 1 then
	X0N_prime, fs_prime := GetModelandAL(N_prime);
	j_map_N_prime := AbsoluteJmap(X0N_prime, fs_prime);
	prec := precision_for_j(X0N, N);
	cover := CoveringMap(X0N, X0N_prime, fs, fs_prime, prec);
	j_map := cover*j_map_N_prime;
    else
	j_map := AbsoluteJmap(X0N, fs);
    end if;

    printf "Computing images of rational points...";
    
    images := AssociativeArray(Keys(maps));
    for S in Keys(maps) do
	C := quots[S];
	g := Dimension(Ambient(C)) + 1;
	print "Searching for rational points on quotient by S = ", S;
	if (g gt 3) or
	   ((g eq 3) and (Genus(C) eq 3) and not IsHyperelliptic(C)) then
	    pts := PointSearch(C, Bound);
	else
	    pts := Points(C : Bound := Bound);
	end if;
	printf "Computing images under the j_map...";
	images[S] := [j_map(pt@@maps[S]) : pt in pts];
	printf "Done!\n";
    end for;

    printf "Done!\n";

    // extending the images to work with every subset
    for grp in Keys(maps) do
	for S in Qs_in_grp[grp] do
	    images[S] := images[grp];
	end for;
    end for;
    
    return images;
end function;

// temporary stuff

// This part id from Philippe's code -
// we want to modify to work for stacky curves
//////////////////
/// simul_diag /// (auxiliary function)
//////////////////

// This is an auxiliary function for later code.

// Input: A sequence of matrices that are involutions
// Output: The matrix T that simultaneuosly diagonalised them and the diagonalised matrices.

simul_diag := function(seqw);
    n := NumberOfRows(seqw[1]);
    Vs := [VectorSpace(Rationals(),n)];

    for w in seqw do
        NVs := [];
        for U in Vs do
            BU := Basis(U);
            N1 := Nullspace(w-1) meet U;
            N2 := Nullspace(w+1) meet U;
            NVs := NVs cat [N1,N2];
            Vs := NVs;
        end for;
     end for;

     new_basis := &cat[Basis(V) : V in NVs | Dimension(V) gt 0];
     T := Matrix(new_basis);
     new_als := [T*w*T^(-1) : w in seqw];
     return T, new_als;
end function;

// This handles the following bug
/*
> AtkinLehnerOperator(ModularForms(5,2),5);
Runtime error: OH NO!!  Didn't find Eisenstein series!
*/

// This is from [Young]
function decompose_character(chi, Q)
    dec := Decomposition(chi);
    triv := DirichletGroup(1)!1;
    chi_Q := triv;
    chi_R := triv;
    for psi in dec do
	if Q mod Modulus(psi) eq 0 then
	    chi_Q *:= psi;
	else
	    chi_R *:= psi;
	end if;
    end for;
    return chi_Q, chi_R;
end function;

// For level raising we use Lemma 3.1 from [Assaf]
function AL_action(chi1, chi2, t, Q, N, k)
    assert IsPrimitive(chi1) and IsPrimitive(chi2);
    chi := chi1 * chi2^(-1);
    N1 := Modulus(chi1);
    N2 := Modulus(chi2);
    N_prime := N1*N2;
    Q1 := GCD(N1, Q);
    Q2 := GCD(N2, Q);
    assert N mod Q eq 0;
    R := N div Q;
    assert GCD(Q,R) eq 1;
    R1 := GCD(N1, R);
    R2 := GCD(N2, R);
    chi_Q, chi_R := decompose_character(chi, Q);
    chi_1_Q, chi_1_R := decompose_character(chi1, Q);
    chi_2_Q, chi_2_R := decompose_character(chi2, Q);
    chi_1_prime := chi_2_Q * chi_1_R;
    chi_2_prime := chi_1_Q * chi_2_R;
    scalar := Evaluate(chi_2_Q, -1) * Evaluate(chi_Q^(-1), R2) * Evaluate(chi_R^(-1), Q2);
    sqrt_arg := Q1 / Q2;
    assert (N div N_prime) mod t eq 0;
    Q_prime := GCD(Q, N_prime);
    t_prime := GCD(Q, (N div (t*N_prime))) * GCD(t, R);
    scalar *:= (t_prime /t)^(k div 2);
    return sqrt_arg, scalar, chi_1_prime, chi_2_prime, t_prime;
end function;

function find_eis(eis, chi1p, chi2p, tp)
    assert exists(j){idx : idx in [1..#eis] |
		     (eis[idx]`eisenstein[1] eq chi1p) and
		     (eis[idx]`eisenstein[2] eq chi2p) and
		     (eis[idx]`eisenstein[3] eq tp)};
    return j;
end function;

function AL_on_eis_char_basis(eis, Q, N, k)
    QQ := Rationals();
    mat := MatrixAlgebra(QQ, #eis)!0;
    for i->e in eis do
	chi1 := e`eisenstein[1];
	chi2 := e`eisenstein[2];
	t := e`eisenstein[3];
	_, c, chi1p, chi2p, tp := AL_action(chi1, chi2, t, Q, N, k);
	if (k eq 2) and IsTrivial(chi1) and IsTrivial(chi2) then
	    mat[i, find_eis(eis, chi1p, chi2p, Q)] := -1;
	    if (tp ne 1) then
		mat[i, find_eis(eis, chi1p, chi2p, tp)] := 1;
	    end if;
	else
	    mat[i, find_eis(eis, chi1p, chi2p, tp)] := c;
	end if;
    end for;
    return mat;
end function;

function AtkinLehner(Q,N,k)
    QQ := Rationals();
    M := ModularForms(N,k);
    M_QQ, emb_QQ := BaseChange(M, QQ);
    E := EisensteinSubspace(M_QQ);
    eis := EisensteinSeries(M_QQ);
    K<zeta_N> := CyclotomicField(EulerPhi(N));
    eis_K := [];
    for e in eis do
	mf := Parent(e);
	mf_K, emb := BaseChange(mf, K);
	Append(~eis_K, emb(e)); 
    end for;
    W := AL_on_eis_char_basis(eis, Q, N, k);
    eisW := [&+[W[i,j]*eis_K[j] : j in [1..#eis]] : i in [1..#eis]];
    if (k ne 2) then
	assert eisW eq [AtkinLehnerOperator(Q, eis_K[i]) : i in [1..#eis]];
    end if;
    cob := Matrix([Eltseq(e) : e in eis]);
    W_eis := ChangeRing(cob^(-1)*W*cob, QQ);
    eis_QQ := Basis(E);
    eis_QQ_W := [&+[W_eis[i,j]*eis_QQ[j] : j in [1..#eis]]
		 : i in [1..#eis]];
    if (k ne 2) then
	assert eis_QQ_W eq [AtkinLehnerOperator(Q,eis_QQ[i]) : i in [1..#eis]];
    end if;
    C := CuspidalSubspace(M_QQ);
    cfs_QQ := Basis(C);
    if Dimension(C) gt 0 then	
	W_cfs := Matrix([Eltseq(AtkinLehnerOperator(Q,f)) : f in cfs_QQ]);
	W_EC := DirectSum(W_eis, W_cfs);
    else
	W_EC := W_eis;
    end if;
    cob := Matrix([Eltseq(M_QQ!e) : e in eis_QQ] cat
		  [Eltseq(M_QQ!f) : f in cfs_QQ]);
    W := cob^(-1) * W_EC * cob;
    d := Dimension(M_QQ);
    WB := [&+[W[i,j]*Basis(M_QQ)[j] : j in [1..d]] : i in [1..d]];
    if (k ne 2) then
	assert WB eq [AtkinLehnerOperator(Q,f) : f in Basis(M_QQ)];
	assert AtkinLehnerOperator(M, Q) eq W;
    end if;
    return W;
end function;

// We dont realy need this
function DirectSumList(lst)
    if IsEmpty(lst) then
	return MatrixAlgebra(Universe(lst),0)!0;
    end if;
    A := lst[1];
    for B in lst[2..#lst] do
	A := DirectSum(A,B);
    end for;
    return A;
end function;

function all_diag_basis(N, ks)
    QQ := Rationals();
    mfs := [ModularForms(N, k) : k in ks];
    g := &+[Dimension(M) : M in mfs];

    al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];

    al_invols := [* AssociativeArray(al_inds) : M in mfs *];
    for i in [1..#mfs] do
	for d in al_inds do
	    al_invols[i][d] := AtkinLehner(d, N, ks[i]);
	end for;
    end for;

    new_al_invols := [* AssociativeArray(al_inds) : M in mfs *];
    NBs := [* *];
    
    for i->al_M in al_invols do
	T, new_als := simul_diag(Values(al_M));
	for j in [1..#al_inds] do
	    new_al_invols[i][al_inds[j]] := new_als[j];
	end for;
	//Append(~new_al_invols, new_als);
	M := mfs[i];
	M_QQ := BaseChange(M, QQ);
	B := Basis(M_QQ);
	cleardenom := LCM([Denominator(x) : x in Eltseq(T)]);
	NB := [&+[cleardenom*T[i,j]*B[j] : j in [1..#B]] : i in [1..#B]];
	Append(~NBs, NB);
    end for;
    
    return NBs, new_al_invols;
end function;

// This is based on [VZB]
function get_degrees(s)
    g := s[1];
    e := s[2];
    delta := s[3];
    assert delta ge 1;
    r := #e;
    if (r eq 0) and (g ge 1) then
	// This is Theorem 4.1.3 in DZB+Voight Stacky curve paper
	// for log curves
	gen_degs := [3,2,1,1];
	rel_degs := [6,4,3,2];
	idx := Minimum(delta, 4);
	gen_deg := gen_degs[idx];
	rel_deg := rel_degs[idx];
	return gen_deg, rel_deg;
    end if;
    if (r eq 0) and (g eq 0) then
	// This follows from the discussion of the genus 0 case
	gen_degs := [0,1,1,1];
	rel_degs := [0,0,0,2];
	idx := Minimum(delta, 4);
	gen_deg := gen_degs[idx];
	rel_deg := rel_degs[idx];
	return gen_deg, rel_deg;
    end if;
    e := Maximum(e);
    // We try to do better using theorem 8.3.1
    if (g ge 2) or ((g eq 1) and (r + 2*delta ge 2)) or
       ((g eq 0) and (delta eq 2)) then
	elliptic := (r eq 1) select [] else Remove(s[2],e);
	s_prime := <s[1], elliptic, s[3]>;
	gen_deg_prime, rel_deg_prime := get_degrees(s_prime);
	// y_e is an extra generator of degree e
	gen_deg := Maximum(e, gen_deg_prime);
	// description of relations in 8.3.1 (ii) suggests the following
	rel_deg := Maximum(rel_deg_prime, e + gen_deg_prime);
	if (e ge 3) then
	    rel_deg := Maximum(rel_deg, 2*e);
	end if;
	return gen_deg, rel_deg;
    end if;
    if g ge 1 then
	// This is Theorem 8.4.1 in stacky curve
	gen_deg := Maximum(3,e);
	rel_deg := 2*gen_deg;	
    else
	if delta eq 0 then
	    if r eq 3 then 
		exceptional := [[2,3,7],[2,3,8],[2,3,9],[2,4,5],[2,5,5],[3,3,4],[3,3,5],
				[3,3,6],[3,4,4],[3,4,5],[4,4,4]];
		gen_degs := [21,15,9,10,6,12,9,6,8,5,4];
		rel_degs := [42,30,24,20,16,24,18,15,16,16,5];
	    elif r eq 4 then
		exceptional := [[2,2,2,3], [2,2,2,4],[2,2,2,5],[2,2,3,3],
				[2,2,3,4],[2,3,33]];
		gen_degs := [9,7,5,6,4,3];
		rel_degs := [18,14,12,12,13,9];
	    elif r eq 5 then
		exceptional := [[2,2,2,2,2],[2,2,2,2,3]];
		gen_degs := [5,3];
		rel_degs := [10,8];
	    else
		exceptional := [[2 : i in [1..r]]];
		gen_degs := [3];
		rel_degs := [6];
	    end if;
	    
	    if s[2] in exceptional then
		idx := Index(exceptional, s[2]);
		gen_deg := gen_degs[idx];
		rel_deg := rel_degs[idx];
	    end if;
	else
	    // Theorem 9.3.1
	    gen_deg := e;
	    rel_deg := 2*e;
	end if;
    end if;

    return gen_deg, rel_deg;
end function;

function find_prec_j_canonical(N, gen_deg)
    s := Signature(Gamma0(N));
    g := s[1];
    nu2 := #[e : e in s[2] | e eq 2];
    nu3 := #[e : e in s[2] | e eq 3];
    ncusps := s[3];
    h := Index(Gamma0(N));
    k := 2*gen_deg;
    degL:= ((k*(2*g-2)) div 2 + Floor(k/4)*nu2 + Floor(k/3)*nu3
	    + (k div 2)*ncusps);
    old_degL := 0;
    old_degL := degL;
    maxd := Floor((h + g - 1)/degL) + 1;
    mind := maxd - 1;
    maxprec := Floor(N*(k*maxd/12 + 1)) + 1;
    return maxprec, mind, maxd;
end function;

function StackyCurveAL(N)
    gen_deg, rel_deg := get_degrees(Signature(Gamma0(N)));

    k := 2*rel_deg;
    h := Index(Gamma0(N));
    prec := (k*h) div 12 + 1;

    fs, als := all_diag_basis(N, [2..2*gen_deg by 2]);

    big_als := AssociativeArray(Keys(als[1]));
    for d in Keys(als[1]) do
	big_als[d] := DirectSumList([* al[d] : al in als *]);
    end for;
    // big_als := [DirectSumList([* al[i] : al in als *]) : i in [1..#als[1]]];
    
    _, I := FindRelations(fs, prec : n_rel := rel_deg);
    R := Universe(Basis(I));
    X<[x]> := Curve(ProjectiveSpace(R), I);

    return X, big_als, fs;
    
    // als_X := [ iso<X->X | [w[i,i]*x[i] : i in [1..#x]],
    // [w[i,i]*x[i] : i in [1..#x]]>  : w in big_als];
    
    // prec_j, _, _ := find_prec_j_canonical(N, gen_deg);
    
    // qexps := &cat[[qExpansion(f, prec_j) : f in fs_d] : fs_d in fs];

    /*
    cusp_seq := [];
    min_v := Minimum([Valuation(f) : f in qexps]);
    for f in qexps do
	Append(~cusp_seq, Coefficient(f,min_v));
    end for;
    cusp := X ! cusp_seq;
    */
   
    // j_map := JMap(X,qexps);

    // return X, cusp, qexps, big_als, als_X;
end function;

function StackyALQuotients(X, Qs_in_grp, big_als)
    // Qs_in_grp := ALSubgroups(N);
    // X<[x]>, big_als, fs := StackyCurveAL(N);
    _<[x]> := X;
    quots := AssociativeArray(Keys(Qs_in_grp));
    maps := AssociativeArray(Keys(Qs_in_grp));
    for grp in Keys(Qs_in_grp) do
	gen_subsets := [S : S in Qs_in_grp[grp]];
	_, argmin := Minimum([#S : S in gen_subsets]);
	S := gen_subsets[argmin];
	if IsEmpty(S) then
	    // the trivial quotient
	    quots[grp] := X;
	    maps[grp] := IdentityMap(X);
	    continue;
	end if;
	mat := Matrix([[GF(2) | (1-d) / 2 :
				d in Diagonal(big_als[Q])] : Q in S]);
	exps_mod_2 := Basis(Kernel(Transpose(mat)));
	ZZ := Integers();
	exps := [ChangeRing(v, ZZ) : v in exps_mod_2];
	e := [Vector([0 : j in [1..i-1]] cat [1] cat [0 : j in [i+1..#x]])
	      : i in [1..#x]];
	exps cat:= [2*v : v in e | v notin exps];
	mons := [&*[x[i]^v[i] : i in [1..#x]] : v in exps];
	degmons := Sort([<Degree(m),m> : m in mons]);
	wts := [dm[1] : dm in degmons];
	mons := [dm[2] : dm in degmons];
	QQ := Rationals();
	P<[y]> := ProjectiveSpace(QQ, wts);
	maps[grp] := map<X->P | mons>;
	quots[grp] := Image(maps[grp]);
	maps[grp] := map<X->quots[grp] | mons>;
    end for;
    return quots, maps;
end function;

function CoveringMap(X0N, X0N_prime, fs_N, fs_N_prime, prec)
    // The commented out code works for stacky curves, if we want it
    // assert N mod N_prime eq 0;
    // X0N<[x]>, big_alsN, fs_N := StackyCurveAL(N);
    // bases := [* Matrix([Eltseq(Universe(fs_N[d])!f)
//			: f in fs_N[d]]) : d in [1..#fs_N] *];
    // X0N_prime<[y]>, big_alsN_prime, fs_N_prime := StackyCurveAL(N_prime);
    // targets := [* Matrix([Eltseq(Universe(fs_N[d])!f)
	//		  : f in fs_N_prime[d]]) : d in [1..#fs_N_prime] *];
    // lin_combs := [* targets[j]*bases[j]^(-1) : j in [1..#targets] *];
    // T := DirectSumList(lin_combs);
    QQ := Rationals();
    _<[x]> := X0N;

    basis := Matrix([Eltseq(Universe(fs_N)!f) : f in fs_N]);
    target := Matrix([Eltseq(Universe(fs_N)!f) : f in fs_N_prime]);
    lin_comb := ChangeRing(target,QQ)*ChangeRing(basis, QQ)^(-1);
    
    if IsHyperelliptic(X0N_prime) then
	g := Genus(X0N_prime);
	assert #fs_N_prime eq g;
	
	mat := Submatrix(lin_comb,[g-1..g],[1..#fs_N]);
	x_mat := Vector(x)*ChangeRing(Transpose(mat), Universe(x));
	x_exp := x_mat[1] / x_mat[2];
	
	qexps_N := [qExpansion(f, prec) : f in fs_N];
	qexps_N_prime := [qExpansion(f, prec) : f in fs_N_prime];

	x_ser<q> := qexps_N_prime[g-1] / qexps_N_prime[g];

	assert IsWeaklyZero(Evaluate(x_exp, qexps_N) - x_ser);
	
	y_ser := q * Derivative(x_ser) / qexps_N_prime[g];
	v_y := Valuation(y_ser);
	N := Level(Universe(fs_N));
	N_prime := Level(Universe(fs_N_prime));
	max_deg := Index(Gamma0(N)) div Index(Gamma0(N_prime));
	R := CoordinateRing(Ambient(X0N)); 
	degmons := &join[MonomialsOfDegree(R,d) : d in [0..max_deg]];
	prods := [q^(-v_y)*Evaluate(m, qexps_N) + O(q^(prec+v_y))
		  : m in degmons];
	prods cat:= [q^(-v_y)*y_ser*Evaluate(m, qexps_N) + O(q^(prec+v_y))
		     : m in degmons];
	mat := Matrix([&cat[Eltseq(x) :  x in AbsEltseq(f : FixedLength)]
		       : f in prods]);
	ker := Kernel(mat);
	found := exists(v){v : v in Basis(ker) |
			   not &and[v[i] eq 0 : i in [1..#degmons]]
			       and not &and[v[#degmons+i] eq 0
					    : i in [1..#degmons]]};
	assert found;
	num := &+[v[i]*degmons[i] : i in [1..#degmons]];
	denom := -&+[v[#degmons+i]*degmons[i] : i in [1..#degmons]];
	y_exp := num/denom;

	assert IsWeaklyZero(Evaluate(y_exp, qexps_N) - y_ser);

	coords := [x_exp, y_exp, 1];
    else
	T := lin_comb;
	coords := Eltseq(Vector(x)*ChangeRing(Transpose(T), Universe(x)));
    end if;
    cover := map<X0N->X0N_prime | coords>;
    return cover;
end function;	


// At the moment these down here dont work for silly reasons
// !! TODO - make them usable. 
// Using Jeremy's jmap function (with all the Groebner basis improvements)

function MissingMonomials(I, maxd)
    R := I^0;
    Md := [mon : mon in MonomialsOfDegree(R, 2) | not (mon in I)];
    M := [[], Md];
    r := Rank(R);
    for d in [3..maxd] do
        nmon := Binomial(r+d-1, d);
        if nmon gt r * #M[#M] then
            Md := {mon * R.i : mon in M[#M], i in [1..r]};
        else
            Md := MonomialsOfDegree(R, d);
        end if;
        Append(~M, [mon : mon in Md | not mon in I]);
    end for;
    return M;
end function;

function nicefy(M)
  M0, T := EchelonForm(M);
  // Rows of T give current basis.
  ee := Eltseq(M0);
  denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
  vprint User1: Sprintf("Nicefying %ox%o matrix.",NumberOfRows(M),NumberOfColumns(M));
  M2 := Matrix(Integers(),NumberOfRows(M),NumberOfColumns(M),[ denom*ee[i] : i in [1..#ee]]);
  vprint User1: "Computing saturation.";
  //SetVerbose("Saturation",2);
  AA := Saturation(M2);
  vprint User1: "Done.";
  chk, mult := IsConsistent(ChangeRing(M2,Rationals()),ChangeRing(AA,Rationals()));
  curbat := denom*mult*T;
  vprint User1: "Calling LLL.";
  newlatbasismat, change := LLL(AA : Proof := false);
  vprint User1: "Done.";
  finalbat := ChangeRing(change,Rationals())*curbat;
  return finalbat;
end function;

function AbsoluteJMap(X, fs, prec, N)
    psi := Basis(Ideal(X));
    // Assumes we are using weight 2 modular forms, change later
    g := Genus(Gamma0(N));
    h := Index(Gamma0(N));
    maxd := Floor(h/(2*g-2) + 3/2);
    if ((maxd-1) ge h/(2*g-2)) and ((maxd-1) le (h/(2*g-2) + 1/2)) then
	mind := maxd-1;
	vprint User1: Sprintf("The smallest degree that might work is %o.", mind);
	vprint User1: Sprintf("Degree %o definitly works.", maxd);
    else
	mind := maxd;
	vprint User1: Sprintf("The smallest degree that might work is %o and it definitely works.", maxd);
    end if;
    R<q> := LaurentSeriesRing(Rationals());
    modforms := [qExpansion(f, prec) : f in fs];
    modforms := [R | qexp : qexp in modforms];

    // Build log-canonicalish ring

    polyring := PolynomialRing(Rationals(),#modforms,"grevlex");
    vars := [ polyring.i : i in [1..#modforms]];
    gens := [ Evaluate(psi[j],vars) : j in [1..#psi]];
    I := ideal<polyring | gens>;
    G := GroebnerBasis(I);
    LMs := [ LeadingMonomial(G[i]) : i in [1..#G]];
    initideal := ideal<polyring | LMs>;

    // canring is a tuple of pairs.
    // The first thing in a pair is list of Fourier expansions
    // of the degree d generators of the canonical ring.
    // The second thing in a pair is list of degree d
    // monomials representing the
    // elements.

    canring := <<modforms,vars>>;

    // Let's choose monomials that will *always* work!

    multcount := 0;
    doneper := -1;
    missing_monomials := MissingMonomials(initideal, maxd);
    total := &+[ #mons : mons in missing_monomials];
    for d in [2..maxd] do
	bas := missing_monomials[d];
	newfourier := <>;
	newvars := [];
	for curmon in bas do
	    // We have to be able to write curmon as a product of a degree (d-1)
	    // monomial not in initideal, and a degree 1 element.
	    // If we couldn't, then curmon would be in initideal
	    ind := Index([ IsDivisibleBy(curmon,canring[d-1][2][k]) : k in [1..#canring[d-1][2]]],true);
	    chk, q := IsDivisibleBy(curmon,canring[d-1][2][ind]);
	    ind2 := Index(vars,q);
	    multcount := multcount + 1;
	    if Floor(100*multcount/total) gt doneper then
		doneper := Floor(100*multcount/total);
		vprint User1: Sprintf("Doing multiplication %o of %o. %o\%% complete.", multcount, total, doneper);
	    end if;
	    newprd := modforms[ind2]*canring[d-1][1][ind];
	    Append(~newfourier,newprd);
	    Append(~newvars,curmon);
	end for;
	Append(~canring,<newfourier,newvars>);
    end for;

    _<q> := R;
   
    j := (1728*Eisenstein(4,q : Precision := prec+2)^3)/(Eisenstein(4,q : Precision := prec+2)^3 - Eisenstein(6,q : Precision := prec+2)^2);

    func := j;
    done := false;

    curd := mind;
    jmat := ZeroMatrix(Rationals(),0,prec);
    for i in [1..#canring[curd][1]] do
	vecseq := [];
	pp := (func*canring[curd][1][i]);
	vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-1..-1+prec-1]]);
	jmat := VerticalJoin(jmat,Matrix(Rationals(),1,prec,vecseq));
    end for;

    for i in [1..#canring[curd][1]] do
	vecseq := [];
	pp := -canring[curd][1][i];
	vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-1..-1+prec-1]]);
	jmat := VerticalJoin(jmat,Matrix(Rationals(),1,prec,vecseq));
    end for;
    NN := NullSpace(jmat);
    dimdim := Dimension(NN);
    vprint User1: Sprintf("For d = %o, dimension of null space is %o.", curd, dimdim);
    if dimdim ge 1 then
	found :=  exists(v){v : v in Basis(NN)
 			    | not &and[v[i] eq 0 :
 				       i in [1..#canring[curd][1]]] and
 				  not &and[v[#canring[curd][1]+i] eq 0 :
 					   i in [1..#canring[curd][1]]]};
	
	if found then done := true; end if;
    end if;
    
    if (done eq false) then
	curd := maxd;
	jmat := ZeroMatrix(Rationals(),0,prec);
	for i in [1..#canring[curd][1]] do
	    vecseq := [];
	    pp := (func*canring[curd][1][i]);
	    vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-1..-1+prec-1]]);
	    jmat := VerticalJoin(jmat,Matrix(Rationals(),1,prec,vecseq));
	end for;
	
	for i in [1..#canring[curd][1]] do
	    vecseq := [];
	    pp := -canring[curd][1][i];
	    vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-1..-1+prec-1]]);
	    jmat := VerticalJoin(jmat,Matrix(Rationals(),1,prec,vecseq));
	end for;
	NN := NullSpace(jmat);
	vprint User1: Sprintf("For d = %o, dimension of null space is %o.", curd, Dimension(NN));
    end if;

    // Now actually write down the map to the j-line
    canringdim := #canring[curd][1];
    assert exists(j){j : j in [1..Dimension(NN)]
 		     | not &and[Basis(NN)[j][i] eq 0 :
 				i in [1..canringdim]] and
 			   not &and[Basis(NN)[j][canringdim+i] eq 0 :
 				    i in [1..canringdim]]};
    nullmat := Matrix(Basis(NN));
    changemat := nicefy(nullmat);
    v := (changemat*nullmat)[j];
    num := &+[ (polyring!v[i])*canring[curd][2][i] : i in [1..canringdim]];
    denom := &+[ (polyring!v[i+canringdim])*canring[curd][2][i] : i in [1..canringdim]];
    weakzero := &+[ v[i]*canring[curd][1][i] : i in [1..canringdim]]*func - &+[ v[i+canringdim]*canring[curd][1][i] : i in [1..canringdim]];
    assert IsWeaklyZero(weakzero);
    
    jmap := map<X -> ProjectiveSpace(Rationals(),1) | [num,denom]>;

    return jmap;
end function;
