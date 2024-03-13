/// this code is used to determine lower bounds for the F_p-gonality and hence the Q-gonality

// load "new_models.m";

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

//this function takes a model X of a curve and a prime p of good reduction of the model as input and checks whether there are any degree d functions over F_p. It assumes that #X(F_p)/(p+1)< B+1 (and checks this) which can be used so that only the R-R spaces of divisors supported on at most B F_p-rational points need be checked.
// This generalizes the following functions

intrinsic ExistsFqDegreeUpTo(X::Crv[FldRat], q::RngIntElt, 
			     d::RngIntElt, B::RngIntElt) -> BoolElt
{Returns true if there is a degree d function over F_q, supported on at most B F_p rational points.}
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
    C2:=ChangeRing(C,GF(q));
    FF := FunctionField(C2);
    AFF := AlgorithmicFunctionField(FF);
    pls := [Places(AFF, i) : i in [1..d]];

    assert (#pls[1])/(q+1) lt B+1;

    s := {};
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
		    Include(~s, Dimension(RiemannRochSpace(divisor)));
		end for;
	    end for;
	end for;
    end for;
    if #s eq 1 then 
	return true; 
    end if;
    return false;
end intrinsic;
    
// d = 5, B = 1

//this function takes a model X of a curve and a prime p of good reduction of the model as input and checks whether there are any degree 6 functions over F_p. It assumes that #X(F_p)/(p+1)<2 (and checks this) which can be used so that only the R-R spaces of divisors supported on a single F_p-rational point need be checked 

function fp_deg6_max1(X, q)
D:=DefiningEquations(X);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(X)-1),D2);
C2:=ChangeRing(C,GF(q));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
assert (#pls1)/(q+1) lt 2;
pls3:=Places(AFF,3) ;


// 1+2+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=j to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls2[j]+pls2[k]))};
end for;
end for;
end for;


// 1+4
for i:=1 to #pls1 do
for k:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+Places(AFF,4)[k]))};
end for;
end for;

// 2+3

for i:=1 to #pls2 do
for k:=1 to #pls3 do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+pls3[k]))};
end for;
end for;


// 5
for i:=1 to #Places(AFF,5) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,5)[i]))};
end for;


//2*1 +3
for p in pls1 do 
for q in pls3 do
s:=s  join {Dimension(RiemannRochSpace(p+p+q))};
end for;
end for;

//3*1 +2
for p in pls1 do 
for q in pls2 do
s:=s  join {Dimension(RiemannRochSpace(p+p+p+q))};
end for;
end for;

//5*1
for p in pls1 do 
s:=s  join {Dimension(RiemannRochSpace(p+p+p+p+p))};
end for;

if #s eq 1 then return true; else return false; end if;
end function;



// d = 5, B = 2

//this function takes a model X of a curve and a prime p of goode reduction of the model as input and checks whether there are any degree 6 functions over F_p. It assumes that #X(F_p)/(p+1)<3 (and checks this) which can be used so that only the R-R spaces of divisors supported on at most 2 F_p-rational point need be checked 



function fp_deg6_max2(X, q)
D:=DefiningEquations(X);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(X)-1),D2);
C2:=ChangeRing(C,GF(q));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
assert (#pls1)/(q+1) lt 3;
pls3:=Places(AFF,3) ;


// 1+2+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=j to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls2[j]+pls2[k]))};
end for;
end for;
end for;


// 1+4
for i:=1 to #pls1 do
for k:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+Places(AFF,4)[k]))};
end for;
end for;

// 2+3

for i:=1 to #pls2 do
for k:=1 to #pls3 do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+pls3[k]))};
end for;
end for;


// 5
for i:=1 to #Places(AFF,5) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,5)[i]))};
end for;


//2*1 +3
for p in pls1 do 
for q in pls3 do
s:=s  join {Dimension(RiemannRochSpace(p+p+q))};
end for;
end for;

//3*1 +2
for p in pls1 do 
for q in pls2 do
s:=s  join {Dimension(RiemannRochSpace(p+p+p+q))};
end for;
end for;

//1+2*1+2

for p in pls1 do 
for q in pls1 do
for u in pls2 do
s:=s join {Dimension(RiemannRochSpace(p+q+q+u))};
end for;
end for;
end for;

//1+1+3

for p in pls1 do 
for q in pls1 do
for u in pls3 do
s:=s join {Dimension(RiemannRochSpace(p+q+u))};
end for;
end for;
end for;

/// 3*1+2*1, 4*1+1*1
for p in pls1 do 
for q in pls1 do
s:=s join {Dimension(RiemannRochSpace(p+p+p+q+q))};
s:=s join {Dimension(RiemannRochSpace(p+p+p+p+q))};
end for;
end for;

if #s eq 1 then return true; else return false; end if;
end function;


// d = 5, B = 0

//this function takes a model X of a curve and a prime p of goode reduction of the model as input and checks whether there are any degree 6 functions over F_p. It assumes that #X(F_p)/(p+1)<1 (and checks this) which can be used so that only the R-R spaces of divisors supported on no F_p-rational point need be checked 



function fp_deg6_max0(X, q)
D:=DefiningEquations(X);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(X)-1),D2);
C2:=ChangeRing(C,GF(q));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
assert (#pls1)/(q+1) lt 1;
pls3:=Places(AFF,3) ;

s:={};
//2+2
for i:=1 to #pls2 do
for k:=i to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+pls2[k]))};
end for;
end for;


// 2+3

for i:=1 to #pls2 do
for k:=1 to #pls3 do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+pls3[k]))};
end for;
end for;

// 4

for j:=l to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,4)[j]))};
end for;




// 5
for i:=1 to #Places(AFF,5) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,5)[i]))};
end for;




if #s eq 1 then return true; else return false; end if;
end function;


// the following function checks trigonality: if true, the curve is trigonal if false, we haven't proved anything


function not_trigonal(X, q)
D:=DefiningEquations(X);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),3),D2);
C2:=ChangeRing(C,GF(q));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
div1:=Places(AFF,1);
s:={};
s:=s join{Max([Dimension(RiemannRochSpace(p+q+r)) : p,q,r in div1])};
s:=s join{Max([Dimension(RiemannRochSpace(p+q)) : p in div1, q in Places(AFF,2)])};
s:=s join{Max([Dimension(RiemannRochSpace(p)) : p in Places(AFF,3)])};
if #s eq 1 then return true; else return false; end if;
end function;



function fp_deg8_max0(X, q)
D:=DefiningEquations(X);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(X)-1),D2);
C2:=ChangeRing(C,GF(q));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
assert (#pls1)/(q+1) lt 1;
pls3:=Places(AFF,3) ;
pls4:=Places(AFF,4) ;
pls5:=Places(AFF,5) ;

// 2+2+2
s:={};
for j:=1 to #pls2 do
for k:=j to #pls2 do
for l:=k to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(pls2[j]+pls2[k]+pls2[l]))};
end for;
end for;
end for;
s;

// 2+4
s:={};
for j:=1 to #pls2 do
for k:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(pls2[j]+Places(AFF,4)[k]))};
end for;
end for;
s;

// 3+3
s:={};
for j:=1 to #Places(AFF,3) do
for k:=j to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,3)[j]+Places(AFF,3)[k]))};
end for;
end for;
s;

// 6
s:={};
for k:=1 to #Places(AFF,6) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,6)[k]))};
end for;
s;

// 2+2+3
s:={};
for i:=1 to #pls2 do
for j:=i to #pls2 do
for k:=1 to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+pls2[j]+Places(AFF,3)[k]))};
end for;
end for;
end for;
s;

// 2+5
s:={};
for i:=1 to #pls2 do
for k:=1 to #Places(AFF,5) do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+Places(AFF,5)[k]))};
end for;
end for;
s;

// 3+4
s:={};
for i:=1 to #Places(AFF,3) do
for j:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,3)[i]+Places(AFF,4)[j]))};
end for;
end for;
s;

// 7
s:={};
for i:=1 to #Places(AFF,7) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,7)[i]))};
end for;
s;
end function;



function fp_deg8_max1(X, q)
D:=DefiningEquations(X);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(X)-1),D2);
C2:=ChangeRing(C,GF(q));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
assert (#pls1)/(q+1) lt 2;
pls3:=Places(AFF,3) ;
pls4:=Places(AFF,4) ;
pls5:=Places(AFF,5) ;

s:={};

// 1+2+2+2
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=j to #pls2 do
for l:=k to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls2[j]+pls2[k]+pls2[l]))};
end for;
end for;
end for;
end for;


// 1+2+4
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls2[j]+Places(AFF,4)[k]))};
end for;
end for;
end for;


// 1+3+3
for i:=1 to #pls1 do
for j:=1 to #pls3 do
for k:=j to #pls3 do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls3[j]+pls3[k]))};
end for;
end for;
end for;



// 1+6
for i:=1 to #pls1 do
for k:=1 to #Places(AFF,6) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+Places(AFF,6)[k]))};
end for;
end for;


// 2+2+3
for i:=1 to #pls2 do
for j:=i to #pls2 do
for k:=1 to #pls3 do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+pls2[j]+pls3[k]))};
end for;
end for;
end for;



// 2+5
for i:=1 to #pls2 do
for k:=1 to #Places(AFF,5) do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+Places(AFF,5)[k]))};
end for;
end for;



// 3+4
for i:=1 to #pls3 do
for j:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(pls3[i]+Places(AFF,4)[j]))};
end for;
end for;



// 7
for i:=1 to #Places(AFF,7) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,7)[i]))};
end for;

//2*1+5
for p in pls1 do
for q in pls5 do 
s:=s  join {Dimension(RiemannRochSpace(p+p+q))};
end for;
end for;

//2*1+3+2
for p in pls1 do
for q in pls2 do
for u in pls3 do 
s:=s  join {Dimension(RiemannRochSpace(p+p+q+u))};
end for;
end for;
end for;

//3*1+4
for p in pls1 do
for q in pls4 do 
s:=s  join {Dimension(RiemannRochSpace(p+p+p+q))};
end for;
end for;

//4*1+3
for p in pls1 do
for q in pls3 do 
s:=s  join {Dimension(RiemannRochSpace(p+p+p+p+q))};
end for;
end for;


//5*1+2
for p in pls1 do
for q in pls3 do 
s:=s  join {Dimension(RiemannRochSpace(p+p+p+p+p+q))};
end for;
end for;

//7*1
for p in pls1 do 
s:=s  join {Dimension(RiemannRochSpace(p+p+p+p+p+p+p))};
end for;


if #s eq 1 then return true; else return false; end if;
end function;

function fp_deg8_max2(X, q)
D:=DefiningEquations(X);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(X)-1),D2);
C2:=ChangeRing(C,GF(q));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
assert (#pls1)/(q+1) lt 2;
pls3:=Places(AFF,3) ;
pls4:=Places(AFF,4) ;
pls5:=Places(AFF,5) ;

s:={};

// 2+2+3
s:={};
for i:=1 to #pls2 do
for j:=i to #pls2 do
for k:=1 to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+pls2[j]+Places(AFF,3)[k]))};
end for;
end for;
end for;
s;

// 2+5
s:={};
for i:=1 to #pls2 do
for k:=1 to #Places(AFF,5) do
s:=s  join {Dimension(RiemannRochSpace(pls2[i]+Places(AFF,5)[k]))};
end for;
end for;
s;

// 3+4
s:={};
for i:=1 to #Places(AFF,3) do
for j:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,3)[i]+Places(AFF,4)[j]))};
end for;
end for;
s;

// 7
s:={};
for i:=1 to #Places(AFF,7) do
s:=s  join {Dimension(RiemannRochSpace(Places(AFF,7)[i]))};
end for;
s;

// 1+2+2+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=j to #pls2 do
for l:=k to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls2[j]+pls2[k]+pls2[l]))};
end for;
end for;
end for;
end for;
s;

// 1+2+4
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls2[j]+Places(AFF,4)[k]))};
end for;
end for;
end for;
s;

// 1+3+3
s:={};
for i:=1 to #pls1 do
for j:=1 to #Places(AFF,3) do
for k:=j to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+Places(AFF,3)[j]+Places(AFF,3)[k]))};
end for;
end for;
end for;
s;

// 1+6
s:={};
for i:=1 to #pls1 do
for k:=1 to #Places(AFF,6) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+Places(AFF,6)[k]))};
end for;
end for;
s;

// 1+1+2+3
s:={};
for i:=1 to #pls1 do
for j:=i to #pls1 do
for k:=1 to #pls2 do
for l:=1 to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls1[j]+pls2[k]+Places(AFF,3)[l]))};
end for;
end for;
end for;
end for;
s;

// 1+1+5
s:={};
for i:=1 to #pls1 do
for j:=i to #pls1 do
for k:=1 to #Places(AFF,5) do
s:=s  join {Dimension(RiemannRochSpace(pls1[i]+pls2[j]+Places(AFF,5)[k]))};
end for;
end for;
end for;
s;

// now we consider the cases with poles of higher multiplicity

// 3*1+2+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=j to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(3*pls1[i]+pls2[j]+pls2[k]))};
end for;
end for;
end for;
s;

// 3*1+4
s:={};
for i:=1 to #pls1 do
for j:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(3*pls1[i]+Places(AFF,4)[j]))};
end for;
end for;
s;

// 4*1+3
s:={};
for i:=1 to #pls1 do
for j:=1 to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(4*pls1[i]+Places(AFF,3)[j]))};
end for;
end for;
s;

// 5*1+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(5*pls1[i]+pls2[j]))};
end for;
end for;
s;

// 7*1
s:={};
for i:=1 to #pls1 do
s:=s  join {Dimension(RiemannRochSpace(7*pls1[i]))};
end for;
s;

// 2*1+1+2+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=j to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(2*pls1[1]+pls1[i]+pls2[j]+pls2[k]))};
end for;
end for;
end for;
s;

// 2*1+1+4
s:={};
for i:=1 to #pls1 do
for j:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(2*pls1[1]+pls1[i]+Places(AFF,4)[j]))};
end for;
end for;
s;

// 1+2*1+2+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
for k:=j to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(pls1[1]+2*pls1[i]+pls2[j]+pls2[k]))};
end for;
end for;
end for;
s;

// 1+2*1+4
s:={};
for i:=1 to #pls1 do
for j:=1 to #Places(AFF,4) do
s:=s  join {Dimension(RiemannRochSpace(pls1[1]+2*pls1[i]+Places(AFF,4)[j]))};
end for;
end for;
s;

// 3*1+1+3
s:={};
for i:=1 to #pls1 do
for j:=1 to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(3*pls1[1]+pls1[i]+Places(AFF,3)[j]))};
end for;
end for;
s;

// 2*1+2*1+3
s:={};
for i:=1 to #pls1 do
for j:=1 to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(2*pls1[1]+2*pls1[i]+Places(AFF,3)[j]))};
end for;
end for;
s;

// 1+3*1+3
s:={};
for i:=1 to #pls1 do
for j:=1 to #Places(AFF,3) do
s:=s  join {Dimension(RiemannRochSpace(pls1[1]+3*pls1[i]+Places(AFF,3)[j]))};
end for;
end for;
s;

// 4*1+1+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(4*pls1[1]+pls1[i]+pls2[j]))};
end for;
end for;
s;

// 3*1+2*1+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(3*pls1[1]+2*pls1[i]+pls2[j]))};
end for;
end for;
s;

// 2*1+3*1+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(2*pls1[1]+3*pls1[i]+pls2[j]))};
end for;
end for;
s;

// 1+4*1+2
s:={};
for i:=1 to #pls1 do
for j:=1 to #pls2 do
s:=s  join {Dimension(RiemannRochSpace(pls1[1]+4*pls1[i]+pls2[j]))};
end for;
end for;
s;

// k*1+(7-k)*1
s:={};
for i:=1 to #pls1 do
for k:=1 to 6 do
s:=s  join {Dimension(RiemannRochSpace(k*pls1[1]+(7-k)*pls1[i]))};
end for;
end for;
s;
end function;
