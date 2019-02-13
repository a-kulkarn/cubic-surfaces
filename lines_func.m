

// Computing the Brundu-logar normal form

// Algortithm:
// 1. Compute an L-set
// 2. Compute the transformation taking the standard L-set to the given one
// 3. pullback


// I don't know why this isn't in Magma already
function Variables(R)
    if Type(R) eq RngUPol then
	return [R.1];
    elif Type(R) eq RngMPol then
        return [R.i : i in [1..Rank(R)]];
    end if;
    error "R must be a Polynomial Ring.";
end function;

//***********************************************
//    Main Groebner solving engine.
//

// Computes the set of solutions of a zero dimensional affine scheme
// and the field of definition.
//
// INPUTS:
// I -- An ideal in a multivariate polynomial ring over the rational field.
// Qp-- Completion of QQ at a prime.
//
// OUTPUTS:
// -- the set of points of the affine scheme associated to I over Qp.
// -- the field of definition of these points as an extension of Qp. 
function pAdicSolutionsOverSplittingField(I, Qp)

    R := Generic(I);     // Who names these things???
    gs := GroebnerBasis(I);

    u := UnivariatePolynomial(gs[#gs]);
    up := ChangeRing(u,Qp);
    K := SplittingField(up);
    
    vars_padic := Variables(ChangeRing(R,K));
    padic_rts := Roots(ChangeRing(up,K));
    
    function backSolve(rt)
	rt_coords := [rt];
	for i in [#gs-1 .. 1 by -1]  do
            g := Evaluate(gs[i], vars_padic[1..i] cat rt_coords);
            rti := Roots(UnivariatePolynomial(g));
            assert #rti eq 1;
            Insert(~rt_coords, 1, rti[1][1]);
	end for;
	return rt_coords;
    end function;

    return [ backSolve(rt[1]) : rt in padic_rts], K;
end function;


//***********************************

// Lines are returned as a 4x2 matrix with pAdic entries
// corresponding to a pair of distinct linear forms
function FormsOfpAdicLines(X : Place:=2, AbsolutePrecision:=10000)
    
    if Type(X) eq Sch then
	// Ensure that X is a cubic surface.
	assert Dimension(AmbientSpace(X)) eq 3;
	assert Degree(X) eq 3;
	assert Dimension(X) eq 2;
	assert Characteristic(BaseRing(X)) eq 0;
        f := DefiningEquation(X);
    elif Type(X) eq RngMPolElt then
	f := X;
    else
	error "Type of argument is", Type(X)," . Must be of type Sch or RngMPolElt.";
    end if;
    
    print "Warning: program is unstable and assumes a certain affine chart contais all lines.";

    k := BaseRing(Parent(f));
    Qp := pAdicField(Place , AbsolutePrecision);

    h<h1,h2,h3,h4> := PolynomialRing(k,4);
    Rt<t> := PolynomialRing(h);

    // Some chart of the Stiefel coordinates is made here.
    ll := [ 1, t, h.1 + t*h.3, h.2+t*h.4]; 
    eqns := Coefficients(Evaluate(f,ll));

    I := ideal<h|eqns>;    
    h_solutions, K := pAdicSolutionsOverSplittingField(I, Qp);
    
    function FormatSol(sol)
        return Matrix(K, [[ 1, 0, sol[1], sol[2]], [0,1,sol[3],sol[4]]]);
    end function;
    
    function Dualize(sol)
	return Transpose(Matrix(Basis(NullspaceOfTranspose(sol))));
    end function;

    return [Dualize(FormatSol(sol)) : sol in h_solutions], K;
    
end function;

// construct the incidence graph of the lines.
function LinesIncidenceGraph(lines)
    number_of_lines:=#lines;
    adjacency_matrix:=ZeroMatrix(Integers(),number_of_lines,number_of_lines);
    for i,j in [1..number_of_lines] do
	if i ne j and IsZero(Determinant(HorizontalJoin(lines[i],lines[j]))) then
	    adjacency_matrix[i,j]:= 1;
	end if;
    end for;
    return  Graph<number_of_lines| adjacency_matrix>;
end function;


// Simple test function
function mytest(f,ll)
    Rt<t> := PolynomialRing(BaseRing(ll));
    v := Vector([1,t]);
    Type(v);
    Type(ll);
    param := Eltseq(v*ChangeRing(ll,Rt));
    fp := ChangeRing(f,BaseRing(ll));
    return [Valuation(co) : co in Coefficients(Evaluate(fp,param))];
end function;

// Trim precision and shorten representation.
function ShortForm(M)
    if Type(M) eq ModTupFldElt then
	M := Matrix(M);
    end if;
    Qpshort := pAdicField(2 : Precision:=13);
    dummy := Matrix(Qpshort, [[1 : i in [1..Ncols(M)]] : i in [1..Nrows(M)]]);
    return ChangeRing((ChangeRing(M, Qpshort) + dummy) - dummy, Rationals());
end function;


// Given 27 lines, construct an L-set.
// Also return the unique line meeting l2,l4, and l5.
function LSet(lines)
    print "Warning: programmer was lazy and assumed choices are symmetric.";

    function IsIntersecting(l1,l2)
	return IsZero(Determinant(HorizontalJoin(l1,l2)));
    end function;

    l2 := lines[1];

    cand := lines[2 .. 27];
    cand := [ ll : ll in cand | IsIntersecting(l2,ll)];
    l1 := cand[1];

    cand := cand[2 .. #cand];
    cand := [ ll : ll in cand | not IsIntersecting(l1,ll)];
    l3 := cand[1];

    cand := cand[2 .. #cand];
    cand := [ ll : ll in cand | not IsIntersecting(l1,ll) and not IsIntersecting(l3,ll)];
    l5 := cand[1];

    l4 := [ ll : ll in lines | IsIntersecting(ll,l1) and
			       IsIntersecting(ll,l3) and
			       not IsIntersecting(ll,l5) and
			       not IsIntersecting(ll,l2)][1];

    return [l1,l2,l3,l4,l5];
end function;


// CONSTRUCT THE TRANSFORM taking an L-set to the standard L-set.
function ConstructTransform(lset)
    
    assert #lset eq 5;
    error if not (Ncols(lset[1]) eq 2 and Nrows(lset[1]) eq 4), 
	  "Lines must be expressed as a 4x2 matrix.";

    Qp := BaseRing(lset[1]);
    
    P21 := Basis(Kernel(HorizontalJoin(lset[1], lset[2])))[1];
    P23 := Basis(Kernel(HorizontalJoin(lset[3], lset[2])))[1];
    P25 := Basis(Kernel(HorizontalJoin(lset[5], lset[2])))[1];
    P41 := Basis(Kernel(HorizontalJoin(lset[1], lset[4])))[1];
    P43 := Basis(Kernel(HorizontalJoin(lset[3], lset[4])))[1];

    // We need one last point on the 5th line to determine it. To do this, 
    // find the plane going through P14, P34, P23. Compute the intersection with l5.
    // We call this point the friend of the L-set.

    // Given 3 points and l5, compute the friend
    function obtainFriend(Lpts, l5)
	M := Matrix(Lpts);
	h := Transpose(Matrix(Basis(NullspaceOfTranspose(M))));
	return Basis(Kernel(HorizontalJoin(h,l5)))[1];
    end function;

    friend := obtainFriend([P41, P43, P23], lset[5]);

    // First, send 4 points to a standard tetrahedron. This determines the transform up
    // to a torus action. We can fix the torus action with the two other points.
    M := Matrix( [P21,P23,P41,P43]);
    MP := Matrix( [P21,P23,P41,P43,P25,friend]);
    T := MP*M^(-1);

    rightEntries := [-T[5,1], T[5,2], -2*T[6,3]*T[5,2]/T[6,2], -2*T[6,4]*T[5,2]/T[6,2]];
    leftEntries := rightEntries[1..4] cat [1, -2*T[5,2]/T[6,2]];
    Dright := DiagonalMatrix(rightEntries)^(-1);
    Dleft := DiagonalMatrix(leftEntries);
    T := Dleft*T*Dright;

    // The standard data from Brundu-Logar 1998.
    P21std := Vector([0,0,0,1]);
    P23std := Vector([0,0,1,0]);
    P25std := Vector([0,0,1,-1]);
    P41std := Vector([1,0,0,1]);
    P43std := Vector([0,1,1,0]);
    l5std := Transpose(Matrix([[1,-1,0,0],[0,0,1,1]]));
    friendstd := obtainFriend([P41std, P43std, P23std], l5std);

    Mstd := Matrix([P21std,P23std,P41std,P43std]);
    MPstd := Matrix([P21std,P23std,P41std,P43std, P25std, friendstd]);
    Tstd := MPstd*Mstd^(-1);

    // return Dleft as well for the sake of printing.
    return M^(-1)*Dright*ChangeRing(Mstd,Qp), Dleft;
end function;

//********************************************************************************************
// Q27: Methods related to question 27. Essentially uses the same engine for the solution.

// Calculate the 27 lines
ZZ := Integers();
k := Rationals();

R<x0,x1,x2,x3> := PolynomialRing(k,4);

// Bernd's cubic.
f := 16384 * x0^3 + 32 * x0^2 * x1 + x0 * x1^2 + 8 * x1^3 + x0^2 * x2
  + 32 * x0 * x1 * x2 + 16384 * x1^2 * x2 + 4194304 * x0 * x2^2
  + 67108864 * x1 * x2^2 + 281474976710656 * x2^3
  + 256 * x0^2 * x3 + 2 * x0 * x1 * x3 + 2 * x1^2 * x3
  + 4 * x0 * x2 * x3 + 512 * x1 * x2 * x3 + 67108864 * x2^2 * x3
	   + 8 * x0 * x3^2 + 32 * x2 * x3^2 + x3^3 + x1 * x3^2;

// Each line is expressed as a 4x2 matrix. i.e, Points_on_lines*Lines = 0.
time lines, Qp := FormsOfpAdicLines(f);


// Finds a double-six. That is, a pair of sets {ai},{bj} of 6 pairwise orthogonal exceptional curves
// such that ai.bj = 1 iff i neq j.
//
// Also return the remaining lines cij, where cij is the unique line incident to ai and bj
// NOTE: cij is equal to cji. This isn't immediately obvious, but follows from the combinatorics.
function DoubleSix(lines)
    // Find a set of 27 pairwise orthogonal exceptional curves
    G := LinesIncidenceGraph(lines);
    A := AdjacencyMatrix(G);
    coG := Complement(G);
    boo, as := HasClique(coG,6);
    as := [Index(v) : v in as];

    // Note that a line on a cubic surface is uniqulely identified from its incidence with a1,...,a6.
    // We use the defining property of the double-six to compute b1,...,b6
    bs := [];
    for i in [1 .. 6] do
	line_id := [1 : i in [1..6]];
	line_id[i] := 0;

	line_cands := [1..#lines];
	for j in [1..6] do
	    line_cands := [ ln : ln in line_cands | A[ln,as[j]] eq line_id[j] ];
	end for;

	assert #line_cands eq 1;
	Include(~bs,line_cands[1]);
    end for;

    // Label the remaining lines in terms of the double-six
    C := ZeroMatrix(Integers(),6,6);
    verts := VertexSet(G);
    for i,j in [1 .. 6] do
	if i eq j then continue; end if;
	C[i,j] := Index(Random(Neighbours(verts ! as[i]) meet Neighbours(verts ! bs[j])));
    end for;
    
    return as,bs,C;
end function;

as,bs,C := DoubleSix(lines);

//*********************************************
// COMBINATORIAL FUNCTIONS: (Move to separate file).

// Given a set S, return the set of lists of the form `[A,B]`, where A,B are disjoint
// two element subsets of S. (Note [A,B] ne [B,A].)
function PairsOfOrderedPairs(S)
    subs := Subsets(S,2);

    function PairListsWithPrefix(a)
	J := S diff a;
	subs_next := Subsets(J,2);
	return { [a,b] : b in subs_next};
    end function;
    
    return &join [PairListsWithPrefix(a) : a in subs];
end function;

// Given a set `S` of size 6, return the different ways of writing S as a disjoint union
// S = A join B of 3-element subsets.
function BalancedPartitionOfSixEltSet(S)
    assert #S eq 6;
    subs := Subsets(S,3);
    return { { a, S diff a} : a in subs };
end function;

/*
Comments regarding the Triederpaar grids.
# 
# CASE 1:
#
[ a_i  b_j  c_ij ]
[ b_k  c_jk a_j  ]
[ c_ik a_k  b_i  ]

SYMMETRIES: S3-permutations of the ai
NUMBER:     20

#
# CASE 2:
#
[ c_ij c_kl c_mn ]
[ c_ln c_im c_jk ]
[ c_km c_jn c_il ]

| step                  | count                                     |     |
|-----------------------+-------------------------------------------+-----|
|                       |                                           |     |
| choose first row      | Binomial(6,2)*Binomial(4,2)*Binomial(2,2) |  90 |
| choose A[2,1] legally | Binomial(4,2)-2                           |   4 |
| choose A[2,2] legally | Binomial(3,2)-1                           |   2 |
| rest is determined    | 1                                         |   1 |
|-----------------------+-------------------------------------------+-----|
| (total distint mats.) |                                           | 720 |
|-----------------------+-------------------------------------------+-----|
| SYMMETRIES            |                                           |     |
|-----------------------+-------------------------------------------+-----|
| row permutations      |                                           |  6! |
| col permutations      |                                           |  6! |
| transpose             |                                           |   2 |
|-----------------------+-------------------------------------------+-----|
| (total symmetries)    |                                           |  72 |
|-----------------------+-------------------------------------------+-----|
|-----------------------+-------------------------------------------+-----|
| FINAL TOTAL           |                                           |  10 |

# NUMBER 10

As a computational note, we obtain non-equivalent representatives from the
10 ways of populating two fixed mutually orthogonal 3x3 latin squares,
with 3 values of {1..6} going to the first square and the other 3 going to
the second. Up to symmetries, this gives all 720 of the 3x3 Steiner matrices.


#
# CASE 3:
#
[ a_i  b_j  c_ij ]
[ b_k  a_l  c_kl ]
[ c_ik c_jl c_mn ]

# SYMMETRIES: S2xS2 permutations of the ai,bi
# NUMBER: 90

###
GRAND TOTAL: 120 distinct Triederpaars.
###
*/

//
// Compute the 3x3 tables of indices corresponding to the 120 distinct Triederpaars.
function TriederpaarIndices(a,b,C)
    triederpaars := [];
    S := {1..6};

    // CASE 1:

    // `I` is a subset of {1..6} of size 3.
    function TypeOneTriederpaar(I)
	ssI := Setseq(I);
	i := ssI[1]; j := ssI[2]; k := ssI[3];
	M := [ [   a[i],    b[j],  C[i,j] ],
	       [   b[k],  C[j,k],    a[j] ],
	       [ C[i,k],    a[k],    b[i] ]];
	return Matrix(Integers(),M);
    end function;

    triederpaars cat:= [TypeOneTriederpaar(I) : I in Subsets(S, 3)];
    
    // CASE 2:    
    // `bpos` is a "balanced partition of S". See function comments for more details.
    function TypeTwoTriederpaar(bpos)
	I := Setseq(Setseq(bpos)[1]);
	J := Setseq(Setseq(bpos)[2]);
	
	/*
	Note that the (i,j)-subscripts of the entries of M are determined by the
	following two pairwise orthogonal 3x3 Latin squares.

	First Latin square:
	[ i  j  k]
	[ j  k  i]
	[ k  i  j]

	Second Latin square:
	[ d  e  f]
	[ f  d  e]
	[ e  f  d]

	Amazingly, permuting the symbols within either square still results in the
	same Triederpaar, even though the associated matrices are not conjugate.
       */
	i := I[1]; j := I[2]; k := I[3];
	d := J[1]; e := J[2]; f := J[3];
	
	M := [ [ C[i,d], C[j,e], C[k,f] ],
	       [ C[j,f], C[k,d], C[i,e] ],
	       [ C[k,e], C[i,f], C[j,d] ]];
	return Matrix(Integers(),M);
    end function;

    triederpaars cat:= [TypeTwoTriederpaar(bpos) : bpos in BalancedPartitionOfSixEltSet(S)];
    
    // CASE 3:
    // `pop` is an ordered set of pairs of pairs. See function comments for more details.
    function TypeThreeTriederpaar(pop)
	apair := Setseq(pop[1]);
	bpair := Setseq(pop[2]);
	i := apair[1]; j := bpair[1];
	k := bpair[2]; l := apair[2];

	nm := Setseq(S diff {i,j,k,l});
	n := nm[1]; m := nm[2];
	
	M := [ [   a[i],    b[j],  C[i,j] ],
	       [   b[k],    a[l],  C[k,l] ],
	       [ C[i,k],  C[j,l],  C[n,m] ]];
	return Matrix(Integers(),M);
    end function;

    triederpaars cat:= [TypeThreeTriederpaar(pop) : pop in PairsOfOrderedPairs(S)];
    
    return triederpaars;
end function;

triederpaar_index_list := TriederpaarIndices(as,bs,C);

// Need a new parent for linear forms
Rp<x0,x1,x2,x3> := ChangeRing(R, Qp);

//
// `M` is the matrix of indices of the 9 lines in one of Steiner's 3x3 matrices.
function TriederpaarFromIndex(lines, M)

    K := BaseRing(Rp);
    
    function HyperplaneFromIndexTriple(inds)
	V := VectorSpace(K,4);
	W := &meet [sub<V| RowSequence(Transpose(lines[i]))> : i in inds];
	assert Dimension(W) eq 1;
	b := Eltseq(Basis(W)[1]);
	return &+[Variables(Rp)[i]*b[i] : i in [1..4]];
    end function;

    row_triple := {HyperplaneFromIndexTriple(tri) : tri in RowSequence(M)};
    col_triple := {HyperplaneFromIndexTriple(tri) : tri in RowSequence(Transpose(M))};
       
    return {row_triple, col_triple};
end function;

triederpaars := [TriederpaarFromIndex(lines, tridp_inds) : tridp_inds in triederpaar_index_list];

// To have cubics, we multiply the three linear forms in the triederpaars together.
summands := [ [ &*tri : tri in tridp] : tridp in triederpaars];

// We confirm that there exist scalar coefficients A,B such that
//    f = A*l_1*l_2*l_3 + B*r_1*r_2*r_3,   with { { l_1,l_2,l_3} , { r_1,r_2,r_3} }
// a triederpaar.
// (the coefficients are of course dependent on the particular triederpaar.)

mons := Monomials( (&+Variables(Rp))^3 );
V := VectorSpace(Qp,#mons);

Ws := [ sub<V | [Vector([ MonomialCoefficient(g,m) : m in mons]) : g in aexprs]>
	: aexprs in summands];

assert #Seqset(Ws) eq 120; // check that the 120 triederpaars are indeed inequivalent.

fvec := Vector(Qp, [ MonomialCoefficient(Rp ! f,m) : m in mons]);

// The moment of truth.
assert &and [ fvec in W : W in Ws];

// Solving for the particular coefficients is linear algebra. We leave this to the reader of
// the code.


//********************************************************************************************
// Start Q26 script.

ZZ := Integers();
k := Rationals();

R<x0,x1,x2,x3> := PolynomialRing(k,4);

// Bernd's cubic.
f := 16384 * x0^3 + 32 * x0^2 * x1 + x0 * x1^2 + 8 * x1^3 + x0^2 * x2
  + 32 * x0 * x1 * x2 + 16384 * x1^2 * x2 + 4194304 * x0 * x2^2
  + 67108864 * x1 * x2^2 + 281474976710656 * x2^3
  + 256 * x0^2 * x3 + 2 * x0 * x1 * x3 + 2 * x1^2 * x3
  + 4 * x0 * x2 * x3 + 512 * x1 * x2 * x3 + 67108864 * x2^2 * x3
	   + 8 * x0 * x3^2 + 32 * x2 * x3^2 + x3^3 + x1 * x3^2;

// Each line is expressed as a 4x2 matrix. i.e, Points_on_lines*Lines = 0.
time lines, Qp := FormsOfpAdicLines(f);
lset := LSet(lines);
Transform := ConstructTransform(lset);


// SOLVE FOR THE BRUNDU-LOGAR COEFFICIENTS
Rp<x,y,z,t> := PolynomialRing(Qp,4);
fbl := Evaluate(f, Eltseq(Vector(Variables(Rp))*ChangeRing(Transform^(-1),Rp)));


// Linearly solve for the coefficients
mons := Monomials(fbl);
coeffs := Coefficients(fbl);

V20 := VectorSpace(Qp,#mons);
fblvec := V20 ! coeffs;

ga := 2*x^2*y - 2*x*y^2 + x*z^2 - x*z*t - y*t^2 + y*z*t;
gb := (x - t)*(x*z + y*t);
gc := (z + t)*(y*t - x*z);
gd := (y - z)*(x*z + y*t);
gg := (x-y)*(y*t-x*z);

gs := [ga,gb,gc,gd,gg];
gvecs := [V20 ! Vector([ MonomialCoefficient(g,m) : m in mons]) : g in gs];


A := Matrix(gvecs cat [fblvec]);
solcoeffs := Eltseq(Basis(Nullspace(A))[1]);
brunduLogarCoefficients :=  [-solcoeffs[i]/solcoeffs[6] : i in [1..5]];
brunduLogarStandardForms := [ga,gb,gc,gd,gg];

// Some statistics and tests.
print "Valuations of Brundu-Logar coefficients:", [Valuation(x) : x in brunduLogarCoefficients];

// test stability of the computation.
testpoly := fbl - &+[brunduLogarCoefficients[i]*brunduLogarStandardForms[i] : i in [1..5]]; 
assert Min([Valuation(co) : co in Coefficients(testpoly)]) gt 9000;
