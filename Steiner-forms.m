

//********************************************************************************************
// Q27: Methods related to question 27. Essentially uses the same engine for the solution.

load "lines_func.m";
load "combinatorics_util.m";


// Finds a double-six. That is, a pair of sets {ai},{bj} of 6 pairwise orthogonal exceptional curves
// such that ai.bj = 1 iff i neq j.
//
// Also return the remaining lines cij, where cij is the unique line incident to ai and bj
// NOTE: cij is equal to cji. This isn't immediately obvious, but follows from the paper of
//       Buckly-Kosir.
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

//
// `Rp` is the future parent of the linear forms.
// `M` is the matrix of indices of the 9 lines in one of Steiner's 3x3 matrices.
function TriederpaarFromIndex(Rp,lines, M)

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

//********************************************************************************************
// START MAIN SCRIPT

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
time lines, K := FormsOfpAdicLines(f);

// Need a new parent for linear forms
Rp<x0,x1,x2,x3> := ChangeRing(R, K);


as,bs,C := DoubleSix(lines);
triederpaar_index_list := TriederpaarIndices(as,bs,C);

triederpaars := [TriederpaarFromIndex(Rp, lines, tridp_inds) : tridp_inds in triederpaar_index_list];

// To get the cubic terms in the Steiner forms,
// we multiply the three linear forms in the triederpaars together.
summands := [ [ &*tri : tri in tridp] : tridp in triederpaars];

// We confirm that there exist scalar coefficients A,B such that
//    f = A*l_1*l_2*l_3 + B*r_1*r_2*r_3,   with { { l_1,l_2,l_3} , { r_1,r_2,r_3} }
// a triederpaar.
// (the coefficients are of course dependent on the particular triederpaar.)

mons := Monomials( (&+Variables(Rp))^3 );
V := VectorSpace(K,#mons);

Ws := [ sub<V | [Vector([ MonomialCoefficient(g,m) : m in mons]) : g in aexprs]>
	: aexprs in summands];

assert #Seqset(Ws) eq 120; // check that the 120 triederpaars are indeed inequivalent.



// The moment of truth.
fvec := V ! Vector(K, [ MonomialCoefficient(Rp ! f,m) : m in mons]);
assert &and [ fvec in W : W in Ws];

print "Computation terminated correctly. Linear forms in Steiner representation given by
      identifier `triederpaars`, up to scaling by a constant. 
      Constants presently not computed.";

// Solving for the particular coefficients is linear algebra. We leave this to the reader of
// the code.


