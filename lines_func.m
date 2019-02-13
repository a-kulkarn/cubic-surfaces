

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
