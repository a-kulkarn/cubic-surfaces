
//********************************************************************************************
// Start Q26 script.

// Computing the Brundu-logar normal form

// Algorithm:
// 1. Compute an L-set
// 2. Compute the transformation taking the standard L-set to the given one
// 3. pullback

include "lines_func.m";

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
