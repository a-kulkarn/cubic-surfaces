
//********************************************************************************************
// Start Q26 script.

// Computing the Brundu-logar normal form

// Algorithm:
// 1. Compute an L-set
// 2. Compute the transformation taking the standard L-set to the given one
// 3. pullback

load "lines_func.m";

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

// Geiger's data, example:
no := 2;
t  := 2;
fileid := t;


for no in [1,2] do
for tt in [2,3] do

fileid:=tt;
    
// Geiger's first cubic.
if no eq 1 then
    f := tt^143*x0^3 + x0^2*x1 + tt^64*x0^2*x2 + tt^122*x0^2*x3
	 + x0*x1^2 + tt^2*x0*x1*x2 +x0*x1*x3 + tt^15*x0*x2^2
	 + tt^55*x0*x2*x3 + tt^107*x0*x3^2 + tt^36*x1^3 + tt^23*x1^2*x2
	 + tt^39*x1^2*x3 + tt^16*x1*x2^2 + tt^14*x1*x2*x3 + tt^48*x1*x3^2
	 + tt^12*x2^3 + tt^12*x2^2*x3 + tt^49*x2*x3^2 + tt^95*x3^3;
end if;
// Geiger's second cubic.
if no eq 2 then
	f := x0^3 + tt^12*x0^2*x1 + tt^30*x0^2*x2 + x0^2*x3
	     + tt^30*x0*x1^2 + tt^12*x0*x1*x2 +tt^3*x0*x1*x3 + tt^145*x0*x2^2
	     + tt^54*x0*x2*x3 + tt^10*x0*x3^2 + tt^51*x1^3 + x1^2*x2
	     + tt^18*x1^2*x3 + tt^123*x1*x2^2 + tt^30*x1*x2*x3 + x1*x3^2
	     + tt^265*x2^3 + tt^150*x2^2*x3 + tt^80*x2*x3^2 + tt^21*x3^3;
end if;


// Each line is expressed as a 4x2 matrix. i.e, Points_on_lines*Lines = 0.
time lines, Qp := FormsOfpAdicLines(f : Place:=tt);
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
// assert Min([Valuation(co) : co in Coefficients(testpoly)]) gt 9000;

// Write data.
/*
Write("Geiger-transform-no:"*Sprint(no)*"-"*"p:"*Sprint(fileid), Transform);
Write("Geiger-BrunduLogar-no:"*Sprint(no)*"-"*"p:"*Sprint(fileid), fbl);
Write("Geiger-lines-no:"*Sprint(no)*"-"*"p:"*Sprint(fileid), lines);
*/

// Write the Brundu-logar forms of the lines.
BL_lines := [Transform*line : line in lines];
// Write("Geiger-BL-lines-no:"*Sprint(no)*"-"*"p:"*Sprint(fileid), BL_lines );

// Write the Tropicalizations.

// Take a 4x2 matrix and compute the tropicalizations of the minors.
function TropicalizeLine(line)
    return [Valuation(minor) : minor in Minors(line,2)];
end function;

trop_lines := [TropicalizeLine(line) : line in lines];
BL_trop_lines := [TropicalizeLine(line) : line in BL_lines];

Write("Geiger-lines-tropical-no:"*Sprint(no)*"-"*"p:"*Sprint(fileid), trop_lines);
Write("Geiger-BL-lines-tropical-no:"*Sprint(no)*"-"*"p:"*Sprint(fileid), BL_trop_lines );

end for;
end for;
