
k = GF(13)
RP4.<x,y,z,w,t> = PolynomialRing(k,5, order='lex')
P4 = ProjectiveSpace(RP4)

# Some random list of cubics.
cubs = [8*x^3+5*x^2*y+x*y^2+4*y^3+4*x^2*z+9*x*y*z+2*y^2*z+6*x*z^2+5*z^3+x^2*w
+x*y*w+2*y^2*w+3*x*z*w+9*y*z*w+5*z^2*w+7*x*w^2+4*y*w^2+6*w^3,4*x^3+4*x*y^2+
6*y^3+x^2*z+3*x*y*z+7*y^2*z+6*x*z^2+8*y*z^2+9*z^3+9*x^2*w+7*x*y*w+2*y^2*w+8
*x*z*w+8*y*z*w+6*z^2*w+6*x*w^2+7*y*w^2+3*z*w^2+3*w^3,3*x^3+2*x^2*y+9*x*y^2+
2*y^3+4*x^2*z+3*x*y*z+8*x*z^2+8*y*z^2+7*z^3+2*x^2*w+7*x*y*w+7*y^2*w+y*z*w+7
*z^2*w+4*x*w^2+3*y*w^2+6*z*w^2+4*w^3,x^3+6*x^2*y+6*x*y^2+5*y^3+x*y*z+7*y^2*
z+2*x*z^2+3*y*z^2+2*z^3+x^2*w+4*x*y*w+6*y^2*w+7*x*z*w+y*z*w+7*z^2*w+2*x*w^2
 +2*y*w^2+z*w^2+6*w^3]

# A cubic, otherwise random aside from the fact that the field of definition of the eigenpoints
# is nice.
f = cubs[1] + 2*cubs[2] + cubs[3]
quads = [f.derivative(v) - t*v for v in RP4.gens()][0:4]

X = P4.subscheme(quads)
I = X.defining_ideal()
B = I.groebner_basis()

lb = B[-1]
print("Factorizaion of lex-minimal basis element: \n" + str(factor(lb)) + "\n")

# Note: we do not care about the solution where w=0, as this corresponds to the
# solution (0,0,0,0,1) in P4.

# push to affine space
Ra.<x,y,z,t> = PolynomialRing(k,4)
Ia = Ra.ideal([b.subs(w=1) for b in B]).triangular_decomposition()[0]

# solve for the eigenpoints
lb = Ia.gens()[0].univariate_polynomial()
K = lb.splitting_field('a')

RKa = Ra.change_ring(K)
BK = [b.change_ring(K) for b in Ia.gens()]
IaK = RKa.ideal(BK)

# A lazy, but slow way to get all of the rational points.
PD = IaK.primary_decomposition()
assert len(PD) == 15

# We need the points in the correct P3 (i.e, coords (x,y,z,w). Not (x,y,z,t).
def replace_last_with_one(lst):
    return lst[0:len(lst)-1] + [1]

def ideal_to_point_in_P3(I):
    lst = I.gens()
    cords = [-f.coefficient({x:0,y:0,z:0,t:0}) for f in lst[::-1]]
    return replace_last_with_one(cords), cords[-1]

pts, lambs = zip(*[ ideal_to_point_in_P3(I) for I in PD] )

# Actually check to make sure that we've computed the eigenpoints.
assert all([q(pt + [lamb])==0 for b in BK for pt,lamb in zip(pts,lambs) for q in quads])


##########################################################################
# Start looking for syzygies
RP3.<x,y,z,w> = PolynomialRing(K,4)

# first, verify that f is actually smooth
assert ProjectiveSpace(RP3).subscheme(f.change_ring(K)).is_smooth()


# In P3, no subset of 4 points lie on a common hyperplane.

sub_inds = Subsets( range(len(pts)) ,4)
debts = [ matrix([ pts[i] for i in ss]).det() for ss in sub_inds ]
assert not 0 in debts
print("No 4 eigenpoints lie on a common hyperplane.")

# No 10 lie on a common quadric either
B2 = list(set((RP3.irrelevant_ideal()^2).gens()))

sub_inds = Subsets( range(len(pts)) ,10)
debts = [ matrix([ [ m(pts[i]) for m in B2] for i in ss]).det() for ss in sub_inds ]
assert not 0 in debts
print("No 10 eigenpoints lie on a common quadric.")

# The 15 eigenpoints lie on an "extra" cubic. In fact, the 15 eigenpoints are defined as the zero
# locus of 6 cubics in P3. While not "generic", this is what we expected; the defining ideal is
# spanned by the 2x2 minors of the 2x4 matrix we started with in the first place.
#
# This is special, but in the context of 15 points defined by the minors of a 2x4 matrix, not really...
# As far as I can tell, there isn't anything else we can really say about the points in terms of syzygys.
#

B3 = list(set((RP3.irrelevant_ideal()^3).gens()))

sub_inds = Subsets( range(len(pts)) ,15)
debts_mat = [ matrix([ [ m(pts[i]) for m in B3] for i in ss]) for ss in sub_inds ]
M3 = debts_mat[0].change_ring(K)
assert M3.rank() == 14
print("There IS an extra cubic syzygy!")

#ker = M.right_kernel()
#ker_cubics = [sum([ a*b for a,b in zip(g,B3)]) for g in ker.basis()]
#J = RP3.ideal(ker_cubics)

#
# Check for extra syzygies in higher degrees.

def check_extra_syzygies(d):
    assert d >= 3
    Bmons = list(set((RP3.irrelevant_ideal()^d).gens()))

    sub_inds = Subsets( range(len(pts)) ,15)
    debts_mat = [ matrix([ [ m(pts[i]) for m in Bmons] for i in ss]) for ss in sub_inds ]
    M = debts_mat[0].change_ring(K)
    return len(Bmons) - M.right_kernel().dimension() == 15


for d in range(4,15):
    assert check_extra_syzygies(d)
    print("Dimension of vanishing degree " + str(d) +" forms is as expected.")

    


# Bmons = list(set((RP3.irrelevant_ideal()^4).gens()))

# sub_inds = Subsets( range(len(pts)) ,15)
# debts_mat = [ matrix([ [ m(pts[i]) for m in Bmons] for i in ss]) for ss in sub_inds ]
# M = debts_mat[0].change_ring(K)

# assert len(Bmons) - M.right_kernel().dimension() == 15
# print("Dimension of vanishing quartics is as expected.")

# #
# # Check for extra quintics
# Bmons = list(set((RP3.irrelevant_ideal()^5).gens()))

# sub_inds = Subsets( range(len(pts)) ,15)
# debts_mat = [ matrix([ [ m(pts[i]) for m in Bmons] for i in ss]) for ss in sub_inds ]
# M = debts_mat[0].change_ring(K)

# assert len(Bmons) - M.right_kernel().dimension() == 15
# print("Dimension of vanishing quintics is as expected.")

#
# It appears that the Hilbert series has stabilized.
