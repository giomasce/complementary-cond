# -*- coding: utf-8 -*-

import itertools

latex.blackboard_bold(True)

additional_defs = []

# Declare all the variables we want to use
all_vars = []
xvars = ['t', 'tt', 'q']
all_vars += xvars
xvars_latex = ['\\tau', '\\tilde\\tau', '\\sqrt{-2p}']
zvars = ['z1', 'z2', 'z3']
all_vars += zvars
zvars_latex = ['\\zeta_1', '\\zeta_2', '\\zeta_3']
additional_defs.append(('x0', 't'))
additional_defs.append(('tx0', 'tt'))
for i in xrange(1, 4):
    additional_defs.append(('x%d' % (i), 'z%d' % (i)))
    additional_defs.append(('tx%d' % (i), 'z%d' % (i)))

hvars = []
hvars_latex = []
thvars = []
thvars_latex = []
def add_var_h(i, j):
    hvars.append('h%d%d' % (i, j))
    hvars_latex.append('h_{%d%d}' % (i, j))
    thvars.append('th%d%d' % (i, j))
    thvars_latex.append('\\tilde h_{%d%d}' % (i, j))
    additional_defs.append(('h%d%d' % (j, i), 'h%d%d' % (i, j)))
    additional_defs.append(('th%d%d' % (j, i), 'th%d%d' % (i, j)))
# Many loops are used to generate h variables in a canonical order
for i in xrange(4):
    add_var_h(i, 0)
for i in xrange(1, 4):
    add_var_h(i, i)
for i in xrange(1, 4):
    for j in xrange(i+1, 4):
        add_var_h(j, i)
all_vars += hvars
all_vars += thvars

# Declare all the polynomial rings we want to use
exec(preparse('Wbar.<%s> = QQbar[]' % (",".join(xvars + zvars))))
Wbar.latex_variable_names()[:] = xvars_latex + zvars_latex
exec(preparse('W.<%s> = QQ[]' % (",".join(xvars + zvars))))
W.latex_variable_names()[:] = xvars_latex + zvars_latex

exec(preparse('Rbar.<%s> = QQbar[]' % (",".join(xvars))))
Rbar.latex_variable_names()[:] = xvars_latex
exec(preparse('R.<%s> = QQ[]' % (",".join(xvars))))
R.latex_variable_names()[:] = xvars_latex

exec(preparse('Zbar.<%s> = Rbar[]' % (",".join(zvars))))
Zbar.latex_variable_names()[:] = zvars_latex
exec(preparse('Z.<%s> = R[]' % (",".join(zvars))))
Z.latex_variable_names()[:] = zvars_latex

exec(preparse('MRbar.<%s> = Zbar[]' % (",".join(hvars + thvars))))
MRbar.latex_variable_names()[:] = hvars_latex + thvars_latex
exec(preparse('MR.<%s> = Z[]' % (",".join(hvars + thvars))))
MR.latex_variable_names()[:] = hvars_latex + thvars_latex

for a, b in additional_defs:
    exec('%s = %s' % (a, b))
SF = SymmetricFunctions(R)
SFbar = SymmetricFunctions(Rbar)

hvars_mat = [[eval('h%d%d' % (i, j)) for i in xrange(4)] for j in xrange(4)]
hvars_diag = [eval('h%d%d' % (i, i)) for i in xrange(4)]
hvars_real = [eval(var_) for var_ in hvars]
thvars_mat = [[eval('th%d%d' % (i, j)) for i in xrange(4)] for j in xrange(4)]
thvars_real = [eval(var_) for var_ in thvars]
thvars_diag = [eval('th%d%d' % (i, i)) for i in xrange(4)]
xvars_real = [eval('x%d' % (i)) for i in xrange(4)]

def gen_simplifier(part):
    """Generate a simplifier in the ring of symmetric functions over 3
    variables.

    A simplifier is an expression whose highest order term is the
    specified partition, and that simplifies to zero when expanded
    over 3 variables.

    """
    if len(part) == 0:
        return None
    base = part[0]
    if base % 2 != 0:
        return None
    this_SFring = SymmetricFunctions(QQ)
    this_ring = QQ[z1,z2,z3]
    simp = this_SFring.p()(this_SFring.from_polynomial(this_ring(SR((z1^2+z2^2+z3^2)^(base//2))))) - this_SFring.p()[2]^(base//2)
    coeff = simp.coefficient([base])
    if coeff == 0:
        return None
    simp /= coeff
    coeff = simp.coefficient([base])
    assert coeff == 1
    simp *= this_SFring.p()(part[1:])
    assert simp.expand(3) == 0
    return simp

def simplify_SF(poly):
    """Simplifies a symmetric functions.

    The input symmetric function (assumed to be over 3 variables) is
    simplified as much as possible by subtracting all the possible
    simplifiers.

    """
    origpoly = poly
    ring = poly.parent()
    one_SF = ring(1)
    while True:
        if poly == 0:
            break
        part, coeff = poly.leading_item()
        simp = gen_simplifier(part)
        if simp is None:
            break
        assert part == simp.leading_item()[0], (part, simp)
        poly -= (one_SF * coeff) * ring(simp)
    assert poly.expand(3) == origpoly.expand(3)
    return poly

def map_poly(poly, monom_map=None, coeff_map=None):
    """Return a poly obtained by mapping all monomials of poly through
    monom_map and all coefficients through coeff_map.

    """
    ret = None
    if monom_map is None:
        monom_map = lambda x: x
    if coeff_map is None:
        coeff_map = lambda x: x
    for monom in poly.monomials():
        coeff = poly.monomial_coefficient(monom)
        monom = monom_map(monom)
        coeff = coeff_map(coeff)
        if ret is None:
            ret = coeff * monom
        else:
            ret += coeff * monom
    return ret

tilde_map = dict([(v1, v2) for v1, v2 in zip(hvars_real, thvars_real)] + [(v2, v1) for v1, v2 in zip(hvars_real, thvars_real)])
tilde_map_t = {t: tt, tt: t}

def double_eqs(eqs):
    """Given a list of equations with t and h**, return return another
    list in which each equation has been doubled (i.e., an copy of it
    with tt instead of t and th** instead of h** is added to it).

    This implements the passage from B0 to (B0(tau_1^+), B0(tau_1^-)).

    """
    tmp = []
    for eq in eqs:
        # There are three levels of polynomials: the outer variables
        # are h_{ij}, the intermediate ones are z_i and the inner ones
        # are t, tt and p. That's why we need two levels of map_poly.
        modified = map_poly(eq,
                            lambda monom: monom.subs(tilde_map),
                            lambda coeff: map_poly(coeff,
                                                   lambda monom: monom,
                                                   lambda coeff: coeff.subs(tilde_map_t)))
        tmp.append(eq + modified)
    return tmp

def eqs_to_matrix(eqs, double=True):
    """Given a list of homogeneous polynomials of degree one in h** and
    th**, returns a matrix in which each row contains the coefficients
    of h** and th**.

    """
    tmp = []
    for eq in eqs:
        assert eq.degree() <= 1
        assert eq.monomial_coefficient(MR(1)) == 0
        tmp2 = []
        if double:
            var_list = hvars_real + thvars_real
        else:
            var_list = hvars_real
        for var_ in var_list:
            tmp2.append(eq.monomial_coefficient(var_))
        tmp.append(tmp2)
    return matrix(tmp)

def monomial_divides(monom, poly):
    """Return true iff the monomial monom divides the polynomial poly.

    Differently from the original SageMath implementation, it works on
    every field.

    """
    assert parent(monom) == parent(poly)
    # If monom is not a monomial, this line raises an exception
    [struct] = monom.dict().keys()
    for poly_struct in poly.dict():
        if not all([x <= y for (x, y) in zip(struct, poly_struct)]):
            return False
    return True

assert monomial_divides(t, t*tt+tt*(q*t + t))
assert not monomial_divides(t, t*tt+tt*(q*t + tt))

def positive_imag(z):
    """Return one between z and -z, which has nonnegative imaginary part.

    """
    return z if z.imag() >= 0 else -z

def mangle(poly):
    """Returns a copy of poly in which every appearance of t^2 and tt^2 is
    substituted with -1+q or -1-q as appropriate.

    """
    polyring = poly.parent()
    new_q = polyring(q)
    one = QQ(1)
    new_t2 = -polyring(1) + new_q
    new_tt2 = -polyring(1) - new_q
    t_here = polyring(t)
    tt_here = polyring(tt)
    ret = polyring(0)
    for i, monom in enumerate(poly.monomials()):
        coeff = poly.monomial_coefficient(monom)
        fact = one
        while monomial_divides(t_here**2, monom):
            monom //= t_here**2
            fact *= new_t2
        while monomial_divides(tt_here**2, monom):
            monom //= tt_here**2
            fact *= new_tt2
        ret += monom * fact * coeff
    return ret

def separate_var(poly, var):
    """Return poly as sum of two polynomial, the second of which does not
    contain any appearance of the variable var.

    """
    ring = poly.parent()
    with_var = ring(0)
    without_var = ring(0)
    var = ring(var)
    for monom in poly.monomials():
        coeff = poly.monomial_coefficient(monom)
        if monomial_divides(var, monom):
            with_var += monom * coeff
        else:
            without_var += monom * coeff
    assert poly == with_var + without_var
    return (with_var, without_var)

def super_mangle(poly):
    """Iteratively apply mangle(), separate variable and square the
    equation until t and tt do not appear anymore in the polynomial.

    This procedure can (and most probably will) introduce new roots in
    the polynomial, so each root must be checked a posteriori to
    divide the original polynomial.

    """
    poly = mangle(poly)
    good_vars = set([t, tt])
    eligible_vars = list(set(poly.variables()).intersection(set([t, tt])))
    if len(eligible_vars) == 0:
        return poly
    var = eligible_vars[0]
    with_var, without_var = separate_var(poly, var)
    with_var = mangle(with_var^2)
    without_var = mangle(without_var^2)
    return super_mangle(with_var - without_var)

class NotFunctionOfZetaSquareException(Exception):
    pass

def evaluate_sym_map(at):
    """Helper function used by evaluate_sym().

    """
    def subs_func(item, coeff):
        if at == 1:
            if len(item) > 0 and (item[0] != 2 or item[-1] != 2):
                raise NotFunctionOfZetaSquareException()
            return Partition([0]), coeff
        elif at == 0:
            if item == Partition([0]):
                return item, coeff
            else:
                return item, 0.0
        else:
            raise Exception("at must be 0 or 1")
    return subs_func

def evaluate_sym(sym, at):
    """Evaluate a symmetric function at 0 or 1.

    If sym is not a function of |\zeta|^2,
    NotFunctionOfZetaSquareException() is raised.

    """
    coeffs = sym.map_item(evaluate_sym_map(at)).coefficients()
    if len(coeffs) == 0:
        return sym.base_ring()(0)
    else:
        [ret] = coeffs
        return ret

def to_alg_closure(poly):
    """Raise a polynomial to the algebraic closure of its base field.

    """
    return poly.change_ring(poly.parent().base_ring().algebraic_closure())

def subs_vars(poly, this_q):
    """Helper function used by check_factor().

    """
    subs_dict = {}
    ring = poly.parent()
    subs_dict[ring(t)] = positive_imag(sqrt(-1 + this_q))
    subs_dict[ring(tt)] = positive_imag(sqrt(-1 - this_q))
    subs_dict[ring(q)] = this_q
    return poly.subs(subs_dict)

def check_factor(factor):
    """Check that a polynomial does not have roots that contradict the
    complementary condition.

    Return False is bad roots are found, True otherwise.

    """
    # We use powersum elementary polynomials because p[2] is the
    # |\zeta|^2 and p[a,b,c] = p[a]*p[b]*p[c]. No powers other than 2
    # should appear, since we expect the condition te be geometrical
    # and thus rotational invariant.
    sym = SF.p()(SF.from_polynomial(Z(factor)))
    sym = simplify_SF(sym)
    print "Symmetric function: %s" % (sym)
    try:
        atz1 = evaluate_sym(sym, 1)
    except NotFunctionOfZetaSquareException:
        print "Not a function of |\zeta|^2..."
        return False
    atz0 = evaluate_sym(sym, 0)
    print "Evaluated at |\zeta| = 0: %s" % (atz0)
    print "Evaluated at |\zeta| = 1: %s" % (atz1)

    # Use super_mangle() to reduce to a polynomial of a single
    # variable; then find the roots and for each root check that it is
    # an actual root of atz1 (super_mangle can introduce new roots)
    # and that it does not violate parabolicity
    final = to_alg_closure(super_mangle(atz1))
    print "Final equation: %s" % (final)
    if final == 0:
        ">> Final equation is zero, this is wrong"
        return False
    sols = [x[0] for x in QQbar[q](final).roots()]
    ret = True
    print "Its roots are:"
    for this_q in sols:
        this_p = -1/2 * this_q^2
        y = subs_vars(atz1, this_q)
        valid = y == 0
        # If the exact comparison is too slow, the following inexact
        # comparison can be used: this introduces the risk of
        # rejecting a valid root, but not the (worse) risk of
        # accepting an invalid root
        #valid = abs(y).n(digits=5) < 1e-3
        parabolic = this_p.real() < 0
        print "  * q=%s, p=%s, y=%s, valid=%s, parabolic=%s" % (this_q, this_p, y, valid, parabolic)
        if valid and not parabolic:
            print ">> This solution a problem!"
            ret = False

    return ret

def main():
    # The system
    B0_eqs = []

    # Tangential metric
    B0_eqs += [h11, h22, h33, h12, h13, h23]
    # Conformal class of tangential metric
    #B0_eqs += [3 * h11 - h11 - h22 - h33, 3 * h22 - h11 - h22 - h33, h12, h13, h23]

    # Second fundamental form
    B0_eqs += list(itertools.chain(*[[t * hvars_mat[i][j] - xvars_real[i] * hvars_mat[j][0] - xvars_real[j] * hvars_mat[i][0] for i in xrange(1, j+1)] for j in xrange(1, 4)]))
    # Mean curvature
    #B0_eqs += [t * sum([hvars_mat[i][i] for i in xrange(1,4)]) - 2 * sum([hvars_mat[i][0] * xvars_real[i] for i in xrange(1, 4)])]
    # Normal derivative of mean curvature
    #B0_eqs += [t^2 * sum([hvars_mat[i][i] for i in xrange(1,4)]) - t * 2 * sum([hvars_mat[i][0] * xvars_real[i] for i in xrange(1, 4)])]

    # Assigned normal (fails DeTurck)
    #B0_eqs += [h00, h01, h02, h03]
    # Assigned normal direction (fails DeTurck)
    #B0_eqs += [h01, h02, h03]

    # Ricci-nu-nu
    #B0_eqs += [-sum([xvars_real[k] * xvars_real[k] for k in xrange(4)]) * h00 - t^2 * sum([hvars_mat[k][k] for k in xrange(4)]) + 2 * t * sum([xvars_real[k] * hvars_mat[k][0] for k in xrange(4)])]
    # Normal derivative of Ricci-nu-nu
    #B0_eqs += [-t * sum([xvars_real[k] * xvars_real[k] for k in xrange(4)]) * h00 - t^3 * sum([hvars_mat[k][k] for k in xrange(4)]) + 2 * t^2 * sum([xvars_real[k] * hvars_mat[k][0] for k in xrange(4)])]

    # Scalar curvature
    #B0_eqs += [sum(list(itertools.chain(*[[hvars_mat[i][j] * xvars_real[i] * xvars_real[j] - hvars_mat[i][i] * xvars_real[j] * xvars_real[j] for i in range(4)] for j in range(4)])))]
    # Normal derivative of scalar curvature
    #B0_eqs += [t * sum(list(itertools.chain(*[[hvars_mat[i][j] * xvars_real[i] * xvars_real[j] - hvars_mat[i][i] * xvars_real[j] * xvars_real[j] for i in range(4)] for j in range(4)])))]

    # Ricci-DeTurck field
    B0_eqs += [2 * sum([xvars_real[j] * hvars_mat[j][i] for j in xrange(4)]) - xvars_real[i] * sum([hvars_mat[j][j] for j in xrange(4)]) for i in xrange(4)]
    # Tangential component of the Ricci-DeTurck field
    #B0_eqs += [2 * sum([xvars_real[j] * hvars_mat[j][i] for j in xrange(4)]) - xvars_real[i] * sum([hvars_mat[j][j] for j in xrange(4)]) for i in xrange(1, 4)]

    # Bour-DeTurck field
    B0_eqs += [sum(list(itertools.chain(*[[2 * xvars_real[k] * xvars_real[k] * xvars_real[j] * hvars_mat[i][j] - xvars_real[i] * xvars_real[j] * xvars_real[k] * hvars_mat[j][k] for k in xrange(4)] for j in xrange(4)]))) for i in xrange(4)]

    D0_eqs = double_eqs(B0_eqs)
    D0 = eqs_to_matrix(D0_eqs)

    # Compute determinant and remove the expected degeneration factor.
    # Determinant needs to be computer in the ring W because of
    # performance reasons. Also polynomial operations (division and
    # factorization) must be performed in the ring W, otherwise they
    # are ill-defined.
    D0 = D0.change_ring(W)
    print "D0 is in %s" % (str(D0.parent()))
    try:
        det_poly = D0.det()
    except ValueError:
        print " > Matrix is not square"
        print " > Rank is %d" % (D0.rank())
        return
    known_factor = (t-tt)^10
    assert known_factor.divides(det_poly)
    det_poly //= known_factor

    # Check individual factors
    if det_poly == 0:
        print " > Determinant is zero, this is wrong"
        print " > Rank is %d" % (D0.rank())
        return
    det_factor = det_poly.factor()
    print "Factorization: %s" % (det_factor)
    factors_ok = True
    for factor, mult in det_factor:
        print "== Factor %s ==" % (factor)
        good = check_factor(factor)
        if good:
            print " > Good!"
        else:
            print " > U-hu, we have problems..."
            factors_ok = False

    if factors_ok:
        print "Complementary condition is satisfied for gamma = 1"
    else:
        print "Complementary condition is NOT satisfied for gamma = 1"

    # Copy local variables in global environment for post-mortem
    globals().update(locals())

main()
