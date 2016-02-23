"""
Hypercircles

This is a set of different algorithms related to the reparametrization
problem and adds the class Hypercircle.

The git-aware user may use my github branch: https://github.com/lftabera/sage/tree/hypercircles

You may also download directly the module from http://personales.unican.es/taberalf/Documentos/Hypercircle.zip, unzip it and load from your Sage session::

load('hypercircle.py')
u=random_linear_fraction(QQ[I]['t'])
H=Hypercircle([u])

In this case, ignore the import sentence of the examples and tests.

In any case, it is advisable to run at lest Sage 6.1.1 and apply the trac patch:

    - patch #8558 fast gcd for polynomials with number field coefficients.

    TESTS:

    The following is a subtle error that can happen if, for a parameter t,
    Phi(t) is attained by Phibeta on two parameters, tb and infinity. This test
    shows that the method woks in this case::

        sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
        sage: N = NumberField(x^2-2, 'a')
        sage: QQx=QQ['x']
        sage: D = QQx.random_element(2)
        sage: x = QQx.gen()
        sage: C = [(x**2-2)*QQx.random_element(2)/D for i in range(2)]
        sage: a = N.gen()
        sage: C = [f((a*x-a)/(x+1)) for f in C]
        sage: H = Hypercircle(C)
        sage: H.parametrization()
        [(1/2*x^2 + 1/2)/x, (1/4*a*x^2 - 1/4*a)/x]
"""

from time import time
from copy import copy
import sage
from sage.arith.all import gcd, lcm
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.power_series_ring import PowerSeriesRing
from sage.sets.set import Set
from sage.rings.polynomial.polynomial_element import is_Polynomial
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.modules.free_module_element import vector
from sage.rings.number_field.number_field import NumberField
from sage.structure.sequence import Sequence
from sage.matrix.constructor import matrix, identity_matrix
from sage.all import pari, oo
from sage.rings.qqbar import QQbar

def parametrization_to_common_denominator(Phi):
    """
    Take a list of rational functions representing a parametrization and reduce
    it to common denominator.

    INPUT:

    - ``Phi``: a list of rational functions.

    OUTPUT:

    - ``Num``: a list of polynomials

    - ``Den``: a polynomial

    The length of ``Num`` equals the length of ``Phi`` and ``Phi[i]`` =
    ``Num[i]/Den``

    gcd of ``Num[0]``, ..., ``Num[-1]``, ``Den``  is 1

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import parametrization_to_common_denominator
        sage: K = QQ[x].fraction_field()
        sage: Phi = [K.random_element(3) for i in range(5)]
        sage: Num, Den = parametrization_to_common_denominator(Phi)
        sage: [Num[i] / Den - Phi[i] for i in range(5)]
        [0, 0, 0, 0, 0]
        sage: from sage.rings.polynomial.polynomial_element import is_Polynomial
        sage: is_Polynomial(Den)
        True
        sage: [is_Polynomial(i) for i in Num]
        [True, True, True, True, True]
    """
    Den = my_lcm([foo.denominator() for foo in Phi])
    Num = [foo.numerator() * Den.quo_rem(foo.denominator())[0] for foo in Phi]
    return Num, Den


def my_inverse_big_absnfield(s):
    """
    Algorithm to compute the inverse of an element over an absolute number
    field. This is faster than current sage code for big number fields with big
    defining coefficients and big s, maybe due to flint faster xgcd.

    INPUT:

    - ``s``: an absolute number field element

    OUTPUT:

    - The inverse of ``s``

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import my_inverse_big_absnfield
        sage: N = NumberField(x^7+1213451*x^4 -135156164614,'a')
        sage: c = 0
        sage: while c.is_zero(): c = N.random_element()
        ...
        sage: my_inverse_big_absnfield(c) * c
        1
    """
    if type(s) != \
      sage.rings.number_field.number_field_element.NumberFieldElement_absolute:
        return ~s
    else:
        var = s.parent().polynomial().variable_name()
        a = s.polynomial(var).numerator()
        b = s.parent().polynomial().numerator()
        if a.degree() == 0 or b.degree() ==0:
            return ~s
        r = a.xgcd(b)
        return s.parent(r[1]) * ~ZZ(r[0]) * s.denominator()

def simsim(f):
    """
    Given a rational fraction  a / b,  return a canonical representative with
    monic denominator.

    INPUT:

    - ``f``: a fraction field element of a polynomial rings

    OUTPUT:

    - The unique representative of ``f`` such that
      f.denominator().leading_coefficient() = 1

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import simsim
        sage: K.<x> = QQ[x]
        sage: f =  (3*x^2+1) /(3*x^3)
        sage: f
        (3*x^2 + 1)/(3*x^3)
        sage: simsim(f)
        (x^2 + 1/3)/x^3
        sage: f = K.fraction_field().random_element(20,10**6,10)
        sage: f - simsim(f)
        0
        sage: f = NumberField(x^4+2,'a')[x].fraction_field().random_element(10, 10,10)
        sage: g = simsim(f)
        sage: f - g
        0
        sage: g.denominator().leading_coefficient()
        1
    """
    l = my_inverse_big_absnfield( f.denominator().leading_coefficient())
    return (f.numerator()* l ) / (f.denominator() *l)


def random_linear_fraction(K, n_bound = 100, d_bound = 1, reduced = False):
    """
    Return a linear fraction on the fraction field of K

    INPUT:

    - ``K``: a ring of the form N[t]
    - ``reduced``: a bolean
    - ``n_bound``: option passed to the random polynomial generator
    - ``d_bound``: option passed to the random polynomial generator

    OUPUT:

    A linear fraction ``u`` with monic denominator:

    - If reduced is true, ``witness([u])`` is a reduced hypercircle.
    - If reduced is false, ``witness([u])`` is `NOT` a reduced hypercircle.
      Moreover, the denominator is of degree 1.

    .. warning:: Note that if the base_ring is of relative degree 1, reduced is
      ignored, since this does not make sense.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import *
        sage: L.<t> = NumberField(x^3-2, 'a')[]
        sage: u = random_linear_fraction(L)
        sage: is_com_unit(u)
        True
        sage: Phi = witness([u])
        sage: l = is_hypercircle(Phi, inverse_unit(u,t)(0))
        sage: is_com_unit(l)
        True
        sage: is_reduced_hypercircle(Phi)
        Traceback (most recent call last):
        ...
        ValueError: Not reduced hypercircle
        sage: v = random_linear_fraction(L, reduced=True)
        sage: is_com_unit(v)
        True
        sage: Psi = witness([v])
        sage: l = is_reduced_hypercircle(Psi)
        sage: is_com_unit(l)
        True
    """
    if K.base_ring() == QQ:
        u = K.random_element(1, n_bound, d_bound) / \
            K.random_element(1, n_bound, d_bound)
        while not is_com_unit(u):
            u = K.random_element(1, n_bound, d_bound) / \
                K.random_element(1, n_bound, d_bound)
    elif K.base_ring().relative_degree() == 1:
        u = K.random_element(1, n_bound, d_bound) / \
            K.random_element(1, n_bound, d_bound)
        while not is_com_unit(u):
            u = K.random_element(1, n_bound, d_bound) / \
            K.random_element(1, n_bound, d_bound)
    elif reduced:
        u = K.random_element(1, n_bound, d_bound) / K.gen()
        while not is_com_unit(u):
            u = K.random_element(1, n_bound, d_bound) / K.gen()
    else:
        u = K.fraction_field().one()
        while not is_com_unit(u):
            un = K.random_element(1, n_bound, d_bound)
            ud = K.gen() + K.random_element(0, n_bound, d_bound)
            #Check that the INVERSE of un/ud is not associated to a reduced HC
            if (ud[0] != 0) and (not un[0]/ud[0] in K.base_ring().base()):
                u = un / ud
    return u

def is_com_unit(u):
    """
    Check if ``u`` is a linear fraction over a univariate polynomial rings.

    INPUT:

    - ``u``: a fraction field element.

    OUTPUT:

    - ``True`` if an only if numerator and denominator are of degree at most one
      and is not a base_ring element.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import is_com_unit
        sage: K.<x> = QQ[]
        sage: u = (2*x+1)/(4*x+2)
        sage: is_com_unit(u)
        False
        sage: u = (2*x+1)/(1*x)
        sage: is_com_unit(u)
        True
        sage: u = K.fraction_field()(x)
        sage: is_com_unit(u)
        True
        sage: u = K.fraction_field()(0)
        sage: is_com_unit(u)
        False
        sage: u = K.fraction_field()(1+x^3)
        sage: is_com_unit(u)
        False
    """
    n = u.numerator()
    d = u.denominator()
    S = (n.degree(), d.degree())
    return S in [(1,1),(1,0),(0,1)]

def sums_alpha(Nu, De, alpha):
    """
    Compute the sum

        sum( [( Nu[i] * alpha**i ) for i in range(len(Nu)) ] ) / De

    Horner is not significant here alpha**i is immediate.
    It is expected to be used to deal with unit-parametrizations in terms of
    alpha.

    INPUT:

    - ``Nu``: a list or tuple (expected a list of univariate polynomials)
    - ``alpha``:  an element (expected an algebraic number of degree len(Nu))
    - ``De``: an element (expected a polynomial)

    Expected to be used if ``[X/De for X in Nu]`` is a unit parametrization.

    OUTPUT:

    - ``sum([(Nu[i]*alpha**i) for i in range(len(Nu))]) / De``

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import *
        sage: N.<i> = NumberField(x^2+1)
        sage: K.<t> = N[]
        sage: Nu = [t^2 - i*t, -i*t^2 + 2*i*t]
        sage: De = 2*t - i - 2
        sage: sums_alpha(Nu, De, i)
        t

    A random example::

        sage: N.<a> = NumberField(x^3-2, 'a')
        sage: K.<t> = N[]
        sage: u = random_linear_fraction(K)
        sage: r = witness([u],name = 't')
        sage: D = my_lcm([f.denominator() for f in r])
        sage: Nu = [K(f*D) for f in r]
        sage: sums_alpha(Nu, D, a)
        t
    """
    w = sum([(Nu[i]*alpha**i) for i in range(len(Nu))]) / De
    return w

def newton_sums(N):
    """
    Compute Newton sums of the generator of a NumberField

    INPUT:

    - ``N``: a number fields of degree > 1

    OUTPUT:

    - If ``b`` is the generator of ``N`` over its base field, and ``N`` is of
      degree ``n`` over its base, compute the traces of ``1, b, ..., b**(n-1)``

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import newton_sums
        sage: N=NumberField(x^3+x^2-1,'b')
        sage: newton_sums(N)
        [3, -1, 1]
        sage: f = x^5-3
        sage: N.<b> = NumberField(f)
        sage: vector(newton_sums(N)) - vector((b**i).trace() for i in range(5))
        (0, 0, 0, 0, 0)
    """
    f = N.relative_polynomial()
    d = f.degree()
    if d == 1:
        return [1]
    x, = f.variables()
    f = f(~x).numerator()
    f = - f.derivative()*(~PowerSeriesRing(N.base_ring(), name = str(x),\
          default_prec = d)(f))
    return (d + f*x).list()[0:d]

def rel_trace(new_sums, element):
    """
    Compute the trace of an element on a relative number field over its base
    field. Uses newton_sums.

    This is intended to be used with the method newton_sums.

    INPUT:

    - ``new_sums``: if ``b`` is the generator of the number field, this list
      contains the traces of the powers of ``b``.
    - ``element``: algebraic element to compute the traces.

    OUTPUT:

    - ``trace``: The trace of ``element`` over the base ring defining the
      extension

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import rel_trace, newton_sums
        sage: N = NumberField([x^3-2,x^2+4], 'a,b')
        sage: nn = newton_sums(N)
        sage: r = N.random_element()
        sage: rel_trace(nn, r) - r.trace(N.base_ring())
        0
    """
    element = element.vector()
    trace = sum([new_sums[i]*element[i] for i in range(len(new_sums))])
    return trace

def composition_by_unit(Num, Den, unit, verbose=False):
    """
    Compute the composition of the parametrization represented by ``Num`` and
    ``Den`` with ``unit``.

    This is optimized for dealing with number fields as coefficients.

    INPUT:

    - ``Num``: a list of polynomials
    - ``Den``: a polynomials
    - ``unit``: a linear fraction_field

    OUTPUT:

    - ``NN`` a list, ``DD`` a polynomial such that ``NN[i]/DD = (Num[i]/Den)
      (unit)``

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import composition_by_unit, random_linear_fraction
        sage: N = NumberField(x^3-2,'a')
        sage: K.<t> = N[]
        sage: Num = [K.random_element(3) for i in range(7)]
        sage: Den = 0
        sage: while Den == 0: Den = K.random_element(5)
        ...
        sage: unit = random_linear_fraction(K)
        sage: NN, DD = composition_by_unit(Num, Den, unit)
        sage: [NN[i]/DD - (Num[i]/Den)(unit) for i in range(7)]
        [0, 0, 0, 0, 0, 0, 0]
    """
    if verbose: tt=time()
    a = unit.numerator()
    b = unit.denominator()
    m = max(max([num.degree() for num in Num]), Den.degree())
    if verbose: print('nothing to see here: ' + str(time()-tt))
    if verbose: tt =time()
    #precompute the powers
    A = [a.parent().one()]
    B = A[:]
    for i in range(m+1):
        A += [A[-1]*a]
        B += [B[-1]*b]
    precalc = [A[i] * B[m-i] for i in range(m+1)]
    if verbose: print('precalc: ' + str(time()-tt))
    if verbose: tt = time()
    nuevonum = [sum([num[i]*precalc[i] for i in \
               range(num.degree()+1)],a.parent().zero()) for num in Num]
    nuevoden = sum([Den[i]*precalc[i] for i in range(Den.degree()+1)])
    if verbose: print('other: ' + str(time()-tt))
    return nuevonum, nuevoden

def inverse_unit(w, var = None):
    """
    Compute the inverse of a linear fraction.

    INPUT:

    - ``u``: a linear fraction in ``K(x)``.
    - ``var``: the variable for the inverse ``u``, by default the same variable
      as ``u``.

    OUTPUT:

    - ``v``: a linear fraction in var such that ``u(v) = var``, ``v(u) = x``

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import inverse_unit, random_linear_fraction
        sage: K.<a,b,c,d> = QQ['a,b,c,d']
        sage: L.<x> = K.fraction_field()['tr']
        sage: u = (a*x+b)/(c*x+d)
        sage: inverse_unit(u)
        (-d*tr + b)/(c*tr - a)

    Note that the variable may be different from the variable of u::

        sage: K1.<xx> = QQ['xx']
        sage: K2.<t> = QQ['t']
        sage: u = random_linear_fraction(K1)
        sage: v = inverse_unit(u, t)
        sage: u(v)
        t
        sage: v(u)
        xx
    """
    a = w.numerator()[1]
    b = w.numerator()[0]
    c = w.denominator()[1]
    d = w.denominator()[0]
    if var == None:
        var = w.parent().gen()
    return (-d*var+b)/(c*var-a)

def is_hypercircle(Phi, tstar, verbose = False):
    """
    Check if a parametrization is a parametrization of a hypercircle.

    INPUT:

    - ``Phi``: the parametrization as a list of elements in ``K(a)(t)``.
    - ``tstar``: an element in ``K(a)`` such that ``Phi(tstar)`` is a point in
      ``K``.

    OUTPUT:

    - An associated unit if ``Phi`` is an hypercircle, the string ``'Not
      hypercircle'`` otherwise.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import *
        sage: N = NumberField(x^3-2, 'a')
        sage: K.<t> = N[]
        sage: u = random_linear_fraction(K)
        sage: Phi = witness([u], name=t)
        sage: v = is_hypercircle(Phi, inverse_unit(u,t)(0))
        sage: simsim(u(v)) in QQ[t].fraction_field()
        True

    TODO:

    Support for non-primitive hypercircles, more tests

    REFERENCE:

    ACA algorithm
    """
    K = Sequence(Phi).universe()
    if K.is_field():
        K = K.base()
    t = K.gen()
    a = K.base_ring().gen()
    d = a.parent().relative_degree()
    No = 'Not hypercircle'
    if verbose: tt=time()

    #represent the parametrization with common denominator
    Num, Den = parametrization_to_common_denominator(Phi)
    if verbose: print('common denom: ' + str(time()-tt))
    if verbose: tt = time()

    #check if it is a unit parametrization
    w = sums_alpha(Num, Den, a)
    if verbose: print('w: ' + str(time()-tt))
    if w.numerator().degree() not in [0,1] or \
       w.denominator().degree() not in [0,1]:
        raise ValueError(No)
    if verbose: tt = time()

    #pass to a standar parametrization
    wm1 = inverse_unit(w)
    if verbose: print('wm1: ' +str(time()-tt))
    if verbose: tt = time()
    varphinum, varphiden = composition_by_unit(Num, Den, wm1)
    if verbose: print('varphi: ' + str(time()-tt))

    #compute the rational point from the parameter
    if verbose: tt =time()
    wtstar = w(tstar)
    if verbose: print('wstar: '+ str(time()-tt))
    if verbose: tt =time()
    Destar = ~Den(tstar)
    pointstar = [foo(tstar)*Destar for foo in Num]

    #pass to a reduced standar parametrization
    if verbose: print('point: ' + str(time()-tt))
    if verbose: tt=time()
    phistarden = varphiden(t+wtstar)
    phistarnum = [varphinum[i](t+wtstar) - pointstar[i]*phistarden for i in\
                  range(d)]
    if verbose: print('phistar: ' + str(time()-tt))
    if phistarden[0].is_zero():
        raise ValueError(No)
    if Set([K.base_ring().zero()]) != Set([foo[0] for foo in phistarnum]):
        raise ValueError(No)

    #check if the resulting parametrization is a reduced hypercircle
    ustar = is_hypercircle_unit_reduced_standar(phistarnum, phistarden,\
            K, t, a, d)
    if ustar == 'Not reduced hypercircle':
        raise ValueError(No)
    return simsim(ustar + wtstar)

def is_reduced_hypercircle(Phi, verbose = False):
    """
    Check if a parametrization is a parametrization of a reduced hypercircle.

    INPUT:

    - ``Phi``: the parametrization as a list of elements in ``K(a)(t)``

    OUTPUT:

    - An associated unit if ``Phi`` is a reduced hypercircle, a ValueError otherwise.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import *
        sage: N = NumberField(x^3-2, 'a')
        sage: K.<t> = N[]
        sage: u = random_linear_fraction(K, reduced = True)
        sage: Phi = witness([u], name=t)
        sage: v = is_reduced_hypercircle(Phi)
        sage: simsim(u(v)) in QQ[t].fraction_field()
        True

    TODO:

    Support for non-primitive hypercircles, more tests

    REFERENCE:

    ACA algorithm
    """
    K = Phi[0].numerator().parent()
    t = K.gen()
    a = K.base_ring().gen()
    d = a.parent().relative_degree()
    No = 'Not reduced hypercircle'

    #pass to a common denominator
    if verbose: tt=time()
    Num, Den = parametrization_to_common_denominator(Phi)
    if verbose: print('prelim num: ' + str(time()-tt))
    if verbose: tt = time()

    #check if it is a unit parametrization
    w = sums_alpha(Num, Den, a)
    if verbose: print('w: ' + str(time()-tt))
    if not is_com_unit(w):
        raise ValueError(No)

    #pass to a standar representation
    if verbose: tt = time()
    wm1 = inverse_unit(w,t)
    if verbose: print('wm1: ' +str(time()-tt))
    if verbose: tt = time()
    varphinum, varphiden = composition_by_unit(Num, Den, wm1)

    #pass to the subalgorithm
    if verbose: print('varphi: ' + str(time()-tt))
    ustar = is_hypercircle_unit_reduced_standar(varphinum, varphiden,\
                                                K, t, a, d)
    if ustar == No:
        raise ValueError(No)
    return simsim(ustar)

def is_hypercircle_unit_reduced_standar(Num, Den, K, t, a, d, verbose = False):
    """
    Auxiliary function to ``is_hypercircle``. It accepts the following data:

    INPUT:

    - ``Num``: a list of polynomials in ``N(a)[t]``
    - ``Den``: a polynomial in ``N(a)[t]``
    - ``K``: The ring ``N(a)[t]``
    - ``t``: The variable of ``K``
    - ``a``: The defining algebraic element of ``N(a)``
    - ``d``: The degree of ``a``

    Such that the parametrization ``Num / Den`` is a unit parametrization
    passing through the origin in standard form.

    OUTPUT:

    - The string ``'Not reduced hypercircle'`` if ``Num/Den`` does not define a
      reduced hypercircle or a linear fraction associated to the reduced
      hypercircle.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import is_hypercircle_unit_reduced_standar
        sage: N.<a> = QQ[I]
        sage: K.<t> = N[]
        sage: d = 2
        sage: Num = 29*t^2 - 26*a*t, -29*a*t^2
        sage: Den = 58*t - 26*a
        sage: is_hypercircle_unit_reduced_standar(Num, Den, K, t, a, d)
        1/(t - 29/26*I)

    TODO:

    Support for non-primitive hypercircles, more tests

    REFERENCE:

    ACA algorithm
    """
    No = 'Not reduced hypercircle'
    if verbose: tt =time()
    if verbose: tt =time()
    N = Den
    r = N.degree()+1 # Degree of the hypercircle
    for i in range(d):
        if Num[i].degree() != -1 and Num[i].degree() != r:
            raise ValueError(No)
    phistarnum = [p.shift(-1) for p in Num]
    if verbose: print('algo1sub phistar: ', str(time()-tt))
    if verbose: tt =time()
    if set([foo(0) for foo in phistarnum])==set([K.zero()]) or Den(0)==K.zero():
        raise ValueError(No)
    #look for a nonconstant term
    for i in range(d):
        if phistarnum[i](0) !=0:
            ee = N(0)/phistarnum[i](0)
            gamma = ee * (N.derivative())(0)/N(0)
            dd = -(gamma - gamma.polynomial()(0))/r
            ustar = ee /(t+dd)
            ustar = simsim(ustar)
            if verbose: print('algo1sub ustar: ', str(time()-tt))
            if verbose: tt =time()
            L = list(composition_by_unit(Num, Den, ustar))
            b = ~L[1].leading_coefficient()
            L[0] = [foo*b for foo in L[0]]
            L[1] = b*L[1]
            L = max( max([-10]+[y.lift().degree() for y in L[1].coefficients()]), \
                max( [max([-10]+[y.lift().degree() for y in foo.coefficients()])\
                      for foo in L[0]]))
            if L!=0:
                raise ValueError(No)
            if verbose: print("check res: " + str(time()-tt))
            return ustar
    if verbose: print('algo1sub ustar: ', str(time()-tt))
    raise ValueError(No)

def conjugate_pol(f, conjugation, K2):
    """
    Compute the conjugate of a polynomial.

    INPUT:

    - ``f``: a polynomial or rational function in ``K[t]`` or ``K(t)``
    - ``conjugation``: an homomorphism of fields ``K -> L``
    - ``K2`` a ring of the form ``L[x]``

    OUTPUT:

    - The image of ``f`` by the natural extension of conjugation as an element
      in:

    ``K[t] -> L[t]`` or ``K(t) -> L(t)``

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import conjugate_pol
        sage: N.<I> = QQ[I]
        sage: conj = N.automorphisms()[1]
        sage: conj
        Ring endomorphism of Number Field in I with defining polynomial x^2 + 1
        Defn: I |--> -I
        sage: K.<x> = N[]
        sage: f = (1-I)*x-(2+3*I)
        sage: conjugate_pol(f, conj, K)
        (I + 1)*x + 3*I - 2
        sage: f = K.random_element(20)
        sage: f + conjugate_pol(f, conj, K) in QQ[x]
        True
        sage: I*(f - conjugate_pol(f, conj, K)) in QQ[x]
        True

    A more interesting example::

        sage: var('y')
        y
        sage: N.<a> = NumberField(y^5-2, 'a')
        sage: K.<x> =N[]
        sage: f = x^4 + a*x^3 + a^2*x^2 + a^3*x + a^4
        sage: M.<b> = NumberField(f)
        sage: conj1 = N.hom([M(a)])
        sage: conj1
        Ring morphism:
        From: Number Field in a with defining polynomial y^5 - 2
        To:   Number Field in b with defining polynomial x^4 + a*x^3 + a^2*x^2 +
        a^3*x + a^4 over its base field
        Defn: a |--> a
        sage: conj2 = N.hom([1/2*a^4*b^2])
        sage: conj2
        Ring morphism:
        From: Number Field in a with defining polynomial y^5 - 2
        To:   Number Field in b with defining polynomial x^4 + a*x^3 + a^2*x^2 +
        a^3*x + a^4 over its base field
        Defn: a |--> 1/2*a^4*b^2
        sage: p = a + x + a^3*x^2
        sage: p1 = conjugate_pol(p, conj1, M[x]); p1
        a^3*x^2 + x + a
        sage: p2 = conjugate_pol(p, conj2, M[x]); p2
        a^2*b*x^2 + x + 1/2*a^4*b^2
        sage: sage.rings.polynomial.polynomial_element.is_Polynomial(p1)
        True
        sage: sage.rings.polynomial.polynomial_element.is_Polynomial(p2)
        True
        sage: q = p / p.parent().one(); q
        a^3*x^2 + x + a
        sage: q1 = conjugate_pol(q, conj1, M[x])
        sage: sage.rings.polynomial.polynomial_element.is_Polynomial(q1)
        False
    """
    if is_Polynomial(f):
        return K2([conjugation(foo) for foo in f.list()])
    return K2([conjugation(foo) for foo in f.numerator().list()])/\
    K2([conjugation(foo) for foo in f.denominator().list()])

def unitfrom3points(Map, T):
    """
    Compute an automorphism of ``P^1`` from the images of three points.

    INPUT:

    - ``Map``: a list of the form ``[[i_1,j_1], [i_2, j_2], [i_3, j_3]]``
      representing an automorphism of ``P^1``
    - ``T``: a variable

    OUTPUT:

    - A linear fraction ``u`` with monic denominator such that ``u(i_k) = j_k``,
      ``k=1..3``

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import unitfrom3points, is_com_unit
        sage: K.<i1, i2, i3, j1, j2, j3> = QQ[]
        sage: L.<t> = K.fraction_field()[]
        sage: M = [[i1, j1], [i2, j2], [i3, j3]]
        sage: u = unitfrom3points(M,t)
        sage: is_com_unit(u)
        True
        sage: u(i1)
        j1
        sage: u(i2)
        j2
        sage: u(i3)
        j3
        sage: K.<t> = NumberField(x^3 - 2, 'a')[]
        sage: u = (t+4) / (t + 1)
        sage: i1, i2, i3 = randint(0, 10^6), randint(0, 10^6), randint(0, 10^6)
        sage: M = [[i1, u(i1)], [i2, u(i2)], [i3, u(i3)] ]
        sage: v = unitfrom3points(M,t)
        sage: u - v
        0
    """
    #15 products, 3 subtractions, 8 additions
    i1,i2,i3 = [foo[0] for foo in Map]
    j1,j2,j3 = [foo[1] for foo in Map]
    j12 = j1-j2
    j31 = j3-j1
    j23 = j2-j3
    i23 = i2*i3*j23
    i12 = i1*i2*j12
    i13 = i1*i3*j31
    i1j23 = i1*j23
    i2j31 = i2*j31
    i3j12 = i3*j12
    a = i1j23 * j1 + i2j31 * j2 + i3j12 * j3
    b = i12 * j3 + i13 * j2 + j1 * i23
    c = i1j23 + i2j31 + i3j12
    d = i12 + i13 + i23
    nu = a*T+b
    de =c*T+d
    l = my_inverse_big_absnfield(de.leading_coefficient())
    de = l * de
    nu = l * nu
    return nu/de

def my_gcd(list_of_polys):
    """
    Compute the gcd of a list of polys.

    The difference with the general gcd is that, once a gcd is computed, before
    computed next, check if the gcd already divides next element. In most cases,
    for long lists, one only needs to check a few (expect one) gcd to obtain the
    gcd of the whole list, and division is cheaper, at least in the conjugation
    process of the hypercircle model.

    INPUT:

    - ``list_of_poly``: a list of univariate polynomials.

    OUTPUT:

    - ``g``: The gcd of the elements of the list.

    EXAPLES::

            sage: from sage.geometry.hypercircles.hypercircle import my_gcd
            sage: K.<x> = QQ[x]
            sage: f = [K.random_element() for i in range(5)]
            sage: gcd(f) - my_gcd(f)
            0
            sage: h = K.random_element()
            sage: f = [ h*m for m in f]
            sage: gcd(f) - my_gcd(f)
            0
    """
    if len(list_of_polys) == 1:
        return my_inverse_big_absnfield(list_of_polys[0].leading_coefficient())\
        * list_of_polys[0]
    elif len(list_of_polys) == 2:
        return gcd(*list_of_polys)
    else:
        g = gcd(list_of_polys[0], list_of_polys[1])
        for f in list_of_polys[2:]:
            if my_quo_rem(f,g)[1] != 0:
                g=gcd(g,f)
    return g

def my_quo_rem(self, other):
    """
    Custom quotient and remainder

    TESTS::

        sage: from sage.geometry.hypercircles.hypercircle import my_quo_rem
        sage: N = QQ[I]
        sage: K.<t> = N[]
        sage: f = K.random_element(10)
        sage: g = K.random_element(10)
        sage: f.quo_rem(g) == my_quo_rem(f,g)
        True
    """
    P = self.parent()
    if other.is_zero():
        raise ZeroDivisionError, "other must be nonzero"

    # This is algorithm 3.1.1 in Cohen GTM 138
    A = self
    B = other
    b = other.leading_coefficient()
    b = my_inverse_big_absnfield(b)
    R = A
    Q = P.zero()
    while R.degree() >= B.degree():
        aaa = R.leading_coefficient()*b
        diff_deg=R.degree()-B.degree()
        Q += P(aaa).shift(diff_deg)
        R = R[:R.degree()] - (aaa*B[:B.degree()]).shift(diff_deg)
    return (Q, R)



def my_lcm(list_of_polys):
    """
    Compute the monic lcm of a list of polynomials, avoiding calling to
    Singular.

    INPUT:

    - ``list_of_polys``: A list of univariate polynomials

    OUTPUT:

    - ``g``: The lcm of the list

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import my_lcm
        sage: K.<x> = NumberField(x^3-2, 'a')[]
        sage: f = [K.random_element(3) for i in range(3)]
        sage: l = my_lcm(f)
        sage: [ l % m for m in f]
        [0, 0, 0]
        sage: f = [x-1, x+1, x^2-1]
        sage: my_lcm(f)
        x^2 - 1
    """
    if len(list_of_polys) == 1:
        return my_inverse_big_absnfield(list_of_polys[0].leading_coefficient())\
        * list_of_polys[0]
    else:
        g = (list_of_polys[0] * list_of_polys[1]).quo_rem(gcd(list_of_polys[0],\
        list_of_polys[1]))[0]
        g = my_inverse_big_absnfield(g.leading_coefficient()) * g
        for f in list_of_polys[2:]:
            f = my_inverse_big_absnfield(f.leading_coefficient()) * f
            if (g % f) != 0:
                g = (g * f).quo_rem(gcd(g,f))[0]
                g = my_inverse_big_absnfield(g.leading_coefficient()) * g
    return g.monic()

def __witness_deg_2(Phi, check, name, verbose, n, K, N, t, alpha, polmin, Not_defined):
    """

    This is a special case of witness variety for degree 2 extensions.
    This function is for internal use only and should not be called directly.
    Use witness instead.

    INPUT:

    - ``Phi``: The original parametrization.
    - ``check``: Boolean, compute a certificate of K-definability.
    - ``name``: A string with the name of the variable of the parametrization of
    the witness variety.
    - ``verbose``: Boolean, provide verbose information of the steps of the
    computation.
    - ``n``: The ambient dimension of ``Phi``.
    - ``K``: The underlying polynomial ring of ``Phi``.
    - ``N``: The coefficient field of ``K``.
    - ``t``: the variable of ``K``.
    - ``alpha``: The generator of ``N``. It must be of degree 2.
    - ``polmin``: The minimal polynomial of alpha.
    - ``Not_defined``: The string 'The curve is not defined over the ground field'

    OUTPUT:

    - The string 'The curve is not defined over the ground field' or the
    standard parametrization of a hypercircle. If ``check``=False there is a
    small probability that the answer is a parametrization but that the curve
    is not defined over the ground field. If ``check`` is True there cannot be
    such error.

    TEST:

        sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
        sage: N = NumberField(x^2-2, 'a')
        sage: K = N['t']
        sage: t = K.gen()
        sage: alpha = N.gen()
        sage: Phi = [(alpha*t+alpha)/(t-1)]
        sage: n = 1
        sage: name = 'rr'
        sage: polmin = QQ['x'](x^2-2)
        sage: Not_defined = ''
        sage: from sage.geometry.hypercircles.hypercircle import __witness_deg_2 as wit2
        sage: W1 = wit2(Phi, False, name, False, n, K, N, t, alpha, polmin, Not_defined); W1
        [(1/2*rr^2 + 1/2)/rr, (1/4*a*rr^2 - 1/4*a)/rr]
        sage: H = Hypercircle(Phi, name='rr')
        sage: W1 == H.parametrization()
        True
    """
    if verbose: tt = time()
    diffpolmin = polmin.derivative()
    x = polmin.variables()[0]
    m = polmin.quo_rem(x-alpha)[0]

    #Compute the conjugate
    beta = -m[0]/m[1]
    NT = N[name]
    T = NT.gen()

    #start computing the hypercircle
    Den = my_lcm([foo.denominator() for foo in Phi])
    degree_denominator = Den.degree()
    deg = max(0, max([foo.numerator().degree()-foo.denominator().degree() for\
    foo in Phi])) + degree_denominator
    if deg == 0:
        raise ValueError("the parametrization does not define a curve")

    #is the following correct?
    bound_npoints = 3
    #degree_denominator + max([foo.numerator().degree() for foo in Phi]) + 1

    if verbose: print('pre: ' + str(time()-tt))
    if verbose: tt =time()
    counter_ndef = 0
    if N == QQbar:
        conjugation = lambda foo: foo.conjugate()
    else:
        conjugation = lambda foo: foo[0]+beta*foo[1]
    #N.hom([beta])#!!!There is an error in Pari
    #nffactor: precision too low in floorr (precision loss in truncation)
    ##def conjugation(r):
        #return N([r[0], -r[1]])
    Phibeta = [conjugate_pol(foo, conjugation, NT) for foo in Phi]
    tb = Phibeta[0].parent().gen()

    try:
        punto_infinito = [foo(~tb)(0) for foo in Phibeta]
    except ZeroDivisionError:
        punto_infinito = None

    #Compute values to interpolate the change of
    #variable.
    pairs = []
    parameter = -1

    if verbose: print("create context: " + str(time()-tt))

    while len(pairs) < 3:
        parameter +=1
        if Den(parameter) != 0:
            if verbose: tt = time()
            point = [foo(parameter) for foo in Phi]
            if point != punto_infinito:
                equa = [ Phibeta[i].numerator() - point[i] *\
                        Phibeta[i].denominator() for i in range(n)]
                if verbose: print('compute system: ' + str(time() -tt))
                if verbose: tt = time()
                equa_s = my_gcd(equa)
                if verbose: print('gcd: ' + str(time()-tt))
                if verbose: tt =time()
                if equa_s.degree() ==1:
                    pairs += [(parameter, -equa_s[0]/equa_s[1])]
                else:
                    if verbose: print('degree: ' + str(equa_s.degree()))
                    counter_ndef += 1
                    if counter_ndef > bound_npoints:
                        raise ValueError(Not_defined)
                if verbose: print('solve parameter: ' + str(time() - tt))
    if verbose: tt = time()

    #Now we compute the change of variable s that transforms Phibeta in Phi
    s = (unitfrom3points(pairs, T))

    if verbose: print('interpolate s: ' + str(time()-tt))
    if check == True:
        #a certificate of definability over K, chaeck that Phi and Phibeta
        #intersects in enough points. Enough has to be discussed.

        if verbose: tt = time()

        Numphibeta, Denphibeta = \
                            parametrization_to_common_denominator(Phibeta)
        parameter = -1
        counter_ndef = 0

        #There are two possibilities, check that Phi and Phibeta intersect
        #in enugh points of that Phibeta(s) = Phi. Depending on the degree
        #of Phi and alpha, one can beat the other, wo we try a little bit of
        #each and decide later which one is preferable.
        #First, check at many points that the curves are the same.

        counter_one = time()
        while s.denominator()(parameter) == 0 or Den(parameter).norm()\
            == 0 or  Den(s(parameter)) ==0:
            parameter +=1

        sp = s(parameter)
        point = [foo(parameter) for foo in Phi]
        evalden = my_inverse_big_absnfield(Denphibeta(sp))
        point2 = [Numphibeta[foo](sp) * evalden for foo in range(n)]
        if point != point2:
            raise ValueError(Not_defined)

        #Now, check directly the composition.
        #We try to check if two rational functions of degree d are the same,
        #so it suffices to evaluate in 2*deg + 2 points

        counter_one = (deg*2 + 2) *(time() - counter_one)

        if verbose: print('time first try K-definability: ' + \
                              str(counter_one / (deg +1)))
        #counter_two = time()
        #L = Phibeta[0](s)
        #if L != Phi[0](T):
            #return Not_defined

        #c = time() - counter_two # n may be 1
        #counter_two = (n - 1) * c

        #if verbose: print('time second try K-definability: ' + str(c))

        #Continue with the method that is expected to be faster.

        if True:#counter_one < counter_two:
            while counter_ndef <= 2*deg +1:
                if verbose: tt1 = time()
                parameter += 1
                if s.denominator()(parameter) != 0 and Den(parameter).norm() != 0 and  Den(s(parameter)) !=0:
                    #Should be able to eliminate next Nb
                    sp = s(parameter)
                    point = [foo(parameter) for foo in Phi]
                    evalden = my_inverse_big_absnfield(Denphibeta(sp))
                    point2 = [Numphibeta[foo](sp) * evalden for foo in\
                            range(n)]
                    if point != point2:
                        raise ValueError(Not_defined)
                    counter_ndef += 1
                if verbose: print("a point: " + str(time()-tt1))
            if verbose: print('check def one: ' + str(time()-tt))
        else:
            if verbose: tt = time()
            L = [p(s)(T) for p in Phibeta[1:]]
            if L != Phi[1:]:
                raise ValueError(Not_defined)
            if verbose: print('check def two: ' +str(time()-tt))
    if verbose: tt=time()
    # we now compute psi, which is quite explicit.

    b = (T-s)/(alpha-beta)
    lc = b.denominator().leading_coefficient()
    b = (b.numerator()/lc)/(b.denominator()/lc)
    a = T - alpha*b

    return [a,b]

def witness(Phi, check = True, name = 't', verbose = False):
    """
    Compute the a witness variety of the parametrization of a rational curve.
    The witness variety is represented by its standard parametrization.

    INPUT:

    - ``Phi``: a list of rational functions in one variable representing a
      proper parametrization of a rational curve.

    - ``check``: a bolean value, if ``True``, it will perform a deterministic
      test to check that the original curve is defined over the base field. If
      ``False``, there will be no check. Note that, even if there are no check,
      the probability that the result is wrong is very unlikely.

    - ``name``: the variable that parametrizes the parametric Weil variety.

    OUTPUT:

    - ``Psi``: a list. If the parametrization ``phi`` has coefficients in
      ``N(a)``, ``Psi`` is the parametrization is standard form of the witness
      variety of ``Phi`` for the extension ``N`` in ``N(a)`` with primitive
      element ``a``. ``Psi`` will be an hypercircle if and only if the curve
      contains points in ``N``.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import *
        sage: N.<a> = NumberField(x^3 - 2)
        sage: K.<t> = N[]
        sage: u = random_linear_fraction(K)
        sage: Phi = witness([u])
        sage: Phi2 = witness(Phi)
        sage: Phi == Phi2
        True
        sage: v = inverse_unit(u,t)
        sage: L = QQ[t].fraction_field()
        sage: [simsim(f(v)) in L for f in Phi]
        [True, True, True]
        sage: Phi[0] + a*Phi[1] + a^2*Phi[2]
        t

    Relative fields are supported (somehow, if it does not work, please
    report)::

        sage: KalphaX.<xl> = NumberField([x^2-2, x^2-3], 's2,s3')[]
        sage: Kalpha = KalphaX.base_ring()
        sage: K = Kalpha.base_ring()
        sage: u = random_linear_fraction(KalphaX, 10, 1)
        sage: Phi = witness([u], name = xl)
        sage: change = is_hypercircle(Phi, inverse_unit(u,xl)(0))
        sage: is_com_unit(change)
        True

    Non-primitive hypercircle and relative extensions. See ``Fields of
    Parametrization and Optimal Affine Reparametrization of Rational Curves``::

        sage: Kalpha.<a> = NumberField(x^4-4*x^3+12*x^2-16*x+8,'a')
        sage: K = Kalpha.base_ring()
        sage: KalphaX.<t> = Kalpha['t']
        sage: Den = -22+26*a-9*a^2+2*a^3+4*t
        sage: Phi = [ (-6 + 18*a -9*a^2 + 6*a^3 + (44 -52*a +18*a^2 -4*a^3)*t -4*t^2) / Den, (-12 -2*a +9*a^2 -a^3 +(4+4*a+4*a^2)*t +(12-16*a+6*a^2-2*a^3)*t^2) / Den]
        sage: W = witness(Phi,name = 't')
        sage: W[0]+a*W[1]+a^2*W[2]+a^3*W[3]
        t
        sage: [p.denominator().degree() for p in W]
        [1, 1, 1, 1]

    It is a conic, so we compute an intermediate field::

        sage: point_infinity = [simsim(p(1/t)*t)(0) for p in W]
        sage: gamma = point_infinity[0]
        sage: gamma.minpoly().degree()
        2

    ``gamma`` is a primitive element of a field such that ``QQ(gamma)`` in
    ``QQ(a)`` defines a line as hypercircle, relativize is broken::

        sage: gamma *= gamma.lift().denominator() #Bug in relativize
        sage: Kgamma_alpha.<new_alpha, new_gamma> = Kalpha.relativize(gamma)

    Recompute the original parametrization in ``Kgamma_alpha``::

        sage: to_Kgamma_alpha = Kgamma_alpha.structure()[1]
        sage: Kgamma_alpha.register_coercion(to_Kgamma_alpha)
        sage: NewPhi = [conjugate_pol(p, to_Kgamma_alpha, Kgamma_alpha[t]) for p in Phi]
        sage: W2 = witness(NewPhi)
        sage: W2
        [t + (1/4*new_gamma + 1/2)*new_alpha, -1/4*new_gamma - 1/2]

    The new hypercircle is a line. It can be parametrized by ``[t,
    -1/4*new_gamma - 1/2]``
    We have found an algebraically optimal affine reparametrization.::

        sage: change = t + W2[1] * new_alpha
        sage: [simsim(p(change)) for p in NewPhi]
        [(-t^2 + (1/6*new_gamma + 5/3)*t - 1/6*new_gamma - 1/6)/(t -
        1/12*new_gamma - 5/6), ((-1/6*new_gamma + 1/3)*t^2 + (1/3*new_gamma -
        5/3)*t - 1/6*new_gamma + 4/3)/(t - 1/12*new_gamma - 5/6)]

    The reparametrization is over ``QQ[new_gamma]``.

    Now an example not defined over K but over an strict intermediate field::

        sage: x = var('x')
        sage: N = NumberField(x^4-2,'a')
        sage: a = N.gen()
        sage: K = N['t']
        sage: t = K.gen()
        sage: Phi = [(t^2-a^2)/(t^2+(2+a^2)*t-a^2-3), ((4*a^4+3)*t-2)/(t^2+(2+a^2)*t-a^2-3)]
        sage: u = random_linear_fraction(K)
        sage: Phi = [f(u) for f in Phi]
        sage: witness(Phi)
        ['N', 1, a^2]
        sage: witness([t,a*t])
        ['N', 1, a, a^2, a^3]
        sage: N = NumberField(x^9-2, 'a')
        sage: a = N.gen()
        sage: K = N['t']
        sage: t = K.gen()
        sage: Phi = [(t^2-a^3)/(t^2+(2+a^3+3*a^6)*t-a^6-3), ((4*a^3+3*a^6+1)*t-2-3*a^6)/(t^2+(2+a^3+3*a^6)*t-a^6-3)]
        sage: u = random_linear_fraction(K)
        sage: Phi = [f(u) for f in Phi]
        sage: witness(Phi)
        ['N', 1, a^3, a^6]

        sage: N = NumberField((x^7-1)/(x-1),'a')
        sage: a = N.gen()
        sage: K = N['t']
        sage: t = K.gen()
        sage: Phi = [t^3+1, (3*a+3*a**6+a^3+a^4)*t]
        sage: u = random_linear_fraction(K)
        sage: Phi = [f(u) for f in Phi]
        sage: witness(Phi)
        ['N', 1, a^5 + a^2, a^4 + a^3]

    TODO:

    - Add a non primitive example with relative K
    - Add nonprimitive example
    - Add degree one example

    TESTS:

    The following used to fail::

        sage: N.<I> = QQ[I]
        sage: K.<x> = N[]
        sage: u = (x-I)/(x+I)
        sage: witness([u])
        [0, -I*t]
        sage: var('x')
        x
        sage: N.<a> = NumberField(x^4-5, 'a')
        sage: K.<x> = N[]
        sage: u = (a**2*x-(a**2+1))/((4-a**2)*x+(a**2+3))
        sage: witness([u])
        [(1/2*t^2 - 1/10*a^2*t + 1/4)/(t - 1/10*a^2 - 1/4), 0, (1/10*a^2*t^2 -
        1/20*a^2*t - 1/20*a^2)/(t - 1/10*a^2 - 1/4), 0]

    For higher towers there were problems, they should be fixed now with
    Nbase_to_M morphism::

        sage: var('x')
        x
        sage: KalphaX.<xl> = NumberField([x^2-2, x^2-3, x^2-5], 's2, s3, s5')[]
        sage: Kalpha = KalphaX.base_ring()
        sage: K = Kalpha.base_ring()
        sage: u = random_linear_fraction(KalphaX, 10, 1)
        sage: Phi = witness([u], name = xl)
        sage: change = is_hypercircle(Phi, inverse_unit(u,xl)(0))
        sage: is_com_unit(change)
        True
    """
    #For performance reasons, try to stay with univariate rings
    if verbose: tt = time()
    #Better guess for K
    N_defined = True
    Not_defined = 'The curve is not defined over the ground field'

    n = len(Phi)
    K = Sequence(Phi).universe()
    if K.is_field():
        K = K.base()

    Phi = [K.fraction_field()(f) for f in Phi]

    N = K.base_ring()
    t = K.gen()
    alpha = N.gen()
    polmin = N.relative_polynomial()
    d = polmin.degree()

    def_L = [vector(QQ,d)]

    if d == 2:
        return __witness_deg_2(Phi, check, name, verbose, n, K, N, t, alpha, polmin, Not_defined)

    #these are used to interpolate the hypercircle
    diffpolmin = polmin.derivative()
    x = polmin.variables()[0]
    m = polmin.quo_rem(x-alpha)[0]

    #Compute the extension fields beta
    conjugates = m.factor()
    NT = N[name]
    T = NT.gen()

    #start computing the hypercircle
    psi = m.coefficients(sparse=False)
    psi = [foo / diffpolmin(alpha) *T for foo in psi]
    Den = my_lcm([foo.denominator() for foo in Phi])
    degree_denominator = Den.degree()
    deg = max(0, max([foo.numerator().degree()-foo.denominator().degree() for\
    foo in Phi])) + degree_denominator
    if deg == 0:
        raise ValueError("the parametrization does not define a curve")

    #is the following correct?
    bound_npoints = 3
    #degree_denominator + max([foo.numerator().degree() for foo in Phi]) + 1

    if verbose: print('pre: ' + str(time()-tt))

    for partial_extension in conjugates:
        good_extension = True
        if verbose: tt =time()

        #construct extension field K[alpha][beta] and the conjugate
        #parametrizations
        Nb = N.extension(partial_extension[0], 'hc_'+str(alpha)+'beta')
        N_to_Nb = Nb.coerce_map_from(N)
        beta = Nb.gen()
        nb = Nb.relative_degree()
        M = Nb.absolute_field('gc_'+str(alpha)+'gamma')
        M_to_Nb, Nb_to_M = M.structure()
        N_to_M = N_to_Nb.post_compose(Nb_to_M)
        beta_in_M = Nb_to_M(beta)
        counter_ndef = 0
        #This is ugly, but no idea how to circunvent this

        if N.is_absolute():
            conjugation = N.hom([beta_in_M])
        else:
            Nbase_to_M = Nb.coerce_map_from(N.base_ring()).post_compose(Nb_to_M)
            conjugation = N.Hom(M)(beta_in_M, base_hom = Nbase_to_M)

        Phibeta = [conjugate_pol(foo, conjugation, M[t]) for foo in Phi]
        tb = Phibeta[0].parent().gen()

        try:
            punto_infinito = [foo(~tb)(0) for foo in Phibeta]
        except ZeroDivisionError:
            punto_infinito = None
        Den_in_M = conjugate_pol(Den, N_to_M, M[t])
        Phi_in_M = [conjugate_pol(foo, N_to_M, M[t]) for foo in Phi]
        Num_in_M = [foo*Den_in_M for foo in Phi_in_M]

        #Now, everithing is in M, compute values to interpolate the change of
        #variable.
        pairs = []
        parameter = -1

        if verbose: print("create context: " + str(time()-tt))

        while len(pairs) < 3 and good_extension:
            parameter +=1
            if Den_in_M(parameter) != 0:
                if verbose: tt = time()
                point = [foo(parameter) for foo in Phi_in_M]
                if point != punto_infinito:
                    #I should be able to eliminate next Nb
                    equa = [ Phibeta[i].numerator() - point[i] *\
                            Phibeta[i].denominator() for i in range(n)]
                    if verbose: print('compute system: ' + str(time() -tt))
                    if verbose: tt = time()
                    equa_s = my_gcd(equa)
                    if verbose: print('gcd: ' + str(time()-tt))
                    if verbose: tt =time()
                    if equa_s.degree() ==1:
                        pairs += [(parameter, -equa_s[0]/equa_s[1])]
                    else:
                        if verbose: print('degree: ' + str(equa_s.degree()))
                        counter_ndef += 1
                        if counter_ndef > bound_npoints:
                            if verbose:
                                print 'Not defined over K, bad conjugate'
                            good_extension = False
                            N_defined = False
                    if verbose: print('solve parameter: ' + str(time() - tt))
        if verbose: tt = time()

        #Now we compute the change of variable s that transforms Phibeta in Phi
        if good_extension:
            s = (unitfrom3points(pairs, M[T].gen()))

        if verbose: print('interpolate s: ' + str(time()-tt))
        if check == True and good_extension:
            #a certificate of definability over K, chaeck that Phi and Phibeta
            #intersects in enough points. Enough has to be discussed.

            if verbose: tt = time()

            Numphibeta, Denphibeta = \
                                  parametrization_to_common_denominator(Phibeta)
            #parameter = 2
            #counter_ndef = 0

            #There are two possibilities, check that Phi and Phibeta intersect
            #in eough points of that Phibeta(s) = Phi. Depending on the degree
            #of Phi and alpha, one can beat the other, so we try a little bit of
            #each and decide later which one is preferable.
            #First, check at many points that the curves are the same.

            #counter_one = time()
            #while (s.denominator()(parameter) == 0 or Den_in_M(parameter)             == 0 or  Den_in_M(s(parameter)) ==0):
                #parameter +=1

            #sp = s(parameter)
            #point = [foo(parameter) for foo in Phi_in_M]
            #evalden = my_inverse_big_absnfield(Denphibeta(sp))
            #point2 = [Numphibeta[foo](sp) * evalden for foo in\
                      #range(n)]

            #if point != point2:
                #print 'Not defined over K, bad conjugate'
                #N_defined = False
                #good_extension = False

            #counter_one = time() - counter_one

            #Now, check directly the composition.
            #We try to check if two rational functions of degree d are the same,
            #so it suffices to evaluate in 2*deg + 2 points

            #if verbose: print('time first try K-definability: ' + \
                              #str(counter_one))

            counter_two = time()
            L = Phibeta[0](s)(M[t].gen())
            if L != Phi_in_M[0]:
                print 'Not defined over K, bad conjugate'
                N_defined = False
                good_extension = False

            counter_two = time() - counter_two # n may be 1

            if verbose: print('time second try K-definability: ' +
                               str(counter_two))

            #Continue with the method that is expected to be faster.

            if False:#counter_one*(2*deg+1) < counter_two*n:
                while counter_ndef <= 2*deg +1 and good_extension:
                    if verbose: tt1 = time()
                    parameter += 1
                    if s.denominator()(parameter) != 0 and Den_in_M(parameter).norm() != 0 and  Den_in_M(s(parameter)) !=0:
                        #Should be able to eliminate next Nb
                        sp = s(parameter)
                        point = [foo(parameter) for foo in Phi_in_M]
                        evalden = my_inverse_big_absnfield(Denphibeta(sp))
                        point2 = [Numphibeta[foo](sp) * evalden for foo in\
                                  range(n)]
                        if point != point2:
                            print 'Not defined over K, bad conjugate'
                            N_defined = False
                            good_extension = False
                        counter_ndef += 1
                    if verbose: print("a point: " + str(time()-tt1))
                if verbose: print('comprobar def one: ' + str(time()-tt))
            elif good_extension:
                if verbose: tt = time()
                L = [p(s)(M[t].gen()) for p in Phibeta[1:]]
                if L != Phi_in_M[1:]:
                    print 'Not defined over K, bad conjugate'
                    N_defined = False
                    good_extension = False
                if verbose: print('check def two: ' +str(time()-tt))
        if verbose: tt=time()

        #Now, we update the psi with the information of s, to go down to
        #K[alpha] we use traces. But to do it efficiently, we need the norm of
        #the denominator first.

        if N_defined:
            de = s.denominator() # in M
            nu = [conjugation(foo) * my_inverse_big_absnfield(Nb_to_M(diffpolmin(beta))) * s.numerator() for foo in m] # in M

            if verbose: print('trace, numer and denom: ' + str(time()-tt))
            if verbose: tt =time()

            if de.degree() == 0:
                #nu = nu/de
                nu = [foo/de[0] for foo in nu] # in M
                De_N = N[T].one() # in N
                De_M = M[T].one() # in M
            elif de.degree() == 1:
                #Ugly coercion
                if verbose: tt0 = time()
                element = -de[0]/de[1] # in M
                if verbose: print(time()-tt0)
                if verbose: tt2=time()
                element = M_to_Nb(element) # in Nb
                if verbose: print(time()-tt2)
                if verbose: tt1=time()
                De_N = element.minpoly(T)
                if verbose: print('rel: ', time() -tt1)
                De_M = conjugate_pol(De_N, N_to_M, M[T]) # in M
                if verbose: print(time()-tt1)
            else:
                raise RuntimeError('unexpected degree')

            if verbose: print('trace, norm of denom: ' + str(time()-tt))
            if verbose: tt=time()

            nu2 = De_M.quo_rem(de)[0] # in M

            if verbose: print("trace, cofactor of denom: " + str(time()-tt))
            if verbose: tt=time()

            Nu = [foo*nu2 for foo in nu] # in M

            if verbose: print("trace, new numer: " + str(time()-tt))
            if verbose: tt = time()

            nsums = newton_sums(Nb) # in N

            if verbose: tt1=time()

            Nu = [N[T]([rel_trace(nsums, M_to_Nb(coe)) for coe in foo.coefficients(sparse=False)]) for foo in Nu] # in N

            if verbose: print("trace, compute trace: " + str(time()-tt))
            if verbose: tt =time()

            #update psi
            psi = [psi[i] + Nu[i]/De_N for i in range(d)]

            if verbose: print("update F, multivariate gcd: " + str(time()-tt))

        if good_extension:
            if verbose:
                print('computing equations for field of definition')
                tt = time()
            if nb == d-1 and not N_defined:
                if verbose: print Not_defined
                return ['N']+[alpha**i for i in range(d)]
            Mat = matrix([sum([f.list() for f in (beta**i).list()],[]) for i in range(d)])
            def_L = def_L + (Mat.matrix_from_columns(range(d)) - identity_matrix(d)).columns()
            def_L = def_L + Mat.matrix_from_columns(range(d,Mat.ncols())).columns()
            if verbose:
                print('time of equations: '+ str(time()-tt))
            #return Mat
            #print(Mat)
            #print(len(Mat[0]))
            #M0 = matrix([f[0].vector() for f in Mat]) - identity_matrix(d)
            #M1 = matrix([f[i].vector() for f in Mat for i in range(1,nb)])
            #def_L = def_L + M0.rows() + M1.rows()

    if not N_defined:
        if verbose: print Not_defined
        if verbose: tt = time()
        def_L = matrix(def_L)
        out = ['N']+[N(f) for f in def_L.right_kernel().basis()]
        if verbose:
            print('time to compute field of definition: '+ str(time()-tt))
        return out
    return psi

def alpha_components(P):
    """
    Write a multivariate polynomial ``P`` in ``K(alpha)[t]`` as a vector in
    ``K[t]``. This is the inverse of ``sums_alpha``.

    INPUT:

    - ``P``: a polynomial in ``K(alpha)``

    OUTPUT:

    - A vector ``L`` such that ``sums_alpha(L, alpha) =  P``. The elements of
      ``L`` are in ``K[t]``.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import alpha_components, sums_alpha
        sage: N.<a> = QQ[2^(1/3)]
        sage: K.<x,y> = N['x,y']
        sage: f = K.random_element(5)
        sage: P = alpha_components(f)
        sage: P[0] in QQ['x,y']
        True
        sage: f - sums_alpha(P, 1, a)
        0

    TESTS::

        sage: K1=PolynomialRing(QQ[sqrt(2)], ('t','x','y'), order=TermOrder('degrevlex', 1) + TermOrder('degrevlex',2))
        sage: t,x,y=K1.gens()
        sage: a=K1.base_ring().gen()
        sage: a**2
        2
        sage: f=a*x-y
        sage: alpha_components(f)
        (-y, x)

    """
    #Better idea?
    Kalpha = P.base_ring()
    K = Kalpha.base_ring()
    n = Kalpha.relative_degree()
    PP = P.parent()
    varis = PP.gens()
    if len(varis)==1:
        KX = PolynomialRing(K, varis)
    else:
        KX = PolynomialRing(K, varis, order=PP.term_order())
    V = vector(KX, n)
    VS=V.parent()
    coef = P.coefficients()
    mon = P.monomials()
    mon = [KX(m) for m in mon]
    for m in range(len(mon)):
        V += mon[m] * VS(coef[m].vector())
    return V

def implicite_hc(Phi, name = 'Y', method = 'echelon', verbose = False):
    """
    Compute the implicit ideal of an hypercircle using the algorithm in ``Fast
    computation of the implicit ideal of a hypercircle``.

    INPUT:

    - ``Param``: Proper parametrization of a primitive hypercircle
    - ``W``: variable for the implicit equations
    - ``method``: ``echelon`` (default), ``grobner`` or ``dummy``

    OUTPUT:

    - ``I``: The projective implicit ideal of ``Phi`` in ``K[W_i]`` where ``K``
      is the ground field.

    One a set of generators is computed, perform a reduction to return less
    generators. ``echelon`` uses linear algebra, ``grobner`` use groebner bases,
    ``dummy`` does not perform any reduction and return all generators.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import *
        sage: N.<I> = QQ[I]
        sage: K.<x> = N[]
        sage: u = (I*x-2)/(x+1+3*I)
        sage: w = witness([u])
        sage: implicite_hc(w)
        Ideal (Y0^2 + Y1^2 + Y0*Y2 + 5*Y1*Y2 + 6*Y2^2) of Multivariate
        Polynomial Ring in Y0, Y1, Y2 over Rational Field
        sage: var('x')
        x
        sage: N.<a> = NumberField(x^3-2)
        sage: K = N['p']
        sage: u = random_linear_fraction(K)
        sage: w = witness([u])
        sage: I = implicite_hc(w)
        sage: L = I.gens()
        sage: len(L)
        3
        sage: L[0](w[0], w[1], w[2], 1)
        0
        sage: L[1](w[0], w[1], w[2], 1)
        0
        sage: L[2](w[0], w[1], w[2], 1)
        0

    A non-primitive case::

        sage: var('x')
        x
        sage: N.<alpha> = NumberField(x^4-2)
        sage: K.<t> = N[]
        sage: u = ((1-alpha**2)*t+(1+alpha**2*3) ) /((1+3*alpha**2)*t+5*alpha**2-7)
        sage: H =  witness([u])
        sage: I = implicite_hc(H)
        sage: I
        Ideal (Y0^2 - 2*Y2^2 - 1/2*Y0*Y4 - 5*Y2*Y4 + 13/2*Y4^2, Y1, Y3) of
        Multivariate Polynomial Ring in Y0, Y1, Y2, Y3, Y4 over Rational Field

    Another examples, where the linear part is not constant::

        sage: var('x')
        x
        sage: N.<a> = NumberField(x^6 + 6*x^5 + 15*x^4 + 20*x^3 + 15*x^2 + 6*x - 1)
        sage: K.<t> = N['t']
        sage: u = ((-a^3 - 3*a^2 - 3*a + 1)*t - 2*a^3 - 6*a^2 - 6*a - 1)/((13*a^3 + 39*a^2 + 39*a + 14)*t - 7*a^3 - 21*a^2 - 21*a - 11)
        sage: H = witness([u])
        sage: I = implicite_hc(H)
        sage: I = I.gens()
        sage: [I[i](H[0], H[1], H[2], H[3], H[4], H[5], 1) for i in range(len(I))]
        [0, 0, 0, 0, 0]
        sage: I[1]
        Y1 - 3*Y3

    REFERENCE:

    AGGM algorithm
    """
    from sage.matrix.constructor import matrix
    from sage.rings.ideal import Ideal

    #extract data from the input
    d = len(Phi)
    KalphaX = Phi[0].numerator().parent()
    Kalpha = KalphaX.base_ring()
    K = Kalpha.base_ring()
    alpha = Kalpha.gen()

    #pass to a projective parametrization

    Phiproj, Den = parametrization_to_common_denominator(Phi)
    Phiproj.append(Den)

    #Compute the matrix of linear change of variables and enough variables.

    degree_curve = max(p.degree() for p in Phiproj)
    Q = matrix(Kalpha, d+1, degree_curve+1, lambda x,y: Phiproj[x][y])
    X = PolynomialRing(Kalpha, 'X', d+1).gens() # change this
    Y = vector( PolynomialRing(K, name, d+1).gens() )

    #precompute the ideal of the rational normal curve of degree d

    Id = sum([[X[i]*X[j-1]-X[i-1]*X[j] for j in range(i+1,degree_curve+1)] for i in range(1,degree_curve +1)], [])

    if d == degree_curve:
        T = (~Q)*(Y)
        T_linear = []
    else:
        #the matrix is of size (d+1) x (r+1)
        #Compute first a regular submatrix
        pivots = Q.pivot_rows()
        nopivots = sorted(list(set(range(d+1)).difference(set(pivots))))
        Am = Q.matrix_from_rows(pivots).inverse()
        B_ = Q.matrix_from_rows(nopivots)
        B = - B_*Am
        Q1 = matrix(Kalpha, d+1, d+1)
        Q1[0:degree_curve +1, 0:degree_curve +1] = Am
        Q1[degree_curve +1:, 0:degree_curve +1 ] = B
        Q1[degree_curve+1:, degree_curve +1:] = matrix(Kalpha,\
                                              d-degree_curve, d-degree_curve, 1)
        Y1 = vector([Y[p] for p in pivots] + [Y[p] for p in nopivots])
        T = Q1*Y1
        T_linear = T[degree_curve +1: ].list()


    # Construct the ideal, note that the polynomials obtained contains alpha's
    # but that the ideal is defined over the ground field, so we can just take
    # the alpha ocmponents to obtain generators over the ground field.

    Equa = [ p(T.list()) for p in Id] + T_linear #This is slowww!

    Gene = sum( [alpha_components(p).list() for p in Equa] , [])

    # We obtained too much generators, so we give the obtion to reduce them
    # using grobner basis or linear algebra.

    if method == 'dummy':
        return Ideal(Gene)
    elif method == 'grobner':
        return Ideal(Ideal(Gene).groebner_basis())
    elif method != 'echelon':
        raise ValueError('Unknown output')
    monomials = sum([[Y[i]*Y[j] for i in range(j,d+1)] for j in range(d+1)],[])\
                    + Y.list()
    Q = matrix(K, len(Gene), len(monomials), lambda x,y:\
                Gene[x].monomial_coefficient(monomials[y]))
    Q = Q.echelon_form()
    G = (Q*vector(monomials)).list()[0:Q.rank()]
    return Ideal(G)

def unit_to_hc_sqrt(U, name = None, verbose = False):
    """
    Take a unit for a extension of degree 2 of the form ``N[sqrt(x)]`` and
    compute the parametrization of the associated conic. Units under
    composition are isomorphic to GL(2,F)

    INPUT:

    - ``U``: a linear fraction with coefficients in ``N[beta]`` and ``beta``
      is of degree 2.

    OUPUT:

    - ``S``: The standar parametrization of the hypercircle associated to
      ``[U]``, this is much faster than witness, specially if the ground field
      is complicated.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import *
        sage: N.<I> = QQ[I]
        sage: K.<xul> = N[]
        sage: u = random_linear_fraction(K)
        sage: unit_to_hc_sqrt(u) == witness([u], name = xul,check = False)
        True
    """
    from sage.matrix.constructor import matrix
    if not is_com_unit(U):
        raise ValueError("The input %s is not a unit")%s(U)
    if verbose: tt = time()

    #Extract the data.

    N = U.base_ring()
    if name is None:
        name = str(U.parent().gen())
    t = N[name].gen()
    a = U.numerator()[1]
    b = U.numerator()[0]
    c = U.denominator()[1]
    d = U.denominator()[0]
    if verbose: print('create context: ' + str(time()-tt))
    if verbose: tt = time()

    #compute the conjugate, without extending the field.
    beta = N.gen()
    abar = a[0]-beta*a[1]
    bbar = b[0]-beta*b[1]
    cbar = c[0]-beta*c[1]
    dbar = d[0]-beta*d[1]

    if verbose: print('compute morphism and conjugates: ' + str(time() -tt))
    if verbose: tt = time()

    #matrix representation
    M = matrix(N, [[a,b], [c,d]])
    Mbar = matrix(N, [[abar, bbar], [cbar, dbar]])

    if verbose: print('create matrices: ' +str(time() -tt))
    if verbose: tt = time()

    #compute  Mbar^{-1}(M)

    S = Mbar.solve_right(M)

    if verbose: print('solve system: ' +str(time() -tt))
    if verbose: tt = time()

    #reconstruct the unit.

    s = (S[0,0]*t+S[0,1]) / (S[1,0]*t+S[1,1])

    if verbose: print('create composition unit: ' +str(time() -tt))
    if verbose: tt = time()

    # Compute the standar parametrization,
    # this would be the psi in method witness.
    p0 = simsim((s+t)/2)
    p1 = simsim((t-s)/(2*beta))

    if verbose: print('compute standar parametrization: ' +str(time() -tt))

    return [p0,p1]

def rational_point_conic(Phi, parameter, verbose = False):
    """
    Compute a parameter ``t0`` such that ``Phi(t0)`` is a rational point:

    INPUT:

    - ``Phi``: a standar parametrization of a conic as hypercircle in
      ``QQ[alpha][beta]``.
    - ``parameter``: an element in ``QQ[alpha][beta]`` such that
      ``Phi(parameter)`` gives an odd divisor over ``QQ[alpha]``. ``alpha`` must
      be of odd degree over ``QQ``.

    OUPUT:

    - ``t0``: element in ``QQ[alpha][beta]`` such that ``Phi(t0)`` is a rational
      point.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import rational_point_conic
        sage: N.<beta, alpha> = NumberField([x^2+23, x^3+2], 'beta, alpha')
        sage: K.<t> = N[]
        sage: conic = [(1/2*t^2 - 10/69*beta*t - 49/3)/(t - 10/69*beta - 20/3),         (-1/46*beta*t^2 + 20/69*beta*t - 49/69*beta)/(t - 10/69*beta - 20/3)]
        sage: t_odd = (-1/108*alpha^2 + 8/27*alpha + 19/54)*beta -         187/108*alpha^2 + 38/27*alpha + 421/54
        sage: conic[0](t_odd), conic[1](t_odd) # An odd point
        (-187/108*alpha^2 + 38/27*alpha + 421/54, -1/108*alpha^2 + 8/27*alpha +
        19/54)
        sage: t0 = rational_point_conic(conic, t_odd)
        sage: t0
        5/6*beta + 11/2
        sage: conic[0](t0), conic[1](t0)
        (11/2, 5/6)

    TODO:

    Do not ask the parameter to give an element in ``QQ[alpha]``. Needed if the
    original curve is of odd degree but ``alpha`` is of even degree.
    """
    from sage.matrix.constructor import matrix
    if verbose: tt = time()
    #extract data
    Kbetat = Phi[0].parent().base()
    t = Kbetat.gen()
    Kbeta = Kbetat.base_ring()
    beta = Kbeta.gen()
    Kalpha = Kbeta.base_ring()
    deg = Kbeta.base_ring().relative_degree()

    #degree of second curve and curves of degree m passing thorugh the odd
    #divisor.
    m = (deg + 1)/2
    tstring = str(Kbeta.gen())
    KalphaWt = PolynomialRing(Kalpha, sum([ [tstring + 'W' + str(i) + '_' +\
               str(j) for j in range(0,m-i+1)] for i in range(0,m+1)], []))
    W = KalphaWt.gens()

    if verbose: print('pre: ' + str(time()-tt))
    if verbose: tt = time()
    x, y = [Kalpha(p(parameter).lift()) for p in Phi]
    Equa = sum([sum([ KalphaWt(tstring+'W'+str(i)+'_'+str(j))*x**i*y**j\
                for j in range(0,m-i+1)]) for i in range(0,m+1)])
    Equa = alpha_components(Equa)
    if verbose: print('computing equations: ' + str(time()-tt))
    if verbose: tt = time()
    QQW = QQ[W].gens()
    Q = matrix(QQ, len(Equa), len(QQW), lambda x,y:\
        Equa[x].monomial_coefficient(QQW[y]))

    #reduce the basis of curves
    Q , _ = Q._clear_denom()
    for i in range(Q.nrows()):
        d = gcd(Q.row(i))
        Q.set_row( i , (Q.row(i) /d))

    # pretty illegal, but I do not need chache
    L = Q._rational_kernel_iml().transpose()
    for i in range(L.nrows()):
        d = gcd(L.row(i))
        L.set_row( i , (L.row(i) /d))
    if verbose: print('find solutions: ' + str(time()-tt))
    if verbose: tt = time()

    L = L.saturation(max_dets = 0).LLL() #it is almost never saturated

    if verbose: print('reducing size solutions: ' + str(time()-tt))
    if verbose: tt = time()
    x, y = Phi

    #pass the parametrization to QQ[beta]
    r= beta.minpoly().change_ring(ZZ)
    SS = QQ.extension(r, str(beta))[t]
    #I should be able to avoid this now...
    x = SS(str(Phi[0].numerator())) / SS(str(Phi[0].denominator()))
    y = SS(str(Phi[1].numerator())) / SS(str(Phi[1].denominator()))

    evaluation_vector = vector(sum([[ x**i * y**j for j in range(0,m-i+1)]\
                        for i in range(0,m+1)], []))
    evaluation_vector, _ = \
                        parametrization_to_common_denominator(evaluation_vector)
    evaluation_vector = vector(evaluation_vector)

    if verbose: print('computing evaluation vector: ' +str(time()-tt))
    if verbose: tt = time()

    # look for a curve of degree at most m passing through the odd divisor but
    # not containing the conic.
    i = 0
    c = L[0] * evaluation_vector
    while c == 0:
        i = i + 1
        c = L[i] * evaluation_vector

    if verbose: print('choosing a small solution: ' + str(i) + ', '\
                      + str(time()-tt))
    if verbose: tt = time()

    # intersect the small curve found with the conic. The intersection will be
    # the odd divisor plus a rational point.

    c = c.numerator()
    c = c // gcd(c, SS(parameter.absolute_minpoly()))
    if c.degree() != 1:
        raise ValueError("There is an error somewhere")

    #et voila!
    c = Kbeta((-c[0]/c[1]).list())
    if verbose: print('compute parameter from solutions: ' + str(time()-tt))
    return c

def drop_beta(U):
    """
    Take a fraction in ``N(beta)(t)`` but whose coefficients are in ``N``.
    Output de same rational fraction in ``N(t)``.

    INPUT:

    - A rational function ``U`` with parent ``N(beta)(t)`` with coefficients in
      ``N(t)``.

    OUTPUT:

    - The same rational function ``U`` in ``N(t)``.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import drop_beta
        sage: N = QQ[sqrt(2), sqrt(3)]
        sage: s2, s3 = N.gens()
        sage: K.<x> = N[]
        sage: u = (s3*x^2 + (1 - s3)*x +1) / (s3 * x^2 +1 -3*s3)
        sage: v = drop_beta(u)
        sage: u == v
        True
        sage: u.parent() is K.fraction_field()
        True
        sage: v.parent() is K.fraction_field()
        False
        sage: v.parent() is N.base_ring()[x].fraction_field()
        True

    """
    Un = U.numerator().list()
    Ud = U.denominator().list()
    t = U.parent().gen()
    Kalpha = U.base_ring().base_ring()
    Kalphat = Kalpha[t]
    Un = Kalphat([x.lift() for x in Un])
    Ud = Kalphat([x.lift() for x in Ud])
    return simsim(Un / Ud)

def simplify_unit(U):
    """
    Take a linear fraction ``U`` with coefficients on a number field and return
    a linear fraction ``V`` such that ``V = U(S)``, where ``S`` is a linear
    fraction in ``QQ``.

    It is expected that ``V`` has smaller coefficients that ``U``.

    INPUT:

    - ``U``: A linear fraction with coefficients in a number field ``N``.

    OUTPUT:

    - ``V = U(S)``, with ``S`` a linear fraction with coefficients in ``QQ``,
      it is expected that ``V`` is simpler than ``U``.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import *
        sage: K.<x> = QQ[I][]
        sage: I = QQ[I].gen()
        sage: u = (125*x+I) / (125*x-I)
        sage: simplify_unit(u)
        (x + I)/(x - I)
        sage: u = random_linear_fraction(K)
        sage: v = simplify_unit(u)
        sage: w = inverse_unit(u)(v)
        sage: w in K.fraction_field()
        True
    """
    from sage.misc.functional import denominator
    from sage.matrix.constructor import matrix

    #extract data
    Kalphat = U.parent()
    t = Kalphat.gen()
    Kalpha = Kalphat.base_ring()

    #pass to absolute extension
    if not Kalpha.is_absolute():
        beta = 'beta'.join(map(str,Kalpha.gens()))
        M = Kalpha.absolute_field(beta)
        from_M, to_M = M.structure()
        UM = conjugate_pol(U, to_M, M[t])
        #recursive call
        UM = simplify_unit(UM)
        UM = conjugate_pol(UM, from_M, Kalphat)
        return simsim(UM)

    #extract more data
    d = Kalpha.degree() # absolute field only
    U = simsim(U)
    un = U.numerator()
    ud = U.denominator()
    A = un[1].list()
    B = un[0].list()
    C = ud[1].list()
    D = ud[0].list()
    v1 = A + C
    v2 = B + D
    denom = lcm(map(denominator, v1+v2))

    #A subset of the orbit of the unit is represented by Q
    Q, _ = matrix(QQ, [v1, v2])._clear_denom()

    # reducing Q, we look for a simpler representation of U
    # on its equivalent class.
    Q = Q.saturation().LLL(0.99)
    f = lambda x: Kalpha(list(x)[0])

    #reconstruct the unit from Q.
    V = (f(Q[0,0:d])*t + f(Q[1,0:d])) / (f(Q[0,d:])*t + f(Q[1,d:]))
    V = simsim(V)
    return V

class Hypercircle():
    """
    This is a class representing a hypercircle for a extension ``QQ`` in
    ``QQ(alpha)``

    Accesing the elements of the Hypercircle are interpreting as accesing
    elements of the standard parametrization.

    It is initialized by a proper parametrization of a curve ``C`` in
    ``QQ(alpha)`` represented by a list of rational functions.
    The hypercircle will be associated to the parametrization.
    In particular, if one wants to compute the hypercircle generated by a unit
    ``u``, one can call Hypercircle in the parametrization [inverse_unit(u)]
    defined by the inverse of ``u``.

    While some features work if the ground field is different from ``QQ`` this
    is not assured to work.

    INPUT:

    - Phi: a list of rational functions in ``K(alpha)[t]`` representing
      the parametrization.
    - check (optional, default: True): check K-definability.
    - name: (optional) a name for the parameter of the parametrization of the
      hypercircle. By default it takes the variable of Phi.
    - verbose (optional, defaul: False) print verbose information.

    EXAMPLES::

        sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, random_linear_fraction
        sage: N.<I> = QQ[I]
        sage: K.<t> = N[]
        sage: u = t
        sage: H = Hypercircle([u])
        sage: H
        Hypercircle over Number Field in I with defining polynomial x^2 + 1
        sage: H.parametrization()
        [t, 0]
        sage: H[0] # Extract a term form the parametrization
        t
        sage: H(2/3) # compute the point corresponding to parameter 2/3
        [2/3, 0]
        sage: H.compute_associated_unit(0) #See the documentation
        t
        sage: v = random_linear_fraction(NumberField(x^6-2,'a')['x']);
        sage: H2 = Hypercircle([v])
        sage: alpha = v.base_ring().gen()
        sage: sum([H2[i]*alpha**i for i in range(6)])
        x
    """
    def __init__(self, Phi, check = True, name = False, verbose = False):
        """
        Indirect doctest.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N = QQ[I]
            sage: K.<t> = N[]
            sage: u = t
            sage: H = Hypercircle([u], check = false, name = 'y', verbose=false)
            sage: H
            Hypercircle over Number Field in I with defining polynomial x^2 + 1
            sage: H.parametrization()
            [y, 0]
            sage: H[0] # Extract a term form the parametrization
            y
            sage: H(2/3) # compute the point corresponding to parameter 2/3
            [2/3, 0]
            sage: H.compute_associated_unit(0) #See the documentation
            y
        """
        K = Sequence(Phi).universe()
        if K.is_field():
            K = K.base()

        N = K.base_ring()
        self.__Kalpha_t = K
        #Problemas con name
        if not name:
            name = K.gen()
        self.__Kalpha = N
        self.__K = N.base_ring()
        alpha = N.gen()
        self.__alpha = alpha
        polmin = N.relative_polynomial().monic()
        self.__polmin = polmin
        d = polmin.degree()
        self.__ambient_dimension = d

        Not_defined = 'The curve is not defined over the ground field'

        #The case that Phi is polynomial can make things not work
        Kf = K.fraction_field()
        Phi = [Kf(foo) for foo in Phi]

        if len(Phi) == 1 and is_com_unit(Phi[0])\
                         and N.relative_polynomial()[1]==0\
                         and N.relative_degree() == 2:
            psi = unit_to_hc_sqrt(Phi[0], name, verbose)
        else:
            psi = witness(Phi, check, name, verbose)

        if psi[0] == 'N':
            raise ValueError(Not_defined, psi)

        self.__standar_parametrization = psi
        self.__t = psi[0].numerator().parent().gen()

    def __repr__(self):
        """
        Return the representation of the hypercircle

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H
            Hypercircle over Number Field in a with defining polynomial x^3 - 2
        """
        return 'Hypercircle over %s'%(self.K_alpha())

    def K_alpha(self):
        """
        Return the number field K(alpha)

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H.K_alpha() is N
            True
        """
        return self.__Kalpha

    def alpha(self):
        """
        Return the primitive element of the extension.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H.alpha()
            a
        """
        return self.__alpha

    def t(self):
        """
        Return the variable of the parametrization

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<s>=N[]
            sage: u = 1/(s-a)
            sage: H = Hypercircle([u])
            sage: H.t()
            s
            sage: H2 = Hypercircle([u], name='var9')
            sage: H2.t()
            var9
        """
        return self.__t

    def K(self):
        """
        Return the base field K

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H.K() is QQ
            True
        """
        return self.__K

    def ambient_dimension(self):
        """
        Return the ambient dimension of the hypercircles

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H.ambient_dimension() == N.degree()
            True
        """
        return self.__ambient_dimension

    def polmin(self):
        """
        Return the minimal polynomial of alpha

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H.polmin()
            x^3 - 2
        """
        return self.__polmin

    def parametrization(self):
        """
        Return the standar parametrization of the hypercircle

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H.parametrization()
            [t - a, 1, 0]
        """
        return self.standard_parametrization()

    def __getitem__(self, i):
        """
        Return the i-th component of the standar parametrization

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H[0]
            t - a
            sage: H[3]
            Traceback (most recent call last):
            ...
            IndexError: list index out of range
        """
        return self.__standar_parametrization[i]

    def ideal(self, name = 'Y', method = 'echelon', verbose = False):
        """
        Return the implicit ideal of the hypercircle

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = (a*t+a)/(t-a)
            sage: H=Hypercircle([u])
            sage: I = H.ideal(); I
            Ideal (Y0^2 - 2*Y1*Y2 + Y0*Y3 + 2*Y2*Y3, Y0*Y1 - 2*Y2^2, -Y1^2 +
            Y0*Y2 + Y1*Y3 + Y2*Y3) of Multivariate Polynomial Ring in Y0, Y1,
            Y2, Y3 over Rational Field
            sage: [foo(Y0=H[0],Y1=H[1],Y2=H[2],Y3=1) for foo in I.gens()]
            [0, 0, 0]
            sage: H.ideal(name='x')
            Ideal (x0^2 - 2*x1*x2 + x0*x3 + 2*x2*x3, x0*x1 - 2*x2^2, -x1^2 +
            x0*x2 + x1*x3 + x2*x3) of Multivariate Polynomial Ring in x0, x1,
            x2, x3 over Rational Field
        """
        try:
            return self.__ideal[name]
        except(AttributeError):
            I = implicite_hc(self.parametrization(), name = name,\
                           method = method, verbose = verbose)
            self.__ideal = {name:I}
        except(KeyError):
            I = implicite_hc(self.parametrization(), name = name,\
                           method = method, verbose = verbose)
            self.__ideal[name] = I
        return self.__ideal[name]

    def degree(self):
        """
        Return the degree of the hypercircle

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = (a*t+a)/(t-a)
            sage: H=Hypercircle([u])
            sage: H.degree()
            3
            sage: u = (t+a)/(t-a)
            sage: H = Hypercircle([u])
            sage: H.degree()
            1
        """
        i = 0
        while self[i].numerator().degree() < 1:
            i += 1
        return self[i].numerator().degree()

    def is_primitive(self):
        """
        Check if the hypercircle is primitive

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = (a*t+a)/(t-a)
            sage: H=Hypercircle([u])
            sage: H.is_primitive()
            True
            sage: u = 1/(t-a)
            sage: H=Hypercircle([u])
            sage: H.is_primitive()
            False
        """
        return self.degree() == self.ambient_dimension()

    def is_line(self):
        """
        Return wether the hypercircle is a line or not.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = (a*t+a)/(t-a)
            sage: H = Hypercircle([u])
            sage: H.is_line()
            False
            sage: H = Hypercircle([t])
            sage: H.is_line()
            True
        """
        return self.degree() == 1

    def unit(self):
        """
        Return an associated unit

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, simsim
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t>=N[]
            sage: u = (a*t+a)/(t-a)
            sage: H = Hypercircle([u])
            sage: H.unit()
            Traceback (most recent call last):
            ...
            ValueError: Associated unit not yet discovered
            sage: H.compute_associated_unit(0)
            (-a^2 + a + 2)/(t + a^2 - a)
            sage: [simsim(P(H.unit())) for P in H]
            [(2*t^2 - 4*t + 2)/(t^3 + 6*t + 2), (t^2 + 4*t + 4)/(t^3 + 6*t + 2),
            (-t^2 - t + 2)/(t^3 + 6*t + 2)]
        """
        try:
            return self.__unit
        except(AttributeError):
            raise ValueError('Associated unit not yet discovered')

    def set_unit(self, unit, check = True, simplify = False):
        """
        Declare an associated unit to the hypercircle. If check is True, compute
        also an associated rational parametrization and cache it. If simplify is
        True, an equivalent unit with possibly smaller coefficients will be used instead.

        As a side effect, it will change the internal unit and, as a side effect
        if check = True, change the internar rational parametrization.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, inverse_unit
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t> = N[]
            sage: u = (t+a)/(t-a)
            sage: v = inverse_unit(u)
            sage: H = Hypercircle([v])
            sage: H.set_unit(t) # not an associated unit
            Traceback (most recent call last):
            ...
            TypeError: not a constant polynomial
            sage: H.set_unit(u)
            sage: H.rational_parametrization()
            [(t^3 + 2)/(t^3 - 2), 2*t^2/(t^3 - 2), 2*t/(t^3 - 2)]
            sage: H.set_unit((a*t + 1)/(-a*t + 1)) # another unit
            sage: H.rational_parametrization()
            [(-t^3 - 1/2)/(t^3 - 1/2), -t/(t^3 - 1/2), -t^2/(t^3 - 1/2)]
        """
        if simplify:
            unit = simplify_unit(unit)

        if check:
            rep = [simsim(p(unit)) for p in self.parametrization()]
            rep = map(drop_beta, rep)
            self.__rational_parametrization = rep
        self.__unit = unit

    def rational_parametrization(self):
        """
        Return a rational parametrization if precomputed or if we already have
        a unit. See also compute_rational_parametrization. The result is cached

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, inverse_unit
            sage: N.<a> = NumberField(x^4+3)
            sage: K.<t> = N[]
            sage: u = ((2*a+a**3)*t+1)/((1-a)*t-2*a)
            sage: H = Hypercircle([u])
            sage: H.set_unit(inverse_unit(u))
            sage: H.rational_parametrization()
            [(-3/2*t^4 - 41/4*t^3 - 21*t^2 - 18*t)/(t^4 + 9*t^3 + 57/2*t^2 +
            42*t + 147/4), (1/2*t^4 + 13/4*t^3 + 29/4*t^2 + 3*t + 21/4)/(t^4 +
            9*t^3 + 57/2*t^2 + 42*t + 147/4), (1/2*t^4 + 11/4*t^3 + 7*t^2 +
            43/4*t)/(t^4 + 9*t^3 + 57/2*t^2 + 42*t + 147/4), (1/2*t^4 + 9/4*t^3
            + 9/4*t^2 + 15/4*t + 7/2)/(t^4 + 9*t^3 + 57/2*t^2 + 42*t + 147/4)]
        """
        try:
            return self.__rational_parametrization
        except AttributeError:
            u = self.unit()
            rep = [simsim(p(u)) for p in self.parametrization()]
            rep = map(drop_beta, rep)
            self.__rational_parametrization = rep
            return rep

    def standard_parametrization(self):
        """
        Returns the standard parametrization of the hypercircle.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = 1/(t-a**3)
            sage: H=Hypercircle([u])
            sage: H.standard_parametrization()
            [t + 2*a, -2, 0]
        """
        return self.__standar_parametrization

    def compute_associated_unit(self, t0, verbose = False):
        """
        Compute an associated unit of the hypercircle from t0 where t0 is either
        a parameter that gives a rational point or a list or coordinates of a
        rational point.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u= (t+a)/(t-a)
            sage: H1 = Hypercircle([u])
            sage: H2 = Hypercircle([u])
            sage: H1.degree()
            1
            sage: H1(a)
            [0, 1, 0]
            sage: H1.compute_associated_unit(a)
            a*t
            sage: H2.compute_associated_unit([0, 1, 0])
            a*t

        A non linear, non primitive case::

            sage: N.<a> = NumberField(x^4-2)
            sage: K.<t> = N[]

            False
        """
        if self.is_line():
            #we are in the line case
            i = 0
            while self[i].derivative().is_zero():
                i = i+1
            U = inverse_unit(self[i])
            U = simplify_unit(U)
            self.set_unit(U)
            return U
        if t0 in self.K_alpha():
            U = is_hypercircle(self, t0, verbose)
            if U == 'Not hypercircle':
                raise ValueError(U)
            U = simplify_unit(U)
            self.set_unit(U)
            return U
        point = map(lambda x: (x[0]-x[1]).numerator(), zip( self, t0))
        parameter = - gcd(point)[0]
        self.compute_associated_unit(parameter, verbose)
        return self.unit()

    def compute_small_place(self, beta_name = 'beta', gamma_name ='gamma', verbose = False, discriminant_bound = 10^6):
        """
        Compute a place of degree 1 or 2 of the hypercircle.

        Note that, since the method uses LLL to basis reduction, it only works
        for absolute number fields. In particular, the hypercircle must be
        defined over QQ.

        The method tries to help with the hell of number fields. If we start with a
        number field ``QQ[alpha]``. It will compute a field ``QQ[beta]`` such that
        the hypercircle has points in ``QQ[beta]``. These structures are
        incompatible, so it also computes a new field ``QQ[gamma] = QQ[alpha,beta]``
        as well as relative representations ``QQ[alpha][beta]``, ``QQ[beta][alpha]``
        and isomorphisms with ``QQ[gamma]``

        NOTE: With improvements in coercion, there may be some morphisms that
        are not needed.

        INPUT:

        - ``Phi``: a list of rational fractions in QQ[alpha] that are the
          standard parametrization of an hypercircle.
        - ``beta_name``: variable for the new quadratic element
        - ``gamma_name``: variable for a primitive of QQ(alpha, beta)
        - ``discriminant_bound``: parameter passed to ``squarefree_part``,
          default is -1 and will perform a full factorization of the
          discriminant.

        OUPUT:

        If the place is of degree 1, a dictionary with the following keys:

        - ``degree_place``: 1
        - ``parameter_to_QQ``: a parameter that gives a rational point in the
          hypercircle.
        - ``rational_point_witness``: the rational point in the hypercircle
          obtained.
        - ``W_D``: A basis of the space of quadrics W_D

        If the place is of degree 2, a dictionary with the following keys:

        - ``K_alpha_beta``: The field ``QQ[alpha][beta]``
        - ``K_alpha_beta_to_NewK``: isormporphism from ``QQ[alpha][beta]`` to
          ``QQ[gamma]``
        - ``K_alpha_to_NewK``: morphism from ``QQ[alpha]`` to ``QQ[gamma]``
        - ``K_beta``: ``QQ[beta]``
        - ``K_beta_alpha``: The field ``QQ[beta][alpha]``
        - ``K_beta_alpha_to_NewK``: isomorphism from ``QQ[beta][alpha]`` to
          ``QQ[gamma]``
        - ``K_beta_to_NewK``: morphism from ``QQ[beta]`` to ``QQ[gamma]``
        - ``NewK``: ``the field QQ[alpha, beta]=QQ[gamma]``
        - ``NewK_to_K_alpha_beta``: isomorphism from ``QQ[gamma]`` to
          ``QQ[alpha][beta]``
        - ``NewK_to_K_beta_alpha``: isomorphism from ``QQ[gamma]`` to
          ``QQ[beta][alpha]``
        - ``beta``: quadratic element
        - ``degree_place``: 2
        - ``gamma``: primitive element of ``QQ[alpha][beta]``
        - ``parameter_to_beta_in_K_beta_alpha``: element in ``QQ[beta][alpha]``
          that provides a point over ``QQ[beta]``
        - ``parameter_to_beta_in_NewK``: the same elemnt but in ``QQ[gamma]``
        - ``point_beta_in_K_beta_alpha``: a place of degree 1 or 2 in as a point
          in ``QQ[beta]``
        - ``point_beta_in_NewK``: the same point but in ``QQ[gamma]``
        - ``witness_in_K_beta_alpha``: The standar parametrization of the
          hypercircle with coefficients in ``QQ[beta][alpha]``.
        - ``witness_in_NewK``: The standar parametrization of the hypercircle
          with coefficients in ``QQ[gamma]``.
        - ``W_D``: A basis of the space of quadrics W_D

        EXAMPLES:

        This used to fail::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, random_linear_fraction
            sage: var('x')
            x
            sage: N.<alpha> = NumberField(x^3-2,'alpha')[x]
            sage: u = random_linear_fraction(N, reduced = True)
            sage: w = Hypercircle([u])
            sage: w.compute_small_place()
            sage: P = w._small_place_structure()
            sage: P['degree_place']
            1
            sage: [foo in QQ for foo in P['rational_point_witness']]
            [True, True, True]
            sage: [p(P['parameter_to_QQ']) for p in w] == P['rational_point_witness']
            True
            sage: p = P['parameter_to_QQ']
            sage: u = random_linear_fraction(N)
            sage: w = Hypercircle([u])
            sage: w.compute_small_place()
            sage: P = w._small_place_structure()
            sage: sorted(P.keys())
            ['K_alpha_beta', 'K_alpha_beta_to_NewK', 'K_alpha_to_NewK', 'K_beta',
            'K_beta_alpha', 'K_beta_alpha_to_NewK', 'K_beta_to_NewK', 'NewK',
            'NewK_to_K_alpha_beta', 'NewK_to_K_beta_alpha', 'W_D', 'beta',
            'degree_place', 'gamma', 'parameter_to_beta_in_K_beta_alpha',
            'parameter_to_beta_in_NewK', 'point_beta_in_K_beta_alpha',
            'point_beta_in_NewK', 'witness_in_K_beta_alpha', 'witness_in_NewK']
            sage: len(P['point_beta_in_K_beta_alpha'])
            3
            sage: P['beta'].minpoly().degree()
            2
            sage: Phi_ba = P['witness_in_K_beta_alpha']
            sage: Kba = P['K_beta_alpha']
            sage: parameter = P['parameter_to_beta_in_K_beta_alpha']
            sage: point_beta = P['point_beta_in_K_beta_alpha']
            sage: beta = P['beta']
            sage: x = Phi_ba[0].parent().gen()
            sage: W = P['witness_in_K_beta_alpha']
            sage: [foo(parameter) for foo in W] == point_beta
            True
            sage: str(alpha) in str(point_beta)
            False
            sage: str(beta) in str(point_beta)
            True

        Rational points can be found during the process::

            sage: var('x')
            x
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t> = N[]
            sage: u = (a*t+1)/t
            sage: H = Hypercircle([u])
            sage: H.compute_small_place()
            sage: P = H._small_place_structure()
            sage: P['degree_place']
            1
            sage: P['rational_point_witness']
            [0, 0, 0]

        A non-reduced case with a rational point found::

            sage: var('x')
            x
            sage: N.<a> = NumberField(x^3-2)
            sage: K.<t> = N[]
            sage: u = (a*t - a^2 + 1)/(t - a)
            sage: H = Hypercircle([u])
            sage: H(0)
            [70/433*a^2 - 145/433*a + 22/433, 13/433*a^2 + 4/433*a + 301/433,
            -78/433*a^2 - 24/433*a - 74/433]
            sage: H.compute_small_place()
            sage: P = H._small_place_structure()
            sage: P['degree_place']
            1
            sage: P['rational_point_witness']
            [0, 1, 0]

        TEST:

        This used to fail::

            sage: var('x')
            x
            sage: N.<a> = NumberField(x^4-5, 'a')
            sage: K.<x> = N[]
            sage: u = (a*x-(a**2+1))/((4-a**2)*x+(a**2+3))
            sage: S = Hypercircle([u])
            sage: S.compute_small_place()

        EXAMPLES::

            sage: var('x')
            x
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = ((a-1)*t+a+3)/(a**2*t-a)
            sage: H = Hypercircle([u])
            sage: H.compute_small_place()
            sage: H.small_place_degree()
            2
            sage: H.small_place_coordinates()
            [13/8*beta - 121/8, -5/8*beta + 41/8, 1/2*beta - 7/2]
            sage: H.small_place_beta_minpoly()
            x^2 - 73
            sage: t0 = H.small_place_parameter(); t0
            (1/2*beta - 7/2)*a^2 + (-5/8*beta + 41/8)*a + 13/8*beta - 121/8
            sage: H(t0)
            [13/8*beta - 121/8, -5/8*beta + 41/8, 1/2*beta - 7/2]
            sage: v = random_linear_fraction(K, reduced='true')
            sage: H1 = Hypercircle([v,v])
            sage: H1.compute_small_place(beta_name = 'jj', gamma_name = 'gg')
            sage: H1.small_place_beta()
            1
        """
        try:
            self.__place_structure
            return
        except AttributeError:
            pass

        from sage.matrix.constructor import matrix
        from sage.rings.number_field.number_field import QuadraticField

        #Compute a canonical divisor
        if verbose: tt = time()

        i = 0
        dx = self[0].derivative().numerator()

        while dx == 0:
                i += 1
                dx = self[i].derivative().numerator().monic()

        if dx == 0:
            raise ValueError('unknown error')

        if dx.degree() == 0:
            #we are dealing with a line
            if verbose: print('rational point found!')

            u = inverse_unit(self[i])
            i = 0
            while u.denominator()(i) == 0:
                i += 1

            f = u(i)
            output = dict()
            output['degree_place'] = ZZ.one()
            output['parameter_to_QQ'] = f
            output['rational_point_witness'] = map(QQ, self(f))
            #cache the result
            self.__place_structure = output
            return None

            dx = dx.monic()

        d = self.ambient_dimension()
        Kalpha = dx.base_ring()
        alpha = Kalpha.gen()
        K = Kalpha.base_ring()
        tstring = str(self[0].parent().gen())
        KalphaWt = PolynomialRing(Kalpha, [tstring] + sum([ [tstring + 'W' + str(i) + '_' + str(j) for j in range(i,d+1)] for i in range(d+1)], []))
        W = KalphaWt.gens()[1:] # in KalphaWt
        t = KalphaWt.gens()[0]

        if verbose: print("pre: " + str(time()-tt))
        if verbose: tt = time()

        #compute the cuadrics passing through the divisor.

        Phiproj, Den = parametrization_to_common_denominator(self)
        Phiproj.append(Den)
        if verbose: print("common denominator: " + str(time()-tt))
        if verbose: tt = time()

        PhiprojWt = map(KalphaWt, Phiproj)
        if verbose: print("change ring: " + str(time()-tt))
        if verbose: tt = time()

        Equa = [[ KalphaWt(tstring+'W'+str(i)+'_'+str(j))*PhiprojWt[j]*PhiprojWt[i]\
           for j in range(i,d+1)] for i in range(d+1)]
        if verbose: print("write equations: " + str(time()-tt))
        if verbose: tt = time()


        Equa = sum(Equa, [])
        Equa = sum(Equa)
        if verbose: print("add equations: " + str(time()-tt))
        if verbose: tt = time()


        # In equa we have the equation of a quadrics passing through a generic point
        # of the hypercircle. We reduce modulo the divisor

        total_equations = []

        Idx = dx * KalphaWt
        equation = Idx.reduce(Equa)
        if verbose: print("reduce equations: " + str(time()-tt))
        if verbose: tt = time()

        equation = map(alpha_components, [equation.coefficient({t:i}) for i in \
               range(equation.degree(t)+1)])
        total_equations += sum([p.list() for p in equation],[])
        if verbose: print("extract components: " + str(time()-tt))
        if verbose: tt = time()

        if Set([p.degree() for p in total_equations if p != 0]) != Set([1]):
            raise ValueError("This should never happen, please report")

        if verbose: print("compute system: " + str(time()-tt))
        if verbose: tt = time()

        #Compute a basis of all the quadrics
        QQWt = K[KalphaWt.gens()]
        W = QQWt.gens()[1:]
        Q = matrix(K, len(total_equations), len(W), lambda x, y:\
               total_equations[x].monomial_coefficient(W[y]) )

        if verbose:
            print(W)
            print("compute matrix: " + str(time()-tt))
        if verbose: tt = time()

        #reduce the basis to obtain a small cuadric.
        L = Q.right_kernel().basis_matrix()
        if verbose:
            print('base of quadrics:')
            print(L)

        if K == QQ:
            L, _ = L._clear_denom()
            L = L.saturation().LLL()
        else:
            raise NotImplementedError("Tower of Fields Not Implemented")

        cuadric_vector = vector(sum([[ Phiproj[j]*Phiproj[i] for j in range(i,d+1)]\
                     for i in range(d+1)],[]))

        if verbose:
            print("LLL: " + str(time()-tt))
            print(L)
            print("rows: " +str(L.nrows()))
            print("cols: " +str(L.ncols()))
        if verbose: tt = time()

        # Tipically, the first cuadrics of L contain the whole hypercircle,
        # so we choose the first one that does not contain the hypercircle.

        i = 0
        while L[i] * cuadric_vector == 0:
            i +=1

        if verbose:
            print("first not zero: " +str(i))

        place2 = (L[i] * cuadric_vector).quo_rem(dx)

        if place2[1] != 0:
            raise ValueError("This should never happen, please report")

        place2 = place2[0]

        if verbose: print('small cuadric: ' + str(time()-tt))
        if verbose: tt = time()

        # compute point of degree at most 2
        coorpoint = range(d)
        place2W = KalphaWt(place2)
        for i in range(d):
            Idx = KalphaWt(self[i].numerator()) - W[0]*KalphaWt(self[i].denominator())
            p = Idx % place2
            p = Idx.resultant(place2W, t)
            coorpoint[i] = p / p.coefficients()[0]

        if max(p.degree() for p in coorpoint) > 2:
            raise ValueError("This should never happen, please report")

        if verbose: print('polynomial deg2: ' + str(time()-tt))
        if verbose: tt = time()

        #Compute a quadratic defining field.
        for i in range(d):
            coorpoint[i] = QQ[t]([coorpoint[i].coefficient({W[0]:j}) for j in range(3)])
            coorpoint[i] = coorpoint[i].numerator()
            coorpoint[i] = (coorpoint[i]/coorpoint[i].content()).change_ring(ZZ)

        if verbose: print('nice polynomial: ' + str(time()-tt))
        if verbose: tt = time()

        discv = [p.discriminant() for p in coorpoint]
        # TODO: eliminate discv in the future

        #the gcd is faster than factorization :)
        #Another alternative where to take just one coordinate of the point to
        #construct the field, but generally the discriminant is ridiculously large.
        #This approach with the gcd of all the discriminants on each coordinate
        #is better.
        #Probabilistically one should not need so much elements.

        #quitar los cuadrados perfectos
        disc = gcd(filter(lambda x: x!=0, discv))
        if discv[0] < 0:
            disc = -disc

        #If every discriminant is zero, gcd will return 0
        if disc == 0:
            disc = ZZ.one()

        if verbose: print('discriminant: ' + str(time()-tt))
        if verbose: print('old disc: ', p.discriminant())
        if verbose: print('disc', disc)

        #eliminate unused square factors that will make further operations too hard.

        disc = disc.squarefree_part(discriminant_bound)

        if verbose: print('disc', disc)

        if False in [((p / disc)).is_square() for p in discv]:
            raise ValueError("unknown error, please report")

        if verbose: print('partial sqfree: ' + str(time()-tt))
        if verbose: tt = time()

        if verbose: print('complete sqfree: ' + str(time()-tt))

        #Construct new field with alpha and beta and morphisms, this is a hell.

        if disc.is_square():
            #we have found a rational point
            if verbose: print('rational point found!')
            place2 = place2.factor()[-1][0]
            f = - place2[0]/place2[1]
            output = dict()
            output['degree_place'] = ZZ.one()
            output['parameter_to_QQ'] = f
            output['rational_point_witness'] = map(QQ, self(f))
            output['W_D'] = L, cuadric_vector
            #Cache the result
            self.__place_structure = output
            return None

        Kbeta = QuadraticField(disc, beta_name)
        beta = Kbeta.gen()
        pol_beta = Kbeta.polynomial()
        pol_beta = Kalpha['x'](pol_beta).factor()[0][0]
        K_alpha_beta = Kalpha.extension(pol_beta, beta_name)
        NewK = K_alpha_beta.absolute_field(gamma_name)
        NewK_to_K_alpha_beta, K_alpha_beta_to_NewK = NewK.structure()
        K_alpha_beta.register_coercion(NewK_to_K_alpha_beta)
        NewK.register_coercion(K_alpha_beta_to_NewK)
        alpha_in_NewK = K_alpha_beta_to_NewK(alpha)
        beta_in_NewK = K_alpha_beta_to_NewK(K_alpha_beta.gen())
        var_string = str(alpha) + beta_name +gamma_name+'0'
        fake_NewK = NewK.relativize(beta_in_NewK, var_string)
        pol_alpha_over_beta = fake_NewK.structure()[1](alpha_in_NewK).minpoly()
        pol_alpha_over_beta = Kbeta['x'](str(pol_alpha_over_beta).replace(\
                                                     var_string+'1', beta_name))
        K_beta_alpha = Kbeta.extension(pol_alpha_over_beta, str(alpha))
        K_beta_alpha.register_coercion( Kalpha.hom([K_beta_alpha.gen()]))
        if K_beta_alpha.absolute_degree() == Kalpha.degree():
            Kalpha.register_coercion(K_beta_alpha.hom([Kalpha.gen()]))
        gamma_in_alpha_beta = NewK_to_K_alpha_beta(gamma_name)

        #This is ugly!!
        NewK_to_K_beta_alpha = NewK.hom([K_beta_alpha(str(gamma_in_alpha_beta))])
        K_beta_to_NewK = Kbeta.hom([beta_in_NewK])
        K_beta_alpha_to_NewK = K_beta_alpha.Hom(NewK)(alpha_in_NewK, base_hom =\
                               K_beta_to_NewK)
        K_alpha_to_NewK = Kalpha.hom([alpha_in_NewK])
        #ugly coercions
        K_beta_alpha.register_coercion(NewK_to_K_beta_alpha)
        NewK.register_coercion(K_beta_to_NewK)
        NewK.register_coercion(K_beta_alpha_to_NewK)
        NewK.register_coercion(K_alpha_to_NewK)

        place2 = conjugate_pol(place2, K_alpha_to_NewK, NewK[t])

        if verbose: print('beta and morphisms: ' + str(time()-tt))
        if verbose: tt = time()

        #Take only one parameter
        if place2.is_squarefree():
            fv = [foo._pari_('a') for foo in place2]
            fp=pari(fv).Polrev()
            place2c = place2._factor_pari_helper(fp.factor())
            f = place2c[0][0]
            #print('tic')
        else:
            f = gcd(place2, place2.derivative()).monic()
            #print('tac')

        if f.degree() != 1:
            raise ValueError("something is wrong somewhere")

        if verbose: print('looking for squarefree: ' + str(time()-tt))
        if verbose: tt = time()

        f = -f[0]/f[1] #Should be f[1] =1

        #pass to the familiar representation.
        f_beta = NewK_to_K_beta_alpha(f)

        if verbose: print('factorization and parameter: ' +str(time()-tt))
        if verbose: tt  = time()

        #compute the point in QQ[alpha][beta] and friends.

        Num, Den = parametrization_to_common_denominator(self)

        if verbose: print('common denominator: '+ str(time()-tt))
        if verbose: tt = time()

        Den_NewK = conjugate_pol(Den, K_alpha_to_NewK, NewK[t])
        Num_NewK = map(lambda x: conjugate_pol(x, K_alpha_to_NewK, NewK[t]), Num)

        Den_ba = conjugate_pol(Den_NewK, NewK_to_K_beta_alpha, K_beta_alpha[t])
        Num_ba = map(lambda x: conjugate_pol(x, NewK_to_K_beta_alpha,\
                K_beta_alpha[t]), Num_NewK)

        if verbose: print('pass the parametrization to new context: '\
                + str(time()-tt))
        if verbose: tt = time()

        point = [x(f) for x in Num_NewK]
        denf = my_inverse_big_absnfield(Den_NewK(f))
        point = [x * denf for x in point]
        point_beta = map(NewK_to_K_beta_alpha, point)

        if verbose: print('compute point: ' + str(time()-tt))

        #SAVE all the work done

        output = dict()
        output['parameter_to_beta_in_NewK'] = f
        output['point_beta_in_NewK'] = point
        output['parameter_to_beta_in_K_beta_alpha'] = f_beta
        output['point_beta_in_K_beta_alpha'] = point_beta
        output['K_alpha_to_NewK'] = K_alpha_to_NewK
        output['K_beta'] = Kbeta
        output['K_beta_to_NewK'] = K_beta_to_NewK
        output['K_alpha_beta'] = K_alpha_beta
        output['K_beta_alpha'] = K_beta_alpha
        output['K_alpha_beta_to_NewK'] = K_alpha_beta_to_NewK
        output['K_beta_alpha_to_NewK'] = K_beta_alpha_to_NewK
        output['NewK_to_K_alpha_beta'] = NewK_to_K_alpha_beta
        output['NewK_to_K_beta_alpha'] = NewK_to_K_beta_alpha
        output['witness_in_NewK'] = [p / Den_NewK for p in Num_NewK]
        output['witness_in_K_beta_alpha'] = [p / Den_ba for p in Num_ba]
        output['NewK'] = NewK
        output['beta'] = Kbeta.gen()
        output['gamma'] = NewK.gen()
        output['degree_place'] = ZZ(2)
        output['W_D'] = L, cuadric_vector

        #Cache the result
        self.__place_structure = output
        return None

    def _small_place_structure(self):
        """
        Returns the dict computed by compute_small_place.

        TEST:

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<x> = NumberField(x^3-2,'a')[x]
            sage: a = N.base_ring().gen()
            sage: u = ((34*a^2 + 44*a + 19)*x + 76*a^2 + 2*a + 27)/x
            sage: w = Hypercircle([u])
            sage: w.compute_small_place()
            sage: P = w._small_place_structure();
            sage: keys = P.keys()
            sage: keys.sort()
            sage: keys
            ['W_D', 'degree_place', 'parameter_to_QQ', 'rational_point_witness']
        """
        try:
            return self.__place_structure
        except(AttributeError):
            self.compute_small_place()
            return self.__place_structure

    def small_place_degree(self):
        """
        Return the degree of a small place computed. The degree is garanteed to
        be 1 or 2.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = ((a-1)*t+a+3)/(a**2*t-a)
            sage: H = Hypercircle([u])
            sage: H.compute_small_place()
            sage: H.small_place_degree()
            2
            sage: v = [((59*a^2 + 21*a + 84)*t + 47*a^2 + 54*a + 54)/t]
            sage: H1 = Hypercircle(v)
            sage: H1.compute_small_place()
            sage: H1.small_place_degree()
            1
        """
        try:
            return self.__place_structure['degree_place']
        except AttributeError:
            self.compute_small_place()
            return self.__place_structure['degree_place']

    def small_place_parameter(self):
        """
        Return a parameter in ``QQ(beta, alpha)`` such that the image, by the
        parametrization, is in ``QQ(beta)``

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = ((a-1)*t+a+3)/(a**2*t-a)
            sage: H = Hypercircle([u])
            sage: t0=H.small_place_parameter(); t0
            (1/2*beta - 7/2)*a^2 + (-5/8*beta + 41/8)*a + 13/8*beta - 121/8
            sage: H(t0)
            [13/8*beta - 121/8, -5/8*beta + 41/8, 1/2*beta - 7/2]
            sage: v = [((59*a^2 + 21*a + 84)*t + 47*a^2 + 54*a + 54)/t]
            sage: H1 = Hypercircle(v)
            sage: t1=H1.small_place_parameter(); t1
            2255/26446*a^2 + 580/13223*a + 1735/26446
            sage: H1(t1)
            [1735/26446, 580/13223, 2255/26446]
        """

        if self.small_place_degree() == 1:
            return self.__place_structure['parameter_to_QQ']
        else:
            return self.__place_structure['parameter_to_beta_in_K_beta_alpha']

    def small_place_coordinates(self):
        """
        Return a list representing the coordinates of a point in an extension of
        degree at most 2 over ``QQ``

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = ((a-1)*t+a+3)/(a**2*t-a)
            sage: H = Hypercircle([u])
            sage: t0=H.small_place_parameter(); t0
            (1/2*beta - 7/2)*a^2 + (-5/8*beta + 41/8)*a + 13/8*beta - 121/8
            sage: H(t0)
            [13/8*beta - 121/8, -5/8*beta + 41/8, 1/2*beta - 7/2]
            sage: H.small_place_coordinates()
            [13/8*beta - 121/8, -5/8*beta + 41/8, 1/2*beta - 7/2]
            sage: v = [((59*a^2 + 21*a + 84)*t + 47*a^2 + 54*a + 54)/t]
            sage: H1 = Hypercircle(v)
            sage: t1=H1.small_place_parameter(); t1
            2255/26446*a^2 + 580/13223*a + 1735/26446
            sage: H1(t1)
            [1735/26446, 580/13223, 2255/26446]
            sage: H1.small_place_coordinates()
            [1735/26446, 580/13223, 2255/26446]
        """

        if self.small_place_degree() == 1:
            return self.__place_structure['rational_point_witness']
        else:
            return self.__place_structure['point_beta_in_K_beta_alpha']

    def small_place_beta(self):
        """
        Return the primitive element of ``QQ[beta]`` used to define this field.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = ((a-1)*t+a+3)/(a**2*t-a)
            sage: H = Hypercircle([u])
            sage: H.small_place_beta()
            beta
            sage: HH = Hypercircle([u])
            sage: HH.compute_small_place(beta_name = 'jj')
            sage: HH.small_place_beta()
            jj
            sage: v = [((59*a^2 + 21*a + 84)*t + 47*a^2 + 54*a + 54)/t]
            sage: H1 = Hypercircle(v)
            sage: H1.small_place_beta()
            1
        """
        if self.small_place_degree() == 1:
            return self.K().one()
        else:
            return self.__place_structure['beta']

    def small_place_beta_minpoly(self):
        """
        Retuns the minimal polynomia of ``beta`` that is the defining polynomial
        of ``QQ[beta]``.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = ((a-1)*t+a+3)/(a**2*t-a)
            sage: H = Hypercircle([u])
            sage: H.small_place_beta_minpoly()
            x^2 - 73
            sage: v = [((59*a^2 + 21*a + 84)*t + 47*a^2 + 54*a + 54)/t]
            sage: H1 = Hypercircle(v)
            sage: H1.small_place_beta_minpoly()
            x - 1
        """
        return self.small_place_beta().minpoly('x')

    def small_place_in_subfield(self):
        """
        Returns true is self.small_place_beta() defines a subfield of
        ``K[alpha]``

        Examples::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, random_linear_fraction, inverse_unit
            sage: N.<alpha>=NumberField(x^6-2*x^3-17,'alpha')
            sage: K.<t>=N[]
            sage: v = (-alpha^3*t + 1/3*alpha^3 - 1/3)/(-alpha*t + 1)
            sage: H = Hypercircle([v])
            sage: H.small_place_in_subfield()
            True
            sage: v = ((alpha+1)*t-alpha**4)/(t+alpha**2-alpha)
            sage: H = Hypercircle([v])
            sage: H.small_place_in_subfield()
            False
            sage: v = random_linear_fraction(K, reduced=True)
            sage: H = Hypercircle([ inverse_unit(v)])
            sage: H.small_place_in_subfield()
            True
        """
        if self.small_place_degree() == 1:
            return True
        beta = self.small_place_beta()
        return not self.K_alpha()['t'](beta.minpoly()).is_irreducible()

    def __call__(self, parameter):
        """
        Return the point corresponding to the parameter, including infinity.

        Note: For the case of infinity, returns the projective coordinates.
        In the rest of cases, the affine coordinates.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = ((a-1)*t+a+3)/(a**2*t-a)
            sage: H = Hypercircle([u])
            sage: H(0)
            [-19587/144853*a^2 - 19980/144853*a - 92235/144853, -9825/144853*a^2
            + 42093/144853*a - 25899/144853, -1797/144853*a^2 - 8622/144853*a -
            26100/144853]

        It also works if the parameter is in QQ[beta]

            sage: H(H.small_place_beta())
            [(1431634160101598779/63256860060562508708*beta +
            2558572756437300143/63256860060562508708)*a^2 +
            (-4937517254370458595/63256860060562508708*beta -
            8980475997848831195/63256860060562508708)*a +
            23728568183455667483/63256860060562508708*beta -
            2540328980120517785/63256860060562508708,
            (-988889281865605658/15814215015140627177*beta -
            211295714823944252/15814215015140627177)*a^2 +
            (-246029257868650955/31628430030281254354*beta -
            6398257988427999713/31628430030281254354)*a -
            2463832800094049575/31628430030281254354*beta -
            2725977802324770357/31628430030281254354,
            (1189226779256835749/63256860060562508708*beta -
            2683260002090032959/63256860060562508708)*a^2 +
            (-3950101247958945613/63256860060562508708*beta +
            337117063271673451/63256860060562508708)*a +
            1438877914149374629/63256860060562508708*beta +
            4871423216238633365/63256860060562508708]

        We can also compute the point at infinity::

            sage: H(oo)
            [a^2 + 2, a, 1, 0]
            sage: var('x')
            x
            sage: N1 = NumberField(x^6+2,'a')
            sage: N1.<a1> = NumberField(x^6+2,'a')
            sage: K1.<x1> = N1[]
            sage: u1 = 1/(x1+a1**2)
            sage: from sage.geometry.hypercircles.hypercircle import inverse_unit
            sage: H1 = Hypercircle([inverse_unit(u1)])
            sage: H1(oo)
            [a1^4, 0, a1^2, 0, 1, 0, 0]

        """
        if parameter == oo:
            Num, Den = parametrization_to_common_denominator(self(~self.t()))
            Num.append(Den)
            i = -2
            while Num[i](0) == 0:
                i -= 1
            coe = Num[i](0)
            return [f(0)/coe for f in Num]
        if parameter in self.K_alpha():
            return [p(parameter) for p in self.parametrization()]
        elif hasattr(self, '_Hypercircle__place_structure'):
            if self.small_place_degree() == 1:
                return [p(parameter) for p in self.parametrization()]
            elif parameter in self.__place_structure['K_beta_alpha']:
                par = self.__place_structure['witness_in_K_beta_alpha']
                return [p(parameter) for p in par]
            elif parameter in self.__place_structure['K_beta']:
                par = self.__place_structure['witness_in_K_beta_alpha']
                point = [p(parameter) for p in par]
                point = map(drop_beta, point)
                return point
            elif parameter in self.__place_structure['NewK']:
                par = self.__place_structure['witness_in_NewK']
                return [p(parameter) for p in par]
        return [p(parameter) for p in self.parametrization()]

    def small_place_unit(self, verbose = False):
        """
        Return a unit that reparametrizes the hypercircle over ``QQ[beta]``.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, simsim
            sage: N.<a> = NumberField(x^3+2*x+5)
            sage: K.<t>=N[]
            sage: u = ((a-1)*t+a+3)/(a**2*t-a)
            sage: H = Hypercircle([u])
            sage: ubeta = H.small_place_unit(); ubeta
            (((1/2*beta - 7/2)*a^2 + (-5/8*beta + 41/8)*a + 13/8*beta - 121/8)*t
            + (255/2*beta - 1259)*a^2 + (384*beta + 12803/2)*a + 16945/8*beta +
            74901/8)/(t + (4461/8*beta + 44765/8)*a^2 + (17635/8*beta +
            141935/8)*a + 1487/2*beta + 9812)
            sage: map(simsim, H(ubeta))
            [((13/8*beta - 121/8)*t^3 + (183391/16*beta + 1134121/16)*t^2 +
            (350112143/16*beta + 2855716015/16)*t + 434921034785763/128*beta +
            3715851728706871/128)/(t^3 + 14107/2*t^2 + (15409306305/32*beta +
            131798889317/32)*t - 225946444725621/32*beta - 1930463829601393/32),
            ((-5/8*beta + 41/8)*t^3 + (32285/4*beta + 160159/2)*t^2 +
            (-6579417895/32*beta - 56095033211/32)*t - 93993070662403/128*beta -
            803026632222679/128)/(t^3 + 14107/2*t^2 + (15409306305/32*beta +
            131798889317/32)*t - 225946444725621/32*beta - 1930463829601393/32),
            ((1/2*beta - 7/2)*t^3 + (34803/16*beta + 174853/16)*t^2 +
            (-1326724227/32*beta - 11418602135/32)*t + 200770410597589/128*beta
            + 1715344616464353/128)/(t^3 + 14107/2*t^2 + (15409306305/32*beta +
            131798889317/32)*t - 225946444725621/32*beta - 1930463829601393/32)]
            sage: v = [((59*a^2 + 21*a + 84)*t + 47*a^2 + 54*a + 54)/t]
            sage: H1 = Hypercircle(v)
            sage: vbeta = simsim(H1.small_place_unit()); vbeta
            ((2255/26446*a^2 + 580/13223*a + 1735/26446)*t + 79827/26446*a^2 +
            20532/13223*a + 61419/26446)/(t - 45347/13223*a^2 + 17819/26446*a -
            3841/26446)
            sage: par_base_field = map(simsim, H1(vbeta)); par_base_field
            [(1735/26446*t^3 + 144843/52892*t^2 + 974961/26446*t +
            41451453/52892)/(t^3 + 50179/3778*t^2 + 495569/52892*t -
            28845451/26446), (580/13223*t^3 + 23773/52892*t^2 - 574608/13223*t -
            8236341/52892)/(t^3 + 50179/3778*t^2 + 495569/52892*t -
            28845451/26446), (2255/26446*t^3 + 99807/26446*t^2 + 1303349/52892*t
            - 3937719/52892)/(t^3 + 50179/3778*t^2 + 495569/52892*t -
            28845451/26446)]
            sage: sum([par_base_field[i] * a**i for i in range(3)]) == vbeta
            True
            sage: simsim(v[0](vbeta))
            (2867/5*t + 13706/5)/(t + 177/5)
            sage: H2 = Hypercircle([t])
            sage: w = H2.small_place_unit(); w
            t

        The following example used to fail, It is a primitive hypercircle such
        that we find a point on a subfield of degree 2. Hence, it needs
        relativize::

            sage: var('x')
            x
            sage: N.<alpha>=NumberField(x^6-2*x^3-17,'alpha')
            sage: K.<t>=N[]
            sage: v = (-alpha^3*t + 1/3*alpha^3 - 1/3)/(-alpha*t + 1)
            sage: H = Hypercircle([v])
            sage: H.small_place_unit()
            ((-36*beta + 114)*alpha^2 + (-51*beta + 306)*alpha + 867)/(t +
            (-51*beta + 306)*alpha^2 + 867*alpha)
            sage: parbeta = map(simsim,H(H.small_place_unit()))
            sage: S = str(parbeta)
            sage: 'beta' in S
            True
            sage: 'alpha' in S
            False
            sage: parbeta[0]
            ((136/699*beta + 323/699)*t^6 + (-169932/233*beta - 100572/233)*t^5
            + (-202469643/233*beta + 76760712/233)*t^4 + (224927147781/233*beta
            + 680118435243/233)*t^3 + (-310588970748192/233*beta -
            321170435162694/233)*t^2 + (81307917817026876/233*beta +
            107073950888577564/233)*t - 5484690082401920928/233*beta -
            14990067970691614488/233)/(t^6 + (106488/233*beta + 359856/233)*t^5
            + (-1583088246/233*beta - 1056775896/233)*t^4 +
            (677541778002/233*beta + 1127117771766/233)*t^3 +
            (3177467265953376/233*beta + 5570316058860162/233)*t^2 +
            (-6201603752918368986/233*beta - 9890189581198153140/233)*t +
            3701691290153002346406/233*beta + 5448920353023639800187/233)

        This used to fail::

            sage: N.<alpha> = NumberField(x^4 - 26*x^2 + 49, 'alpha')
            sage: K.<t>  = N[]
            sage: Phi = [((-5/7*alpha^3 + 165/7*alpha)*t^3 + (45*alpha^3 + 15*alpha^2 + 315*alpha + 135)*t^2 + (31266/7*alpha^3 + 3150*alpha^2 - 44358/7*alpha - 4410)*t + 110952*alpha^3 + 116454*alpha^2 - 219996*alpha - 231556)/(25*t^4 + (-5/7*alpha^3 + 300*alpha^2 + 865/7*alpha)*t^3 + (945*alpha^3 + 35265*alpha^2 + 315*alpha - 65955)*t^2 + (523382/7*alpha^3 + 1719810*alpha^2 - 970146/7*alpha - 3488310)*t + 1811964*alpha^3 + 31409338*alpha^2 - 3674832*alpha - 64192860), (50*t^3 + (-15/14*alpha^3 + 450*alpha^2 + 2595/14*alpha)*t^2 + (945*alpha^3 + 35265*alpha^2 + 315*alpha - 66255)*t + 261706/7*alpha^3 + 859005*alpha^2 - 487668/7*alpha - 1744155)/(25*t^4 + (-5/7*alpha^3 + 300*alpha^2 + 865/7*alpha)*t^3 + (945*alpha^3 + 35265*alpha^2 + 315*alpha - 65955)*t^2 + (523382/7*alpha^3 + 1719810*alpha^2 - 970146/7*alpha - 3488310)*t + 1811964*alpha^3 + 31409338*alpha^2 - 3674832*alpha - 64192860)]
            sage: H = Hypercircle(Phi)
            sage: H.degree() # It is not primitive
            2
            sage: H.small_place_beta_minpoly()
            x^2 + 2
            sage: H.small_place_unit()
            ((3/2870*alpha^3 - 3*alpha^2 - 2969/2870*alpha - 61/41*beta)*t +
            (45/328*beta - 57/2870)*alpha^3 + (15/328*beta + 99/82)*alpha^2 +
            (315/328*beta + 1518/1435)*alpha + 357/328*beta)/(t +
            15/2296*beta*alpha^3 - 495/2296*beta*alpha - 33/82)
            sage: map(simsim, H(H.small_place_unit()))
            [(-61/41*beta*t^2 + 111/82*beta*t - 9/164*beta)/(t^2 - 33/41*t +
            27/82), (-2969/2870*t^2 + 3036/1435*t - 10611/11480)/(t^2 - 33/41*t
            + 27/82), -3, (3/2870*t^2 - 57/1435*t + 207/11480)/(t^2 - 33/41*t +
            27/82)]
        """
        try:
            return self.__small_place_unit
        except AttributeError:
            if self.degree() == 1:
                i = 0
                par = self.parametrization()
                while par[i].derivative().is_zero():
                    i = i+1
                U = inverse_unit(par[i])
                U = simplify_unit(U)
                self.__small_place_unit = U
                return U
            elif self.small_place_degree() == 1:
                U = is_hypercircle(self,\
                    self.small_place_parameter(), verbose)
                U = simplify_unit(U)
                self.__small_place_unit = U
                return U
            elif not self.small_place_in_subfield():
                U = is_hypercircle(\
                             self.__place_structure['witness_in_K_beta_alpha'],\
                             self.small_place_parameter(), verbose)
                U = simplify_unit(U)
                self.__small_place_unit = U
                return U
            else:
                polbeta = self.K_alpha()['t'](self.small_place_beta().minpoly())
                beta = polbeta.roots()[0][0]
                H, phi, mat = self.relativize(beta)
                U = is_hypercircle(H, self.small_place_parameter(), verbose)
                U = simplify_unit(U)
                self.__small_place_unit = U
                return U

    def relativize(self, beta, name = 'beta'):
        """
        If beta is an algebraic integer of K_alpha, compute the hypercircle
        associated to K(beta) in K(alpha).

        INPUT:

        - ``beta``: and element of K_alpha

        OUTPUT:

        - ``(H, phi, mat)`` such that:
        - ``H``: is the hypercircle of self associated to the extension K(beta)
          in K(alpha)
        - ``phi``: isomorphism from K(alpha) to K(beta)(alpha)
        - ``mat`` a matrix such that if ``p`` is the coordinates of a point in
          self, ``mat*p`` is the corresponding point in ``H`` under the natural
          isomorphism.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N.<a> = NumberField(x^6 + 6*x^5 + 15*x^4 + 20*x^3 + 15*x^2 + 6*x - 1)
            sage: K.<t> = N['t']
            sage: u = (a*t+1)/(t-a)
            sage: H=Hypercircle([u])
            sage: H.degree()
            6
            sage: H.small_place_degree()
            2
            sage: beta = a^3 + 3*a^2 + 3*a
            sage: beta.minpoly()
            x^2 + 2*x - 1

        If the hypercircle is of degree 6 and beta is of degree 2, then the
        hypercircle associated to u with base field K[beta] must be of
        degree 3.::

            sage: H2, phi, mat = H.relativize(beta)
            sage: H2.degree()
            3
            sage: H2.ambient_dimension()
            3
            sage: phi
            Ring morphism:
            From: Number Field in a with defining polynomial x^6 + 6*x^5 +
            15*x^4 + 20*x^3 + 15*x^2 + 6*x - 1
            To:   Number Field in a with defining polynomial x^3 + 3*x^2 + 3*x -
            beta over its base field
            Defn: a |--> a
            sage: mat
            [           1            0            0         beta      -3*beta
            6*beta]
            [           0            1            0           -3     beta + 9
            -3*beta - 18]
            [           0            0            1           -3            6
            beta - 9]
            sage: N2 = phi.codomain(); N2
            Number Field in a with defining polynomial x^3 + 3*x^2 + 3*x - beta
            over its base field
            sage: N.is_isomorphic(N2)
            True

        Compute directly the hypercircle over the field N2::

            sage: uu = N2[t].fraction_field()(u); uu
            (a*t + 1)/(t - a)
            sage: H3 = Hypercircle([uu])
            sage: H2.parametrization() == H3.parametrization()
            True

        Check that the matrix mat is the isomorphism searched::

            sage: t0 = N.random_element()
            sage: mat * vector(H(t0)) == vector(H2(phi(t0)))
            True
        """
        beta = self.K_alpha()(beta)
        Kbeta = self.K()[beta]
        Kbeta = Kbeta.change_names(name)
        p = self.polmin()
        x = p.variable_name()
        p0 = Kbeta[x](p).factor()[0][0]
        Kbeta_alpha = Kbeta.extension(p0, str(self.alpha()))
        alphab = Kbeta_alpha.gen()
        phi = self.K_alpha().hom([alphab])
        par_in_Kbeta_alpha = map(lambda x: conjugate_pol(x, phi,\
                                 Kbeta_alpha[self.t()]), self.parametrization())
        Kbeta_alpha.register_coercion(phi)
        m = [alphab**i for i in range(self.ambient_dimension())]
        m = map(lambda x: x.vector(), m)
        m = matrix(Kbeta_alpha, m).transpose()
        return Hypercircle(par_in_Kbeta_alpha), phi, m

    def birational_conic(self, name = None):
        """
        Return the conic hypercircle associated to small_place_unit.

        We have to be quite carful since since the ground field is ``QQ[alpha]``
        although the standard parametrization is over ``QQ[beta]``.

        If the hypercircle is of degree 1 or the small place is of degree 1,
        then returns a line.

        If ``beta`` is not in ``QQ[alpha]`` then it computes the hypercircle
        from small_place_unit.

        If ``beta`` is in ``QQ[alpha]`` it projects using relativize and then
        computes the conic from small_place_unit in the projection.

        Warning::
            ``beta`` is ``QQ[alpha]`` not yet implemented.

        The result is the conic hypercircle for the extension ``QQ`` in
        ``Q[beta]``.

        EXAMPLES::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, inverse_unit
            sage: N.<a> = NumberField(x^5 + 15*x^4 + 20*x^3 + 15*x^2 + 6*x - 1)
            sage: K.<t> = N['t']
            sage: u = (a*t+1)/(t-2*a)
            sage: H1=Hypercircle([u])
            sage: H1.degree()
            5
            sage: H1.small_place_degree()
            2
            sage: conic = H1.birational_conic(); conic
            Hypercircle over Number Field in beta with defining polynomial
            x^2 - 2883
            sage: conic.parametrization()
            [(1/2*t^2 - 1776455701/1302*beta*t + 4529581007743677/2)/(t -
            1776455701/1302*beta - 28998415), (1/5766*beta*t^2 -
            28998415/2883*beta*t - 1509860335914559/1922*beta)/(t -
                1776455701/1302*beta - 28998415)]
            sage: conic.ideal('R')
            Ideal (R0^2 - 2883*R1^2 - 57996830*R0*R2 + 55070126731/7*R1*R2 -
            4529581007743677*R2^2) of Multivariate Polynomial Ring in R0, R1, R2
            over Rational Field

        Note that, since N is of odd degree, we can easily define an odd divisor
        in the conic.::

            sage: odd = inverse_unit(H1.small_place_unit())(0);odd
            (-1256591910/186889*beta + 644442070590/1308223)*a^4 +
            (-19357049580/186889*beta + 9863976192090/1308223)*a^3 +
            (-32933742355/186889*beta + 15916658306895/1308223)*a^2 +
            (-31764862315/186889*beta + 14651617450070/1308223)*a +
            15728077502199/11587118*beta + 78287276434345/2616446
            sage: oddpoint = conic(odd); oddpoint
            [644442070590/1308223*a^4 + 9863976192090/1308223*a^3 +
            15916658306895/1308223*a^2 + 14651617450070/1308223*a +
            78287276434345/2616446, -1256591910/186889*a^4 -
            19357049580/186889*a^3 - 32933742355/186889*a^2 -
            31764862315/186889*a + 15728077502199/11587118]
            sage: pol0 = oddpoint[0].absolute_minpoly()
            sage: pol0.degree()
            5
            sage: pol1 = oddpoint[1].absolute_minpoly()
            sage: pol1.degree()
            5
            sage: NumberField(pol0, 'g').is_isomorphic(NumberField(pol1, 'g'))
            True

        An example where we have to relativize the hypercircle before computing the conic::

            sage: var('x')
            x
            sage: N.<alpha>=NumberField(x^6-2*x^3-17,'alpha')
            sage: K.<t>=N[]
            sage: u = (-alpha^3*t + 1/3*alpha^3 - 1/3)/(-alpha*t + 1)
            sage: H = Hypercircle([u])
            sage: v = H.small_place_unit(); v
            ((-36*beta + 114)*alpha^2 + (-51*beta + 306)*alpha + 867)/(t +
            (-51*beta + 306)*alpha^2 + 867*alpha)
            sage: len(H.small_place_beta_minpoly().roots(H.K_alpha()))
            2

        beta is in K_alpha, so we cannot use v to compute the conic. Internally we
        use relativize, but this is transparent to the user, although probably
        slower::

            sage: C = H.birational_conic(); C
            Hypercircle over Number Field in beta with defining
            polynomial x^2 - 2
            sage: par = inverse_unit(u(v))(0); par
            867/2*beta + 2601
            sage: C(par)
            [2601, 867/2]

        Note that par is in QQ[beta][alpha]::

            sage: w = C.compute_associated_unit(par[0]); w
            ((306*beta - 102)*t - 153*beta - 1683)/(t - beta + 8)
            sage: u(v(v.parent(w)))
            t + 8

        Another example where beta is of degree one::

            sage: N = NumberField(x^3+x+4, 'a')
            sage: K = N['t']
            sage: a = N.gen()
            sage: t = K.gen()
            sage: u = (a*t+a)/(t-1)
            sage: H = Hypercircle([u])
            sage: H.degree()
            3
            sage: C = H.birational_conic(); C
            Hypercircle over Number Field in c with defining polynomial x
            sage: C.degree()
            1
            sage: C.ambient_dimension()
            1
        """

        try:
            return self.__birational_conic
        except AttributeError:
            pass

        if name is None:
            name = str(self.t())

        if self.is_line():
            u = self.compute_associated_unit(0)
            self.__birational_conic = Hypercircle([NumberField(QQ['x'].gen(),'c')[name].gen()])
            return self.__birational_conic

        self.compute_small_place()
        if self.small_place_degree() == 1:
            u = self.compute_associated_unit(self.small_place_parameter())
            self.__birational_conic = Hypercircle([NumberField(QQ['x'].gen(),'c')[name].gen()])
            return self.__birational_conic

        K_alpha_beta = self.__place_structure['K_alpha_beta']
        K_alpha_beta_t = K_alpha_beta[name]
        var = K_alpha_beta.gen()
        if self.small_place_degree() == 1:
            self.__birational_conic = Hypercircle([var])

        if self.small_place_in_subfield():
            minpol = self.small_place_beta_minpoly()
            roots = minpol.roots(self.K_alpha())
            beta = roots[0][0]
            Hb = self.relativize(beta)
            par = self.small_place_parameter()
            par = Hb[1](par)
            U = Hb[0].compute_associated_unit(par)
            phibeta = map(lambda x: drop_beta(simsim(x)), self(U))
            #We have a parametrization in QQ[beta] of the hypercircle
            C = Hypercircle(phibeta)
            self.__birational_conic = C
            return self.__birational_conic

        U = self.small_place_unit()
        U_ = K_alpha_beta_t.fraction_field()(U)
        V = unit_to_hc_sqrt(U_, name)
        K_beta_alpha_t = self.__place_structure['K_beta_alpha'][name].fraction_field()
        V = [drop_beta(K_beta_alpha_t(foo)) for foo in V]
        self.__birational_conic = Hypercircle(V)#Improve
        return self.__birational_conic

    def is_conic(self):
        """
        Check if the hypercircle is a conic.

        TEST::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle, random_linear_fraction, inverse_unit
            sage: N = QQ[I]
            sage: K = N['t']
            sage: u1 = random_linear_fraction(K)
            sage: H1 = Hypercircle([u1])
            sage: H1.is_conic()
            True
            sage: u2 = random_linear_fraction(K, reduced=True)
            sage: H2 = Hypercircle([inverse_unit(u2)])
            sage: H2.is_conic()
            False
        """
        return self.degree() == 2

    def compute_associated_unit_from_odd_divisor(self, divisor = 0, verbose = False):
        """
        Computes an associated unit from an odd divisor.

        The hypercircle must be a plane conic or a line.

        INPUT:

        - ``divisor``: The minimal polynomial of a parameter that defines a divisor of odd degree.

        - ``verbose``: A boolean, if true print verbose information about the time of computation.

        OUTPUT:

        - An associated unit of the hypercircle.

        TESTS::

            sage: from sage.geometry.hypercircles.hypercircle import *
            sage: N = NumberField(x^3+2*x+4, 'a')
            sage: K = N['t']
            sage: u = random_linear_fraction(K)
            sage: H = Hypercircle([u])
            sage: v = H.small_place_unit()
            sage: v1 = inverse_unit(v)
            sage: C = H.birational_conic()
            sage: divisor = v1(0).minpoly()
            sage: i = 1
            sage: while divisor.degree() != 3:
            ...    divisor = v1(i).minpoly()
            ...    i = i + 1
            sage: w = C.compute_associated_unit_from_odd_divisor(divisor)
            sage: u1 = v(v.parent(w))
            sage: drop_beta(simsim(u(u1))) in QQ['t'].fraction_field()
            True

        Another example in which the conic is a line because beta is in QQ::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: N = NumberField(x^3+x+4, 'a')
            sage: K = N['t']
            sage: a = N.gen()
            sage: t = K.gen()
            sage: u = (t+a)/(t-a)
            sage: H = Hypercircle([u])
            sage: C = H.birational_conic(); C
            Hypercircle over Number Field in c with defining polynomial x

        An explicit one::

            sage: from sage.geometry.hypercircles.hypercircle import Hypercircle
            sage: u = (2*a*t-a^2)/(t+a+2-a^2)
            sage: H = Hypercircle([u])
            sage: v = H.small_place_unit(); v
            (((1/36*beta - 5/36)*a^2 + (1/9*beta - 1/18)*a - 1/36*beta -
            31/36)*t + (3190/9*beta - 30586/9)*a^2 + (11381/9*beta + 22357/9)*a
            - 540*beta - 24964/3)/(t + (790/3*beta + 566/3)*a^2 + (164/3*beta -
            6812/3)*a + 1580/9*beta + 209356/9)
            sage: C = H.birational_conic()
            sage: par = inverse_unit(v)(0); par
            (-10442/81*beta + 99926/81)*a^2 + (29872/81*beta - 172624/81)*a -
            44836/81*beta - 579140/81
            sage: C(par)
            [99926/81*a^2 - 172624/81*a - 579140/81, -10442/81*a^2 + 29872/81*a
            - 44836/81]
            sage: w = C.compute_associated_unit_from_odd_divisor(par.minpoly())
            sage: w
            ((239552/99*beta + 657400/99)*t - 523552/99*beta - 504560/99)/(t -
            1/11*beta - 41/11)
            sage: u1 = simsim(v(v.parent(w))); u1
            ((41402330111/282972916566*a^2 + 251048485799/282972916566*a -
            200797966037/282972916566)*t - 47061795353/141486458283*a^2 -
            344736433073/141486458283*a + 263070188339/141486458283)/(t -
            1248255360/15720717587*a^2 + 566134272/15720717587*a -
            48682972618/15720717587)
            sage: u1 = simplify_unit(u1); u1
            (1/2*a*t - 2*a^2 - 8*a + 2)/(t + a^2 - 7)
            sage: H(u1(0))
            [-22/27, 25/27, 4/27]
            sage: simsim(u(u1))
            8/(t - 8)
        """

        try:
            return self.__unit
        except(AttributeError):
            pass

        #The unit is not computed

        if self.is_line():
            if verbose: print('Hypercircle is a line:')
            u = self.compute_associated_unit(0)
            return u

        if not self.is_conic() or self.ambient_dimension() != 2:
            raise ValueError("Only implemented for plane conics")

        m = divisor.degree()
        if m % 2 == 0:
            raise ValueError('the divisor given is even')

        if verbose: tt =time()
        r = (m+1) // 2
        Kalpha = self.K_alpha()
        tstring = str(self.t())
        KalphaWt = PolynomialRing(Kalpha, [tstring] + sum([ [tstring + 'W' + str(i) + '_' + str(j) for j in range(r+1-i)] for i in range(r+1)], []))
        W = KalphaWt.gens()[1:] # in KalphaWt
        t = KalphaWt.gens()[0]
        Kalphat = Kalpha[t]
        t0 = Kalphat.gens()[0]
        divisor = divisor(t0)
        if verbose:
            print('Computed algebraic context: ' +str(time()-tt))
            tt =time()

        Phiproj, Den = parametrization_to_common_denominator(self)
        Phiproj.append(Den)
        PhiprojWt = map(KalphaWt, Phiproj)
        Equa = [[ KalphaWt(tstring+'W'+str(i)+'_'+str(j))*PhiprojWt[0]**i*PhiprojWt[1]**j*Phiproj[2]**(r-i-j)\
           for j in range(r+1-i)] for i in range(r+1)]

        Equa = sum(Equa, [])
        Equa = sum(Equa)
        Equa_red = Equa.reduce([KalphaWt(divisor)])
        Equa = [Equa.coefficient({foo:1}) for foo in W]
        # It is a conic

        Equa0, Equa1 = alpha_components(Equa_red)
        if verbose:
            print('computed equations: ' + str(time()-tt))
            tt = time()

        p = []
        for i in range(r):
            p += [[Equa0.coefficient({t : i}).coefficient({foo:1}) for foo in W]]
            p += [[Equa1.coefficient({t : i}).coefficient({foo:1}) for foo in W]]

        M = matrix(p)
        M = M.change_ring(QQ)
        if verbose:
            print('computed matrix: ' + str(time()-tt))
            tt = time()

        N = M.right_kernel().basis_matrix()
        if verbose:
            print('computed kernel: ' + str(time()-tt))
            tt = time()

        #N is immutable
        N = copy(N)
        for i in range(N.nrows()):
            N.rescale_row(i, N.row(i).denominator())
            N.rescale_row(i, ~gcd(map(ZZ, N.row(i))))

        N = N.change_ring(ZZ)
        N = N.LLL()
        if verbose:
            print('computed LLL of kernel: ' + str(time()-tt))
            tt = time()


        R = N * vector(Equa)
        R = [Kalphat(R[i].coefficients()).reverse() for i in range(len(R))]
        if verbose:
            print('Computed space of curves: '+ str(time()-tt))
            tt = time()

        i = 0

        while R[i] == 0:
            i+=1

        parameter, remainder = R[i].quo_rem(divisor)

        if remainder != 0 or parameter.degree()!= 1:
            raise ValueError('unknown error, please report!')

        parameter = -parameter[0]/parameter[1]
        if verbose:
            print('computed parameter: ' + str(time()-tt))
            tt = time()

        self.compute_associated_unit(parameter)
        if verbose:
            print('computed associated unit: ' + str(time()-tt))

        return self.unit()
