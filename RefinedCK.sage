r"""
Sage code for the paper "Refined Chabauty-Kim calculations for the thrice-
punctured line over `\ZZ[1/6]`" [Lüd24].

This file contains functions for computing refined Chabauty-Kim loci in depth 2
and depth 4 for the thrice-punctured line `X` over the ring `\ZZ_S` of
`S`-integers, where `S = \{2,q\}` consists of two primes. The relevant functions
are ``CK_depth_2_locus`` and ``CK_depth_4_locus``, computing the loci
`X(\ZZ_p)_{\{2,q\},2}^{(1,0)}` and `X(\ZZ_p)_{\{2,q\},\mathrm{PL},4}^{(1,0)}`,
respectively. These are finite subsets of `X(\ZZ_p)` containing the set of
`S`-integral points whose mod `2` reduction is in `X \cup \{1\}` and whose
mod `q` reduction is in `X \cup \{0\}`. If this inclusion is satisfied, then
Kim's conjecture holds. This holds for all depth `4` loci which have been
computed but it does not typically hold in depth `2`. Currently, the explicit
coefficients appearing in the Coleman functions defining the depth 4 locus are
only known for `q = 3`, where they can be computed via the function
``Z_one_sixth_coeffs``.

EXAMPLES:

For `q = 3` and auxiliary prime `p = 7` the depth 2 locus contains 8 elements;
the depth 4 locus only 4. These are precisely the `S`-integral points
`{-3,-1,3,9}`, so Kim's conjecture for `S = \{2,3\}` holds in depth 4:

    sage: p = 7; q = 3; N = 6
    sage: coeffs = Z_one_sixth_coeffs(p,N)
    sage: CK_depth_2_locus(p,q,N,coeffs[0])
    [2 + 7 + O(7^5),
     2 + O(7^5),
     3 + 7 + 3*7^2 + 2*7^3 + 7^4 + O(7^5),
     3 + O(7^5),
     4 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + O(7^5),
     4 + 5*7 + 6*7^2 + 5*7^3 + 2*7^4 + O(7^5),
     6 + 6*7 + 6*7^2 + 6*7^3 + O(7^4),
     6 + 6*7 + 3*7^2 + 2*7^3 + O(7^4)]
    sage: CK_depth_4_locus(p,q,N,coeffs)
    [2 + 7 + O(7^5),
     3 + O(7^5),
     4 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + O(7^5),
     6 + 6*7 + 6*7^2 + 6*7^3 + O(7^4)]

REFERENCES:

 - [BJ08] Amnon Besser, Rob de Jeu, "Li(p) service? An algorithm for computing
   p-adic polylogarithms"

 - [Lüd24] Martin Lüdtke, "Refined Chabauty-Kim calculations for the thrice-
   punctured line over `\ZZ[1/6]`"


AUTHORS:

- Martin Lüdtke (2024-01-25)

"""


load("Zproots.sage")

from sage.rings.padics.precision_error import PrecisionError


def compute_g(n, p, M):
    r"""
    Compute mod `p^M` reductions of the power series `g_m(v)`, m=0,...,n from
    [Prop. 4.3, BJ08].

    The power series `g_m(v) \in \ZZ_p[[v]]` are used for computing the values
    of the p-adic polylogarithms at the `(p-1)`-st roots of unity `\zeta \neq 1`
    via the formula `\mathrm{Li}_m(\zeta) = \frac{p^m}{p^m-1} g_m(1/(1-\zeta))`.

    INPUT:

    - ``n`` -- a nonnegative integer

    - ``p`` --  a prime

    - ``M`` -- a nonnegative integer

    OUTPUT:

    A list of polynomials over `\ZZ/p^M\ZZ` whose m-th entry is the reduction of
    `g_m(v)` modulo `p^M`

    EXAMPLES::

    Compute g_0(v), g_1(v), g_2(v) for p=5 modulo 5^2::

        sage: compute_g(2,5,2)
        [5*v^9 + 15*v^8 + 10*v^7 + 20*v^6 + 24*v^5 + v,
        10*v^8 + 10*v^7 + 5*v^6 + 6*v^4 + 8*v^3 + 12*v^2 + 24*v,
        5*v^7 + 20*v^6 + 15*v^5 + 2*v^3 + 7*v^2 + v]
    """

    # determine gsl s.t. for all k >= gsl, coefficient of t^k in the series g_m(t)
    # has valuation >= M (m=0,...,n)
    gsl = max(_findprec(1/(p-1), 1, M + _polylog_c(m,p), p) for m in range(1,n+1))
    # store coefficients with higher precision to account for intermediate divisions
    coeff_prec = M + n * floor(log(float(gsl-1))/log(float(p))) + 1
    R = PolynomialRing(Zp(p,coeff_prec, type='capped-abs'), names='v')
    v = R.gen()
    f = (1 + (-v)^p - (1-v)^p)/p
    fpowersum = 0
    for i in range(coeff_prec):
        fpowersum = 1 + p*f*fpowersum
    g0 = -(1-v) + (1-v)^p * fpowersum
    g = (n+1)*[0]
    g[0] = g0
    for i in range(n):
        psum = 0
        coeffs = [0]
        for k in range(1,gsl):
            psum += g[i][k]
            coeffs.append(-psum/k)
        g[i+1] = R(coeffs)
    return [x.change_ring(Integers(p^M)) for x in g]


def polylog_data(n, p, N):
    r"""
    Precompute power series `g_m(v)` (m=0,...,n) and cutoff parameter `k_0`.

    These data are passed to ``compute_polylog_series`` and ``fast_polylog``for
    quickly computing the power series of `\mathrm{Li}_m(\zeta+pt)`, resp. values of
    p-adic polylogarithms.

    INPUT:

    - ``n`` -- a nonnegative integer

    - ``p`` -- a prime

    - ``N`` -- a nonnegative integer specifying the desired precision for the
      power series of polylogarithms

    OUTPUT: a pair consisting of

    - ``g`` -- a list of the mod `p^M` reductions of the polynomials g_0,...,g_n,
      where `M = \max(N, N+n(\delta-1))` and `\delta = \lfloor \log_p(k_0-1) \rfloor`

    - ``k0``-- a nonnegative integer with the property that the k-th coefficient
      of `\mathrm{Li}_m(\zeta+pt)` has valuation >= N for all `k \geq k_0` and `m=0,\ldots,n`
      and `(p-1)`-st roots of unity `\zeta \neq 1`
    """

    k0 = max(2, _findprec(1,n,N, p))
    # delta = floor(log_p(k0-1))
    delta = 1
    while p^(delta+1) < k0:
        delta += 1
    M = max(N, N + n*(delta-1))
    g = compute_g(n, p, M)
    return g,k0


def compute_polylog_series(residue, n, p, N, g, k0):
    r"""
    Compute p-adic approximations of the power series `\mathrm{Li}_m(\zeta + pt)`
    (m = 0,...,n) on a residue disc.

    The argument ``residue`` specifies the residue disc. The power series is
    developed around the unique `(p-1)`-st root of unity `\zeta \neq 1` in the disc.
    The desired precision of the coefficients is ``N``. The function takes the
    precomputed series `g_m(v)` (m=0,...,n) and cutoff parameter `k_0` as input.

    INPUT:

    - ``residue`` -- a p-adic integer specifying the residue disc. It has to be
      different from 0 or 1 modulo p.

    - ``n`` -- a nonnegative integer

    - ``p`` --  a prime

    - ``N`` -- a nonnegative integer specifying the desired precision

    - ``g`` -- the list of precomputed series `g_m(v)` (m=0,...,n)

    - ``k0`` -- the precomputed cutoff parameter guaranteeing that after the
      `k_0`-th coefficient, all coefficients have valuation `\geq N`

    OUTPUT:

    A list of polynomials of degree < k0 with p-adic coefficients. The m-th
    element (m=0,...,n) is an approximation of `\mathrm{Li}_m(\zeta+pt)`.
    The coefficients have the specified p-adic precision `N`.
    """

    if residue % p == 0 or residue % p == 1:
        raise ValueError("residue has to be different from 0 and 1")

    # delta = floor(log_p(k0-1))
    delta = 1
    while p^(delta+1) < k0:
        delta += 1

    M = max(N, N + n*(delta-1))
    K = Qp(p,M)  # store M p-adic digits for each coefficient
    R = PolynomialRing(K, names='t')
    zeta = K.teichmuller(residue)
    Li0 = R([zeta/(1-zeta)] + [p^k/(1-zeta)^(k+1) for k in range(1,k0)])
    Li_series = [Li0]
    for m in range(1,n+1):
        Li_m_zeta = p^m/(p^m-1) * K(g[m](lift(1/(1-zeta))))
        coeffs = [Li_m_zeta]
        for k in range(1,k0):
            coeffs.append(-1/k*sum((-p/zeta)^(k-j)*Li_series[m-1][j] for j in range(k)))
        Li_series.append(R(coeffs))
    inexactness = R([K(0,N)]*k0)  # sum_i O(p^N) t^i
    for m in range(n+1):
        Li_series[m] += inexactness
    return Li_series


def eval_poly(f, x):
    r"""
    Evaluate a polynomial at an element.

    This is needed to work around a bug in Sage. Simply writing ``f(x)`` can result
    in wrong precisions if the leading coefficient is an inexact zero.
    See: https://github.com/sagemath/sage/issues/5075#issuecomment-1880116591

    INPUT:

    - ``f`` -- a polynomial over a ring

    - ``x`` -- an element of that ring

    OUTPUT: the value `f(x)`

    EXAMPLES:

    Over the field of 2-adics, the correct value of the polynomial ``O(2)*x + 1``
    at ``1`` is ``1 + O(2)`` but writing ``f(1)`` returns ``1 + O(2^20)``::

        sage: R.<x> = Qp(2)['x']
        sage: f = O(2)*x + 1
        sage: eval_poly(f, 1)
        1 + O(2)
        sage: f(1)
        1 + O(2^20)

    """

    coeffs = list(f)
    return sum(coeffs[i]*x^i for i in range(len(coeffs)))


def fast_polylog(z, n, p, N, g, k0):
    r"""
    Compute the p-adic polylogarithm `\mathrm{Li}_n(z)`.

    The polylogarithm is computed via the power series `\mathrm{Li}_n(\zeta+pt)`
    from ``compute_polylog_series``. This function takes the precomputed series
    `g_m(v)` (m=0,...,n) and cutoff parameter `k_0` as arguments to speed up
    the calculation. The power series are computed to precision `N`.

    INPUT:

    - ``z`` --  a p-adic integer, not in the residue class of 0 or 1

    - ``n`` -- a nonnegative integer

    - ``p`` -- a prime

    - ``N`` -- a nonnegative integer specifying the p-adic precision with which
      the power series of polylogarithms are computed

    - ``g`` -- the list of precomputed series `g_m(v)` (m=0,...,n)

    - ``k0`` -- the precomputed cutoff parameter guaranteeing that after the
      `k_0`-th coefficient, all coefficients of the power series
      `\mathrm{Li}_n(\zeta+pt)` have valuation `\geq N`


    OUTPUT: the value of the p-adic polylogarithm `\mathrm{Li}_n(z)`

    EXAMPLES:

    Computing `\mathrm{Li}_2(3)` in `\QQ_7`::

        sage: p = 7
        sage: N = 10
        sage: g,k0 = polylog_data(2,p,N)
        sage: fast_polylog(3,2,p,N,g,k0)
        2*7^2 + 7^3 + 6*7^4 + 3*7^5 + 7^6 + 7^7 + 3*7^8 + 5*7^9 + O(7^10)

    Summing `\mathrm{Li}_4(z)` in `\QQ_{101}` over `2 \leq z \leq 100`::

        sage: p = 101
        sage: N = 10
        sage: g,k0 = polylog_data(2,p,N)
        sage: sum(fast_polylog(z,2,p,N,g,k0) for z in range(2,101))
        81*101^2 + 53*101^3 + 79*101^4 + 59*101^5 + 11*101^6 + 46*101^7 + 40*101^8 + 4*101^9 + O(101^10)

    """

    Li_series = compute_polylog_series(z, n, p, N, g, k0)
    # delta = floor(log_p(k0-1))
    delta = 1
    while p^(delta+1) < k0:
        delta += 1
    coeff_prec = max(N, N + n*(delta-1)) + 1
    K = Qp(p, coeff_prec)
    zeta = K.teichmuller(z)
    return eval_poly(Li_series[n], (z-zeta)/p).add_bigoh(N)



def CK_depth_2_locus(p, q, N, a_q2):
    r"""
    Compute the refined Chabauty-Kim locus `X(\ZZ_p)_{\{2,q\},2}^{(1,0)}`.

    This locus is defined for an odd prime `q` by the equation
    `\log(2)\log(q) \mathrm{Li}_2(z) - a_{\tau_2 \tau_q} \log(z) \mathrm{Li}_1(z) = 0`,
    for a p-adic constant `a_{\tau_2 \tau_q}` called "DCW coefficient".
    The locus is a finite subset of `X(\ZZ_p)` containing the set of
    `\{2,q\}`-integral points whose mod `2` reduction is in `X \cup \{1\}` and
    whose mod `q` reduction is in `X \cup \{0\}`.

    INPUT:

    - ``p`` -- a prime not equal to `2` or `q`

    - ``q`` -- an odd prime

    - ``N`` -- a nonnegative integer specifying the p-adic precision with which
      the coefficients of power series are calculated

    - ``a_q2`` -- the value of the DCW coefficient `a_{\tau_2 \tau_q}`
      (a p-adic number)

    OUTPUT:

    The refined Chabauty-Kim locus `X(\ZZ_p)_{\{2,q\},2}^{(1,0)}` as a list of
    p-adic numbers.

    .. NOTE::
        This uses the function ``Zproots`` from the file ``Zproots.sage``.

        If the precision `N` or the precision of `a_{\tau_2 \tau_q}` is too low
        to determine the Chabauty-Kim locus, a PrecisionError is thrown.

    EXAMPLES:

    Compute the refined Chabauty-Kim locus `X(\ZZ_p)_{\{2,q\},2}^{(1,0)}` for
    `p = 5` and `q = 3`. The DCW coefficient for `q = 3` is given by
    `a_{\tau_3 \tau_2} = -\mathrm{Li}_2(3)``::

        sage: p = 5; q = 3
        sage: a = -Qp(p)(3).polylog(2)
        sage: CK_depth_2_locus(p,q,10,a)
        [2 + O(5^9),
         2 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + O(5^9),
         3 + O(5^6),
         3 + 5^2 + 2*5^3 + 5^4 + 3*5^5 + O(5^6),
         4 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + O(5^9),
         4 + 5 + O(5^9)]

    Compute the refined Chabauty-Kim locus `X(\ZZ_p)_{\{2,q\},2}^{(1,0)}` for
    `p = 3` and `q = 17`. Since `17 = 2^4+1` is a Fermat prime, the DCW coefficient
    for `q = 17` is given by `a_{\tau_{17} \tau_2} = -\frac{1}{4} \mathrm{Li}_2(17)`::

        sage: p = 3; q = 17
        sage: a = -1/4*Qp(p)(17).polylog(2)
        sage: CK_depth_2_locus(p,q,10,a)
        [2 + O(3^9),
         2 + 2*3 + 2*3^2 + 2*3^3 + 2*3^4 + 2*3^5 + 2*3^6 + 2*3^7 + O(3^8),
         2 + 2*3 + 3^2 + O(3^8)]

    Precision `N = 4` is not enough to determine the locus for `p = 3` and `q = 19`::

        sage: p = 3; q = 17
        sage: a = -1/4*Qp(p)(17).polylog(2)
        sage: CK_depth_2_locus(p,q,4,a)
        Traceback (most recent call last)
        ...
        Insufficient precision to decide if root is liftable: O(3^2)

    """

    g,k0 = polylog_data(2,p,N)
    delta = 1
    while p^(delta+1) < k0:
        delta += 1
    coeff_prec = N + 2*delta
    K = Qp(p, coeff_prec)
    R = PolynomialRing(K, names='t')

    solutions = []
    for residue in range(2,p):
        Li_series = compute_polylog_series(residue, 2, p, N, g, k0)
        zeta = K.teichmuller(residue)
        logseries = R([0] + [(-(-p)^k/(k*zeta^k)).add_bigoh(N) for k in range(1,k0)])
        a2 = K(2).log()
        aq = K(q).log()
        fseries = a2*aq*Li_series[2] - a_q2*(logseries*Li_series[1]).truncate(k0)
        series_prec = min(N + a2.valuation() + aq.valuation(), N + a_q2.valuation())
        roots = Zproots(fseries, series_prec)
        solutions += [zeta + p*r for r in roots]

    return solutions


def CK_depth_4_locus(p, q, N, coeffs):
    r"""
    Compute the refined Chabauty-Kim locus `X(\ZZ_p)_{\{2,q\},\mathrm{PL},4}^{(1,0)}`.

    This locus is defined for an odd prime `q` by the two equations
    `\log(2)\log(q) \mathrm{Li}_2(z) - a_{\tau_2 \tau_q} \log(z) \mathrm{Li}_1(z) = 0`
    and
    `a \mathrm{Li}_4(z) + b \log(z) \mathrm{Li}_3(z) + c\log(z)^3\mathrm{Li}_1(z) = 0`
    for p-adic constants `a_{\tau_2 \tau_q}` and `a`,`b`,`c`.
    The locus is a finite subset of `X(\ZZ_p)` containing the set of
    `\{2,q\}`-integral points whose mod `2` reduction is in `X \cup \{1\}` and
    whose mod `q` reduction is in `X \cup \{0\}`. Currently, the values of the
    p-adic constants are only completely known for `q = 3`, where they can be
    computed via the function ``Z_one_sixth_coeffs``.

    INPUT:

    - ``p`` -- a prime not equal to `2` or `q`

    - ``q`` -- an odd prime

    - ``N`` -- a nonnegative integer specifying the p-adic precision with which
      the coefficients of power series are calculated

    - ``coeffs`` -- a tuple of the four p-adic coefficients
      `(a_{\tau_q \tau_2}, a, b, c)`

    OUTPUT:

    An approximation of the refined Chabauty-Kim locus
    `X(\ZZ_p)_{\{2,q\},\mathrm{PL},4}^{(1,0)}` as a list of p-adic numbers.

    .. NOTE::
        This uses the function ``Zproots`` from the file ``Zproots.sage``.

        If the precision `N` or the precision of the ``coeffs`` is too low
        to determine the Chabauty-Kim locus, a PrecisionError is thrown.

        The function determines the zeros of the first functions for which the
        value of the second function is indistinguishable from zero up to the
        known precision. If the precision is too low to detect a non-vanishing
        of the second function, this can result in a too large set.

    EXAMPLES:

    Compute the depth 4 Chabauty-Kim locus for `q = 3` and auxiliary prime `p = 5`::

        sage: p = 5; q = 3; N = 10
        sage: coeffs = Z_one_sixth_coeffs(p,N)
        sage: CK_depth_4_locus(p,q,N,coeffs)
        [2 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + O(5^9),
         3 + O(5^6),
         4 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + O(5^9),
         4 + 5 + O(5^9)]

    Since the locus contains precisely the `\{2,3\}`-integral points `\{-3,3,-1,9\}`,
    Kim's conjecture for `S = \{2,3\}` and `p = 5` holds in depth 4.

    Verify Kim's conjecture for `S = \{2,3\}` and auxiliary prime `p = 43`::

        sage: p = 43; q = 3; N = 6
        sage: coeffs = Z_one_sixth_coeffs(p,N)
        sage: CK_depth_4_locus(p,q,N,coeffs)
        [3 + O(43^5),
         9 + O(43^5),
         40 + 42*43 + 42*43^2 + 42*43^3 + 42*43^4 + O(43^5),
         42 + 42*43 + 42*43^2 + 42*43^3 + 42*43^4 + O(43^5)]

    For `q = 3` and `p = 5` the precision `N = 5` results in a too large locus:

        sage: p = 5; q = 3; N = 5
        sage: coeffs = Z_one_sixth_coeffs(p,N)
        sage: CK_depth_4_locus(p,q,N,coeffs)
        [2 + O(5^4),
         2 + 4*5 + 4*5^2 + 4*5^3 + O(5^4),
         3 + O(5^3),
         3 + 5^2 + O(5^3),
         4 + 4*5 + 4*5^2 + 4*5^3 + O(5^4),
         4 + 5 + O(5^4)]

    """

    if p == 2 or p == q:
        raise ValueError("prime p has to be different from 2 and q")

    # power series g_m(v) for calculating Li_m(zeta) and truncation parameter k0
    g,k0 =  polylog_data(4,p,N)

    delta = 1
    while p^(delta+1) < k0:
        delta += 1
    coeff_prec = N + 4*delta
    K = Qp(p, coeff_prec)
    R = PolynomialRing(K, names='t')

    a2 = K(2).log()
    aq = K(q).log()
    a_q2,c1,c2,c3 = coeffs

    solutions = []

    for residue in range(2,p):
        # root of unity in this residue disc
        zeta = K.teichmuller(residue)

        # power series for log(z), Li_m(z) (m<=4) in the parameter t, where z = zeta+p*t
        logseries = R([0] + [(-(-p)^k/(k*zeta^k)).add_bigoh(N) for k in range(1,k0)])
        Li_series = compute_polylog_series(residue, 4, p, N, g, k0)

        # first Kim function
        f1series = a2*aq*Li_series[2] - a_q2*(logseries*Li_series[1]).truncate(k0)
        f1prec = min(N + a2.valuation() + aq.valuation(), N + a_q2.valuation())
        # second Kim function
        f2series = (c1*Li_series[4] + c2*logseries*Li_series[3] + c3*logseries^3*Li_series[1]).truncate(k0)
        f2prec = N + min(c.valuation() for c in [c1,c2,c3])

        # normalise power series
        series = [f1series,f2series]
        prec = [f1prec, f2prec]
        for i in range(2):
            minval = min(series[i][k].valuation() for k in range(k0))
            series[i] /= p^minval
            prec[i] -= minval
            if prec[i] <= 0:
                raise PrecisionError(f"function {i+1} has coefficients of precision <= 0")

        # can skip residue disk if functions are coprime mod p
        fmodp = [f.change_ring(GF(p)) for f in series]
        if gcd(fmodp[0], fmodp[1]) == 1:
            continue

        # check which roots of the first Kim function are also roots of the second
        roots = Zproots(series[0])
        for root in roots:
            if eval_poly(series[1],root).add_bigoh(prec[1]) == 0:
                solutions.append(zeta + p*root)

    return solutions



def depth2_constant(p,q, N, steinberg_decomposition):
    r"""
    Compute the DCW coefficient `a_{\tau_q \tau_2}` for an odd prime `q` given a
    Steinberg decomposition of `[2] \wedge [q]`.

    Let `E = \QQ^\times \otimes \bQ` and write `[x] = x \otimes 1 \in E`.
    A Steinberg decomposition of `[2] \wedge [q]` is a way of writing
    `[2] \wedge [q] = \sum_i c_i [t_i] \wedge [1-t_i]` in `E \wedge E` with
    rational numbers `c_i` and `t_i \neq 0,1`. From this the p-adic value of the
    DCW coefficient can be computed as
    `a_{\tau_q \tau_2} = \frac{1}{2} \log(2) \log(q)
    + \sum_i c_i (\mathrm{Li}_2(t_i) + \frac{1}{2} \log(t) \log(1-t))`.
    Steinberg decompositions can be computed with the code available at
    https://github.com/martinluedtke/dcw_coefficients

    INPUT:

    -- ``p`` --  a prime not equal to `2` or `q`

    -- ``q`` -- an odd prime

    -- ``N`` -- a nonnegative integer specifying the p-adic precision with which the
       power series of the dilogarithm are computed

    -- ``steinberg_decomposition`` -- a Steinberg decomposition of `[2] \wedge [q]`
       given as a dict of the form ``{t_i: c_i}`` saying that the Steinberg
       element `[t_i] \wedge [1-t_i]` appears with coefficient `c_i`

    OUTPUT: the value of the DCW coefficient `a_{\tau_q \tau_2}` as a p-adic number

    """

    g,k0 =  polylog_data(2,p,N)
    K = Qp(p,N)
    a2q = 0
    for (t,c) in steinberg_decomposition.items():
        if t.valuation(p) == 0 and (1-t).valuation(p) == 0:
            dilog_t = fast_polylog(t,2,p,N,g,k0)
        else:
            # fall back to library function for dilogs in residue disks of 0 or 1
            dilog_t = Qp(p,N+5)(t).polylog(2)
        a2q -= c * (dilog_t + 1/2*K(1-t).log(0)*K(t).log(0))
    a2q += 1/2 * K(2).log(0) * K(q).log(0)
    aq2 = K(2).log(0) * K(q).log(0) - a2q
    return aq2


def Z_one_sixth_coeffs(p, N):
    r"""
    Compute the `p`-adic coefficients appearing in the Coleman functions
    defining the depth 4 Chabauty-Kim locus for `S = \{2,3\}`.

    INPUT:

    - ``p`` -- a prime not equal to 2 or 3

    - ``N`` -- a nonnegative integer representing the p-adic precision of polylog
      power series

    OUTPUT: a quadruple of p-adic numbers consisting of

    - ``a_32`` -- the value of the DCW coefficient `a_{\tau_3 \tau_2} = - \mathrm{Li}_2(3)`

    - ``a, b, c`` -- the coefficients of a Kim function
      `a \mathrm{Li}_4(z) + b \log(z) \mathrm{Li}_3(z) + c\log(z)^3\mathrm{Li}_1(z)`

    """

    g,k0 =  polylog_data(4,p,N)
    Li = [lambda z,n=n: fast_polylog(z, n, p, N, g, k0) for n in range(5)]
    a_32 = -Li[2](3)
    K = Qp(p,N)
    z1 = K(3)
    z2 = K(9)
    rows = [[Li[4](z), log(z)*Li[3](z), log(z)^3*Li[1](z)] for z in [z1,z2]]
    minors = matrix(rows).minors(2)
    m = min(c.valuation() for c in minors)
    return (a_32, minors[2]/p^m, -minors[1]/p^m, minors[0]/p^m)


####################################### AUXILIARY FUNCTIONS #######################################

# for estimating valuations of power series g_m(v), comes from [Proposition 6.1, BJ08]
def _polylog_c(n, p):
    logp = log(float(p))
    return p/(p-1) - (n-1)/logp + (n-1)*log(n*(p-1)/logp)/logp + log(2*p*(p-1)*n/logp)/logp


 # Return a positive integer k >= 2 such that c_1*k - c_2*log_p(k) > c_3.
def _findprec(c_1, c_2, c_3, p):
    k = Integer(max(ceil(c_2/c_1), 2))
    logp = log(float(p))
    while True:
        if c_1*k - c_2*log(float(k))/logp > c_3:
            return k
        k += 1
