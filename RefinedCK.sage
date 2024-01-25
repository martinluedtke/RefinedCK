load("Zproots.sage")

from sage.rings.padics.precision_error import PrecisionError

# for estimating valuations of power series g_m(v)
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

# Computes approximations of the power series g_m(v) (for m = 0,...,n) such that
# Li_m^{(p)}(z) = g_m(1/(1-z)) for all z in Z_p not congruent 1 mod p.
# The power series have coefficients in Z_p and are computed with precision M.
# The g's are returned as polynomials with coefficients in integers mod p^M.
def compute_g(n, p, M):
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

# precomputes series g_m(v) (m=0,...,n) and cutoff parameter k0 for fast calculation
# of p-adic polylogarithms to precision N
def polylog_data(n, p, N):
    k0 = max(2, _findprec(1,n,N, p))
    # delta = floor(log_p(k0-1))
    delta = 1
    while p^(delta+1) < k0:
        delta += 1
    M = max(N, N + n*(delta-1))
    g = compute_g(n, p, M)
    return g,k0

# Computes power series for log(z) and Li_m(z) (0<=m<=n) in t where z = zeta + p*t
# and zeta != 1 is a (p-1)st root of unity in Z_p.
# It takes the precomputed series g_m(v) and cutoff parameter k0 as input.
def compute_polylog_series(residue, n, p, N, k0, g):
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

# Evaluates a polynomial f at an element x. The usual f(x) is buggy with
# inexact coefficients, precision information can get lost.
def eval_poly(f, x):
    coeffs = list(f)
    return sum(coeffs[i]*x^i for i in range(len(coeffs)))


# fast calculation of p-adic polylog Li_n(z) using precomputed polynomials g_m(v)
def fast_polylog(z, n, p, N, k0, g):
    Li_series = compute_polylog_series(z, n, p, N, k0, g)
    # delta = floor(log_p(k0-1))
    delta = 1
    while p^(delta+1) < k0:
        delta += 1
    coeff_prec = max(N, N + n*(delta-1)) + 1
    K = Qp(p, coeff_prec)
    zeta = K.teichmuller(z)
    return eval_poly(Li_series[n], (z-zeta)/p).add_bigoh(N)



# computes the zero locus of log(2)*log(q)*Li_2(z) - a_q2*log(z)*Li1(z) in X(Z_p)
# where X is the thrice-punctured line
def CK_depth_2_locus(p, q, N, a_q2):
    g,k0 = polylog_data(2,p,N)
    delta = 1
    while p^(delta+1) < k0:
        delta += 1
    coeff_prec = N + 2*delta
    K = Qp(p, coeff_prec)
    R = PolynomialRing(K, names='t')

    solutions = []
    for residue in range(2,p):
        Li_series = compute_polylog_series(residue, 2, p, N, k0, g)
        zeta = K.teichmuller(residue)
        logseries = R([0] + [(-(-p)^k/(k*zeta^k)).add_bigoh(N) for k in range(1,k0)])
        a2 = K(2).log()
        aq = K(q).log()
        fseries = a2*aq*Li_series[2] - a_q2*(logseries*Li_series[1]).truncate(k0)
        series_prec = min(N + a2.valuation() + aq.valuation(), N + a_q2.valuation())
        roots = Zproots(fseries, series_prec)
        solutions += [zeta + p*r for r in roots]

    return solutions


# calculates (1,0)-refined Chabauty-Kim locus for S={2,q} in polylogarithmic depth 4
# p: auxiliary prime
# q: prime in S
# N: precision
# coeffs: (a_{q,2}, a, b, c) with a_{q,2} the DCW coefficient,
#    (a,b,c) defining the relation a*Li4(z) + b*log(z)*Li3(z) + c*log(z)^3*Li1(z) = 0
def CK_depth_4_locus(p, q, N, coeffs):
    if p == 2 or p == q:
        raise ValueError("prime p has to be different from 2 and q")

    # truncation parameter k0 and power series g_m(v) for calculating Li_m(zeta)
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
        Li_series = compute_polylog_series(residue, 4, p, N, k0, g)

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

# computes a_{q,2} using a Steinberg decomposition of [2] \wedge [q]
def depth2_constant(p,q, N, steinberg_decomposition):
    g,k0 =  polylog_data(2,p,N)
    K = Qp(p,N)
    a2q = 0
    for (t,c) in steinberg_decomposition.items():
        if t.valuation(p) == 0 and (1-t).valuation(p) == 0:
            dilog_t = fast_polylog(t,2,p,N,k0,g)
        else:
            # fall back to library function for dilogs in residue disks of 0 or 1
            dilog_t = Qp(p,N+5)(t).polylog(2)
        a2q -= c * (dilog_t + 1/2*K(1-t).log(0)*K(t).log(0))
    a2q += 1/2 * K(2).log(0) * K(q).log(0)
    aq2 = K(2).log(0) * K(q).log(0) - a2q
    return aq2

# computes coefficients (a_{3,2}, a, b, c) appearing in the functions
# for the Chabauty-Kim locus for S = {2,3}
def Z_one_sixth_coeffs(p, N):
    g,k0 =  polylog_data(4,p,N)
    Li = [lambda z,n=n: fast_polylog(z, n, p, N, k0, g) for n in range(5)]
    a_32 = -Li[2](3)
    K = Qp(p,N)
    z1 = K(3)
    z2 = K(9)
    rows = [[Li[4](z), log(z)*Li[3](z), log(z)^3*Li[1](z)] for z in [z1,z2]]
    minors = matrix(rows).minors(2)
    m = min(c.valuation() for c in minors)
    return (a_32, minors[2]/p^m, -minors[1]/p^m, minors[0]/p^m)
