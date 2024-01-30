r"""
Finding roots of p-adic power series

The function ``Zproots`` finds the set of roots in `\ZZ_p` of a p-adic power
series. Unlike the method ``polrootspadic`` from PARI/GP, this code works for
power series with inexact coefficients. This means that it detects when
the precision is insufficient to determine the set of roots. Moreover, roots
are computed with the precision to which they are known given the precision
of the power series.

AUTHORS:

- Martin Lüdtke (2024-01-25)

"""

from sage.rings.padics.precision_error import PrecisionError

def Zproots(f, coeff_prec=Infinity):
    r"""
    Compute the set of roots in `\ZZ_p` of a power series in `\QQ_p[[t]]`.

    Only a p-adic approximation of the power series is given. It is given by
    a polynomial ``f`` with p-adic coefficients along with an integer ``coeff_prec``
    indicating that ``f`` agrees with the true power series to this precision.

    INPUT:

    - ``f`` -- nonzero polynomial with coefficients in p-adic field

    - ``coeff_prec`` -- integer (default: ``Infinity``). Indicates that the
      polynomial ``f`` approximates the power series to this p-adic precision

    OUTPUT:

    The roots of `f` in `\ZZ_p` as a list of p-adic integers

    EXAMPLES:

    This example illustrates finding the square roots of 7 in `\ZZ_3`::

        sage: R.<t> = Qp(3)['t']
        sage: Zproots(t^2-7, 5)
        [2 + 3 + 3^2 + 2*3^3 + O(3^5), 1 + 3 + 3^2 + 2*3^4 + O(3^5)]

    There are no square roots of `-1` in `\ZZ_3`::

        sage: R.<t> = Qp(3)['t']
        sage: Zproots(t^2+1, 5)
        []

    The roots of `t^2 - 1` in `\ZZ_2` cannot be determined if the polynomial is
    only known to precision 2::

        sage: R.<t> = Qp(2)['t']
        sage: Zproots(t^2-1, 2)
        Traceback (most recent call last)
        ...
        PrecisionError: Insufficient precision to decide if root is liftable: 1 + O(2^2)

    The roots of `t^2 - 1` in `\ZZ_2` are determined to precision 2 if the
    polynomial is given with precision 3::

        sage: sage: R.<t> = Qp(2)['t']
        sage: Zproots(t^2-1, 3)
        [1 + O(2^2), 1 + 2 + O(2^2)]

    ALGORITHM:

    Normalise the polynomial so that it has coefficients in `\ZZ_p` and nonzero
    reduction modulo `p`. For each root modulo `p`, if it is simple, it lifts
    to a root in `\ZZ_p` by Hensel's lemma. Otherwise, traverse the lifts modulo
    higher powers of `p`, fixing higher p-adic digits in a depth-first manner,
    until we can decide whether the root lifts to `\ZZ_p` or until we detect
    that the precision of the polynomial insufficient to decide this.
    """

    if f == 0:
        raise ValueError("polynomial is indistinguishable from zero")
    p = parent(f).base_ring().prime()
    minval = min(coeff_prec, min(c.valuation() for c in f.coefficients(sparse = False)))
    f /= p^minval # normalise
    coeff_prec -= minval
    n = min(coeff_prec, min(c.precision_absolute() for c in f.coefficients(sparse = False)))
    if n <= 0:
        raise PrecisionError("normalised polynomial has coefficients of precision 0")
    # now all coefficients are in Z_p and known up to O(p^n)
    R = Zp(p, prec = n, type = 'capped-abs', print_mode = 'series')
    f = f.change_ring(R)
    f_der = f.derivative()
    fmodp = f.change_ring(Integers(p))
    roots = []

    # Evaluates a polynomial f at an element x. Writing just f(x) can result
    # in incorrect precisions, see https://github.com/sagemath/sage/issues/5075#issuecomment-1880116591
    def eval_poly(f, x):
        coeffs = list(f)
        return sum(coeffs[i]*x^i for i in range(len(coeffs)))

    rootsmodp = fmodp.roots()
    for rootmodp, multiplicity in rootsmodp:
        if multiplicity == 1:
            # simple root mod p, can lift to precision n using Hensel
            x = R(lift(rootmodp))
            root_prec = 1
            while root_prec < n:
                x -= eval_poly(f, x) / eval_poly(f_der, x)
                root_prec *= 2
            roots.append(x)
        elif n == 1:
            raise PrecisionError(f"Insufficient precision to decide if root is liftable: {R(rootmodp)}")
        elif eval_poly(f,lift(rootmodp)).valuation() >= 2:
            a = R(lift(rootmodp))
            m = 2

            while True:
                go_to_next_res_class = False
                f_of_a = eval_poly(f,a)
                if f_of_a.valuation() >= m:
                    f_der_a = eval_poly(f_der, a)
                    if (f_der_a != 0 and 2*f_der_a.valuation() < m):
                        # Hensel lifting applies, can lift up to precision n-d
                        d = f_der_a.valuation()
                        x = R(a)
                        root_prec = m-d
                        while root_prec < n-d:
                            x -= eval_poly(f, x) / eval_poly(f_der, x)
                            root_prec = 2*root_prec - d
                        roots.append(x.add_bigoh(n-d))
                        # root is unique mod p^(m-d), can move to next residue class mod p^(m-d)
                        m = m-d
                        a %= p^m
                        go_to_next_res_class = True
                    elif m == n:
                        raise PrecisionError(f"Insufficient precision to decide if root is liftable: {R(a)}")
                    elif f_of_a.valuation() >= m+1:
                        # root lifts mod p^(m+1)
                        m += 1
                    else:
                        # root doesn't lift, move to next residue class
                        go_to_next_res_class = True
                else:
                    # a is not a root mod p^m, move to next residue class
                    go_to_next_res_class = True

                if go_to_next_res_class:
                    # go back to most significant p-adic digit which is not (p-1)
                    x = lift(a)
                    while m >= 2 and (x + p^(m-1)) >= p^m:
                        m -= 1
                        x %= p^m
                    if m == 1:
                        # can stop if the complete residue class mod p has been searched
                        break
                    else:
                        # otherwise increase the most significant digit by 1
                        x += p^(m-1)
                    a = R(x)
    return roots
