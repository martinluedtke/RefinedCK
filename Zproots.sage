from sage.rings.padics.precision_error import PrecisionError

# Computes approximations of roots in Z_p of a p-adic polynomial f.
# The parameter coeff_prec (if present) indicates that coefficients of the polynomial
# are only known up to O(p^prec).
def Zproots(f, coeff_prec=Infinity):
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
            raise PrecisionError("Insufficient precision to decide if root is liftable: ", R(rootmodp))
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
                        raise PrecisionError("Insufficient precision to decide if root is liftable: ", R(a))
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
