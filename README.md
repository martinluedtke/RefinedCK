# RefinedCK
Computing refined Chabauty-Kim loci for the thrice-punctured line

Sage code for the paper "Refined Chabauty–Kim calculations for the thrice-punctured line over $\mathbb{Z}[1/6]$" [Lüd24]

Let $S$ be a finite set of primes, let $\mathbb{Z}\_S$ be the ring of $S$-integers and $X = \mathbb{P}^1 \smallsetminus \\{0,1,\infty\\}$ the thrice-punctured line over $\mathbb{Z}\_S$. The $S$-integral points $X(\mathbb{Z}\_S)$ correspond to solutions of the $S$-unit equation. By the theorems of Siegel (1921) and Mahler (1933), this set is finite. The Chabauty–Kim method [Kim05; Kim09] aims to locate $X(\mathbb{Z}\_S)$ inside the $p$-adic points $X(\mathbb{Z}\_p)$ (for some auxiliary prime $p \not\in S$) by producing Coleman functions which vanish on them. We consider the refined version of this method by Betts and Dogra [BD20] which imposes restrictions on the mod $\ell$ reductions of the $S$-integral points for $\ell \in S$ to obtain more Coleman functions. The vanishing loci of these functions are "refined Chabauty–Kim loci" which can be computed with this Sage code.

## 1. Computing depth 2 loci

Let $S = \\{2,q\\}$ for some odd prime $q$. The refined Chabauty–Kim locus $X(\mathbb{Z}\_p)\_{S,2}^{(1,0)}$ is the vanishing set in $X(\mathbb{Z}\_p)$ of a function

$$ f(z) := \log(2)\log(q) \mathrm{Li}\_2(z) - a\_{\tau\_q \tau\_2} \log(z) \mathrm{Li}_1(z) $$

for some $p$-adic constant $a\_{\tau\_q \tau\_2}$. It contains the $S$-integral points whose mod 2 reduction is in $X \cup \\{1\\}$ and whose mod $q$ reduction is in $X \cup \\{0\\}$. The function `CK_depth_2_locus(p,q,N,a_q2)` computes this locus given $p$, $q$, a precision parameter $N$ and the constant $a\_{\tau\_q \tau\_2}$.

### Example

For $q = 3$ the $p$-adic constant is given by $a\_{\tau\_3 \tau\_2} = - \mathrm{Li}\_2(3)$. Computing the locus $X(\mathbb{Z}\_{5})\_{\\{2,3\\},2}^{(1,0)}$:
```sage
sage: p = 5; q = 3
sage: a = -Qp(p)(3).polylog(2)
sage: CK_depth_2_locus(p,q,10,a)
[2 + O(5^9),
 2 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + O(5^9),
 3 + O(5^6),
 3 + 5^2 + 2*5^3 + 5^4 + 3*5^5 + O(5^6),
 4 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + O(5^9),
 4 + 5 + O(5^9)]
```

In addition to the expected points $\\{-3,-1,3,9\\}$ there are the points $2$ and $3 + 5^2 + 2\cdot 5^3 + 5^4 + 3\cdot 5^5 + O(5^6)$, showing that Kim's conjecture is not satisfied in depth 2.

### Computing DCW coefficients

The constant $a\_{\tau\_q \tau\_2}$ is an example of a "Dan-Cohen–Wewers coefficient". It can be computed from a "Steinberg decomposition" 

$$ [2] \wedge [q] = \sum\_i c\_i [t\_i] \wedge [1 - t\_i] $$

of $[2] \wedge [q]$ in the wedge square $E \wedge E$ of the vector space $E := \mathbb{Q}^\times \otimes \mathbb{Q}$. Such Steinberg decompositions can be computed with the function `steinberg_decompositions` from the Sage code [dcw_coefficients](https://github.com/martinluedtke/dcw_coefficients). The function `depth2_constant(p,q,N,dec)` then computes $a\_{\tau\_q \tau\_2}$ as a $p$-adic number.

### Example

The following code computes $a\_{\tau\_{19} \tau\_2}$ as a $7$-adic number and determines the refined Chabauty–Kim locus $X(\mathbb{Z}\_7)\_{\\{2,19\\},2}^{(1,0)}$:

```sage
sage: p = 7; q = 19
sage: _,dec = steinberg_decompositions(bound=20, p=p)
sage: a = depth2_constant(p,q,10,dec[2,q])
sage: a
7^2 + 2*7^3 + 6*7^4 + 3*7^5 + 2*7^6 + 6*7^7 + 5*7^8 + O(7^10)
sage: CK_depth_2_locus(p,q,10,a)
[2 + 4*7 + 6*7^2 + 4*7^3 + 5*7^4 + 2*7^5 + 5*7^6 + 3*7^7 + 5*7^8 + O(7^9),
 2 + O(7^9),
 3 + 4*7 + 7^2 + 7^3 + 2*7^4 + 6*7^5 + 7^6 + 7^7 + O(7^8),
 3 + 4*7 + 4*7^2 + 6*7^3 + 2*7^4 + 3*7^5 + 4*7^6 + 2*7^7 + O(7^8),
 4 + 2*7 + 7^3 + 6*7^4 + 2*7^5 + 3*7^6 + 3*7^7 + 3*7^8 + O(7^9),
 4 + 4*7 + 6*7^2 + 7^3 + 4*7^5 + O(7^9),
 6 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + 6*7^5 + 6*7^6 + 6*7^7 + 6*7^8 + O(7^9),
 6 + 2*7 + 4*7^3 + 4*7^4 + 5*7^5 + 4*7^6 + 6*7^7 + 5*7^8 + O(7^9)]
```

The locus contains seven points in addition to the expected point $-1$, showing that Kim's conjecture for $S = \\{2,19\\}$ does not hold in depth 2 for the auxiliary prime $p = 7$.


## 2. Computing depth 4 loci

Let $S = \\{2,q\\}$ for some odd prime $q$. The refined Chabauty–Kim locus $X(\mathbb{Z}\_p)\_{S,\mathrm{PL},4}^{(1,0)}$ is contained in the common vanishing locus in $X(\mathbb{Z}\_p)$ of the two Coleman functions

$$ f\_2(z) := \log(2)\log(q) \mathrm{Li}\_2(z) - a\_{\tau\_q \tau\_2} \log(z) \mathrm{Li}_1(z) $$

$$ f\_4(z) := a \mathrm{Li}\_4(z) + b\log(z) \mathrm{Li}\_3(z) + c \log(z)^3 \mathrm{Li}\_1(z) $$

where the DCW coefficient $a\_{\tau\_q \tau\_2}$ is as above and $a,b,c$ are some $p$-adic coefficients which are not all zero. The function `CK_depth_4_locus(p,q,N,coeffs)` computes an approximation of this refined Chabauty–Kim locus given $p$, $q$, a precision parameter $N$ and the tuple of coefficients $(a\_{\tau\_q \tau\_2}, a, b, c)$.
We currently only know these coefficients explicitly in the case $q = 3$ where they can be computed with the function `Z_one_sixth_coeffs(p, N)`.

### Example

The following code computes the locus $X(\mathbb{Z}\_5)\_{\\{2,3\\},\mathrm{PL},4}^{(1,0)}$:

```sage
sage: p = 5; q = 3; N = 10
sage: coeffs = Z_one_sixth_coeffs(p,N)
sage: coeffs
(2*5^2 + 2*5^3 + 2*5^4 + 5^5 + 2*5^6 + 4*5^7 + 5^8 + 4*5^9 + O(5^10),
 1 + 2*5 + 2*5^2 + 2*5^5 + 5^6 + O(5^7),
 3 + 5 + 3*5^2 + 2*5^4 + 3*5^5 + O(5^6),
 2 + 2*5 + 2*5^2 + 5^3 + 3*5^4 + 4*5^5 + O(5^6))
sage: CK_depth_4_locus(p,q,N,coeffs)
[2 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + O(5^9),
 3 + O(5^6),
 4 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + O(5^9),
 4 + 5 + O(5^9)]
```

The four numbers are precisely the $S$-integral points $\\{-3,-1,3,9\\}$, which shows that Kim's conjecture for the thrice-punctured line over $\mathbb{Z}[1/6]$ holds in depth 4 for the auxiliary prime $p = 5$.

# Zproots

Computing roots of $p$-adic power series.

The function `Zproots(f, coeff_prec)` computes the set of roots in $\mathbb{Z}\_p$ of a power series $f \in \mathbb{Q}\_p[[t]]$. The argument `f` is a polynomial which approximates the power series $p$-adically and the argument `coeff_prec` (Infinity by default) indicates that coefficients are only known up to this $p$-adic precision. The function `Zproots` takes precision questions into account, throwing a `PrecisionError` if the precision is insufficient to decide whether a root modulo $p^N$ can be lifted to a root in $\mathbb{Z}_p$. The roots are computed with the precision to which they are known, given the precision of the power series $f$.

### Example

If the polynomial $f(t) = t^2 - 1 \in \mathbb{Q}\_2[t]$ is only known modulo 4 (i.e., to precision 2), its set of roots cannot be determined. It has roots $\pm 1$ in $\mathbb{Z}\_2$ but modulo 4 it cannot be distinguished from the polynomial $t^2-5$ which has no roots in $\mathbb{Z}\_2$.

```sage
sage: K = Qp(2,prec=2)
sage: R.<t> = K['t']
sage: Zproots(t^2-1)  # => PrecisionError
```

Increasing the precision to 3, we can compute its set of roots:


```sage
sage: K = Qp(2,prec=3)
sage: R.<t> = K['t']
sage: Zproots(t^2-1)
[1 + O(2^2), 1 + 2 + O(2^2)]
```

Note that the roots are only determined to precision 2, even though f is given with precision 3. Indeed, modulo 8, the polynomial $t^2 -1$ cannot be distinguished from $t^2-9$, and their sets of roots $\\{1,-1\\}$ and $\\{-3,3\\}$ agree only modulo 4.


## References

 - [BD20] L. Alexander Betts, Netan Dogra, "The local theory of unipotent Kummer maps and refined Selmer schemes" (2020)
 - [Kim05] Minhyong Kim, "The motivic fundamental group of $\mathbb{P}^1 \smallsetminus \\{0,1,\infty\\}$ and the theorem of Siegel" (2005)
 - [Kim09] Minhyong Kim, "The unipotent Albanese map and Selmer varieties for curves" (2009)
 - [Lüd24] Martin Lüdtke, "Refined Chabauty–Kim calculations for the thrice-punctured line over $\mathbb{Z}[1/6]$" (2024)
