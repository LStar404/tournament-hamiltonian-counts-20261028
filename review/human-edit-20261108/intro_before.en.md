# Quantitative Hamiltonian path counts and Wormald's angular Hessian

Xingchen Liu and Xiangyu Ye

7 November 2026

## Abstract

We prove that the maximum number of directed Hamiltonian paths in an $n$-vertex tournament satisfies

$$
P(n)=\left(\frac{\cosh1}{\cos1}+O(n^{-1})\right)\frac{n!}{2^{n-1}}.
$$

The proof builds on our earlier constant-factor counting framework, combining uniform permanent estimates, local diagonal scaling for nonprincipal submatrices, and a score-sensitive path bound with the spectral comparison of Fang and Huang. Divoux and Wang established the sharp leading asymptotic constant for cycles and paths. We also give an independent derivation of the full angular Hessian in Wormald's random blow-up formula and prove its positive definiteness for every regular base. The overlap with Bhattacharjee's results is stated explicitly. For each fixed odd base order, we prove eventual uniqueness of the carousel base for the expected path and cycle counts in both blow-up models, and establish strict monotonicity of the regular-block constants.

## 1. Introduction

A tournament is an orientation of a complete graph. Write $H(T)$ for the number of directed Hamiltonian paths in a tournament $T$, and $C(T)$ for the number of directed Hamiltonian cycles. Paths are counted as vertex orderings, whereas cyclic starting points are identified for cycles. Let

$$
P(n)=\max_{|V(T)|=n}H(T),\qquad
\mu_n=\frac{n!}{2^{n-1}},\qquad
\nu_n=\frac{(n-1)!}{2^n}.
$$

Szele [10] observed that a uniform random tournament has $\mu_n$ Hamiltonian paths in expectation: each vertex ordering is directed with probability $2^{-(n-1)}$. Hence $P(n)\ge\mu_n$. The corresponding expected cycle count is $\nu_n$ for $n\ge3$. These expectations provide the natural normalization for the extremal problem.

Adler, Alon and Ross [9] improved the random lower bound by choosing an almost complete packing of edge-disjoint triangles and orienting each triangle cyclically, independently of the others. A vertex ordering containing one of these triangles in three consecutive positions is more likely to form a directed path than it is in the independent-edge model. For a uniformly random vertex ordering, the number of such occurrences converges in distribution to $\operatorname{Poisson}(1)$, from which they obtained the lower bound $(e-o(1))\mu_n$. Wormald [6] used a different construction: the directions between large vertex classes are prescribed by a fixed tournament, while the tournaments within the classes are random. His calculation for carousel bases gives a cycle lower constant exceeding $2.85588$ along an infinite sequence of orders, already close to the constant considered below.

The upper bounds developed through permanent estimates. If $A$ is the adjacency matrix of a tournament, then $\operatorname{per}A$ counts its spanning unions of vertex-disjoint directed cycles. In particular, it bounds the number of Hamiltonian cycles. Alon [2] applied Brégman's inequality to this permanent and optimized the resulting expression over the outdegrees, obtaining $P(n)=O(n^{3/2}\mu_n)$. Friedgut and Kahn [7] used an entropy argument to improve the polynomial exponent; their cycle bound is $O(n^{\alpha}\nu_n)$ with $\alpha\approx1.249$. These estimates identify the correct exponential scale, but leave a polynomial gap between the upper and lower bounds. At the scale of a leading constant, one must retain information that a bound in terms of the degrees alone discards.

Divoux and Wang [12] determined the sharp leading constant. They proved that the maximum cycle count is $(L+o(1))\nu_n$ and the maximum path count is $(L+o(1))\mu_n$, where $L=\cosh1/\cos1$. Their proof still uses permanents, but replaces a degree bound by a determinant approximation for nearly doubly stochastic matrices. After separating vertices with large degree imbalance, they classify a Hamiltonian cycle by the directed path segments that it induces on the exceptional set. These segments are encoded in modified adjacency matrices of the remaining tournament. Sinkhorn scaling and a determinant–permanent inclusion-exclusion formula then reduce the count to a ratio of determinants of a skew-symmetric matrix. A matrix comparison of Fang and Huang [11] bounds this ratio by its value for a transitive tournament. Odd carousels, and their one-vertex deletions at even orders, attain the bound asymptotically; a separate argument transfers the cycle result to paths.

The first author's path-counting preprint [14], publicly archived on 8 October 2026, had already established $(L-O(n^{-1}))\mu_n\le P(n)\le(C_*+O(n^{-1}))\mu_n$ and the analytic framework used below. Thus it closed the polynomial gap, while leaving a gap between the two leading constants $L<C_*$. That archive contains the positive path convolution, uniform permanent estimate, nonprincipal scaling and exceptional-vertex analysis; it predates the arXiv v1 submission of [12] on 16 October 2026. The present sharp estimate combines that framework with the spectral moment comparison of Fang and Huang [11]. It refines the leading asymptotic in [12, Theorem 1.4] and retains a uniform $O(n^{-1})$ normalized error through deletion, scaling and summation. Determining the optimal error order remains open.

**Theorem 1.1.** There are absolute constants $K',n_1$ such that every integer $n\ge n_1$ satisfies

$$
(L-K'/n)\mu_n\le P(n)\le(L+K'/n)\mu_n.
$$

For odd $n$, the carousel $\mathrm{Car}_n$ has vertex set $\mathbb Z/n\mathbb Z$, with $i\to j$ precisely when the representative of $j-i$ modulo $n$ belongs to $\{1,\ldots,(n-1)/2\}$. The lower bound is attained, up to an error of $O(\mu_n/n)$, by odd carousels and by the even tournaments obtained by deleting one vertex from $\mathrm{Car}_{n+1}$.

![The carousel $\mathrm{Car}_7$ and its even-order subtournament obtained by deleting vertex $0$. Every vertex on the left has outdegree $3$; those on the right have outdegree $2$ or $3$. All arcs are shown.](figures/carousel_deletion.png){width=94%}


The second part of the paper concerns Wormald's random blow-up models. Fix an odd integer $d\ge3$ and a tournament $T^*$ on $d$ vertices. Each vertex is replaced by a block of $m$ vertices, and the directions between blocks are prescribed by $T^*$. In $\mathcal T(T^*,m)$ the internal tournaments are independent and uniform; in $\mathcal R(T^*,m)$ they are independent and uniform among regular tournaments, so $m$ must be odd. Put $N=dm$. The expected cycle and path counts are normalized by $\nu_N$ and $\mu_N$, respectively.

![A blow-up of the directed triangle. Each internal block shown is a directed triangle; a thick arrow between blocks represents all $9$ arcs in that direction. In the random models, the internal blocks are chosen independently from the specified distributions.](figures/triangle_blowup.png){width=78%}


For a regular base, Theorem 4 of Wormald [6] expresses the limiting constant in terms of an angular Hessian, subject to its determinant being nonzero. He computes this determinant for several bases and conjectures that the condition always holds. We prove positive definiteness and evaluate the determinant for every regular base.

**Theorem 1.2.** Let $T^*$ be regular, with adjacency matrix $A$. Set $S=A-A^T$, $C=S/d$, and $E=(e_1-e_d,\ldots,e_{d-1}-e_d)$. The Hessian $\mathbf H$ of Wormald's angular function at the origin is positive definite, and

$$
\mathbf H=E^T(I+C^2)(I-C^2)^{-1}E,\qquad
\mathcal H=d\,\frac{\det(I+C^2)}{\det(I-C^2)}>0,
$$
$$
\sqrt{d/\mathcal H}=\rho_d(S)
:=\frac{\det(I+S/d)}{\det(I+iS/d)}\in\mathbb Q_{>0}.
$$

Here $\mathcal H=\det\mathbf H$, and the square root is positive. The angular function is defined in Section 9. Together with Theorems 1, 4 and 5 of Wormald [6], this shows that, for fixed $d$, the normalized expected cycle and path counts in $\mathcal T(T^*,m)$ both tend to $\rho_d(S)$, while the corresponding limits in $\mathcal R(T^*,m)$ are $e^{1/d}\rho_d(S)$.

The model constants can also be obtained directly from Divoux and Wang [12, Proposition 5.1], without the Hessian calculation; Section 10.1 records that derivation. Their Proposition 7.1 and Lemma 9.1 already give the spectral maximum and the carousel value. The next corollary combines these results with the equality conditions of Fang and Huang [11], the zero-row-sum condition for a regular base, and a separate bound for nonregular bases.

**Corollary 1.3.** For each fixed odd $d\ge3$, there exists $M_d$ such that, for every $m\ge M_d$, the carousel $\mathrm{Car}_d$ is the unique base, up to isomorphism, maximizing the expected number of Hamiltonian cycles and paths in both models. For $\mathcal R(T^*,m)$, only odd $m$ are considered.

The closed form below is the binomial evaluation in Divoux and Wang [12, Section 7 and Lemma 9.1], with the factor $e^{1/d}$ supplied by Wormald [6, Theorem 1]. The known frequencies in Fang and Huang [11, Lemma 4.2] give the following further consequence.

**Corollary 1.4.** Set

$$
r_d=\frac{(1+1/d)^d+(1-1/d)^d}{(1+i/d)^d+(1-i/d)^d},
\qquad \mathfrak r_d=e^{1/d}r_d.
$$

Along odd integers $d\ge3$, the sequence $\mathfrak r_d$ increases strictly to $L$.

Theorem 1.2 directly proves Wormald's Hessian conjecture [6, Conjecture 6]. Corollary 1.3 combines existing counting and spectral results with the equality and nonregular-base arguments given here. The limit in Conjecture 2 follows from the closed form in [12] and Wormald's factor $e^{1/d}$; Corollary 1.4 adds strict monotonicity. Section 10 retains the expansion through $d^{-5}$, with remainder $O(d^{-6})$, as a calculation from that closed form.

Bhattacharjee's public release of 14 October 2026 [16] contains the full original angular Hessian, its positive definiteness, and the associated determinant results. Our Wormald project is cited through the Liu--Ye Git manuscript revision dated 19 October [15]; the later version [13] also acknowledges the independent work. We retain a direct derivation and identify the overlapping results. These records distinguish a public release date from a Git manuscript revision date. The separate single-author path archive of 8 October [14] concerns the $L/C_*$ counting framework described above.

The contribution and dependency structure is as follows.

| Component | Scope and relation to prior work |
|---|---|
| Constant-factor path framework | Independently archived in [14]; the upper constant there was $C_*>L$. |
| Sharp global path estimate | Uniform final $O(n^{-1})$ error, obtained by combining the counting estimates with [11]; the sharp leading asymptotic is in [12]. |
| Signed permanent estimate | The independent proof from [14] is retained; the counting applications use its nonnegative specialization. |
| Angular Hessian and carousel limit | Independent derivation overlapping [13,16]; no priority claim is based on the earlier path archive. |
| Fixed-base extremality | Equality analysis, nonregular-base decay and a finite-class comparison complete eventual uniqueness for expectations. |
| Regular-block monotonicity | A strict monotonicity consequence of the known carousel spectrum. |

For Corollary 1.3 the order $d$ is fixed first. There are finitely many base isomorphism classes; regular noncarousel bases have a strict limiting gap, and the normalized expectations of nonregular bases tend to zero. A common threshold can therefore be chosen for all four expectations and all bases of that fixed order. The statement concerns expectations, and the regular-block model only allows odd $m$.

### 1.1 Counting strategy

McCullagh [5] obtained a determinant approximation with relative error $O(n^{-1})$ under moderate-deviation assumptions. Divoux and Wang [12, Proposition 3.1] give a uniform $1+o(1)$ version for nonnegative doubly stochastic matrices. Theorem 3.1 states the quantitative estimate used here under fixed entry and operator-norm bounds; its coefficient and tail estimates are supplied in the detailed proof companion. The contribution of Theorem 1.1 is the uniform error for the final path count after deletion, scaling and summation.

The positive path convolution in Lemma 5.1 converts the counting problem into permanent estimates. Its deletion-size weights have summable fixed moments, which preserve the $O(n^{-1})$ error after summation. The treatment of exceptional vertices uses a four-block matching expansion, producing independently deleted rows and columns; Lemma 4.4 supplies the required nonprincipal estimate. Section 7 separates large variance, exceptional vertices and the remaining class. In the last class, Proposition 7.3 retains the score penalty needed to absorb the square-root errors. The all-order spectral comparison in Proposition 6.6 then gives the sharp upper constant. Section 8 obtains the matching lower bound from odd carousels and their even-order one-vertex deletions, and derives degree-variance stability.

### 1.2 Hessian and model strategy

For a regular base, Wormald's coefficient asymptotics involve an angular Hessian defined by an implicit equation. Section 9 differentiates that equation directly and proves positive definiteness, including the angular sign and the determinant factor from the nonorthonormal coordinates. Section 10 identifies the four model constants and their carousel values. Section 11 combines the regular equality classification with exponential decay for nonregular bases; finiteness of the base classes at fixed $d$ gives one common threshold. The base order is fixed before the block order tends to infinity.

### 1.3 Further questions and organization

The path maximizers at each finite order and the coefficient of the first correction term remain open problems. It would also be useful to estimate $M_d$ in terms of $d$. Allowing the base order and the block order to grow together would require error bounds uniform in the base order, beyond the fixed-base asymptotics used here.

Section 2 fixes notation. Sections 3 and 4 give the permanent and nonprincipal scaling estimates; Section 5 records the positive path convolution, summable weights and uniform tail. Section 6 proves the spectral comparison for all orders. Sections 7 and 8 establish the sharp path bound directly, followed by degree-variance stability. Sections 9--11 treat the original angular Hessian and fixed-base model extrema. The detailed proof companion retains the original section and equation numbers for the analytic estimates and auxiliary algebra. This concise main text states their precise hypotheses and develops the counting and model arguments; the companion supplies the longer technical derivations.

