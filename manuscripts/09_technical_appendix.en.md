# Technical appendix for Hamiltonian path counts in tournaments

Xingchen Liu and Xiangyu Ye

11 November 2026

## Scope and dependency map

This appendix contains the longer analytic proofs used by the main paper, *Quantitative Hamiltonian path counts and degree stability*. It presents the complete proofs with section, theorem, equation and reference numbers retained for compatibility with the main paper. It is intended to be read with the main paper; the remaining expanded companion is optional further reading, not an additional prerequisite for these proofs.

The permanent approximation is an analytic tool with an independent quantitative proof for fixed entry-bound and spectral-gap parameters. Its determinant main term is not asserted to be new, and this appendix makes no broader novelty claim about its range of admissible matrices. The local comparisons in Section 3 follow the contribution statement in Section 3 of the main paper.

- [Section 3](#technical-permanent) proves Theorem 3.1 in full: Gaussian pairing, compressed non-Gaussian cores, the linear coefficient window, factorial restoration, the coefficient tail and the final uniform error bound.
- [Section 4](#technical-scaling) proves local diagonal scaling and its cost, Gaussian deletion and centering, paired score preprocessing, the exact nonprincipal restoration identity and the small-score estimate. Lemma 4.4 uses Theorem 3.1 and Lemmas 4.1--4.3. Lemma 4.5 uses the same scaling and deletion estimates without paired prescaling.
- [Lemma 6.1](#technical-spectral-cap) is included with its complete proof because A.1 refers to its transitive determinant polynomial. Its eigenvalue calculation also verifies the frequency used in the carousel example in Section 4.3.
- [Sections A.1--A.3](#technical-algebra) supply the transitive determinant identity, alternating-switching isomorphism, equality of power diagonals and the fourth-moment equality algebra used in the main paper's spectral argument. The carousel example in Section 4.3 uses A.2 and Lemma 6.1 directly.

Unqualified section and lemma references refer to this appendix; references to the main paper are explicitly identified. The needed notation is restated below. Standard external tools retain their original citations. The full original reference list is included to preserve citation numbers. The original author statement and personal acknowledgments are not reproduced.

## Notation

We use the main paper's maximum-score notation $\Delta_s=\|S\mathbf1\|_\infty$. In A.2--A.3, $d$ denotes the matrix or tournament order; local block sizes and degree indices in Section 3 also retain $d$. The scalar analytic majorant is

$$
\mathcal G_{C,q}(r)=\exp\!\left(\frac{C^2r^2}{2(1-q^2r^2)}\right),\qquad rq<1.
$$

It is distinct both from the score product $\Gamma=\prod_i(1-a_i^2)$ in Section 4 and from the Gaussian matrix functional $\mathcal G(M)=\det(I-MM^{\mathsf T})^{-1/2}$. The generating series $G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}$ in Section 3 is also a local notation. The symbols $C$ and $q$ there are fixed analytic parameters; in Section 4, $C=2A/(n-1)$ is a matrix, while in A.2, $q=(d-1)/2$ is an integer.

For a tournament adjacency matrix $A$, put

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1,
\qquad s_i=2d_i^+-(n-1),\qquad \sum_i s_i=0,
$$
$$
\mathcal E=\|s\|_2^2,\qquad
\Delta_s=\|s\|_\infty,\qquad
a=\frac{s}{n-1},\qquad \tau=\|a\|_2^2\quad(n\ge2).
$$

Here $I_p$ is the identity, $J_p=\mathbf1_p\mathbf1_p^{\mathsf T}$, $P_p=J_p/p$, and $\Pi_p=I_p-P_p$. Submatrix rows and columns are listed in increasing original-label order; they need not be the same sets. In Section 4, $n$ or $N$ is the full order, $m=n-t$ is the retained order, and $p$ is a general matrix order. Empty sums are zero, empty products are one, and the empty determinant and permanent are one. The symbol $\|\cdot\|_{\rm op}$ denotes the Euclidean operator norm, and $\|\cdot\|_F$ or $\|\cdot\|_{\mathrm F}$ denotes the Frobenius norm.

For the nonzero frequency pairs $\pm i\lambda_j$ of $S$, set

$$
x_j=\lambda_j^2/n^2,\qquad
D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2}
=\prod_j(1-x_j)^{-1},
$$
$$
\rho_n(S)=D_n(S)\det(I+S/n)
=\prod_j\frac{1+x_j}{1-x_j}.
$$

The paired singular values give $\sum_jx_j=(n-1)/(2n)<1/2$, so these determinant factors are positive; all square roots mean the positive roots. The symbols $T_n^0$, $T_n$ and $T_d$ denote the transitive sign matrix in their respective orders, with entries $+1$ strictly above the diagonal. An odd carousel on $d=2q+1$ vertices has arcs $i\to j$ exactly when $j-i\pmod d\in\{1,\ldots,q\}$. Every logarithm is natural. Uniform error constants may depend on the fixed analytic or deletion-window parameters explicitly stated, but not on the particular admissible matrix, tournament or deletion sets.

<!-- Extraction from 08_detailed_proof.en.md; block=technical-permanent; raw_block_sha256=1c5a8952c61e6f7ee166f2a96dd233692eadd6e3e53f404a4d3c36f02f852f9d; copy_block_sha256=bec6fe50425f87eba4bd0783d021d5cc15a49bcc14622a4b7daac2f113b7c9b5; normalization=trailing-tex-control-space-empty-group-v1; transformations=control-space:2,edit-0:1,edit-1:1,edit-2:1,edit-3:1,edit-4:1,edit-5:1,edit-6:1,edit-10:1,analytic-majorant:21. -->

<a id="technical-permanent"></a>

## 3. A uniform permanent approximation

In this section we prove a uniform estimate for permanents. Write a matrix with unit row and column sums as $(J_n+E)/n$, where $E\mathbf1=E^{\mathsf T}\mathbf1=0$. If the entries of $E$ are bounded and $\|E/n\|_{\mathrm{op}}\le q<1$, the main term is a determinant. Section 4 applies this estimate to scaled tournament submatrices.

McCullagh [5, §3] already gives the determinant approximation with an $O(n^{-1})$ error under moderate-deviation hypotheses. For nonnegative inputs, the fixed entry and spectral-gap assumptions here imply weak boundedness and the required gap, and his determinant factor is exactly $\det(I-BB^{\mathsf T})^{-1/2}$; the identification is detailed in Section 3 of the main paper. Uniformity over a fixed class is not by itself a novelty distinction from a theorem valid for every admissible sequence. We retain the independent proof to track constants through compressed cores, the coefficient window and the tail, making them available after deletion and scaling. We do not claim to repair an identified gap in [5]. Li [8, Theorem 2.1] assumes that the maximum absolute row or column sum of the centered perturbation is $o(n)$; this narrower hypothesis does not cover the dense kernels used here, but this comparison is not a novelty claim relative to [5] or [12].

The compressed-core proof was developed independently in the earlier path-counting project [14]. Signed inputs are not a priority distinction: McCullagh [5, §4.1] already discusses complex perturbations. We retain the real signed formulation and its proof; the tournament applications use nonnegative inputs.

### 3.1 The theorem and the proof strategy


**Theorem 3.1 (Uniform permanent approximation).**

Fix $0\le C<\infty$ and $0\le q<1$. Let $n\ge1$, and suppose $E\in\mathbb R^{n\times n}$ satisfies

$$
E\mathbf1=E^{\mathsf T}\mathbf1=0,\qquad
\max_{i,j}|E_{ij}|\le C,\qquad
\|E/n\|_{\mathrm{op}}\le q.
$$

Put $B=E/n$. Uniformly over all matrices satisfying these conditions,

<a id="eq-uniform-permanent"></a>

$$
\frac{\operatorname{per}(J_n+E)}{n!}
=\det(I-BB^{\mathsf T})^{-1/2}+O_{C,q}(n^{-1}).
\tag{3.1}
$$

[Equation (3.1)](#eq-uniform-permanent) can also be written as the determinant factor times the relative error $1+O_{C,q}(n^{-1})$. The subscript $C,q$ means that the error constant and the threshold dimension may depend on these two parameters fixed in advance, but must apply simultaneously to every admissible matrix.


For a concrete signed example, set

$$
B=\frac17\begin{pmatrix}1&2&-3\\-2&1&1\\1&-3&2\end{pmatrix},\qquad E=3B.
$$

Then $B$ is doubly centered and $\|B\|_{\rm op}=5/7<1$, while $J_3+E$ has negative entries. For every $m\ge1$, $E_m=E\otimes J_m$ has order $n=3m$, entry bound $9/7$, and $\|E_m/n\|_{\rm op}=5/7$. This provides signed admissible inputs of arbitrarily large order with fixed parameters. This example concerns the theorem's hypotheses; it does not claim that an alternative method cannot extend to signed inputs.

All determinant square roots in this section are the positive square roots on the relevant real intervals. The assumptions give $\|B\|_{\mathrm F}^2\le C^2$. Thus the determinant factor is at least one and is uniformly bounded by a constant depending only on $C,q$.

Inclusion-exclusion for the row and column indices expresses each coefficient of the permanent as a sum over bipartite multigraphs. Centering eliminates degree-one vertices. The degree-two components correspond to Gaussian pairings and give the determinant main term. We classify the remaining components by their excess, the number of edges minus vertices; each unit of excess contributes a factor $n^{-1}$. We first estimate coefficients of degree at most $\alpha n$, then use a complex-analytic bound for the remaining coefficients.

The proof uses the Gaussian generating series $G(t)$. Put

$$
f(t)=\frac{\operatorname{per}(J_n+tE)}{n!},
\qquad G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}.
$$

Choose $1<\sigma<R<1/q$; when $q=0$, no upper restriction is imposed. For example, take

$$
R=\frac{3+q}{2(1+q)},\qquad \sigma=\frac{1+R}{2}.
$$

Use the scalar analytic majorant $\mathcal G_{C,q}$ defined above:

$$
\mathcal G_{C,q}(r)=\exp\left(\frac{C^2r^2}{2(1-q^2r^2)}\right),
\qquad r\ge0,\ rq<1.
$$

Throughout this section, when $q=0$, upper restrictions involving $1/q$ are omitted. All constants depend only on $C,q$ and the chosen radii. Section 3.6 combines them into an explicit error bound.


For these radii,

$$
R-1=\frac{1-q}{2(1+q)}>0,\qquad
1-Rq=\frac{2-q-q^2}{2(1+q)}=\frac{(1-q)(q+2)}{2(1+q)}>0,
$$

$$
\sigma-1=(R-1)/2>0,\qquad R-\sigma=(R-1)/2>0.
$$

In this section, let $s_i$ denote the singular values of $B$. Then

$$
\sum_i s_i^2=\sum_{i,j}B_{ij}^2\le n^2(C/n)^2=C^2,\qquad
0\le s_i\le q.
$$

Using $-\log(1-u)=\int_0^u(1-v)^{-1}\,dv\le u/(1-u)$,

$$
\begin{aligned}
\log G(r)&=-\frac12\sum_i\log(1-r^2s_i^2)\\
&\le\frac12\sum_i\frac{r^2s_i^2}{1-r^2s_i^2}
\le\frac{r^2\sum_i s_i^2}{2(1-r^2q^2)}
\le\frac{C^2r^2}{2(1-r^2q^2)}.
\end{aligned}
$$

Consequently $1\le G(1)\le\mathcal G_{C,q}(1)$. If $|f(1)-G(1)|\le K/n$, then

$$
\left|\frac{f(1)}{G(1)}-1\right|
=\frac{|f(1)-G(1)|}{G(1)}\le K/n,
$$

Thus the absolute error estimate also gives a relative error of the same order.

### 3.2 Coefficients and Gaussian pairing


**Definition 3.1 (Permanent coefficients and rescaling).**

Write $f(t)=\sum_{k=0}^n a_kt^k$. Expanding according to the entries taken from $E$ gives

$$
a_k=\frac1{(n)_k}
\sum_{\substack{I,J\subseteq[n]\\|I|=|J|=k}}
\operatorname{per}E[I,J],
$$

Here $0\le k\le n$, so the denominator $(n)_k$ is nonzero. For $k>n$, define $a_k=0$ directly, without using an expression containing $1/(n)_k$. Define

$$
F_k=\frac{(n)_k}{n^k}a_k
=\frac1{k!}
\sum_{\substack{i_1,\ldots,i_k\ \mathrm{distinct}\\
j_1,\ldots,j_k\ \mathrm{distinct}}}
\prod_{\ell=1}^kB_{i_\ell j_\ell},
\qquad
F(t)=\sum_{k=0}^nF_kt^k.
$$

The sum on the right remains meaningful when $k>n$: its indexing set is empty, so its value is zero. The formal identities below use this convention.


**Definition 3.2 (Set partitions and weights).**

For a finite set $E$, let $\mathfrak P(E)$ be the set of all partitions of $E$ into disjoint nonempty blocks, and put $\mathfrak P_k=\mathfrak P([k])$. The indicator that the $k$ coordinates are distinct has a standard inclusion-exclusion expansion on the partition lattice. The permanent calculation in [5, Section 8] also uses an expansion over pairs of partitions. A block of size $d$ has Möbius weight $(-1)^{d-1}(d-1)!$; here the weight of an entire partition is defined as $\mu(\pi)=\prod_{D\in\pi}(-1)^{|D|-1}(|D|-1)!$. Apply this expansion separately to the row and column coordinates of $F_k$. Each partition pair determines a bipartite multigraph: its edges have distinct labels $1,\ldots,k$, the vertices on the two sides are the blocks of the row and column partitions, and each block of size $d$ receives the weight above.


The numerical label of each vertex is summed independently over $[n]$; different vertices may have the same numerical label. If a row vertex has degree one, summing its label gives a column sum of $B$, which is zero. A column vertex of degree one similarly gives a zero row sum. Thus only graphs in which every vertex has degree at least two contribute.

For example, in degrees two and three, each surviving row or column partition has a single block. The products of the Möbius weights on the two sides are $1$ and $4$, respectively. Dividing by $k!$ gives

$$
F_2=\frac12\sum_{i,j}B_{ij}^2,
\qquad
F_3=\frac23\sum_{i,j}B_{ij}^3,
\qquad |F_3|\le\frac{2C^3}{3n}.
$$

The quadratic term is part of the Gaussian main term, whereas the cubic term is $O(n^{-1})$.

A connected component whose vertices all have degree two is called a pure degree-two component. Their total exponential generating function is $G(t)$. This can be checked directly with two independent standard real Gaussian vectors $X,Y$. By Wick's formula,

$$
\mathbb E\exp(tX^{\mathsf T}BY)
$$

the coefficient of $t^k$ in this expression is the sum over pairing partitions on the two sides of the edge labels, precisely the graphs whose vertices all have degree two. Integrating first with respect to the conditional Gaussian distribution and then diagonalizing $BB^{\mathsf T}$ gives

$$
\mathbb E\exp(tX^{\mathsf T}BY)
=\mathbb E\exp\!\left(\frac{t^2}{2}X^{\mathsf T}BB^{\mathsf T}X\right)
=\det(I-t^2BB^{\mathsf T})^{-1/2}.
$$

This analytic identity holds when $|t|\|B\|_{\mathrm{op}}<1$ and determines all formal coefficients. In particular, the coefficients of $G$ are nonnegative, and

$$
G(r)\le\mathcal G_{C,q}(r)\qquad(r\ge0,\ rq<1),
$$

because $-\log(1-x)\le x/(1-x)$ and $\sum_i s_i^2=\|B\|_{\mathrm F}^2\le C^2$; here $s_i$ are the singular values of $B$.

Remove all pure degree-two components from every contributing graph, and call what remains its core. A core need not be connected. If it has $h$ edges and $v$ vertices, define its excess as $j=h-v$. Every nonempty core satisfies $j\ge1$. Decomposition into components with labeled edges gives the coefficientwise identity

$$
F(t)=G(t)\left(1+\sum_{j\ge1}C_j(t)\right),
$$

Here $C_j$ is the generating series for cores of excess $j$, with the Möbius signs and matrix contractions included in its coefficients. The identity is formal: a fixed degree $k$ involves only finitely many $j<k$, so no convergence in $j$ at nonzero $t$ is required. The distinct-index definition of $F_k$ makes all coefficients above degree $n$ vanish.


**Definition 3.3 (Core series).**

For $\pi,\sigma\in\mathfrak P_h$, let $D_\pi(a)$ and $D_\sigma(a)$ denote the two partition blocks containing edge label $a$. Give the row blocks labels $x_D\in[n]$ and the column blocks labels $y_E\in[n]$, and define the contraction

$$
\mathcal W_B(\pi,\sigma)
=\sum_{x:\pi\to[n]}\sum_{y:\sigma\to[n]}
\prod_{a=1}^hB_{x_{D_\pi(a)},y_{D_\sigma(a)}}.
$$

Both sums run over all functions, with no injectivity requirement. Define $\mathcal K_{j,h}$ to be the set of partition pairs satisfying the following conditions: every block has size at least two; every connected component of the associated bipartite multigraph contains a block of size at least three; and $h-|\pi|-|\sigma|=j$. Here $|\pi|$ counts blocks, not elements of the original set. A connected component is a maximal set of vertices connected by successive edges. Degree counts incident half-edges, with parallel edges counted separately; after compression, a loop contributes two to the degree of its vertex. Define the core series by

$$
C_j(t)=\sum_{h=0}^{\infty}c_{j,h}t^h,\qquad
c_{j,h}=\frac1{h!}\sum_{(\pi,\sigma)\in\mathcal K_{j,h}}
\mu(\pi)\mu(\sigma)\mathcal W_B(\pi,\sigma).
$$

For fixed $h$, the sum is finite. A nonempty core has at least one block on either side, so $j\le h-2$ and $c_{j,h}=0$ for $h\le j+1$. We shall also use the weaker condition $j<h$. The empty graph contributes $F_0=G(0)=1$ and is not included in $C_j$.


Write $g_k=[t^k]G(t)$ for $k\ge0$, where $[t^k]$ denotes coefficient extraction. Thus $g_0=1$ and $g_k=0$ for odd $k$. Lemma 3.2 will show that the weighted norm $\|C_j\|_R=\sum_h|c_{j,h}|R^h$ is finite.


Fix the entries selected from $E$ by specifying the row set $I$ and image set $J$, both of size $k$. The total weight of bijections at these positions is $\operatorname{per}E[I,J]$. The remaining $n-k$ rows can be bijected arbitrarily to the remaining columns in $(n-k)!$ ways. Hence

$$
[t^k]\operatorname{per}(J+tE)
=(n-k)!\sum_{|I|=|J|=k}\operatorname{per}E[I,J],
$$

$$
a_k=\frac{(n-k)!}{n!}\sum_{|I|=|J|=k}\operatorname{per}E[I,J]
=\frac1{(n)_k}\sum_{|I|=|J|=k}\operatorname{per}E[I,J].
$$

Given the row set, column set, and a bijection, labeling its $k$ matching edges successively by $1,\ldots,k$ can be done in $k!$ ways. Thus

$$
\sum_{\boldsymbol i,\boldsymbol j\ \mathrm{distinct}}\prod_{h=1}^kB_{i_hj_h}
=k!\sum_{|I|=|J|=k}\operatorname{per}B[I,J]
=\frac{k!}{n^k}\sum_{|I|=|J|=k}\operatorname{per}E[I,J].
$$


For a condition $\mathcal A$, $\mathbf1\{\mathcal A\}$ equals one when the condition holds and zero otherwise. It is a scalar indicator, distinct from the all-ones vector $\mathbf1_p$. For a partition $\pi$, define

$$
\mu(\pi)=\prod_{D\in\pi}(-1)^{|D|-1}(|D|-1)!,\quad
\mathbf1_\pi(\boldsymbol i)=\prod_{D\in\pi}\mathbf1\{i_h\text{ constant on }D\text{}\}.
$$

Then

$$
\mathbf1\{i_1,\ldots,i_k\text{ distinct}\}
=\sum_{\pi\in\mathfrak P_k}\mu(\pi)\mathbf1_\pi(\boldsymbol i).
$$

To verify this, let $D_1,\ldots,D_r$ be the equality classes of the given coordinates. The right-hand side factors as

$$
\prod_{a=1}^r\left(\sum_{\pi\in\mathfrak P(D_a)}\mu(\pi)\right).
$$

The permutation sign is $\operatorname{sgn}(\pi)=(-1)^{\#\{(i,j):i<j,\ \pi(i)>\pi(j)\}}$: it is one for an even number of inversions and minus one for an odd number. A block of size $d$ can be arranged into a directed cycle in $(d-1)!$ ways, and such a cycle has sign $(-1)^{d-1}$. Thus each parenthesis is the sum of the signs of all permutations of that set. This equals one for a singleton. For size at least two, multiplication by a fixed transposition bijects positive and negative terms, so they cancel and the sum is zero.

Substituting on both sides gives

$$
F_k=\frac1{k!}\sum_{\pi,\sigma\in\mathfrak P_k}\mu(\pi)\mu(\sigma)
\sum_{\boldsymbol i,\boldsymbol j}\mathbf1_\pi(\boldsymbol i)\mathbf1_\sigma(\boldsymbol j)
\prod_{h=1}^kB_{i_hj_h}.
$$

If $\pi$ has a singleton block $\{h\}$, summing the label $i_h$, which appears only once, gives $\sum_iB_{ij_h}=0$. The column side is identical. For $k=2$ only one pair of two-element blocks survives, with weight $(-1)(-1)=1$; for $k=3$ only one pair of three-element blocks survives, with weight $2\cdot2=4$. Hence

$$
F_2=\frac1{2!}\sum_{i,j}B_{ij}^2,\quad
F_3=\frac4{3!}\sum_{i,j}B_{ij}^3,\quad
|F_3|\le\frac23n^2(C/n)^3=\frac{2C^3}{3n}.
$$

Put $K=BB^{\mathsf T}$ and $Q=B^{\mathsf T}B$. The fourth-order term is

$$
\begin{aligned}
F_4={}&\frac18(\operatorname{tr}K)^2+\frac14\operatorname{tr}(K^2)\\
&-\frac34\sum_i\left(\sum_jB_{ij}^2\right)^2
-\frac34\sum_j\left(\sum_iB_{ij}^2\right)^2
+\frac32\sum_{i,j}B_{ij}^4.
\end{aligned}
$$

The first three classes of partition pairs are: both sides have type $2+2$ ($3\cdot3=9$ pairs); one side has type $4$ and the other type $2+2$ (three pairs in each orientation, with block weight $-6$); and both sides have type $4$ (weight $36$). Dividing by $4!=24$ gives the stated coefficients. The three identical pairing pairs give $3/24=1/8$, and the six distinct pairing pairs give $6/24=1/4$. This also directly confirms the separation of the main term $g_4$ from the non-Gaussian correction.


A standard real Gaussian variable $X$ has density $(2\pi)^{-1/2}e^{-x^2/2}$. For $u\in\mathbb R$, completing the square gives

$$
\mathbb Ee^{uX}=\frac1{\sqrt{2\pi}}\int_{\mathbb R}e^{-x^2/2+ux}\,dx
=e^{u^2/2}\frac1{\sqrt{2\pi}}\int_{\mathbb R}e^{-(x-u)^2/2}\,dx=e^{u^2/2}.
$$

For $v\in\mathbb R^n$, independence gives the multivariate generating function $\mathbb Ee^{v^{\mathsf T}X}=e^{\|v\|^2/2}$. Differentiating with respect to the coordinates gives

$$
\mathbb E\prod_{h=1}^{2r}X_{i_h}
=\sum_{\mathcal P\text{ a pairing}}\prod_{\{a,b\}\in\mathcal P}\mathbf1\{i_a=i_b\},
\qquad \mathbb E\prod_{h=1}^{2r+1}X_{i_h}=0.
$$

We record the real Gaussian moment calculation. A standard real Gaussian vector has independent coordinates with density $(2\pi)^{-1/2}e^{-x^2/2}$. Put

$$
m_r=\frac1{\sqrt{2\pi}}\int_{\mathbb R}x^re^{-x^2/2}\,dx.
$$

Normalization gives $m_0=1$, and symmetry of the integral of an odd function gives $m_{2r+1}=0$. Integration by parts for $r\ge1$ gives

$$
\begin{aligned}
m_{2r}
&=-\frac1{\sqrt{2\pi}}\int_{\mathbb R}x^{2r-1}\,d(e^{-x^2/2})\\
&=\frac{2r-1}{\sqrt{2\pi}}\int_{\mathbb R}x^{2r-2}e^{-x^2/2}\,dx\\
&=(2r-1)m_{2r-2}
=(2r-1)(2r-3)\cdots1.
\end{aligned}
$$

The boundary term vanishes because $|x|^ae^{-x^2/2}\to0$ for every fixed integer $a\ge0$. With $(-1)!!=1$, this can be written uniformly as $m_{2r}=(2r-1)!!$, including $r=0$.

For an index list $i_1,\ldots,i_k$, define the multiplicity $c_a=\#\{h:i_h=a\}$. Independence gives the finite product

$$
\mathbb E\prod_{h=1}^kX_{i_h}=\prod_{a=1}^n m_{c_a}.
$$

If any $c_a$ is odd, the right-hand side is zero. If all $c_a$ are even, every admissible pairing must pair positions with equal indices. The number of pairings of $c_a$ positions satisfies

$$
p_0=1,\qquad p_{2r}=(2r-1)p_{2r-2}
=(2r-1)!!.
$$

Thus the total number of admissible pairings is $\prod_a(c_a-1)!!$, exactly the moment computed above. Defining the Kronecker symbol $\delta_{ab}=\mathbf1\{a=b\}$ gives

$$
\mathbb E\prod_{h=1}^{2r}X_{i_h}
=\sum_{\mathcal P}\prod_{\{a,b\}\in\mathcal P}\delta_{i_ai_b}.
$$

Here $\mathcal P$ ranges over pairings of $[2r]$. The empty pairing contributes one when $r=0$, and odd moments vanish.

First take a real $t$ satisfying $|t|q<1$. Integrate with respect to $Y$, and then orthogonally diagonalize $BB^{\mathsf T}$. The standard-vector density is $(2\pi)^{-n/2}e^{-\|x\|_2^2/2}$. An orthogonal transformation preserves $\|x\|_2$ and has absolute Jacobian one, so the transformed density is unchanged and still factors into the coordinate densities. Therefore,

$$
\begin{aligned}
\mathbb Ee^{tX^{\mathsf T}BY}
&=\mathbb E_Xe^{t^2\|B^{\mathsf T}X\|^2/2}\\
&=\prod_i\frac1{\sqrt{2\pi}}\int_{\mathbb R}
e^{-(1-t^2s_i^2)x^2/2}\,dx\\
&=\prod_i(1-t^2s_i^2)^{-1/2}=G(t).
\end{aligned}
$$

To extend the identity to the complex disk, put $U=X^{\mathsf T}BY$ and choose a real $r$ with $|t|<r<1/q$. If $q=0$, then $B=0$ and the result is immediate. For real $u$,

$$
e^{r|u|}\le e^{ru}+e^{-ru}.
$$

Since $Y$ has the same distribution as $-Y$, $U$ has the same distribution as $-U$. Hence

$$
\mathbb E e^{r|U|}
\le\mathbb E e^{rU}+\mathbb E e^{-rU}
=2G(r)<\infty.
$$

Nonnegativity of the terms in the exponential series gives, for $k\ge0$,

$$
\frac{r^k|U|^k}{k!}\le e^{r|U|}
\quad\Longrightarrow\quad
\mathbb E|U|^k\le\frac{k!}{r^k}\mathbb Ee^{r|U|}
\le\frac{2k!}{r^k}G(r)<\infty.
$$

Consequently, for every integer $N\ge0$, expectation can be taken term by term in the finite sum:

$$
\sum_{k=0}^{N}\frac{r^k}{k!}\mathbb E|U|^k
=\mathbb E\sum_{k=0}^{N}\frac{r^k|U|^k}{k!}
\le\mathbb Ee^{r|U|}\le2G(r).
$$

Next let $s=|t|/r<1$. Bound the remainder of the exponential series pointwise:

$$
\left|e^{tU}-\sum_{k=0}^{N}\frac{t^kU^k}{k!}\right|
\le\sum_{k>N}s^k\frac{r^k|U|^k}{k!}
\le s^{N+1}e^{r|U|}.
$$

Taking expectations yields the explicit error

$$
\left|\mathbb Ee^{tU}-\sum_{k=0}^{N}\frac{t^k}{k!}\mathbb EU^k\right|
\le2G(r)s^{N+1}\longrightarrow0.
$$

This proves that, for every complex $t$ with $|t|<1/q$,

$$
\mathbb E e^{tU}
=\sum_{k=0}^{\infty}\frac{t^k}{k!}\mathbb E U^k,
\qquad
\sum_{k=0}^{\infty}\frac{|t|^k}{k!}|\mathbb E U^k|
\le2G(r)<\infty.
$$

We compare these coefficients with those of $G(t)$. Let $s_i$ be the singular values of $B$. The series for each factor is determined by $c_0=1$ and the recurrence

$$
c_{m+1}=\frac{2m+1}{2m+2}c_m,
\qquad
c_m=\frac{(2m)!}{4^m(m!)^2},
\qquad
(1-z)^{-1/2}=\sum_{m\ge0}c_mz^m\quad(|z|<1).
$$

The recurrence follows by coefficientwise comparison in $(1-z)f'(z)=f(z)/2$; since $c_{m+1}/c_m<1$, the series on the right converges absolutely for $|z|<1$. Further,

$$
\frac{d}{dz}\bigl[(1-z)f(z)^2\bigr]
=-f(z)^2+2(1-z)f(z)f'(z)
=-f(z)^2+f(z)^2=0.
$$

Its value at zero is one, so $(1-z)f(z)^2=1$, which selects the branch taking value one at zero. Multiplying the finitely many factors gives

$$
G(t)=\prod_i\left(\sum_{m\ge0}c_m s_i^{2m}t^{2m}\right),
\qquad |t|q<1.
$$

On the real interval this agrees with the Gaussian integral already computed. If one coefficient differed from that of $\mathbb E U^k/k!$, choose the least differing degree $k_0$, divide the difference of the two series by $t^{k_0}$, and let $t\to0$ along the real axis. This would give

$$
0=\lim_{t\to0}\frac{\mathbb Ee^{tU}-G(t)}{t^{k_0}}
=\frac{\mathbb E U^{k_0}}{k_0!}-[t^{k_0}]G(t)\ne0,
$$

a contradiction. Hence all coefficients agree. Both sides are represented by absolutely convergent series on the stated complex disk, so the identity also holds there. The exponential factor $1/k!$ matches the factor $1/k!$ in the exponential generating function for labeled edges; Wick pairings correspond to partitions whose blocks on both sides all have size two. We interchange convergent series only within the fixed spectral-gap disk. The infinite sum over core excess $j$ is still used only as a formal coefficient identity.

In any contributing graph every degree is at least two, so

$$
2(h-v)=\sum_{u}(\deg u-2)\ge0.
$$

If $h-v=0$, all vertices have degree exactly two and every connected component is pure degree two. After removing those components, any nonempty core has $j=h-v\ge1$. Splitting the edge-label set between the pure degree-two part and the core gives a factor $\binom kh$; multiplying by $1/k!$ gives $1/[h!(k-h)!]$, so the generating functions multiply exactly.


Put $K=BB^{\mathsf T}$. The matrix eigendecomposition and $-\log(1-u)=\sum_{r\ge1}u^r/r$ give

$$
\log G(t)=\frac12\sum_{r=1}^{\infty}\frac{t^{2r}}r\operatorname{tr}(K^r)
=A_st^2+B_st^4+C_st^6+O(t^8),
$$

Within this paragraph define the scalars $A_s=\operatorname{tr}K/2$, $B_s=\operatorname{tr}(K^2)/4$, and $C_s=\operatorname{tr}(K^3)/6$. Exponentiating coefficient by coefficient gives

$$
\begin{aligned}
G(t)
&=1+(A_st^2+B_st^4+C_st^6)
+\frac12(A_st^2+B_st^4)^2+\frac16(A_st^2)^3+O(t^8)\\
&=1+A_st^2+(B_s+A_s^2/2)t^4
+(C_s+A_sB_s+A_s^3/6)t^6+O(t^8).
\end{aligned}
$$

Therefore

$$
\begin{aligned}
g_2&=\tfrac12\operatorname{tr}K,\\
g_4&=\tfrac14\operatorname{tr}(K^2)+\tfrac18(\operatorname{tr}K)^2,\\
g_6&=\tfrac16\operatorname{tr}(K^3)
+\tfrac18\operatorname{tr}K\operatorname{tr}(K^2)
+\tfrac1{48}(\operatorname{tr}K)^3.
\end{aligned}
$$

All odd coefficients are zero because $G(t)$ contains only $t^2$. The scalars $A_s,B_s,C_s$ are used only in this exponential expansion.


There are three two-element partitions $12|34,13|24,14|23$. Choosing one on each side gives nine pairs: three identical and six distinct. Identical pairings give the matrix-label sum $(\sum_{ij}B_{ij}^2)^2=(\operatorname{tr}K)^2$; distinct pairings give $\operatorname{tr}(K^2)$. Thus the pure degree-two contribution is

$$
\frac3{4!}(\operatorname{tr}K)^2+\frac6{4!}\operatorname{tr}(K^2)=g_4.
$$

If one side is a four-element block, its Möbius weight is $-6$. The other side has three possible pairings into two-element blocks, each with weight $(-1)^2=1$. The row-colored degree-four term is therefore

$$
\frac{3(-6)}{24}\sum_i\sum_{j,k}B_{ij}^2B_{ik}^2
=-\frac34\sum_i\left(\sum_jB_{ij}^2\right)^2.
$$

Exchanging row and column colors gives the column-colored degree-four term

$$
-\frac34\sum_j\sum_{i,k}B_{ij}^2B_{kj}^2
=-\frac34\sum_j\left(\sum_iB_{ij}^2\right)^2.
$$

If both sides are four-element blocks, the product of the weights is $(-6)^2=36$. The last term is therefore

$$
\frac{36}{24}\sum_{i,j}B_{ij}^4=\frac32\sum_{i,j}B_{ij}^4.
$$

The four classes sum to the expression for $F_4$ above. Partitions containing degree-one vertices contribute zero by centering.

### 3.3 Estimating non-Gaussian cores

We first sum over the internal indices of each degree-two chain and bound the resulting matrix product by its operator norm. After these chains are compressed, a graph of excess $j$ has at most $2j$ vertices. Put

$$
W=\max\left\{1,CR+\frac{C^2R^2}{1-Rq}\right\},
\qquad D=710W^3,\qquad
T_1=\frac32W^2+\frac{10}{3}W^3.
$$


**Lemma 3.2 (Compressed core activity).**

With the notation above,

<a id="eq-core-activity"></a>

$$
\|C_j\|_R\le(Dj/n)^j\qquad(j\ge1),
\tag{3.2}
$$

and the first excess satisfies the sharper bound

$$
\|C_1\|_R\le T_1/n.
$$

Here $\|H\|_R=\sum_{k\ge0}|[t^k]H|R^k$.


**Proof.**

Compress all maximal paths whose internal vertices have degree two. Each compressed edge represents a chain of positive length whose endpoints have degree at least three. Loops, parallel edges, and disconnected compressed graphs are allowed. If $b$ is the number of vertices of degree at least three and $e$ is the number of compressed edges, compression preserves excess and gives

$$
e=b+j,\qquad
2j=\sum_{i=1}^b(d_i-2),\qquad
1\le b\le2j,\qquad e\le3j.
$$

**The decoration counting identity.** Fix the excess and the original number of edges. Sum over all ordered degree sequences $(d_1,\ldots,d_b)$, assignments of the two vertex colors, pairings of labeled half-edges, and positive chain lengths compatible with the colors. After removing the temporary labels, the absolute Möbius compensation is $1/(b!\prod_i d_i)$. For a chain contraction, its internal numerical indices must be summed before taking the absolute value.

The structural vertices are the blocks of the two partitions of the edge labels, and their numerical indices lie in $[n]$. Distinct blocks remain distinct vertices even when their numerical indices coincide. Möbius inversion has already accounted for the original distinctness constraints, so we count partition pairs directly. Temporarily label the $b$ vertices of high degree and the $d_i$ half-edges at each vertex, and use these labels to choose a unique reading direction for every chain. After summing over all ordered degree sequences, every original core with labeled edges has $b!\prod_i d_i!$ decorations. For any fixed degree sequence, only compatible vertex labelings occur; summing over all sequences produces exactly the full $b!$ factor. Every structural vertex is identifiable by its color and incident original edge labels, and every incident half-edge by its original edge label. There is therefore no additional automorphism stabilizer. Conversely, a decorated half-edge pairing and all positive chain lengths determine every chain position. The original $h$ edge labels can be assigned to these positions in $h!$ ways. When the bipartite color-parity conditions hold, the internal vertices and their colors are then determined as well.

Removing the $h!$ factor from the original exponential generating function and the temporary decorations, and restoring the absolute Möbius weights $\prod_i(d_i-1)!$ of the high-degree vertices, gives the compensation

$$
\frac1{b!\prod_i d_i}.
$$

This step includes loops and chain reversal. Order the two distinct labeled half-edges in each pair, and read the chain starting from the smaller one. Reversal changes the list of original edge labels occupying these positions; it does not supply an additional free factor of two. The two half-edges of a loop follow the same convention. Internal degree-two vertices have absolute Möbius weight one, and there is no additional factorial for chain length. Chains with endpoints of different colors have odd length; those with endpoints of the same color have even length. In particular, every loop has even length at least two. These restrictions are part of the exact identity.

For example, take one row-colored vertex of degree four and two loops of length two, each passing through its own column-colored vertex of degree two. Then $j=b=1$ and $h=4$. There are three ways to split the four original edge labels into two pairs. The degree-four vertex has Möbius weight $(-1)^3 3!=-6$, whereas the product of the two degree-two weights is $+1$. After division by $4!$, the signed contribution is

$$
-\frac34\sum_i\left(\sum_k B_{ik}^2\right)^2.
$$

Even if numerical indices coincide in some summands, the two structural column vertices remain distinct. Exchanging colors gives $-\tfrac34\sum_k(\sum_i B_{ik}^2)^2$. The absolute compensation bound uses the absolute values of these terms. As an example with parallel edges, take three chains of length one between a row vertex and a column vertex. Their contribution is $\tfrac{(2!)^2}{3!}\sum_{i,k}B_{ik}^3=\tfrac23\sum_{i,k}B_{ik}^3$, exactly the cubic term above. These examples include loops, parallel edges, and the reversal convention, while the original graph remains bipartite.

We discard color restrictions only when taking an upper bound. For fixed $j,b$, the resulting total compensation is

$$
U_{j,b}=
\frac{2^b}{b!}\frac{(2e)!}{2^e e!}
\sum_{\substack{d_1+\cdots+d_b=2e\\d_i\ge3}}
\frac1{d_1\cdots d_b},
\qquad e=b+j.
$$

In the following estimate, each chain's internal numerical indices must be summed before taking absolute values. Replacing $B$ by $|B|$ entry by entry at the outset would lose the operator spectral-gap control. A chain of length one is a matrix entry, whose absolute value is at most $C/n$. For a chain of length $\ell\ge2$, first sum its internal labels. Its contraction is an entry of an alternating product of $B,B^{\mathsf T}$. The Euclidean norms of the row or column vectors at the ends are at most $C/\sqrt n$, and the operator norms of the intervening factors are at most $q$. Thus the absolute value of the contraction is at most

$$
\frac{C^2}{n}q^{\ell-2}.
$$

Summing over lengths with weight $R$ bounds the total activity of each chain by $W/n$. Summing the labels of the $b$ high-degree vertices contributes at most $n^b$. Hence

$$
\|C_j\|_R\le n^{-j}
\sum_{b=1}^{2j}U_{j,b}W^{b+j}.
$$

The number of degree compositions is $\binom{2j-1}{b-1}\le4^j$: write $d_i=3+x_i$, so that $\sum_i x_i=2j-b$. In addition, $\prod_i d_i^{-1}\le3^{-b}$, and the number of half-edge pairings is at most $(6j)^{b+j}$. Therefore

$$
\sum_{b=1}^{2j}U_{j,b}W^{b+j}
\le(24jW)^j
\sum_{b=1}^{2j}\frac{(4jW)^b}{b!}.
$$

Taking $\theta=1/(2W)\le1/2$ gives

$$
\sum_{b=0}^{2j}\frac{(4jW)^b}{b!}
\le\theta^{-2j}\exp(4jW\theta)
=(2\mathrm e W)^{2j}.
$$

Thus the activity is at most $(96\mathrm e^2W^3j)^j\le(710W^3j)^j$. For the last inequality, use $\mathrm e<87/32$, obtained by summing the exponential series through degree six and bounding its tail by $8/(7\cdot7!)$.

For $j=1$ only $b=1,2$ are possible. The compensation formula gives, respectively,

$$
U_{1,1}=\frac32,\qquad U_{1,2}=\frac{10}{3}.
$$

Combining this with the chain bound gives $\|C_1\|_R\le T_1/n$.


Compressing one degree-two vertex removes one vertex and one edge, so $h-v$ is unchanged. The compressed graph satisfies

$$
2e=\sum_{i=1}^bd_i,\quad e-b=j,\quad
2j=\sum_{i=1}^b(d_i-2)\ge b,
$$

Consequently $b\le2j$ and $e=b+j\le3j$. The numbers of temporary decorations and original edge labels cancel against the Möbius weights exactly as follows:

$$
\frac1{h!}\cdot\frac{h!}{b!\prod_i d_i!}\cdot\prod_i(d_i-1)!
=\frac1{b!}\prod_i\frac{(d_i-1)!}{d_i!}
=\frac1{b!\prod_i d_i}.
$$

For $2e$ half-edges, the number of pairings follows from $p_{2e}=(2e-1)p_{2e-2}$ and $p_0=1$:

$$
p_{2e}=(2e-1)(2e-3)\cdots1=\frac{(2e)!}{2^ee!}.
$$

There are $2^b$ color assignments. Ignoring compatibility restrictions on colors and chain lengths therefore gives $U_{j,b}$. A chain of length one has contraction $B_{ij}$. For length $\ell\ge2$, write the contraction as $r^{\mathsf T}M_1\cdots M_{\ell-2}c$, where $r,c$ are rows or columns of $B$. Then

$$
\|r\|_2^2,\|c\|_2^2\le n(C/n)^2=C^2/n,
$$

$$
|r^{\mathsf T}M_1\cdots M_{\ell-2}c|
\le\|r\|_2\prod_a\|M_a\|_{\rm op}\|c\|_2
\le(C^2/n)q^{\ell-2}.
$$

Weighting by length gives

$$
R\frac Cn+\sum_{\ell=2}^{\infty}R^\ell\frac{C^2}nq^{\ell-2}
=\frac1n\left(CR+\frac{C^2R^2}{1-Rq}\right)\le W/n.
$$

The $b$ remaining vertices have at most $n^b$ numerical labelings, giving $n^b(W/n)^e=n^{-j}W^{b+j}$. Summing the internal chain indices preserves the factor $q^{\ell-2}$.

To count degree compositions, put $x_i=d_i-3\ge0$. Then $\sum_ix_i=2j-b$, so

$$
\#\{(d_1,\ldots,d_b)\}=\binom{(2j-b)+b-1}{b-1}
=\binom{2j-1}{b-1}\le2^{2j-1}\le4^j.
$$

Moreover, $\prod_i1/d_i\le3^{-b}$ and the number of pairings is at most $(2e)^e\le(6j)^{b+j}$. Thus

$$
\begin{aligned}
U_{j,b}W^{b+j}
&\le\frac{2^b}{b!}(6j)^{b+j}4^j3^{-b}W^{b+j}\\
&=(24jW)^j\frac{(4jW)^b}{b!}.
\end{aligned}
$$

If $0<\theta\le1$ and $b\le2j$, then $\theta^b\ge\theta^{2j}$. Hence

$$
\sum_{b=0}^{2j}\frac{(4jW)^b}{b!}
\le\theta^{-2j}\sum_{b=0}^{\infty}\frac{(4jW\theta)^b}{b!}
=\theta^{-2j}e^{4jW\theta}.
$$

Taking $\theta=1/(2W)$ gives $(2W)^{2j}e^{2j}$. Multiplication by $(24jW)^j$ yields $(96e^2W^3j)^j$. The numerical estimate follows from

$$
e<\sum_{h=0}^6\frac1{h!}+\frac1{7!}\sum_{r=0}^{\infty}8^{-r}
=\frac{1957}{720}+\frac1{4410}<\frac{87}{32},
$$

$$
96(87/32)^2=\frac{22707}{32}=709.59375<710.
$$

When $j=1$, $b=1,e=2,d_1=4$. Thus

$$
U_{1,1}=\frac2{1!}\frac{4!}{2^2\,2!}\frac14=\frac32.
$$

When $b=2,e=3$, the only degree sequence is $(3,3)$. Hence

$$
U_{1,2}=\frac{2^2}{2!}\frac{6!}{2^3\,3!}\frac1{3\cdot3}=\frac{10}{3}.
$$

This gives $T_1=(3/2)W^2+(10/3)W^3$ term by term.


Fix a compressed core and assign numerical labels to its $b$ remaining high-degree vertices. Its $e$ compressed edges have internal structural vertex sets $V_1,\ldots,V_e$, respectively; these sets are pairwise disjoint. Numerical labels may coincide, but each structural vertex has its own independent summation variable. The distributive law for finite sums therefore gives

$$
\sum_{\text{all internal labels}}\prod_{r=1}^e
\left(\prod_{a\in\mathrm{chain}_r}B_{i_aj_a}\right)
=\prod_{r=1}^e\left[
\sum_{\text{internal labels of chain }r\text{}}
\prod_{a\in\mathrm{chain}_r}B_{i_aj_a}\right].
$$

Each bracket is a single entry of an alternating matrix product; only now do we take its absolute value. Summation over positive chain lengths also separates into $e$ geometric series. With the high-degree labels fixed, the total absolute activity is thus at most $(W/n)^e$. Summing over the $n^b$ choices of high-degree labels then gives

$$
n^b(W/n)^e=W^en^{b-e}=W^{b+j}n^{-j}.
$$

The internal vertex sets of the chains are disjoint, so their summation variables are independent; numerical labels may still coincide.


When $j=1,b=1$, there is one degree-four vertex with four half-edges. The only pairings are

$$
(12)(34),\quad(13)(24),\quad(14)(23).
$$

Each pairing gives two loops. There are two colors and the compensation denominator is $b!d_1=4$, giving a total of $2\cdot3/4=3/2$.

When $j=1,b=2$, both vertices have degree three. Half-edge pairings fall into two classes. If all three edges join the vertices, there are $3!=6$ pairings. If each vertex has one loop and the remaining two half-edges form an edge, there are $3\cdot3=9$ pairings. The two counts sum to fifteen. There are four vertex-color assignments and the compensation denominator is $2!\cdot3\cdot3=18$. Therefore

$$
\frac4{18}(6+9)=\frac{10}{3}.
$$

Dropping the color and length compatibility conditions gives an upper bound. The two cases give the two terms of $T_1$. $\square$

### 3.4 A linear coefficient window and factorial restoration

The activity bound [in (3.2)](#eq-core-activity) is useful when $j/n$ is small. Take

$$
\alpha=\min\left\{\frac14,\frac1{16D},\frac{\log\sigma}{2}\right\},
\qquad M=\lfloor\alpha n\rfloor.
$$

and put $v_j=(Dj/n)^j$. When $j+1\le M$,

$$
\frac{v_{j+1}}{v_j}
=\frac{D(j+1)}n\left(1+\frac1j\right)^j
\le\frac{\mathrm e D(j+1)}n
\le3D\alpha<\frac12.
$$

Hence, for $n\ge4/\alpha$,

$$
\sum_{j=2}^{M}v_j\le2v_2=\frac{8D^2}{n^2}.
$$

In the formal core identity, contributions of degree at most $M$ can come only from excess $j\le M$. Combining nonnegativity of the coefficients of $G$, the activity lemma, and the convolution inequality for weighted coefficient sums gives

$$
\sum_{k=0}^{M}|F_k-[t^k]G|R^k
\le\mathcal G_{C,q}(R)\left(\frac{T_1}n+\frac{8D^2}{n^2}\right).
$$

This estimate concerns only coefficients of degree at most $M$.

Write $g_k=[t^k]G$ and, for $0\le k\le M$, put $r_k=n^k/(n)_k$. Since $\alpha\le1/4$,

$$
\log r_k
=\sum_{\ell=0}^{k-1}-\log(1-\ell/n)
\le\frac{k(k-1)}{2n(1-\alpha)}
\le\frac{k^2}n
\le\alpha k.
$$

The condition $\alpha\le(\log\sigma)/2$ implies $r_k\le\sigma^k$. Moreover,

$$
0\le r_k-1
\le\frac{k(k-1)}{2n(1-\alpha)}r_k.
$$

Since $a_k=r_kF_k$, we can decompose

$$
a_k-g_k=r_k(F_k-g_k)+(r_k-1)g_k.
$$

The preceding $R$-weighted estimate bounds the first part. For the second part we use the second moment of the Gaussian coefficients:

$$
\sum_{k\ge0}k(k-1)g_k\sigma^k
=\left((t\partial_t)^2-t\partial_t\right)G(t)\big|_{t=\sigma}.
$$

Put $a_i=\sigma^2s_i^2$. Differentiating $G(t)=\prod_i(1-t^2s_i^2)^{-1/2}$ gives

$$
\frac{\left((t\partial_t)^2-t\partial_t\right)G(t)}{G(t)}
\bigg|_{t=\sigma}
=\left(\sum_i\frac{a_i}{1-a_i}\right)^2
+\sum_i\frac{a_i(1+a_i)}{(1-a_i)^2}.
$$

Define

$$
u_\sigma=\frac{\sigma^2C^2}{1-\sigma^2q^2},
\qquad
v_\sigma=\frac{\sigma^2C^2(1+\sigma^2q^2)}
{(1-\sigma^2q^2)^2},
$$

$$
K_G=\frac{\mathcal G_{C,q}(\sigma)}{2(1-\alpha)}
\left(u_\sigma^2+v_\sigma\right).
$$

The two terms in the derivative formula are at most $u_\sigma^2$ and $v_\sigma$, respectively. Therefore,

$$
\sum_{k=0}^{M}(r_k-1)g_k\le K_G/n.
$$

This gives the first two terms in the error bound.


Since $e<3$ and $\alpha\le1/(16D)$,

$$
\frac{v_{j+1}}{v_j}\le3D\alpha\le3/16<1/2,
\quad
\sum_{j=2}^Mv_j\le v_2\sum_{r=0}^{\infty}2^{-r}
=2(2D/n)^2=8D^2/n^2.
$$

If $H(t)=\sum h_kt^k$ and $K(t)=\sum k_kt^k$, then

$$
\sum_{r=0}^M|[t^r](HK)|R^r
\le\sum_{a,b\ge0}|h_a||k_b|R^{a+b}
=\|H\|_R\|K\|_R.
$$

In coefficients with $r\le M$, only $j\le M$ are needed. We therefore truncate to a finite excess sum before applying this inequality; we do not evaluate $\sum_{j\ge1}C_j(R)$.

The integral estimate for factorial restoration is

$$
-\log(1-u)=\int_0^u\frac{dv}{1-v}\le\frac{u}{1-\alpha}
\quad(0\le u\le\alpha).
$$

Summing over $u=0,1/n,\ldots,(k-1)/n$ gives

$$
\log r_k\le\frac{k(k-1)}{2n(1-\alpha)}\le k^2/n\le\alpha k,
\quad r_k\le e^{\alpha k}\le\sigma^k.
$$

The inequality $e^x-1\le xe^x$ gives $r_k-1\le[k(k-1)/(2n(1-\alpha))]r_k$. Consequently,

$$
\begin{aligned}
\sum_{k=0}^M|a_k-g_k|
&\le\sum_{k=0}^Mr_k|F_k-g_k|+\sum_{k=0}^M(r_k-1)g_k\\
&\le\sum_{k=0}^MR^k|F_k-g_k|
+\frac1{2n(1-\alpha)}\sum_{k\ge0}k(k-1)g_k\sigma^k.
\end{aligned}
$$

Put $D_t=t\partial_t$ and $a_i(t)=t^2s_i^2$. Successive differentiation gives

$$
\begin{aligned}
D_t\log G&=\sum_i\frac{a_i}{1-a_i}=:A(t),\\
D_tA&=\sum_i\frac{2a_i}{(1-a_i)^2},\\
D_tG&=GA,\\
D_t^2G&=G\left[A^2+\sum_i\frac{2a_i}{(1-a_i)^2}\right],\\
\frac{(D_t^2-D_t)G}{G}
&=A^2+\sum_i\left[\frac{2a_i}{(1-a_i)^2}-\frac{a_i}{1-a_i}\right]\\
&=A^2+\sum_i\frac{a_i(1+a_i)}{(1-a_i)^2}.
\end{aligned}
$$

At $t=\sigma$ we have $a_i\le\sigma^2q^2$, so

$$
A(\sigma)\le\frac{\sigma^2C^2}{1-\sigma^2q^2}=u_\sigma,
\quad
\sum_i\frac{a_i(1+a_i)}{(1-a_i)^2}
\le\frac{\sigma^2C^2(1+\sigma^2q^2)}{(1-\sigma^2q^2)^2}=v_\sigma.
$$

Together with $G(\sigma)\le\mathcal G_{C,q}(\sigma)$, this gives exactly $K_G/n$.


Define the projection $\mathcal P_M\sum_kh_kt^k=\sum_{k=0}^Mh_kt^k$. A nonempty core of excess $j$ has at least $j+1$ original edges, so in degrees at most $M$ no $j>M$ occurs. Thus, exactly,

$$
\mathcal P_M(F-G)=\mathcal P_M\left(G\sum_{j=1}^MC_j\right).
$$

The right-hand side involves only finitely many core series, so its weighted coefficient norm is legitimate. The triangle inequality and the convolution bound give

$$
\begin{aligned}
\sum_{k=0}^M|F_k-g_k|R^k
&=\|\mathcal P_M(F-G)\|_R\\
&\le\left\|G\sum_{j=1}^MC_j\right\|_R\\
&\le\|G\|_R\sum_{j=1}^M\|C_j\|_R\\
&\le\mathcal G_{C,q}(R)\left[T_1/n+\sum_{j=2}^M(Dj/n)^j\right]\\
&\le\mathcal G_{C,q}(R)(T_1/n+8D^2/n^2).
\end{aligned}
$$

Only finitely many weighted norms of $C_j$ occur. On restoring $a_k$, the first part satisfies

$$
\sum_{k=0}^Mr_k|F_k-g_k|
\le\sum_{k=0}^M\sigma^k|F_k-g_k|
\le\sum_{k=0}^MR^k|F_k-g_k|.
$$

The second part, $(r_k-1)g_k$, is bounded by the Gaussian derivative moment above.

### 3.5 Controlling the remaining coefficients

We have controlled coefficients through degree $M$, where $M$ is proportional to $n$. To estimate higher coefficients by Cauchy's inequality, it suffices, on the fixed circle $|t|=R>1$, to bound $f$ by $\exp(O(\sqrt n))$. The next two lemmas give this bound while retaining the normalization factor $n!/n^n$.


**Lemma 3.3 (Permanent polarization).**

For a complex square matrix $Z$, its singular values are the nonnegative square roots of the eigenvalues of $Z^*Z$, and the corresponding norms follow the conventions above. Write $|Z|=(Z^*Z)^{1/2}$ for its operator absolute value, taking the Hermitian positive semidefinite square root, rather than the absolute values of individual entries. For a Hermitian matrix, $H\ge0$ means that $x^*Hx\ge0$ holds for every vector. Then

$$
|\operatorname{per}Z|
\le\sqrt{\operatorname{per}|Z|\,
\operatorname{per}|Z^*|}.
$$


**Proof.**

On complex vector spaces we use the inner product $\langle x,y\rangle=x^*y$. In $(\mathbb C^n)^{\otimes n}$, put

$$
\xi=(n!)^{-1/2}
\sum_{\pi\in \mathfrak S_n}
e_{\pi(1)}\otimes\cdots\otimes e_{\pi(n)}.
$$

Then $\|\xi\|=1$ and $\langle\xi,Z^{\otimes n}\xi\rangle=\operatorname{per}Z$. Take the polar decomposition $Z=U|Z|$. If $Z$ is singular, extend the partial isometry in its polar decomposition to a unitary matrix $U$. Write $T=|Z|^{\otimes n}$ and $V=U^{\otimes n}$. Applying Cauchy–Schwarz in the semi-inner product induced by the positive semidefinite operator $T$ gives

$$
|\langle\xi,VT\xi\rangle|
\le\sqrt{\langle V^*\xi,TV^*\xi\rangle
\langle\xi,T\xi\rangle}.
$$

The two factors are $\operatorname{per}(U|Z|U^*)=\operatorname{per}|Z^*|$ and $\operatorname{per}|Z|$, respectively. Both are nonnegative because they are diagonal matrix elements of positive semidefinite tensor powers. $\square$


**Lemma 3.4 (A positive semidefinite permanent bound).**

Let $n\ge1$, and let $H$ be an $n\times n$ Hermitian positive semidefinite matrix with eigenvalues $\lambda_1,\ldots,\lambda_n$. Then

$$
\operatorname{per}H\le\frac{n!}{n^n}h_n(\lambda_1,\ldots,\lambda_n),
$$

Here $h_n$ is the complete homogeneous symmetric polynomial of degree $n$, defined by

$$
h_n(\lambda_1,\ldots,\lambda_n)
=\sum_{\substack{k_1,\ldots,k_n\ge0\\k_1+\cdots+k_n=n}}
\prod_{i=1}^n\lambda_i^{k_i}.
$$

All $k_i$ are integers. Every zeroth power in this polynomial equals one, including, when $\lambda_i=0$, the expression $\lambda_i^0$. This notation is local to the present lemma. If $\lambda_1=1$ and $0\le\lambda_i<1$ for $i\ge2$, then

$$
\operatorname{per}H\le\frac{n!}{n^n}
\prod_{i=2}^n(1-\lambda_i)^{-1}.
$$


**Proof.**

Let $Z$ be a circularly symmetric complex Gaussian vector with covariance matrix $H$. The complex Wick formula gives $\operatorname{per}H=\mathbb E\prod_i|Z_i|^2$. Pointwise AM–GM bounds this product by $n^{-n}\|Z\|^{2n}$. After unitary diagonalization, $\|Z\|^2$ has the same distribution as $\sum_i\lambda_i|\zeta_i|^2$, where $\zeta_i$ are independent standard circularly symmetric complex Gaussian variables satisfying $\mathbb E|\zeta_i|^{2k}=k!$. Expanding the polynomial therefore gives

$$
\mathbb E\left(\sum_i\lambda_i|\zeta_i|^2\right)^n
=n!h_n(\lambda_1,\ldots,\lambda_n).
$$

Finally, $h_n(1,\lambda_2,\ldots,\lambda_n)$ is the sum of all monomials in $\lambda_2,\ldots,\lambda_n$ of total degree at most $n$. It is bounded by the product of the corresponding infinite geometric series. $\square$

The Gaussian identity and AM–GM comparison in Lemma 3.4 are the tools used by Han–Niles-Weed [3, arXiv v2, Lemmas 4.3–4.4] for positive semidefinite inputs. Lemma 3.3 connects them to the general matrices needed here.

Put $\beta=RC/(1-Rq)$ and write $P_n=J_n/n$ for the orthogonal projection onto the all-ones direction. In general, $u^\perp=\{v:u^*v=0\}$ denotes the orthogonal complement of the vector $u$. Double centering gives $P_nB=BP_n=0$. Consequently, on $|t|=R$,

$$
|P_n+tB|=P_n+R(B^{\mathsf T}B)^{1/2},
\qquad
|(P_n+tB)^*|=P_n+R(BB^{\mathsf T})^{1/2}.
$$

Both have eigenvalue $1$ in the all-ones direction and, on $\mathbf1^\perp$, eigenvalues $Rs_i$, including zero singular values when needed. Since $Rq<1$, the two lemmas and the exact identity $f(t)=(n^n/n!)\operatorname{per}(P_n+tB)$ give

$$
|f(t)|\le\prod_i(1-Rs_i)^{-1}
\le\exp\!\left(\frac{R}{1-Rq}\sum_i s_i\right)
\le\exp(\beta\sqrt n).
$$

The last step uses $\sum_i s_i\le\sqrt n\,\|B\|_{\mathrm F}\le C\sqrt n$. Cauchy's coefficient estimate therefore gives

$$
\sum_{k>M}|a_k|
\le\frac{R}{R-1}
\exp\!\left(\beta\sqrt n-\alpha n\log R\right).
$$

For the Gaussian tail, nonnegativity of the coefficients gives the slightly weaker but convenient bound

$$
\sum_{k>M}g_k
\le \mathcal G_{C,q}(\sigma)\sigma^{-M}
\le\sigma\mathcal G_{C,q}(\sigma)\exp\!\left(-\alpha n\log\sigma\right).
$$

Both tails decay exponentially in $n$. Combining them with the $O(n^{-1})$ estimate in the finite window proves Theorem 3.1.


For any $M$,

$$
\begin{aligned}
\langle\xi,M^{\otimes n}\xi\rangle
&=\frac1{n!}\sum_{\pi,\sigma\in \mathfrak S_n}\prod_{h=1}^nM_{\pi(h),\sigma(h)}\\
&=\frac1{n!}\sum_{\pi\in \mathfrak S_n}\sum_{\tau\in \mathfrak S_n}\prod_{i=1}^nM_{i,\tau(i)}
=\operatorname{per}M.
\end{aligned}
$$

Here $\tau=\sigma\circ\pi^{-1}$; for fixed $\pi$, $\sigma\mapsto\tau$ is a bijection. The $n!$ basis tensors are mutually orthogonal, so $\|\xi\|^2=(n!)^{-1}n!=1$. If $T\ge0$,

$$
|\langle a,Tb\rangle|^2
=|\langle T^{1/2}a,T^{1/2}b\rangle|^2
\le\langle a,Ta\rangle\langle b,Tb\rangle.
$$

Taking $a=V^*\xi,b=\xi$ and using $VTV^*=(U|Z|U^*)^{\otimes n}=|Z^*|^{\otimes n}$ gives Lemma 3.3.


A standard circularly symmetric complex variable $\zeta=x+iy$ has density $\pi^{-1}e^{-|z|^2}$. Integration in polar coordinates gives

$$
\begin{aligned}
\mathbb E|\zeta|^{2k}
&=\pi^{-1}\int_0^{2\pi}\!d\theta\int_0^{\infty}r^{2k}e^{-r^2}r\,dr\\
&=\int_0^{\infty}u^ke^{-u}\,du=k!.
\end{aligned}
$$

Writing $I_k=\int_0^\infty u^ke^{-u}\,du$, integration by parts gives $I_k=kI_{k-1}$ and $I_0=1$.

For integers $a,b\ge0$, polar integration gives the one-dimensional mixed moment

$$
\begin{aligned}
\mathbb E[\zeta^a(\overline\zeta)^b]
&=\frac1\pi\int_0^\infty r^{a+b+1}e^{-r^2}\,dr
\int_0^{2\pi}e^{i(a-b)\theta}\,d\theta\\
&=\begin{cases}a!,&a=b,\\0,&a\ne b.\end{cases}
\end{aligned}
$$

If $a\ne b$, the angular integral is $[e^{i(a-b)\theta}/(i(a-b))]_0^{2\pi}=0$. If $a=b$, the angular integral is $2\pi$; the substitution $u=r^2$ then gives $\int_0^\infty u^ae^{-u}\,du=a!$.

Let $\zeta_1,\ldots,\zeta_n$ be independent, and put $Z=L\zeta$ and $H=LL^*$. For index lists $\boldsymbol a,\boldsymbol b\in[n]^n$, the preceding identity and independence imply that the mixed moment is zero if some numerical index has different multiplicities in the two lists. If every multiplicity agrees and is $c_j$, the mixed moment is $\prod_jc_j!$. This is exactly the number of bijective pairings that match every position in the first list to a position of equal value in the second. Thus

$$
\mathbb E\prod_{i=1}^n\zeta_{a_i}\prod_{j=1}^n\overline\zeta_{b_j}
=\sum_{\sigma\in \mathfrak S_n}\prod_{i=1}^n\delta_{a_i,b_{\sigma(i)}}.
$$

Expanding the product and interchanging the finite sums gives

$$
\begin{aligned}
\mathbb E\prod_{i=1}^n|Z_i|^2
&=\sum_{\boldsymbol a,\boldsymbol b}
\prod_iL_{i,a_i}\prod_j\overline L_{j,b_j}
\sum_{\sigma\in \mathfrak S_n}\prod_i\delta_{a_i,b_{\sigma(i)}}\\
&=\sum_{\sigma\in \mathfrak S_n}\sum_{\boldsymbol a}
\prod_i L_{i,a_i}\overline L_{\sigma(i),a_i}\\
&=\sum_{\sigma\in \mathfrak S_n}\prod_i
\left(\sum_{a=1}^nL_{i,a}\overline L_{\sigma(i),a}\right)\\
&=\sum_{\sigma\in \mathfrak S_n}\prod_iH_{i,\sigma(i)}
=\operatorname{per}H.
\end{aligned}
$$

The second line uses $b_{\sigma(i)}=a_i$ to sum out all $b$ indices. The third line uses the independent summation of each $a_i$. The matrix $L$ may be singular: take $L=H^{1/2}$. Thus the proof includes positive semidefinite matrices with zero eigenvalues. The same second-moment calculation also determines the meaning of covariance: $\mathbb EZ_i\overline Z_j=H_{ij}$ and $\mathbb EZ_iZ_j=0$.

For every sample $|Z_i|^2\ge0$. AM–GM gives

$$
\prod_i|Z_i|^2\le\left(\frac{\sum_i|Z_i|^2}{n}\right)^n,
\qquad \operatorname{per}H\le n^{-n}\mathbb E\|Z\|_2^{2n}.
$$

A unitary transformation preserves $\|Z\|$. Applying the multinomial theorem term by term gives

$$
\begin{aligned}
\mathbb E\left(\sum_i\lambda_i|\zeta_i|^2\right)^n
&=\sum_{k_1+\cdots+k_n=n}\frac{n!}{\prod_i k_i!}
\prod_i\lambda_i^{k_i}\mathbb E|\zeta_i|^{2k_i}\\
&=n!\sum_{k_1+\cdots+k_n=n}\prod_i\lambda_i^{k_i}
=n!h_n(\lambda).
\end{aligned}
$$

If $\lambda_1=1$, eliminate the first variable using $k_1=n-\sum_{i\ge2}k_i$:

$$
h_n(1,\lambda_2,\ldots,\lambda_n)
=\sum_{\substack{k_2,\ldots,k_n\ge0\\\sum k_i\le n}}\prod_{i\ge2}\lambda_i^{k_i}
\le\prod_{i=2}^n\sum_{k_i=0}^{\infty}\lambda_i^{k_i}
=\prod_{i=2}^n(1-\lambda_i)^{-1}.
$$


Write $P=P_n$. Since $P^2=P$ and $PB=B^{\mathsf T}P=BP=PB^{\mathsf T}=0$,

$$
(P+tB)^*(P+tB)=P+R^2B^{\mathsf T}B
\quad(|t|=R).
$$

These two parts act on orthogonal subspaces, so the square root is $P+R(B^{\mathsf T}B)^{1/2}$. The two polarization factors have the same eigenvalues $1,Rs_1,\ldots$. The zero singular value corresponding to the all-ones direction may be omitted from the product because its factor is one. Define $A_R=\prod_i(1-Rs_i)^{-1}>0$. Take logarithms only of this positive upper bound, avoiding, when $f(t)=0$, the undefined expression $\log|f(t)|$. Retaining the normalization exactly gives

$$
\begin{aligned}
|f(t)|&=\frac{n^n}{n!}|\operatorname{per}(P+tB)|
\le\prod_i(1-Rs_i)^{-1},\\
\log A_R&=-\sum_i\log(1-Rs_i)\le\sum_i\frac{Rs_i}{1-Rs_i}
\le\frac R{1-Rq}\sum_i s_i
\le\frac{RC}{1-Rq}\sqrt n=\beta\sqrt n.
\end{aligned}
$$

Hence $|f(t)|\le A_R\le e^{\beta\sqrt n}$, including the case $f(t)=0$. Zeros are possible for admissible inputs: take $n=3$ and

$$
E=\begin{pmatrix}0&1&-1\\-1&0&1\\1&-1&0\end{pmatrix},\qquad B=E/3.
$$

This matrix is doubly centered, and

$$
B^{\mathsf T}B=\frac19(3I_3-J_3).
$$

The eigenvalue of $J_3$ is three in the all-ones direction and zero on the zero-sum subspace. The eigenvalues of $B^{\mathsf T}B$ are therefore $0,1/3,1/3$, giving $\|B\|_{\rm op}=1/\sqrt3\le3/5=:q<1$. The six permanent terms come from the identity permutation, three transpositions, and two three-cycles. Hence

$$
\begin{aligned}
6f(t)&=1+3(1-t^2)+(1+t)^3+(1-t)^3\\
&=1+3-3t^2+2+6t^2=6+3t^2,\\
f(i\sqrt2)&=1+(i\sqrt2)^2/2=0.
\end{aligned}
$$

Taking $R=\sqrt2<5/3=1/q$ and $\sigma=(1+\sqrt2)/2$ gives a zero of $f$ on the chosen circle $|t|=R$. Thus $\log|f(t)|$ is not defined everywhere on this circle.

Cauchy's coefficient formula on the circle $t=Re^{i\theta}$ is

$$
a_k=\frac1{2\pi R^k}\int_0^{2\pi}f(Re^{i\theta})e^{-ik\theta}\,d\theta,
\qquad |a_k|\le e^{\beta\sqrt n}R^{-k}.
$$

Thus

$$
\sum_{k>M}|a_k|\le e^{\beta\sqrt n}\frac{R^{-M}}{R-1}
\le\frac R{R-1}e^{\beta\sqrt n-\alpha n\log R}.
$$

Here $M\ge\alpha n-1$. The coefficients on the Gaussian side are nonnegative, so

$$
\sum_{k>M}g_k\le\sigma^{-M}\sum_{k>M}g_k\sigma^k
\le\sigma\mathcal G_{C,q}(\sigma)e^{-\alpha n\log\sigma}.
$$

Put $c=\alpha\log R>0$. For $n\ge(2\beta/c)^2$, we have $\beta\sqrt n-cn\le-cn/2$. Since $ne^{-cn/2}\to0$, the first tail is $o(n^{-1})$, and the same argument applies to the second. Here we use the linear growth of $M=\lfloor\alpha n\rfloor$.

### 3.6 Combining the error bounds


**Proposition 3.5 (An explicit error bound).**

For every integer $n\ge4/\alpha$,

$$
\begin{aligned}
|f(1)-G(1)|
&\le \frac{\mathcal G_{C,q}(R)T_1+K_G}{n}
+\frac{8\mathcal G_{C,q}(R)D^2}{n^2}\\
&\quad+\frac{R}{R-1}\exp\!\left(\beta\sqrt n-\alpha n\log R\right)\\
&\quad+\sigma\mathcal G_{C,q}(\sigma)\exp\!\left(-\alpha n\log\sigma\right).
\end{aligned}
$$


The first two terms come from the coefficient window and factorial-restoration errors in Section 3.4. The last two come from the tail bounds in Section 3.5. Both exponential terms are $o(n^{-1})$, giving the uniform error rate in Theorem 3.1.


Put $c_1=\alpha\log R>0$, $c_2=\alpha\log\sigma>0$, and $\beta=RC/(1-Rq)\ge0$. For

$$
n\ge N_1:=\max\{1,(2\beta/c_1)^2\},
$$

we have

$$
\sqrt n\ge2\beta/c_1
\ \Longrightarrow\ {}
\beta\sqrt n\le(c_1/2)n
\ \Longrightarrow\ {}
\beta\sqrt n-c_1n\le-c_1n/2.
$$

For any fixed $c>0$, the function $u(x)=xe^{-cx}$ satisfies, on $x\ge0$,

$$
u'(x)=e^{-cx}(1-cx),\qquad
\max_{x\ge0}u(x)=u(1/c)=1/(ec).
$$

Thus, for $n\ge N_1$,

$$
\frac R{R-1}\exp(\beta\sqrt n-c_1n)
\le\frac R{R-1}e^{-c_1n/2}
\le\frac{2R}{ec_1(R-1)}\frac1n,
$$

$$
\sigma\mathcal G_{C,q}(\sigma)e^{-c_2n}
\le\frac{\sigma\mathcal G_{C,q}(\sigma)}{ec_2}\frac1n.
$$

If we also require $n\ge4/\alpha$, the right-hand side of Proposition 3.5 is at most

$$
\frac1n\left[
\mathcal G_{C,q}(R)T_1+K_G+8\mathcal G_{C,q}(R)D^2
+\frac{2R}{ec_1(R-1)}
+\frac{\sigma\mathcal G_{C,q}(\sigma)}{ec_2}\right].
$$

Every quantity in brackets depends only on $C,q,R,\sigma$ fixed in advance, and not on the matrix being estimated. To obtain one constant valid for all $n\ge1$, the finitely many smaller dimensions must also be covered. From $|1+E_{ij}|\le1+C$,

$$
|f(1)|\le\frac1{n!}\sum_{\pi\in \mathfrak S_n}(1+C)^n=(1+C)^n,
\qquad 1\le G(1)\le\mathcal G_{C,q}(1).
$$

Let $N=\lceil\max\{N_1,4/\alpha\}\rceil$ and enlarge the uniform constant to at least

$$
\max_{1\le n<N}n\left[(1+C)^n+\mathcal G_{C,q}(1)\right]
$$

covers the remaining orders as well; the maximum of an empty set is taken to be zero. $\square$

**Quantifying the existing permanent proof.**

Divoux and Wang [12, Proposition 3.1] prove a uniform permanent approximation with relative error $o(1)$ for nonnegative doubly stochastic matrices. In the nonnegative setting used in our counting argument, their proof can be refined to give an $O(N^{-1})$ error. This rate is a refinement of their estimates, rather than the statement of their proposition. Theorem 3.1 here allows an arbitrary real doubly centered matrix $E$, without requiring $J+E$ to be nonnegative. We retain that formulation and its detailed proof; the two theorem statements do not have identical hypotheses. The difference in stated hypotheses is not a claim of priority or of a new range beyond McCullagh [5, §4.1]; see also Section 3 of the main paper.

The refinement concerns two estimates in [12, Sections 3.2–3.3]. Their finite coefficient sum is already bounded by

$$
\sum_{1\le E\le K\sqrt N}
\frac{(cE/N)^{\lceil E/3\rceil}}{1-cE/N}.
$$

Put $\eta_N=cK/\sqrt N$. For sufficiently large $N$, this is at most

$$
\frac{c}{N(1-\eta_N)}
\sum_{E\ge1}E\eta_N^{\lceil E/3\rceil-1}
=O(N^{-1}).
$$

The remaining coefficients satisfy the exponential tail estimate in their proof. In the subsequent Gamma average, $G\sim\Gamma(N+1,1)$ and $Z=N/G$ satisfy

$$
\mathbb E(Z-1)=0,\qquad
\mathbb E(Z-1)^2=\frac1{N-1}.
$$

For $\Delta(s)=\det(I-s^2B^TB)^{-1/2}$, the fixed operator-norm gap and Frobenius-norm bound give a uniform bound on $\Delta''$ over the fixed window used there. A second-order Taylor expansion, together with their estimate outside the window, gives an $O(N^{-1})$ error. Thus this permanent error in the nonnegative doubly stochastic case can be obtained by refining the earlier proof. The global path estimate still requires control of the errors from scaling, degree imbalance, and exceptional vertices.

<!-- Extraction from 08_detailed_proof.en.md; block=technical-scaling; raw_block_sha256=352940c54d4dcceb929cbd342fe1f4b11da1e120b860e4b90f83a384237ae7b9; copy_block_sha256=4dfe201c1d1b4c72350025bd924dc61a0a80f7e0e3723ec5776e376ab2cde3f7; normalization=trailing-tex-control-space-empty-group-v1; transformations=control-space:0,edit-7:1,edit-8:2,maximum-score:46. -->

<a id="technical-scaling"></a>

## 4. Diagonal scaling and nonprincipal submatrices

This section returns to the graph notation: $s=S\mathbf1$ is the score vector, $a=s/(n-1)$, and we assume $n\ge2$. Theorem 3.1 applies to matrices whose row and column sums agree after scalar normalization. Tournament matrices generally have different row and column sums: if $C=2A/(n-1)$, then

$$
C\mathbf1=\mathbf1+a,\qquad C^{\mathsf T}\mathbf1=\mathbf1-a.
$$

We must therefore control the permanent and its Gaussian factor while correcting the marginals. We first construct a local diagonal scaling and estimate its total logarithmic cost. We then compare Gram matrices to control the effects of deleting rows and columns. Finally, paired score corrections bring tournament submatrices within the hypotheses of the local theorem, thereby proving Lemma 4.4.

For a general order $p\ge1$, retain $P_p=J_p/p=\mathbf1_p\mathbf1_p^{\mathsf T}/p$ and set $\Pi_p=I_p-P_p$, the orthogonal projection that removes the all-ones direction. The total mass of a matrix is $\mathfrak m(X)=\sum_{i,j}X_{ij}$. A doubly stochastic matrix is a square matrix with nonnegative entries and every row sum and column sum equal to one. Constants in this section are uniform once the density and centered-kernel spectral-gap parameters have been fixed.


**Definition 4.1 (Marginal errors).**

For any real $p\times p$ matrix $Q$ ($p\ge1$; its mass need not yet equal $p$), define

$$
\alpha(Q)=Q\mathbf1_p-\mathbf1_p,\qquad
\beta(Q)=Q^{\mathsf T}\mathbf1_p-\mathbf1_p,
$$

$$
g(Q)=(\alpha(Q),\beta(Q))\in\mathbb R^{2p},\qquad
\varepsilon(Q)=\|g(Q)\|_\infty,
$$

$$
\|g(Q)\|_2^2=\sum_i\alpha(Q)_i^2+\sum_j\beta(Q)_j^2.
$$

Likewise, $(x,y)$ denotes concatenation of two vectors, so $\|(x,y)\|_\infty=\max(\|x\|_\infty,\|y\|_\infty)$. When the mass is $p$, the errors on each side sum to zero. When the mass differs from $p$, these definitions still apply, but normalization is required before invoking Lemma 4.1.


Write $n$ for the full order and $m=n-t$ for the retained order. In Lemmas 4.1 and 4.2, $p$ denotes a general matrix order; in the application we take $p=m$. The matrices $C,C^{\prime},\widehat C$ have order $n$, while $X,\widetilde X,B_X,Z$ have order $m$. Their total masses are

$$
\mathfrak m(C')=n+\nu,\quad \mathfrak m(\widehat C)=n,\quad
\mathfrak m(X)=m+\kappa,\quad
\mathfrak m(\widetilde X)=\mathfrak m(B_X)=m.
$$

Here $Z=\Pi_m[(S-I)/(n-1)][R,T]\Pi_m$, and $B_X$ is the scaled doubly stochastic matrix. In Theorem 3.1, the perturbation is $mB_X-J_m$ and its normalization is $B_X-P_m$.

### 4.1 Local Scaling and Its Cost

We seek a matrix of the form $B_{ij}=X_{ij}e^{x_i+y_j}$ with every row sum and column sum equal to one. Replacing $(x,y)$ by $(x+c\mathbf1,y-c\mathbf1)$ leaves $B$ unchanged; the condition $\sum x_i=\sum y_j$ removes this one-dimensional freedom. The singular-value spectral gap controls the linearized balancing equations on the remaining subspace. The entry bound further provides dimension-independent control in the infinity norm, making a contraction argument applicable.


**Lemma 4.1 (Local scaling).**

Let $p\ge1$, and let $X$ have total mass $p$ and be a real $p\times p$ matrix. Write

$$
\alpha=X\mathbf 1_p-\mathbf 1_p,\qquad \beta=X^{\mathsf T}\mathbf 1_p-\mathbf 1_p,\qquad \varepsilon=\max(\|\alpha\|_\infty,\|\beta\|_\infty).
$$

Assume $|X_{ij}|\le C/p$, that the sum of absolute values in each row and each column is at most $2$, and that

$$
X_0=X-\frac{\alpha\mathbf 1_p^{\mathsf T}+\mathbf 1_p\beta^{\mathsf T}}p,\qquad E=X_0-P_p
$$

satisfies $|E_{ij}|\le C_0/p$ and $\|E\|_{\rm op}\le q<1$, where $C,C_0\ge0$ and $0\le q<1$ are fixed parameters. Define

$$
L_0=\frac32+C_0+\frac{C_0^2}{1-q},
$$

$$
\varepsilon_0=\min\left\{\frac1{256L_0^2},\frac{1-q}{2(32L_0+2)}\right\}.
$$

If $\varepsilon\le\varepsilon_0$, the condition $\sum_i x_i=\sum_j y_j$ is satisfied by finite real potential vectors $x,y$ such that every row sum and column sum of $B=\operatorname{diag}(e^x)X\operatorname{diag}(e^y)$ equals $1$. Moreover,

$$
\|(x,y)\|_\infty\le4L_0\varepsilon,\qquad |B_{ij}|\le2C/p,\qquad \|B-P_p\|_{\rm op}\le(1+q)/2.
$$

If $X$ is entrywise nonnegative, then $B$ is doubly stochastic and has the same zero pattern as $X$.


**Proof.**

The entries of each marginal-error vector sum to zero. Consequently, every row sum and column sum of $X_0$ is $1$, and $E$ is doubly centered. Set $u=(\mathbf 1_p,-\mathbf 1_p)$ and $N=uu^{\mathsf T}/(2p)$. The balanced Hessian $\mathsf H_0$ has diagonal blocks $I$ and off-diagonal blocks $X_0,X_0^{\mathsf T}$, respectively. Its gauge-fixed inverse can be written explicitly. Put

$$
R_L=(I-EE^{\mathsf T})^{-1},\qquad R_R=(I-E^{\mathsf T}E)^{-1},\qquad O=ER_R.
$$

The four blocks of $(\mathsf H_0+N)^{-1}$ are then

$$
M_{LL}=R_L-P_p/4,\qquad M_{RR}=R_R-P_p/4,
$$

$$
M_{LR}=-O-P_p/4,\qquad M_{RL}=-O^{\mathsf T}-P_p/4.
$$

Indeed, on the common constant direction, the inverse eigenvalue is $1/2$; on the gauge direction, it is $1$; and on the two zero-sum subspaces, the usual block inverse applies. The dense entry bound gives

$$
|(R_L-I)_{ij}|,\ |(R_R-I)_{ij}|\le\frac{C_0^2}{p(1-q^2)},
$$

$$
|O_{ij}|\le\frac{C_0}{p}+\frac{C_0^2q}{p(1-q^2)}.
$$

For the last estimate, decompose $O=E+EE^{\mathsf T}ER_R$ and control the two-norms of the row and column at the two ends. The vector one-norm is

$$
\|x\|_1=\sum_i|x_i|,
$$

The corresponding induced matrix one-norm and infinity norm are $\|M\|_{1\to1}=\max_j\sum_i|M_{ij}|$ and $\|M\|_{\infty\to\infty}=\max_i\sum_j|M_{ij}|$, respectively. Both induced norms of the inverse above are therefore at most $L_0$.

Let $\mathsf H_X$ have diagonal blocks $\operatorname{diag}(X\mathbf 1_p)$ and $\operatorname{diag}(X^{\mathsf T}\mathbf 1_p)$, respectively, and off-diagonal blocks $X,X^{\mathsf T}$. Both induced norms of the difference $\mathsf H_X-\mathsf H_0$ are at most $3\varepsilon$. The Neumann series shows that both induced norms of $(\mathsf H_X+N)^{-1}$ are at most $2L_0$.

Write $z=(x,y)$ and $g=(\alpha,\beta)$. The balancing equation is

$$
0=g+\mathsf H_Xz+\mathcal N_X(z).
$$

Here $\mathcal N_X(z)$ is the concatenation of the row sums and column sums of $X_{ij}(e^{x_i+y_j}-1-x_i-y_j)$. On the ball $\|z\|_\infty\le R\le1/4$, the absolute marginal bounds give

$$
\|\mathcal N_X(z)\|_\infty\le8R^2,\qquad \|D\mathcal N_X(z)\|_{\infty\to\infty}\le16R.
$$

All these vectors are orthogonal to $u$. On the gauge subspace $u^\perp$, consider

$$
\mathcal T(z)=-(\mathsf H_X+N)^{-1}(g+\mathcal N_X(z)).
$$

Take $R=4L_0\varepsilon$. The norm of the image of the origin is at most $R/2$, and the Lipschitz constant is at most $128L_0^2\varepsilon\le1/2$. Thus the map preserves the gauge ball and is a contraction, yielding the required finite potential vectors. If $\varepsilon=0$, simply take $z=0$.

Finally, $R\le1/4$ gives the entry bound. The assumptions on absolute row and column sums imply

$$
\|B-X\|_{1\to1},\ \|B-X\|_{\infty\to\infty}\le32L_0\varepsilon.
$$

We also have $\|X-X_0\|_{\rm op}\le2\varepsilon$, so the second condition in $\varepsilon_0$ establishes the spectral gap of the centered kernel. Positive diagonal factors preserve both nonnegativity and the zero pattern. This proves the lemma.

Finding a balanced point alone does not suffice to estimate the permanent: restoring the diagonal factors requires multiplying the permanent by $\exp(-\sum x_i-\sum y_j)$. The next lemma controls this total cost and also gives the Frobenius displacement bound needed to compare Gaussian factors.


**Lemma 4.2 (Displacement and capacity).**

Under the preceding hypotheses, assume in addition that $X\ge0$. Let $\theta_X=\sum_i x_i+\sum_j y_j$ denote the total scaling potential. There is a constant depending only on the fixed density and spectral-gap parameters such that

$$
\|(x,y)\|_2\le K\|(\alpha,\beta)\|_2,\qquad \|B-X\|_F\le\frac K{\sqrt p}\|(\alpha,\beta)\|_2,
$$

$$
0\le\theta_X\le K\|(\alpha,\beta)\|_2^2.
$$

**General mass.** For a nonnegative matrix $X$ of arbitrary positive total mass, suppose that $\widetilde X=pX/\mathfrak m(X)$ satisfies the hypotheses of Lemma 4.1, and apply the preceding conclusions to $\widetilde X$. If $B$ is its scaling, the following exact identities hold:

$$
\theta_X=\theta_{\widetilde X}+p\log\frac p{\mathfrak m(X)},\qquad \operatorname{per}X=e^{-\theta_X}\operatorname{per}B.
$$

In particular, if $\kappa=\mathfrak m(X)-p$, then $\operatorname{per}X\le e^\kappa\operatorname{per}B$. When the mass differs from $p$, $\theta_X$ itself need not be nonnegative.


**Proof.**

The convex potential is

$$
\Phi_X(x,y)=\sum_{i,j}X_{ij}e^{x_i+y_j}-\sum_i x_i-\sum_j y_j.
$$

Its gradient at the origin is $g=(\alpha,\beta)$, and a balanced point is a minimizer. If $R=\|(x,y)\|_\infty$, then the Hessian along $tz$, $0\le t\le1$, is bounded below by the Hessian at the balanced matrix $B$ multiplied by $e^{-2R}$. On the gauge subspace, the smallest eigenvalue of the latter is at least $1-\|B-P_p\|_{\rm op}$. Thus there is a fixed positive lower bound $\lambda$ along the entire segment. Integrating the gradient gives $\|z\|_2\le\lambda^{-1}\|g\|_2$. The dense entry bound together with $|e^{x_i+y_j}-1|\le K|x_i+y_j|$ then gives the Frobenius displacement estimate.

Since $\Phi_X(0)=p$ and $\Phi_X(z)=p-\theta_X$, convexity gives $\theta_X\ge0$. Strong convexity gives $\theta_X\le\|g\|_2^2/(2\lambda)$. The general-mass identity follows by absorbing the scalar $p/\mathfrak m(X)$ into the two diagonal potentials. Finally, $p\log(\mathfrak m(X)/p)\le\kappa$ gives the permanent upper bound.


From the mass identity $\sum_{ij}X_{ij}=p$,

$$
\sum_i\alpha_i=\sum_j\beta_j=0,
\quad X_0\mathbf1=X\mathbf1-\alpha-\mathbf1\frac{\sum_j\beta_j}p=\mathbf1,
\quad X_0^{\mathsf T}\mathbf1=\mathbf1.
$$

Since $P_p\mathbf1=\mathbf1$, we have $E\mathbf1=E^{\mathsf T}\mathbf1=0$. The same calculation also gives

$$
\Pi_pX\Pi_p=X-P_p-\frac{\alpha\mathbf1^{\mathsf T}+\mathbf1\beta^{\mathsf T}}p=E.
$$

On the constant subspace, set $c=(\mathbf1,\mathbf1)$ and $u=(\mathbf1,-\mathbf1)$. Then

$$
\mathsf H_0c=2c,\quad\mathsf H_0u=0,\quad Nc=0,\quad Nu=u.
$$

The inverse therefore has eigenvalues $1/2,1$ on these two lines, respectively. On the two zero-sum subspaces, direct multiplication verifies

$$
\begin{pmatrix}I&E\\E^{\mathsf T}&I\end{pmatrix}
\begin{pmatrix}R_L&-ER_R\\-E^{\mathsf T}R_L&R_R\end{pmatrix}
=\begin{pmatrix}I&0\\0&I\end{pmatrix},
$$

where we use

$$
R_L-ER_RE^{\mathsf T}=I,\quad R_R-E^{\mathsf T}R_LE=I,
\quad R_LE=ER_R.
$$

The last identity can be checked term by term using the Neumann series. Writing the projection onto the constant subspace back in block form gives the four blocks, including $R_L-P_p/4$ and $-ER_R-P_p/4$.

Because every row and column of $E$ has two-norm at most $C_0/\sqrt p$,

$$
R_L-I=E(I-E^{\mathsf T}E)^{-1}E^{\mathsf T},
\quad |(R_L-I)_{ij}|\le\frac{C_0^2}{p(1-q^2)},
$$

$$
O-E=EE^{\mathsf T}E(I-E^{\mathsf T}E)^{-1},
\quad |(O-E)_{ij}|\le\frac{C_0^2q}{p(1-q^2)}.
$$

The absolute sum of each $2p$-dimensional block row is therefore at most

$$
1+\frac14+\frac14+C_0+
\frac{C_0^2(1+q)}{1-q^2}
=\frac32+C_0+\frac{C_0^2}{1-q}=L_0.
$$

The matrix is symmetric, so its induced one-norm is the same. Also,

$$
\|X-X_0\|_{\infty\to\infty},\|X-X_0\|_{1\to1}\le2\varepsilon,
\quad\|\mathsf H_X-\mathsf H_0\|_{\infty\to\infty},
\|\mathsf H_X-\mathsf H_0\|_{1\to1}\le3\varepsilon.
$$

Set $M=(\mathsf H_0+N)^{-1}$ and $D=\mathsf H_X-\mathsf H_0$. Then

$$
(\mathsf H_X+N)^{-1}=(I+MD)^{-1}M
=\sum_{h=0}^{\infty}(-MD)^hM,
$$

$$
\|(\mathsf H_X+N)^{-1}\|\le\frac{L_0}{1-3L_0\varepsilon}\le2L_0.
$$

Here either the one-norm or the infinity norm above may be used; $\varepsilon\le1/(256L_0^2)$ guarantees $3L_0\varepsilon<1/2$.


For $|h|\le2R\le1/2$, the Taylor integral remainder is

$$
e^h-1-h=h^2\int_0^1(1-t)e^{th}\,dt,
\qquad |e^h-1-h|\le\tfrac12e^{1/2}h^2.
$$

Each absolute row sum is at most two, and $|x_i+y_j|\le2R$, so

$$
\|\mathcal N_X(z)\|_\infty\le2\cdot\tfrac12e^{1/2}(2R)^2\le8R^2.
$$

In the derivative, the sum of absolute coefficients for a given row potential and all column potentials is at most

$$
2\sum_j|X_{ij}|\,|e^{x_i+y_j}-1|
\le2\cdot2\cdot2Re^{1/2}\le16R.
$$

The totals on the two sides agree, so $u^{\mathsf T}g=u^{\mathsf T}\mathcal N_X(z)=0$. Also, $\mathsf H_Xu=0$, and hence the inverse preserves $u^\perp$. Setting $R=4L_0\varepsilon$ gives

$$
\|\mathcal T(0)\|_\infty\le2L_0\varepsilon=R/2,
\quad\operatorname{Lip}(\mathcal T)\le2L_0\cdot16R
=128L_0^2\varepsilon\le1/2.
$$

Consequently, $\|\mathcal T(z)\|_\infty\le R/2+\|z\|_\infty/2\le R$. Starting from $z_0=0$ and $z_{h+1}=\mathcal T(z_h)$,

$$
\|z_{h+1}-z_h\|_\infty\le2^{-h}\|z_1-z_0\|_\infty,
\quad\sum_{h=0}^{\infty}\|z_{h+1}-z_h\|_\infty<\infty.
$$

The iteration therefore converges to a finite real vector, and its limit satisfies the balancing equation. Since $R\le1/4$, we have $e^{x_i+y_j}\le e^{1/2}<2$, giving $|B_{ij}|\le2C/p$. At the same time,

$$
\|B-X\|_{\infty\to\infty},\|B-X\|_{1\to1}
\le2\cdot2Re^{1/2}\le8R=32L_0\varepsilon,
$$

$$
\|B-P_p\|_{\rm op}\le q+(32L_0+2)\varepsilon\le(1+q)/2.
$$


For nonnegative $X$, the Hessian quadratic form in any direction $h=(v,w)$ is

$$
h^{\mathsf T}\nabla^2\Phi_X(z)h
=\sum_{ij}X_{ij}e^{x_i+y_j}(v_i+w_j)^2\ge0.
$$

At the balanced point $z_*$, the Hessian is $\left(\begin{smallmatrix}I&B\\B^{\mathsf T}&I\end{smallmatrix}\right)$. On the gauge subspace, decompose into the constant direction and the zero-sum directions. The former has eigenvalue two, and the latter have lower bound $1-\|B-P_p\|_{\rm op}$. If $0\le t\le1$,

$$
X_{ij}e^{t(x_i+y_j)}=B_{ij}e^{-(1-t)(x_i+y_j)}\ge e^{-2R}B_{ij}.
$$

We may therefore take $\lambda=e^{-2R}(1-\|B-P_p\|_{\rm op})>0$. Integrating the gradient along the segment gives

$$
0=\nabla\Phi_X(z_*)=g+\int_0^1\nabla^2\Phi_X(tz_*)z_*\,dt,
$$

$$
\lambda\|z_*\|_2^2\le-\langle g,z_*\rangle\le\|g\|_2\|z_*\|_2,
\quad\|z_*\|_2\le\lambda^{-1}\|g\|_2.
$$

For the Frobenius displacement,

$$
\begin{aligned}
\|B-X\|_F^2
&=\sum_{ij}X_{ij}^2(e^{x_i+y_j}-1)^2\\
&\le K\frac{C^2}{p^2}\sum_{ij}(x_i+y_j)^2\\
&\le K\frac{C^2}{p^2}\left(2p\sum_ix_i^2+2p\sum_jy_j^2\right)
\le\frac{K'}p\|g\|_2^2.
\end{aligned}
$$

At balance, $\sum_{ij}B_{ij}=p$, so $\Phi_X(z_*)=p-\theta_X$. Strong convexity gives

$$
p-\theta_X\ge p+\langle g,z_*\rangle+\frac\lambda2\|z_*\|_2^2,
$$

$$
0\le\theta_X\le-\langle g,z_*\rangle-\frac\lambda2\|z_*\|_2^2
\le\frac{\|g\|_2^2}{2\lambda}.
$$

The last inequality follows from $0\le\|\sqrt\lambda z_*+g/\sqrt\lambda\|_2^2$. If the mass is $p+\kappa$, set $c=p/(p+\kappa)$; add $\tfrac12\log c$ to the potentials on both sides to obtain

$$
\theta_X=\theta_{\widetilde X}+p\log c,\qquad
\operatorname{per}X=e^{-\theta_X}\operatorname{per}B,
$$

$$
-\theta_X\le p\log(1+\kappa/p)\le\kappa.
$$

Here $\kappa$ may be negative, but $p+\kappa>0$ is required.


To shorten the formulas in this calculation, temporarily write $P=P_p$, $L=R_L$, $R=R_R$, and $O=ER_R$. Centering gives

$$
EP=PE=E^{\mathsf T}P=PE^{\mathsf T}=0,\quad
LP=PL=RP=PR=P,\quad OP=PO=O^{\mathsf T}P=PO^{\mathsf T}=0.
$$

After adding the gauge projection, the matrix is

$$
\mathsf H_0+N=\begin{pmatrix}I+P/2&E+P/2\\E^{\mathsf T}+P/2&I+P/2\end{pmatrix},
$$

The proposed inverse is $M=\left(\begin{smallmatrix}L-P/4&-O-P/4\\-O^{\mathsf T}-P/4&R-P/4\end{smallmatrix}\right)$. Multiplying the upper-left block term by term gives

$$
\begin{aligned}
[(\mathsf H_0+N)M]_{LL}
={}&(I+P/2)(L-P/4)+(E+P/2)(-O^{\mathsf T}-P/4)\\
={}&L-P/4+P/2-P/8-EO^{\mathsf T}-P/8\\
={}&L-EO^{\mathsf T}.
\end{aligned}
$$

Since $O^{\mathsf T}=E^{\mathsf T}L$,

$$
L-EO^{\mathsf T}=L-EE^{\mathsf T}L=(I-EE^{\mathsf T})L=I.
$$

The upper-right block is

$$
\begin{aligned}
[(\mathsf H_0+N)M]_{LR}
={}&(I+P/2)(-O-P/4)+(E+P/2)(R-P/4)\\
={}&-O-P/4-P/8+ER+P/2-P/8\\
={}&-O+ER=0.
\end{aligned}
$$

The lower-left block is

$$
\begin{aligned}
[(\mathsf H_0+N)M]_{RL}
={}&(E^{\mathsf T}+P/2)(L-P/4)+(I+P/2)(-O^{\mathsf T}-P/4)\\
={}&E^{\mathsf T}L+P/2-P/8-O^{\mathsf T}-P/4-P/8\\
={}&E^{\mathsf T}L-O^{\mathsf T}=0.
\end{aligned}
$$

The lower-right block is

$$
\begin{aligned}
[(\mathsf H_0+N)M]_{RR}
={}&(E^{\mathsf T}+P/2)(-O-P/4)+(I+P/2)(R-P/4)\\
={}&-E^{\mathsf T}O-P/8+R-P/4+P/2-P/8\\
={}&R-E^{\mathsf T}O\\
={}&R-E^{\mathsf T}ER=(I-E^{\mathsf T}E)R=I.
\end{aligned}
$$

Thus $M$ is the required inverse.


The row-side and column-side remainders are, respectively,

$$
\mathcal N_{L,i}(x,y)=\sum_jX_{ij}(e^{x_i+y_j}-1-x_i-y_j),
$$

$$
\mathcal N_{R,j}(x,y)=\sum_iX_{ij}(e^{x_i+y_j}-1-x_i-y_j).
$$

Its row-side partial derivatives are

$$
\frac{\partial\mathcal N_{L,i}}{\partial x_k}
=\mathbf1\{i=k\}\sum_jX_{ij}(e^{x_i+y_j}-1),\quad
\frac{\partial\mathcal N_{L,i}}{\partial y_j}=X_{ij}(e^{x_i+y_j}-1).
$$

The column-side partial derivatives are

$$
\frac{\partial\mathcal N_{R,j}}{\partial x_i}=X_{ij}(e^{x_i+y_j}-1),\quad
\frac{\partial\mathcal N_{R,j}}{\partial y_k}
=\mathbf1\{j=k\}\sum_iX_{ij}(e^{x_i+y_j}-1).
$$

Thus the absolute sum of each row-side Jacobian row is at most

$$
\left|\sum_jX_{ij}(e^{x_i+y_j}-1)\right|
+\sum_j|X_{ij}||e^{x_i+y_j}-1|
\le2\sum_j|X_{ij}||e^{x_i+y_j}-1|.
$$

When $\|(x,y)\|_\infty\le R\le1/4$, the right-hand side is at most

$$
2\sum_j|X_{ij}|\cdot2Re^{2R}\le8Re^{1/2}\le16R.
$$

The column side has the same bound, using the assumption that each absolute column sum is at most two. Integrating the vector-valued function along the segment joining the two points gives

$$
\mathcal N(z)-\mathcal N(w)=\int_0^1D\mathcal N(w+t(z-w))(z-w)\,dt,
$$

Its Lipschitz constant is therefore at most $16R$. Multiplication by the gauge-fixed inverse bound $2L_0$ gives the contraction constant $32L_0R=128L_0^2\varepsilon$.


Set $E_B=B-P_p$, where $P_p=J_p/p$. For $h=(v,w)\in u^\perp$, we have $\sum_iv_i=\sum_jw_j$, so there is a unique decomposition

$$
v=c\mathbf1+v_0,\quad w=c\mathbf1+w_0,\quad
\mathbf1^{\mathsf T}v_0=\mathbf1^{\mathsf T}w_0=0.
$$

Its squared norm is

$$
\|h\|_2^2=2pc^2+\|v_0\|_2^2+\|w_0\|_2^2.
$$

Since $B\mathbf1=B^{\mathsf T}\mathbf1=\mathbf1$, the mixed constant terms vanish. Computing term by term gives

$$
\begin{aligned}
h^{\mathsf T}\begin{pmatrix}I&B\\B^{\mathsf T}&I\end{pmatrix}h
&=\|v\|^2+\|w\|^2+2v^{\mathsf T}Bw\\
&=4pc^2+\|v_0\|^2+\|w_0\|^2+2v_0^{\mathsf T}E_Bw_0\\
&\ge4pc^2+\|v_0\|^2+\|w_0\|^2-2q_B\|v_0\|\|w_0\|\\
&\ge4pc^2+(1-q_B)(\|v_0\|^2+\|w_0\|^2)\\
&\ge(1-q_B)\|h\|^2,
\end{aligned}
$$

Here $q_B=\|E_B\|_{\rm op}<1$, and the penultimate step uses $2ab\le a^2+b^2$. This gives the strong-convexity constant used in the displacement and capacity lemma.

### 4.2 Gaussian Deletion and Centering

Deleting $t$ rows from a dense normalized matrix removes a total squared row norm of order $t/n$. Applying the log-determinant derivative to the corresponding Gram-matrix loss preserves this order. Switching to the Gram matrix on the other side then handles column deletion. This yields a linear deletion error even when the retained submatrix is nonprincipal.


**Definition 4.2 (Gaussian determinant factor).**

Whenever $\|Z\|_{\rm op}<1$ for a real matrix $Z$, define

$$
\mathcal G(Z)=\det(I-Z^{\mathsf T}Z)^{-1/2}.
$$

Using $ZZ^{\mathsf T}$ gives the same value; adjoining zero rows or zero columns also leaves this value unchanged.


**Lemma 4.3 (Gram deletion and stability).**

Suppose $\|Z\|_{\rm op}\le q_*<1$. Delete the row set $I$ and the column set $J$, leaving the sets $R,T$. Then

$$
0\le\log\mathcal G(Z)-\log\mathcal G(Z[R,T])\le\frac{\sum_{i\in I}\|Z_{i,\cdot}\|_2^2+\sum_{j\in J}\|Z_{\cdot,j}\|_2^2}{2(1-q_*^2)}.
$$

**Double centering.** At order $m\ge1$, assume $\|W\|_{\rm op}\le q_*$ for a square retained matrix $W$. Set $u=\mathbf 1_m/\sqrt m$. Then

$$
0\le\log\mathcal G(W)-\log\mathcal G(\Pi_mW\Pi_m)\le\frac{\|W^{\mathsf T}u\|_2^2+\|Wu\|_2^2}{2(1-q_*^2)}.
$$

**Stability.** For two real matrices of the same dimensions whose operator norms are both at most $q_*$, we also have

$$
|\log\mathcal G(U)-\log\mathcal G(V)|\le\frac{\|U\|_F+\|V\|_F}{2(1-q_*^2)}\|U-V\|_F.
$$


**Proof.**

Let $P_R$ be the diagonal projection onto the retained row coordinates. Deleting rows reduces the column-side Gram matrix by the positive semidefinite matrix $Z^{\mathsf T}(I-P_R)Z$, whose trace is the sum of squared norms of the deleted rows. For $F(H)=-\tfrac12\log\det(I-H)$ and a positive semidefinite direction $D$,

$$
DF(H)[D]=\tfrac12\operatorname{tr}((I-H)^{-1}D)\le\frac{\operatorname{tr}D}{2(1-q_*^2)}.
$$

Integrate this bound, and then use the row-side Gram matrix to handle column deletion. Projecting away the two all-ones directions in turn gives the centering bound by the same method. For the final conclusion, integrate along the segment joining the two Gram matrices and use

$$
\|U^{\mathsf T}U-V^{\mathsf T}V\|_*\le(\|U\|_F+\|V\|_F)\|U-V\|_F,
$$

where $\|\cdot\|_*$ denotes the trace norm. The required operator spectral gap holds along the entire Gram-matrix segment.

Now let $S$ be a tournament sign matrix of order $n\ge4$, with $s=S\mathbf 1_n$ and $\tau=\|s\|_2^2/(n-1)^2$. Set

$$
Y=\frac{S-I}{n-1},\qquad D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2}.
$$

Skew-symmetry and the paired singular values give

$$
\|Y\|_{\rm op}^2\le q_Y^2=\frac{n(n-1)/2+1}{(n-1)^2}<1.
$$

Take an integer $0\le t<n$, delete any $t$ rows and $t$ columns, and write $m=n-t\ge1$ and $Z=\Pi_mY[R,T]\Pi_m$. Every row and column of $Y$ has squared two-norm $n/(n-1)^2$. Moreover,

$$
\|Y\mathbf 1_n\|_2^2=\|Y^{\mathsf T}\mathbf 1_n\|_2^2=\tau+\frac n{(n-1)^2},
$$

Here $\mathbf1_I,\mathbf1_J\in\mathbb R^n$ are indicator column vectors in the original vertex universe $[n]$, for the sets $I,J$: a coordinate is one when it belongs to the corresponding set and zero otherwise.

$$
\|Y\mathbf 1_J\|_2^2,\ \|Y^{\mathsf T}\mathbf 1_I\|_2^2\le\frac{t^2n}{(n-1)^2}.
$$

The preceding lemma therefore gives

$$
0\le\log\mathcal G(Y)-\log\mathcal G(Z)\le\frac{t n/(n-1)^2+2[\tau+n(1+t^2)/(n-1)^2]/m}{1-q_Y^2}.
$$

The full-matrix Gram identity is $Y^{\mathsf T}Y=(S^{\mathsf T}S+I)/(n-1)^2$. Its difference from $S^{\mathsf T}S/n^2$ is positive semidefinite and has trace

$$
\vartheta_n=\frac{2n-1}{n(n-1)}+\frac n{(n-1)^2}.
$$

Consequently, $0\le\log\mathcal G(Y)-\log D_n(S)\le43/(4n)$. If $m\ge n/2$, the first loss is at most $(24t+18\tau+8)/n$. Both are nonnegative losses relative to the same full-matrix kernel, so

$$
|\log\mathcal G(Z)-\log D_n(S)|\le\frac{24t+18\tau+11}{n}.
$$

To make the constants explicit, note that $1-q_Y^2=n(n-3)/(2(n-1)^2)$. Substitution and $t\le n/2$ directly verify the constants above. The estimate applies to independently chosen row and column deletion sets $I,J$; skew-symmetry is used only for the original full matrix $S$.


For $0\le H\le q_*^2I$, spectral decomposition or the determinant derivative formula gives

$$
\frac{d}{dt}\left[-\frac12\log\det(I-H-tD)\right]
=\frac12\operatorname{tr}((I-H-tD)^{-1}D).
$$

If $D\ge0$ and the entire segment remains bounded above by $q_*^2I$, the right-hand side lies in $[0,\operatorname{tr}D/(2(1-q_*^2))]$. For row deletion,

$$
H_0=Z^{\mathsf T}P_RZ,\quad
D=Z^{\mathsf T}(I-P_R)Z\ge0,\quad
\operatorname{tr}D=\sum_{i\in I}\sum_jZ_{ij}^2.
$$

For column deletion, switch to $(P_RZ)(P_RZ)^{\mathsf T}$. The squared norms of the deleted columns are no larger than their original squared norms, so the two losses can be added. Centering uses the projection $I-uu^{\mathsf T}$; the first corresponding Gram loss is $W^{\mathsf T}uu^{\mathsf T}W$, with trace $\|W^{\mathsf T}u\|^2$. The other step contributes at most $\|Wu\|^2$.

For arbitrary $U,V$,

$$
U^{\mathsf T}U-V^{\mathsf T}V
=U^{\mathsf T}(U-V)+(U-V)^{\mathsf T}V,
$$

$$
\|U^{\mathsf T}U-V^{\mathsf T}V\|_*
\le\|U\|_F\|U-V\|_F+\|U-V\|_F\|V\|_F.
$$

Along the Gram segment $H_t=(1-t)V^{\mathsf T}V+tU^{\mathsf T}U$, we still have $0\le H_t\le q_*^2I$. Using $|\operatorname{tr}(AB)|\le\|A\|_{\rm op}\|B\|_*$ and integrating then gives the Lipschitz constant in the lemma.


Since $S^{\mathsf T}=-S$,

$$
(S-I)^{\mathsf T}(S-I)=(-S-I)(S-I)=-S^2+I=S^{\mathsf T}S+I.
$$

Consequently,

$$
q_Y^2=\frac{n(n-1)/2+1}{(n-1)^2},\qquad
1-q_Y^2=\frac{n(n-3)}{2(n-1)^2}>0\quad(n\ge4).
$$

Each row has exactly $n$ entries of modulus $1/(n-1)$, and its squared norm is $n/(n-1)^2$. Also,

$$
Y\mathbf1=(s-\mathbf1)/(n-1),\quad
Y^{\mathsf T}\mathbf1=(-s-\mathbf1)/(n-1),
$$

$$
\|s\mp\mathbf1\|^2=\|s\|^2+n\mp2\sum_i s_i=\|s\|^2+n.
$$

For the indicator vector of the deleted columns, each row satisfies $|(Y\mathbf1_J)_i|\le t/(n-1)$, so the squared norm is at most $nt^2/(n-1)^2$. The all-ones direction of the retained matrix $W=Y[R,T]$ satisfies

$$
\begin{aligned}
\|W\mathbf1_m/\sqrt m\|^2
&\le\frac1m\|Y(\mathbf1_n-\mathbf1_J)\|^2\\
&\le\frac2m\left[\tau+\frac n{(n-1)^2}+\frac{nt^2}{(n-1)^2}\right].
\end{aligned}
$$

The other direction is analogous. Substitution into the deletion and centering bounds gives the loss $L$ above. Multiply it by $n$ and substitute the spectral gap:

$$
nL\le\frac{2nt}{n-3}
+\frac{4(n-1)^2\tau}{m(n-3)}
+\frac{4n(1+t^2)}{m(n-3)}.
$$

When $m=n-t\ge n/2$,

$$
\frac n{n-3}\le4,\quad
\frac{4(n-1)^2}{m(n-3)}\le18,\quad
\frac{4n}{m(n-3)}\le8,
$$

$$
\frac{4nt^2}{m(n-3)}\le16t.
$$

The last inequality follows from $t/m\le1$ and $n/(n-3)\le4$. Hence $nL\le24t+18\tau+8$.

The difference between the full-order Gram matrices is

$$
\left(\frac1{(n-1)^2}-\frac1{n^2}\right)S^{\mathsf T}S
+\frac I{(n-1)^2}\ge0,
$$

Its trace is $\vartheta_n$. The logarithmic loss is at most

$$
\frac{\vartheta_n}{2(1-q_Y^2)}
=\frac{3n^2-3n+1}{n^2(n-3)}\le\frac{43}{4n}.
$$

The last inequality is equivalent to $31n^2-117n-4\ge0$; at $n=4$, its left-hand side is $24>0$, and it increases thereafter. If $a,b\ge0$, then $|a-b|\le\max(a,b)$. Both losses are relative to $\mathcal G(Y)$, so

$$
|\log\mathcal G(Z)-\log D_n(S)|
\le\max\left(\frac{24t+18\tau+8}n,\frac{43}{4n}\right)
\le\frac{24t+18\tau+11}n.
$$

### 4.3 Preprocessing Tournament Submatrices

The row and column errors of $C=2A/(n-1)$ have opposite signs. Multiplying row $i$ by $(1+a_i)^{-1}$ corrects the original row sum; multiplying column $i$ by $(1-a_i)^{-1}$ corrects the original column sum. Applying both corrections simultaneously leaves marginal residuals, which we estimate below. The main effect is to cancel the first-order change in total mass and produce the score penalty $\Gamma$ in the restored product.

Fix $0\le a_0<1$ and finite positive parameters $A_0,B_0$. In this subsection, assume

$$
a_i=\frac{s_i}{n-1},\qquad \max_i|a_i|\le a_0,\qquad \tau=\sum_i a_i^2\le A_0\log n,\qquad t\le B_0\log n.
$$

Define

$$
C=\frac{J-I+S}{n-1}=\frac{2A}{n-1},\qquad \ell_i=\frac1{1+a_i},\qquad r_i=\frac1{1-a_i},\qquad g_i=\frac1{1-a_i^2}.
$$

Set $C'=\operatorname{diag}(\ell)C\operatorname{diag}(r)$, $F=C'-C$, and $\nu=\mathfrak m(C')-n$. To compute the total mass, write $v_i=a_i/(1-a_i^2)$, $w_i=a_i^2/(1-a_i^2)$, and also $V=\sum_i v_i$, $W=\sum_i w_i$. Expanding $\ell=\mathbf 1-v+w$ and $r=\mathbf 1+v+w$ gives the exact identity

$$
\nu=\frac{W^2-V^2+W+2w^{\mathsf T}Sv}{n-1}.
$$

More precisely, $\mathbf 1^{\mathsf T}Sv=-(n-1)W$ cancels the first-order mass change. The fixed score bound gives $W\le K\tau$, $|V|\le K\tau$, and $\|v\|_2\le K\sqrt\tau$. Estimating $Sv$ row by row yields

$$
|\nu|\le K\mathcal M_\tau,\qquad \mathcal M_\tau=\frac{\tau+\tau^2}{n}+\frac{\tau^{3/2}}{\sqrt n}=o(1).
$$

The marginal identities are

$$
C'\mathbf 1_n-\mathbf 1_n=\operatorname{diag}(\ell)C(r-\mathbf 1_n),
$$

$$
(C')^{\mathsf T}\mathbf 1_n-\mathbf 1_n=\operatorname{diag}(r)C^{\mathsf T}(\ell-\mathbf 1_n).
$$

Every row and column of $C$ has two-norm $O(n^{-1/2})$, and $\|C\|_{\rm op}=O(1)$. Thus the marginal error is $O(\sqrt{\tau/n})$ in the infinity norm and $O(\sqrt\tau)$ in the two-norm. A direct entrywise estimate also gives

$$
\|F\|_F\le K\sqrt{\tau/n}.
$$

Normalize $\widehat C=nC'/\mathfrak m(C')$. Denote its row and column errors by $e_i,f_j$, so $\sum e_i=\sum f_j=0$. For arbitrary deletion sets of common size $t$, denoted by $I,J$, write $R=[n]\setminus I$, $T=[n]\setminus J$, $m=n-t$, and set

$$
X=\frac n m\widehat C[R,T],\qquad \kappa=\mathfrak m(X)-m,\qquad \widetilde X=\frac m{\mathfrak m(X)}X.
$$

The exact mass identity for deleting rows and columns is

<a id="eq-deletion-mass"></a>

$$
\kappa=\frac n m\left[-\sum_{i\in I}e_i-\sum_{j\in J}f_j+\sum_{i\in I,j\in J}\widehat C_{ij}-\frac{t^2}{n}\right].
\tag{4.1}
$$

The marginal error in each retained row before the final normalization is

$$
(X\mathbf 1_m)_i-1=\frac n m\left[e_i+\frac t n-\sum_{j\in J}\widehat C_{ij}\right],
$$

The column side has the corresponding identity of the same form. Consequently,

$$
|\kappa|\le K\left[t\sqrt{\tau/n}+t^2/n\right],
$$

$$
\varepsilon(\widetilde X)\le K(\sqrt{\tau/n}+t/n),\qquad \|g(\widetilde X)\|_2\le K(\sqrt\tau+t/\sqrt n).
$$

Here $g(\widetilde X)$ is the concatenated vector of row and column marginal errors. The entries of $\widetilde X$ lie in $[0,K/m]$.

To apply Lemma 4.1, we now verify the centered-kernel conditions for $\widetilde X$. Write

$$
\eta=\frac{n^2}{\mathfrak m(C')\mathfrak m(X)}=1+O((t+1)/n),
$$

Then

$$
\Pi_m\widetilde X\Pi_m=\eta\left[Z+\Pi_mF[R,T]\Pi_m\right].
$$

Since $\mathfrak m(C^{\prime})=n+o(1)$ and $\mathfrak m(X)=m+o(1)$, we have $\eta=(n/m)(1+o(1))$. Compression does not increase the operator norm of $Y$, and the Frobenius estimate above bounds the second term. The centered kernel therefore has operator norm at most $1/\sqrt2+o(1)$ and entries $O(1/m)$. The marginal error of the original matrix $\widetilde X$ tends to zero in the infinity norm. Since $\widetilde X$ has mass $m$, the matrix $E$ in Lemma 4.1 equals $\Pi_m\widetilde X\Pi_m$. Fix $q=3/4$ and entry bounds $C,C_0$. The resulting $L_0,\varepsilon_0$ depend only on $a_0,A_0,B_0$. Lemma 4.1 thus applies uniformly for sufficiently large $n$, giving a doubly stochastic matrix $B_X$ and the spectral-norm bound $7/8$.

The two-norm displacement lemma gives

$$
\|B_X-\widetilde X\|_F\le K(\sqrt{\tau/n}+t/n).
$$

Combined with the stronger centered-kernel bound, this shows that the centered operator norm of $B_X$ is still at most $1/\sqrt2+o(1)$; for example, it is eventually at most $4/5$. The entries continue to satisfy the bound $K/m$.

Apply the Gaussian deletion estimate to $Z$ and use the logarithmic Lipschitz bound for the perturbations due to prescaling, normalization, and diagonal scaling. Since $B_X-P_m=\Pi_mB_X\Pi_m$, this gives

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|\le K\left[\sqrt{\tau/n}+(t+1)/n\right].
$$

The term $\tau/n$ from centering has been absorbed into $\sqrt{\tau/n}$. The deletion error is linear in $t/n$, as needed for summing against the subsequent subset weights.

We can now collect the errors under the fixed dimension conventions. All constants and the final applicability threshold depend only on the fixed parameters $a_0,A_0,B_0$. The full-order mass error contributes $O(|\nu|)\le K\mathcal M_\tau$ to the restoration logarithm. The mass change from deletion is at most $K[t\sqrt{\tau/n}+t^2/n]$, and the Gaussian logarithmic error is $K[\sqrt{\tau/n}+(t+1)/n]$. Applying Theorem 3.1 at order $m\ge n/2$ adds $O(1/m)=O(1/n)$. The final scalar restoration contributes $e^{-1}\exp(O((t+1)/n))$. With total mass $m+\kappa$, the matrix $X$ uses the capacity estimate only in the form $e^{-\theta_X}\le e^\kappa$; one cannot assert that $\theta_X$ is nonnegative for this general mass. Section 4.4 restores these factors exactly and obtains the error exponent in Lemma 4.4.


Verify entry by entry that

$$
1-v_i+w_i=1-\frac{a_i}{1-a_i^2}+\frac{a_i^2}{1-a_i^2}
=\frac1{1+a_i}=\ell_i,
$$

$$
1+v_i+w_i=\frac1{1-a_i}=r_i,\qquad
a_iv_i=w_i,\quad \ell_ir_i=g_i=1+w_i.
$$

Set $L=\mathbf1-v+w$ and $R=\mathbf1+v+w$ (here $L,R$ denote vectors only within this calculation). Then

$$
L^{\mathsf T}JR=(n-V+W)(n+V+W)=(n+W)^2-V^2,
$$

$$
L^{\mathsf T}IR=\sum_i g_i=n+W.
$$

Expand the skew-symmetric part term by term:

$$
\begin{aligned}
L^{\mathsf T}SR
={}&\mathbf1^{\mathsf T}Sv+\mathbf1^{\mathsf T}Sw
-v^{\mathsf T}S\mathbf1-v^{\mathsf T}Sv-v^{\mathsf T}Sw\\
&+w^{\mathsf T}S\mathbf1+w^{\mathsf T}Sv+w^{\mathsf T}Sw\\
={}&-2(n-1)W+2w^{\mathsf T}Sv.
\end{aligned}
$$

Here $\mathbf1^{\mathsf T}Sv=-(n-1)a^{\mathsf T}v=-(n-1)W$; $\mathbf1^{\mathsf T}Sw+w^{\mathsf T}S\mathbf1=0$; $v^{\mathsf T}Sv=w^{\mathsf T}Sw=0$; and $-v^{\mathsf T}Sw=w^{\mathsf T}Sv$. Thus

$$
\begin{aligned}
\mathfrak m(C')&=\frac{(n+W)^2-V^2-(n+W)-2(n-1)W+2w^{\mathsf T}Sv}{n-1}\\
&=n+\frac{W^2-V^2+W+2w^{\mathsf T}Sv}{n-1}.
\end{aligned}
$$

Since $\sum_i a_i=0$,

$$
V=\sum_i\left(a_i+\frac{a_i^3}{1-a_i^2}\right)
=\sum_i\frac{a_i^3}{1-a_i^2},\quad
|V|\le\frac{a_0}{1-a_0^2}\tau,
\quad W\le\frac\tau{1-a_0^2},
$$

$$
\|v\|_2\le\frac{\sqrt\tau}{1-a_0^2},\quad
\|Sv\|_\infty\le\sqrt n\|v\|_2,\quad
|w^{\mathsf T}Sv|\le\|w\|_1\|Sv\|_\infty\le K\sqrt n\tau^{3/2}.
$$

Substitution gives $|\nu|\le K[(\tau+\tau^2)/n+\tau^{3/2}/\sqrt n]$.


Since $\operatorname{diag}(\ell)C\mathbf1=\mathbf1$,

$$
C'\mathbf1-\mathbf1=\operatorname{diag}(\ell)C(r-\mathbf1).
$$

Moreover, $|r_i-1|\le K|a_i|$, $|\ell_i-1|\le K|a_i|$, and $\|C_{i,\cdot}\|_2\le K/\sqrt n$. Hence

$$
\|C'\mathbf1-\mathbf1\|_\infty\le K\sqrt{\tau/n},\quad
\|C'\mathbf1-\mathbf1\|_2\le K\|C\|_{\rm op}\sqrt\tau\le K'\sqrt\tau.
$$

The column side is analogous. Entry by entry,

$$
F_{ij}=C_{ij}(\ell_ir_j-1),\quad
|\ell_ir_j-1|\le K(|a_i|+|a_j|),
$$

$$
\|F\|_F^2\le\frac K{n^2}\sum_{ij}(a_i^2+a_j^2)
=\frac{2K\tau}n.
$$

At total mass $n$, the normalized matrix $\widehat C$ has retained-block mass given directly by inclusion–exclusion:

$$
\begin{aligned}
\sum_{i\in R,j\in T}\widehat C_{ij}
&=n-\sum_{i\in I}(1+e_i)-\sum_{j\in J}(1+f_j)
+\sum_{i\in I,j\in J}\widehat C_{ij}\\
&=n-2t-\sum_Ie_i-\sum_Jf_j+\sum_{I,J}\widehat C_{ij}.
\end{aligned}
$$

Since $m^2/n=n-2t+t^2/n$, multiplying by $n/m$ and then subtracting $m$ gives equation (4.1). By $\widehat C_{ij}\le K/n$,

$$
|\kappa|\le\frac nm\left(2t\max(\|e\|_\infty,\|f\|_\infty)
+(K+1)t^2/n\right)
\le K'[t\sqrt{\tau/n}+t^2/n].
$$

The error in a retained row likewise satisfies, term by term,

$$
\frac nm\left(1+e_i-\sum_{j\in J}\widehat C_{ij}\right)-1
=\frac nm\left(e_i+t/n-\sum_{j\in J}\widehat C_{ij}\right).
$$

The normalization multiplier $m/(m+\kappa)$ differs from one by $O(|\kappa|/m)$. Thus the marginal infinity norm and two-norm are $K(\sqrt{\tau/n}+t/n)$ and $K(\sqrt\tau+t/\sqrt n)$, respectively.


Successive substitution of the definitions gives

$$
\widetilde X=\frac m{m+\kappa}\frac nm\frac n{n+\nu}C'[R,T]
=\frac{n^2}{(n+\nu)(m+\kappa)}C'[R,T]=\eta C'[R,T].
$$

Also, $C=J/(n-1)+Y$. Multiplying on the left and right by $\Pi_m$ removes $J$ and yields the centered-kernel identity. Since $m=n-t$,

$$
\eta=\frac nm(1+\nu/n)^{-1}(1+\kappa/m)^{-1}
=1+O((t+1)/n).
$$

Consequently,

$$
\|\Pi_m\widetilde X\Pi_m-Z\|_F
\le|\eta-1|\|Z\|_F+|\eta|\|F[R,T]\|_F
\le K[(t+1)/n+\sqrt{\tau/n}].
$$

Adding the displacement from diagonal scaling gives

$$
\|(B_X-P_m)-Z\|_F
\le K[(t+1)/n+\sqrt{\tau/n}].
$$

All the matrices above have Frobenius norms $O(1)$, and their operator norms are eventually at most the fixed value $4/5<1$. Adding the Gram Lipschitz bound and the deletion bound gives

$$
\begin{aligned}
|\log\mathcal G(B_X-P_m)-\log D_n(S)|
&\le K\left[\frac{t+\tau+1}n+\sqrt{\tau/n}\right]\\
&\le K'\left[\frac{t+1}n+\sqrt{\tau/n}\right],
\end{aligned}
$$

For sufficiently large $n$, we have $\tau/n\le1$, and hence $\tau/n\le\sqrt{\tau/n}$.


First write

$$
e'=C'\mathbf1-\mathbf1,\quad
f'=(C')^{\mathsf T}\mathbf1-\mathbf1,\quad
\widehat C=\frac n{n+\nu}C'.
$$

Coordinatewise,

$$
\begin{aligned}
e_i&=(\widehat C\mathbf1)_i-1
=\frac n{n+\nu}(1+e'_i)-1
=\frac{ne'_i-\nu}{n+\nu},\\
f_j&=(\widehat C^{\mathsf T}\mathbf1)_j-1
=\frac n{n+\nu}(1+f'_j)-1
=\frac{nf'_j-\nu}{n+\nu}.
\end{aligned}
$$

Since $\sum_ie'_i=\sum_jf'_j=\nu$, these formulas also verify

$$
\sum_ie_i=\frac{n\nu-n\nu}{n+\nu}=0,\quad
\sum_jf_j=0.
$$

When $|\nu|\le n/2$,

$$
\|e\|_\infty\le2\|e'\|_\infty+2|\nu|/n,\quad
\|e\|_2\le2\|e'\|_2+2|\nu|/\sqrt n,
$$

$$
\|f\|_\infty\le2\|f'\|_\infty+2|\nu|/n,\quad
\|f\|_2\le2\|f'\|_2+2|\nu|/\sqrt n.
$$

For $0<\tau\le A_0\log n$, divide $|\nu|/n$ by $\sqrt{\tau/n}$. The mass bound already obtained gives at most a constant times

$$
\frac{\sqrt\tau+\tau^{3/2}}{n^{3/2}}+\frac\tau n=o(1).
$$

Dividing $|\nu|/\sqrt n$ by $\sqrt\tau$ gives the same expression. When $\tau=0$, we have $a=0$, so $\nu=0$, and no division is needed. This yields the infinity-norm bound $K\sqrt{\tau/n}$ and the two-norm bound $K\sqrt\tau$ on both sides, respectively.


Suppose

$$
h=X\mathbf1_m-\mathbf1_m,\quad
k=X^{\mathsf T}\mathbf1_m-\mathbf1_m,\quad
\widetilde X=\frac m{m+\kappa}X.
$$

The normalized errors on the two sides are then exactly

$$
\widetilde\alpha_i=\frac{mh_i-\kappa}{m+\kappa},\qquad
\widetilde\beta_j=\frac{mk_j-\kappa}{m+\kappa}.
$$

Using $\sum_ih_i=\sum_jk_j=\kappa$ again verifies $\sum_i\widetilde\alpha_i=\sum_j\widetilde\beta_j=0$. When $|\kappa|\le m/2$,

$$
\|\widetilde\alpha\|_\infty\le2\|h\|_\infty+2|\kappa|/m,
\quad\|\widetilde\alpha\|_2\le2\|h\|_2+2|\kappa|/\sqrt m,
$$

$$
\|\widetilde\beta\|_\infty\le2\|k\|_\infty+2|\kappa|/m,
\quad\|\widetilde\beta\|_2\le2\|k\|_2+2|\kappa|/\sqrt m.
$$

Here $k$ denotes the column-error vector. The retained row and column errors are, respectively,

$$
h_i=\frac nm\left(e_i+t/n-\sum_{j\in J}\widehat C_{ij}\right),\qquad
k_j=\frac nm\left(f_j+t/n-\sum_{i\in I}\widehat C_{ij}\right).
$$

Since $\widehat C_{ij}\le K/n$,

$$
\|h\|_\infty,\|k\|_\infty\le K'[\sqrt{\tau/n}+t/n],
$$

$$
\|h\|_2,\|k\|_2\le K'[\sqrt\tau+t/\sqrt n].
$$

The mass term $|\kappa|/\sqrt m\le K[t\sqrt\tau/n+t^2/n^{3/2}]$ is absorbed into the two-norm bound above because $t/n\to0$; the infinity-norm mass term is likewise absorbed into its corresponding bound. This verifies all the marginal-error hypotheses of the local scaling lemma, one marginal at a time.


The normalized mass is $m$, so the centered matrix is exactly

$$
E=\widetilde X-P_m-\frac{\widetilde\alpha\mathbf1^{\mathsf T}
+\mathbf1\widetilde\beta^{\mathsf T}}m
=\Pi_m\widetilde X\Pi_m.
$$

If $0\le\widetilde X_{ij}\le C_1/m$ and the infinity norms of both marginal error vectors are at most $\epsilon_n$, then

$$
|E_{ij}|\le\frac{C_1+1+2\epsilon_n}{m}\le\frac{C_1+3}{m}
\quad(\epsilon_n\le1).
$$

Nonnegativity makes each absolute row sum or column sum equal to the corresponding row sum or column sum, which is at most $1+\epsilon_n\le2$. Also,

$$
\|E\|_{\rm op}\le|\eta|\|Z\|_{\rm op}+|\eta|\|F[R,T]\|_F
\le\frac1{\sqrt2}+o(1).
$$

First fix $q=3/4$ and the entry bound $C_0=C_1+3$; these determine $L_0,\varepsilon_0$. Then choose a uniform order threshold such that

$$
\|E\|_{\rm op}\le3/4,\quad
\epsilon_n\le\varepsilon_0,\quad m\ge n/2,
\quad |\nu|\le n/2,\quad |\kappa|\le m/2.
$$

All these conditions follow from bounds involving only fixed parameters and $n$, so the threshold is fixed before choosing the particular graph and deletion sets. The local theorem initially gives $\|B_X-P_m\|_{\rm op}\le7/8$; more precisely,

$$
\|B_X-P_m\|_{\rm op}
\le\|\Pi_m\widetilde X\Pi_m\|_{\rm op}
+\|B_X-\widetilde X\|_F
\le1/\sqrt2+o(1)\le4/5.
$$

This estimate is again uniform over tournaments and deletion sets.


Take a sufficiently large odd integer $n$ and the corresponding regular carousel tournament, with adjacency matrix $A_n$ and sign matrix $S_n^{\mathrm{cir}}$. All scores are then zero, all the preceding prescaling factors are one, and

$$
C=\frac{2A_n}{n-1}=\frac{J_n-I_n+S_n^{\mathrm{cir}}}{n-1},
\qquad C\mathbf1_n=C^{\mathsf T}\mathbf1_n=\mathbf1_n.
$$

Consequently, $C'=X=\widetilde X=C$ (here no rows or columns are deleted, so $t=0$). The potential vectors $x=y=0$ already satisfy the balancing equation; the unique small solution in local scaling gives $B_X=C$. On the constant-vector direction, $C-P_n$ vanishes; on its orthogonal complement,

$$
(C-P_n)|_{\mathbf1_n^\perp}
=\left.\frac{S_n^{\mathrm{cir}}-I_n}{n-1}\right|_{\mathbf1_n^\perp},\qquad
(S_n^{\mathrm{cir}}-I_n)^{\mathsf T}(S_n^{\mathrm{cir}}-I_n)=I_n-(S_n^{\mathrm{cir}})^2.
$$

The alternating switching and permutation in A.2 preserve all frequencies of the sign matrix; Lemma 6.1 gives the largest positive frequency $\cot(\pi/(2n))$. Therefore,

$$
\begin{aligned}
\|B_X-P_n\|_{\rm op}
&=\frac{\sqrt{1+\cot^2(\pi/(2n))}}{n-1}\\
&=\frac1{(n-1)\sin(\pi/(2n))}\\
&=\frac{2n}{\pi(n-1)}
\frac{\pi/(2n)}{\sin(\pi/(2n))}
\longrightarrow\frac2\pi<\frac1{\sqrt2}.
\end{aligned}
$$

Here we use $\sin u/u\to1$. Thus the centered norm need not tend to zero; the fixed bound $4/5$ suffices for Theorem 3.1.

### 4.4 Proof of the Nonprincipal Permanent Bound

We apply the scaling and deletion estimates to tournament submatrices. The deleted row and column sets may differ, since a cycle cover can enter and leave the exceptional set through different core vertices.


**Lemma 4.4 (Nonprincipal permanent bound).**

Fix $0\le b<1$ and positive constants $A_0,B_0$. For a tournament core of order $N\ge2$, set $a=S\mathbf1/(N-1)$ and $\tau=\sum_i a_i^2$. Let $I,J\subseteq[N]$ be the deleted row and column sets, respectively. Here $I,J$ are sets, distinguished from the identity and all-ones matrices by the set operations below. Assume

$$
\max_i|a_i|\le b,\qquad
\tau\le A_0\log N,\qquad
|I|=|J|=t\le B_0\log N.
$$

Define $\ell_i=(1+a_i)^{-1}$, $r_i=(1-a_i)^{-1}$, and

$$
\Gamma=\prod_i(1-a_i^2),\qquad
\mathcal M_\tau=\frac{\tau+\tau^2}{N}+\frac{\tau^{3/2}}{\sqrt N}.
$$

Let $R=[N]\setminus I$ and $T=[N]\setminus J$ be the retained row and column sets, respectively; here $T$ is a column index set. Then

$$
\operatorname{per}A[R,T]\le
e^{-1}D_N(S)\Gamma
\left(\prod_{i\in I}\ell_i\right)
\left(\prod_{j\in J}r_j\right)
\frac{(N-t)!}{2^{N-t}}\exp(\varepsilon_{\tau,t}),
$$

$$
\varepsilon_{\tau,t}\le K\left[
\mathcal M_\tau+\sqrt{\tau/N}+\frac{t+1}{N}
+t\sqrt{\tau/N}+\frac{t^2}{N}\right].
$$

For every sufficiently large $N$, this estimate holds simultaneously for every admissible tournament and every pair $I,J$. The constant $K$ and the threshold depend only on $b,A_0,B_0$.


The factor $\Gamma$ records the cost of degree imbalance. For a principal deleted set $I=J=U$, the restored vertex weight is $\ell_i r_i=(1-a_i^2)^{-1}$; when the deleted sets differ, the row and column factors are retained separately. The error contains a term of order $\sqrt{\tau/N}$. In the final case, it is therefore essential to retain $\Gamma\le e^{-\tau}$.


We now prove Lemma 4.4, using $n$ for the full core order $N$ and taking $a_0=b$. The preceding construction has already produced the scaled matrix $B_X$. It remains to restore all diagonal factors and scalar factors and then compare the resulting Gaussian determinant with $D_n(S)$.

**Proof.**

The construction above gives the entry bound and spectral gap required by Theorem 3.1. Hence

$$
\operatorname{per}B_X=\frac{m!}{m^m}\mathcal G(B_X-P_m)(1+O(1/m)).
$$

The row and column scaling factors are restored exactly as

$$
\prod_{i\in R}(1+a_i)\prod_{j\in T}(1-a_j)=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j.
$$

Thus deleting rows restores the $\ell$ factors, and deleting columns restores the $r$ factors. The complete scalar identity is

<a id="eq-exact-restoration"></a>

$$
\operatorname{per}A[R,T]=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j\left[\frac{m(n-1)\mathfrak m(C')}{2n^2}\right]^m e^{-\theta_X}\operatorname{per}B_X.
\tag{4.2}
$$

After substituting $m!/m^m$ into [equation (4.2)](#eq-exact-restoration), the remaining scalar factor is

$$
\frac{m!}{2^m}(1-1/n)^m\left[\frac{\mathfrak m(C')}{n}\right]^m.
$$

The difference between its logarithm and the logarithm of $e^{-1}m!/2^m$ is $O((t+1)/n+|\nu|)$. The capacity bound gives $e^{-\theta_X}\le e^\kappa$. Substituting the mass error, Gaussian error, and baseline permanent approximation error gives the required exponent bound. The following calculation gives the restoration factors in detail, uniformly over the tournament and deletion sets.


The factors associated with the deleted rows and columns are, respectively,

$$
\begin{aligned}
\operatorname{per}C[R,T]
&=\left(\prod_{i\in R}\ell_i^{-1}\right)
\left(\prod_{j\in T}r_j^{-1}\right)\operatorname{per}C'[R,T]\\
&=\left(\prod_{i=1}^n(1+a_i)\prod_{j=1}^n(1-a_j)\right)
\left(\prod_{i\in I}(1+a_i)^{-1}\right)
\left(\prod_{j\in J}(1-a_j)^{-1}\right)\operatorname{per}C'[R,T]\\
&=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j\operatorname{per}C'[R,T].
\end{aligned}
$$

From $X=n^2C'[R,T]/[m(n+\nu)]$, we obtain

$$
\operatorname{per}C'[R,T]=[m(n+\nu)/n^2]^m\operatorname{per}X.
$$

Using $A=(n-1)C/2$ and $\operatorname{per}X=e^{-\theta_X}\operatorname{per}B_X$ then gives equation (4.2). After substituting the permanent approximation, the scalar factor is

$$
\left[\frac{m(n-1)(n+\nu)}{2n^2}\right]^m\frac{m!}{m^m}
=\frac{m!}{2^m}(1-1/n)^m(1+\nu/n)^m.
$$

Set $u=1/n$. Since

$$
|\log(1-u)+u|\le\frac{u^2}{2(1-u)},
$$

$$
\left|m\log(1-1/n)+1\right|
\le\left|1-\frac mn\right|+\frac{m}{2n^2(1-1/n)}
\le\frac tn+\frac1{2(n-1)}.
$$

When $|\nu|/n\le1/2$, we have $|m\log(1+\nu/n)|\le2|\nu|$. The capacity contribution satisfies $-\theta_X\le\kappa$. The Gaussian factor satisfies $\mathcal G(B_X-P_m)\le D_n(S)e^{K[\sqrt{\tau/n}+(t+1)/n]}$. Finally, $1+O(1/m)\le e^{K/n}$ after increasing the uniform threshold. Thus the error exponent is bounded term by term as follows:

$$
\begin{aligned}
\varepsilon_{\tau,t}\le K\bigg[&\underbrace{\mathcal M_\tau}_{\text{full-order mass}}
+\underbrace{t\sqrt{\tau/n}+t^2/n}_{\text{deletion mass}}\\
&+\underbrace{\sqrt{\tau/n}+(t+1)/n}_{\text{Gaussian and scalar}}
+\underbrace{1/n}_{\text{permanent error}}\bigg].
\end{aligned}
$$

Combining terms of the same order gives Lemma 4.4. $\square$

### 4.5 Two-Sided Estimates for Small Scores

When every score is $o(\sqrt n)$, the original marginals are already sufficiently close to one for local scaling to apply directly. The capacity bound then controls the restoration factor from both sides and gives the approximation needed in Theorem 8.1 of the main paper.


**Lemma 4.5 (Permanent approximation for small scores).**

Suppose $\Delta_s=\|S\mathbf 1_n\|_\infty=o(\sqrt n)$. Fix $0<B_0<\infty$, delete any $t\le B_0\log n$ rows and $t$ columns, and write $m=n-t$. Uniformly over these choices,

<a id="eq-small-score-permanent"></a>

$$
\operatorname{per}A[R,T]=e^{-1}D_n(S)\frac{m!}{2^m}\left[1+O_{B_0}\left(\frac{(\Delta_s+t+1)^2}{n}\right)\right].
\tag{4.3}
$$

More precisely, for fixed $B_0>0$ there are constants $C_{\mathrm{err}},\delta>0$ and an integer $N_0\ge4$ such that the following holds uniformly for $n\ge N_0$. Let $S$ be a tournament sign matrix and let $I,J\subseteq[n]$ satisfy $|I|=|J|=t\le B_0\log n$. Put $\Delta_s=\|S\mathbf1_n\|_\infty$ and $\eta=(\Delta_s+t+1)^2/n$. If $\eta\le\delta$, the absolute relative error in [equation (4.3)](#eq-small-score-permanent) is at most $C_{\mathrm{err}}\eta$. Here $R=[n]\setminus I$, $T=[n]\setminus J$, and $m=n-t$; the two deleted sets may be chosen independently. In the asymptotic range of the lemma, $\eta\to0$.


**Proof.**

Increase $N_0$ so that $2t\le n$ throughout the logarithmic deletion window, giving $m\ge n/2>0$. Paired prescaling is not needed here. Set $C=2A/(n-1)$ and $X=(n/m)C[R,T]$. The row and column errors of the full matrix $C$ are $s_i/(n-1)$ and $-s_i/(n-1)$, respectively. Thus the exact mass identity [equation (4.1)](#eq-deletion-mass) and the marginal formulas in Section 4.3 give

$$
|\kappa|=O(t(\Delta_s+t)/n),\qquad \varepsilon(X)=O((\Delta_s+t)/n),\qquad \|g(X)\|_2=O((\Delta_s+t)/\sqrt n).
$$

The mass error satisfies $|\kappa|\le K\eta$. Decreasing $\delta$ if necessary uniformly ensures $\mathfrak m(X)=m+\kappa>0$. Normalize $\widetilde X=mX/\mathfrak m(X)$. Its density and centered-kernel spectral-gap parameters are fixed, so the local scaling lemma applies. The two-norm displacement and capacity estimates give

$$
\|B_X-\widetilde X\|_F=O((\Delta_s+t)/n),\qquad 0\le\theta_{\widetilde X}=O((\Delta_s+t)^2/n).
$$

The correction for general mass then gives $|\theta_X|=O((\Delta_s+t)^2/n)$. We also have $\tau\le n\Delta_s^2/(n-1)^2$. The finite-deletion estimate, normalization factors, and diagonal-scaling perturbation together give

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|=O((\Delta_s+t+1)^2/n).
$$

The exact restoration now contains no score product and is

$$
\operatorname{per}A[R,T]=\left[\frac{m(n-1)}{2n}\right]^m e^{-\theta_X}\operatorname{per}B_X.
$$

Apply the uniform permanent theorem and use $(1-1/n)^m=e^{-1}\exp(O((t+1)/n))$. Every logarithmic error is controlled by a fixed multiple of $\eta=(\Delta_s+t+1)^2/n$. Choose $\delta$ sufficiently small and exponentiate these bounds. Throughout the preceding finite range, this uniformly bounds the absolute value of the relative error by $C_{\mathrm{err}}\eta$. In the asymptotic range $\Delta_s=o(\sqrt n)$, $t\le B_0\log n$, we have $\eta\to0$. This proves the uniform approximation for submatrices with few deletions used in Theorem 8.1 of the main paper.


Since $|s_i|\le \Delta_s$, the absolute marginal error of the full matrix is at most $\Delta_s/(n-1)$. The deletion-mass formula gives

$$
|\kappa|\le\frac nm\left[\frac{2t\Delta_s}{n-1}+\frac{2t^2}{n-1}+\frac{t^2}n\right]
\le K\frac{t(\Delta_s+t)}n.
$$

The error in a retained row is at most $K(\Delta_s+t)/n$. There are $2m$ row and column errors in total, so

$$
\|g(X)\|_2\le\sqrt{2m}\,K(\Delta_s+t)/n
\le K'(\Delta_s+t)/\sqrt n.
$$

Normalization preserves this order. Capacity and displacement give

$$
0\le\theta_{\widetilde X}\le K(\Delta_s+t)^2/n,
\quad
\|B_X-\widetilde X\|_F\le\frac K{\sqrt m}\frac{\Delta_s+t}{\sqrt n}
\le K'(\Delta_s+t)/n.
$$

Since $|\kappa|/m\le1/2$,

$$
\left|m\log\frac m{m+\kappa}\right|
=m|\log(1+\kappa/m)|\le2|\kappa|,
$$

It follows that $|\theta_X|\le K[(\Delta_s+t)^2+t(\Delta_s+t)]/n\le K'(\Delta_s+t)^2/n$. If $\Delta_s=t=0$, all these quantities are zero.

Gaussian deletion gives $K(t+\tau+1)/n$, while

$$
\tau=\frac{\sum_i s_i^2}{(n-1)^2}\le\frac{n\Delta_s^2}{(n-1)^2}\le\frac{4\Delta_s^2}n.
$$

The centered-kernel displacement is $K(\Delta_s+t+1)/n$, so the total Gaussian logarithmic error is at most

$$
K\left[\frac{t+1}n+\frac{\Delta_s^2}{n^2}+\frac{\Delta_s+t+1}n\right]
\le K'\frac{(\Delta_s+t+1)^2}n=K'\eta.
$$

After complete restoration, we may write

$$
\frac{\operatorname{per}A[R,T]}{e^{-1}D_n(S)m!/2^m}
=e^u(1+v),\qquad |u|\le K\eta,\quad |v|\le K/n\le K\eta.
$$

After choosing a fixed $\delta\le1/(2K)$,

$$
|e^u(1+v)-1|
\le|e^u-1|+e^{|u|}|v|
\le e^{K\delta}(|u|+|v|)
\le2Ke^{K\delta}\eta.
$$

Here $K,\delta,N_0$ depend only on $B_0$ and the fixed analytic parameters.


There is no paired prescaling here: $C=J/(n-1)+Y$, $X=(n/m)C[R,T]$, and $\widetilde X=mX/(m+\kappa)$. Therefore,

$$
\widetilde X=\frac n{m+\kappa}C[R,T],\qquad
\Pi_m\widetilde X\Pi_m=\frac n{m+\kappa}Z.
$$

The scalar displacement is

$$
\left|\frac n{m+\kappa}-1\right|
=\frac{|t-\kappa|}{|m+\kappa|}
\le\frac{4(t+|\kappa|)}n
\quad(m\ge n/2,\ |\kappa|\le m/2).
$$

Hence

$$
\begin{aligned}
\|(B_X-P_m)-Z\|_F
&\le\|\Pi_m(B_X-\widetilde X)\Pi_m\|_F
+\left|\frac n{m+\kappa}-1\right|\|Z\|_F\\
&\le K\frac{\Delta_s+t}{n}+K\frac{t+|\kappa|}{n}\\
&\le K'\left[\frac{\Delta_s+t}{n}+\frac{t(\Delta_s+t)}{n^2}\right].
\end{aligned}
$$

Since $t/n\le1/2$, the last term is absorbed into $K(\Delta_s+t)/n$. If $\Delta_s=t=0$, this displacement is zero. Including the $O(n^{-1})$ difference between $Y$ and $S/n$ gives the uniform error bound $O((\Delta_s+t+1)^2/n)$.

For $\Delta_s,t\ge0$, each of the following terms is at most a fixed multiple of $\eta=(\Delta_s+t+1)^2/n$:

$$
\frac{t+1}n\le\eta,\quad
\frac{\Delta_s+t}n\le\eta,\quad
\frac{(\Delta_s+t)^2}n\le\eta,\quad
\frac{t(\Delta_s+t)}n\le\eta,\quad
\frac{\Delta_s^2}{n^2}\le\eta.
$$

Thus each logarithmic error is $O(\eta)$. The inequality $|e^u-1|\le e^{|u|}|u|$ gives the same order for the relative error. $\square$

<!-- Extraction from 08_detailed_proof.en.md; block=technical-spectral-cap; raw_block_sha256=1566fa652f4782e1a53216f2626610b61615e140ea7ab628ddc485574e2ffdda; copy_block_sha256=1566fa652f4782e1a53216f2626610b61615e140ea7ab628ddc485574e2ffdda; normalization=trailing-tex-control-space-empty-group-v1; transformations=control-space:0. -->

<a id="technical-spectral-cap"></a>

## 6.1 The spectral radius and an elementary uniform bound

**Lemma 6.1 (Spectral cap).** Every tournament sign matrix of order $n$ satisfies

$$
\|S\|_{\rm op}\le\cot\left(\frac\pi{2n}\right)<\frac{2n}\pi,
\qquad \rho_n(S)\le\frac{3n-1}{n+1}<3.
$$

**Proof.** The phase-ordering argument [4, Theorem 3.1] gives the operator bound as follows. Apply a simultaneous signed permutation to $z$ and $S$ so that the phases of the nonzero entries of $z$ lie in increasing order in $[0,\pi)$. Then $c_{ij}=\operatorname{Im}(\overline z_i z_j)\ge0$ for $i<j$, and, for the transitive sign matrix $T_n^0$,

$$
z^*iSz=-2\sum_{i<j}S_{ij}c_{ij}
\le 2\sum_{i<j}c_{ij}=z^*(-iT_n^0)z.
$$

Rayleigh's principle reduces the bound to $T_n^0$. Subtracting consecutive row eigenvalue equations gives $(\lambda-1)v_i=(\lambda+1)v_{i+1}$. The geometric ratio $r=(\lambda-1)/(\lambda+1)$ satisfies $r^n=-1$ by the first row equation. Thus the eigenvalues are $i\cot((2j-1)\pi/(2n))$, $1\le j\le n$. Their largest modulus is $\cot(\pi/(2n))$, and $\tan u>u$ gives the strict inequality (the case $n=1$ is immediate).

For the ratio bound, write the eigenvalues in nonzero pairs $\pm i\lambda_j$ and put $x_j=\lambda_j^2/n^2$. The Frobenius identity gives $\sum_jx_j=(n-1)/(2n)<1/2$. With $\phi(x)=\log((1+x)/(1-x))$, the derivative $\phi'(x)=2/(1-x^2)$ is increasing on $[0,1)$ and $\phi(0)=0$. Hence $\phi(a+b)\ge\phi(a)+\phi(b)$ for $a,b\ge0$, $a+b<1$. Repeatedly merging the $x_j$ gives

$$
\log\rho_n(S)=\sum_j\phi(x_j)
\le\phi\left(\frac{n-1}{2n}\right),
$$

which proves the stated bound, including $n=1$.

The eigenvalue calculation also yields

$$
\det(I+zT_n^0)=\frac{(1+z)^n+(1-z)^n}{2}.
$$

Indeed, each even transitive principal determinant equals one: the positive cotangent frequencies pair with their reciprocals at complementary angles. Odd principal determinants vanish by skew-symmetry. The principal-minor expansion is therefore $\sum_h\binom n{2h}z^{2h}$. $\square$

<!-- Extraction from 08_detailed_proof.en.md; block=technical-algebra; raw_block_sha256=367e0e11472f6d4f97181333616ed6f392c822a92e963729139a72c100edd8ec; copy_block_sha256=4c9b467095a2778603529123f3bf4ef0caac964f0cc04475f53559ee223764f1; normalization=trailing-tex-control-space-empty-group-v1; transformations=control-space:0,edit-9:1. -->

<a id="technical-algebra"></a>

## A. Auxiliary algebra and model calculations

### A.1 The determinant polynomial of the transitive sign matrix

Lemma 6.1 already proves $\det(I+tT_n)=((1+t)^n+(1-t)^n)/2$ at both parities, including the principal-determinant normalization. We use that single proof throughout.

### A.2 Alternating switching and ordinary carousel isomorphism

Let $d=2q+1$. Switch the transitive matrix by alternating signs $\varepsilon_i=(-1)^{i-1}$ and $D_{\varepsilon}=\operatorname{diag}(\varepsilon_i)$. For $i<j$ and $\Delta=j-i$,

$$
(D_{\varepsilon}T_dD_{\varepsilon})_{ij}=(-1)^\Delta.
$$

Define the carousel labeling map

$$
\phi(i)=(q+1)i\pmod d.
$$

Since $2(q+1)=d+1$, the numbers $q+1$ and $d$ are coprime, making $\phi$ a permutation.

If $\Delta=2r$, then $1\le r\le q$ and

$$
\phi(j)-\phi(i)\equiv(q+1)2r\equiv r\pmod d.
$$

This difference belongs to $\{1,\ldots,q\}$, precisely the condition for $\phi(i)\to\phi(j)$ in the carousel. The switched matrix entry is also 1.

If $\Delta=2r+1$, then $0\le r\le q-1$ and

$$
\phi(j)-\phi(i)\equiv q+1+r\pmod d.
$$

This difference belongs to $\{q+1,\ldots,2q\}$, so the direction is reversed; the switched matrix entry is $-1$. Skew symmetry handles $i>j$, and all diagonal entries are zero. Thus the map preserves each directed edge and is an ordinary isomorphism.

The spectral arguments in the main paper also use equality of the diagonal entries of powers of the transitive matrix. Define $Ze_j=e_{j+1}$ for $j<d$ and $Ze_d=-e_1$. When $i,j<d$,

$$
(Z^TT_dZ)_{ij}=(T_d)_{i+1,j+1}=(T_d)_{ij}.
$$

When $i<d,j=d$,

$$
(Z^TT_dZ)_{i,d}=-(T_d)_{i+1,1}=1=(T_d)_{i,d}.
$$

When $i=d,j<d$,

$$
(Z^TT_dZ)_{d,j}=-(T_d)_{1,j+1}=-1=(T_d)_{d,j}.
$$

The remaining diagonal entry is zero in both matrices. Therefore $Z^TT_dZ=T_d$, and for every integer $p\ge0$,

$$
Z^TT_d^{2p}Z=T_d^{2p}.
$$

Taking diagonal entries makes adjacent diagonal entries equal, with the two wraparound minus signs canceling.

### A.3 Fourth-order determinants and fourth-moment equality

Let $a,b,c,g,e,f\in\mathbb R$ and set

$$
M=\begin{pmatrix}
0&a&b&c\\
-a&0&g&e\\
-b&-g&0&f\\
-c&-e&-f&0
\end{pmatrix}.
$$

The Pfaffian formula gives

$$
\det M=\operatorname{Pf}(M)^2=(af-be+cg)^2.
$$

When all six variables are $\pm1$, the expression $af-be+cg$ is a sum of three numbers in $\pm1$, taking values $\pm1$ or $\pm3$. Thus the determinant is 1 or 9. Let $D_4(S)$ count four-vertex principal determinants equal to 9. Expand by column multilinearity, choosing in each column either the identity column or the corresponding column of $tS$:

$$
\det(I+tS)=\sum_{U\subseteq[d]}t^{|U|}\det S[U].
$$

An odd-order skew-symmetric matrix $B$ satisfies $\det B=\det B^T=\det(-B)=-\det B$, so its determinant vanishes. Every second-order principal determinant is 1. Among fourth-order determinants, $D_4$ are 9 and all others are 1. Therefore

$$
\det(I+tS)=1+e_2t^2+e_4t^4+O(t^6),
$$

$$
e_2=\binom d2,\qquad
e_4=(\binom d4-D_4)+9D_4=\binom d4+8D_4.
$$

Use the following expansion only near $t=0$. Choose $|t|\,\|S\|_{\rm op}<1/2$. Every eigenvalue $\mu$ then satisfies $|t\mu|<1/2$. Define $\log(1+t\mu)$ by the logarithmic series with value 0 at 1. Interchanging the power series with a finite eigenvalue sum is valid, and

$$
\det(I+tS)=\prod_\mu(1+t\mu),\qquad
\operatorname{tr}S^k=\sum_\mu\mu^k.
$$

Eigenvalues are counted with multiplicity. The real skew-symmetric canonical form gives diagonalizability over the complex numbers; zero eigenvalues are included.

The logarithmic series for each eigenvalue gives

$$
\log\det(I+tS)
=\sum_{k\ge1}\frac{(-1)^{k+1}t^k}{k}\operatorname{tr}S^k
=-\frac{t^2}{2}\operatorname{tr}S^2
-\frac{t^4}{4}\operatorname{tr}S^4+O(t^6).
$$

Odd traces vanish because $\operatorname{tr}S^{2j+1}=\operatorname{tr}(S^{2j+1})^T=-\operatorname{tr}S^{2j+1}$. On the other hand, substitute $z=e_2t^2+e_4t^4+O(t^6)$ into $\log(1+z)=z-z^2/2+O(z^3)$. Since $z^2=e_2^2t^4+O(t^6)$ and $z^3=O(t^6)$, this gives

$$
\log\det(I+tS)=e_2t^2+(e_4-e_2^2/2)t^4+O(t^6).
$$

Comparing the coefficients of $t^4$ gives

$$
-\operatorname{tr}S^4/4=e_4-e_2^2/2,\qquad
\operatorname{tr}S^4=2e_2^2-4e_4
=2\left(\binom d2\right)^2-4\binom d4-32D_4(S).
$$

In the transitive matrix, any four vertices in increasing order have $a=b=c=g=e=f=1$, giving determinant $(1-1+1)^2=1$. Thus $D_4(T_d)=0$. Subtracting yields

$$
\operatorname{tr}T_d^4-\operatorname{tr}S^4=32D_4(S).
$$

If the fourth moments agree, $D_4(S)=0$. Choose $\varepsilon_1=1,\varepsilon_j=s_{1j}$ for $j>1$, and define $D_{\varepsilon}=\operatorname{diag}(\varepsilon_1,\ldots,\varepsilon_d)$ and $S'=D_{\varepsilon} S D_{\varepsilon}$. Then $s'_{1j}=\varepsilon_1s_{1j}\varepsilon_j=s_{1j}^2=1$. Each principal determinant is multiplied by $(\det D_{\varepsilon}[U])^2=1$, so $D_4$ is unchanged. Choose any $i<j<k$ all different from 1:

$$
\det S'[\{1,i,j,k\}]
=(s'_{jk}-s'_{ik}+s'_{ij})^2.
$$

If these three vertices form a directed triangle, $s'_{ij}=s'_{jk}=-s'_{ik}$, making the expression in parentheses $3s'_{ij}$ and its square 9, a contradiction. Thus the remaining vertices contain no directed triangle. If $i\to j$ and $j\to k$ but $i\not\to k$, then $k\to i$, producing a triangle. The direction relation is therefore a strict total order, and we can label vertices in this order. Vertex 1 dominates all remaining vertices, making the entire switched tournament transitive. Conversely, signed permutation similarity preserves traces, so it gives fourth-moment equality. For $d=3$, two vertices remain after switching; order them according to their unique edge.

<!-- Extraction from 08_detailed_proof.en.md; block=technical-references; raw_block_sha256=1f98b0b8731d3894c571e1a3720298bf214d1eb37d1bcd346c3a008755e1326a; copy_block_sha256=1f98b0b8731d3894c571e1a3720298bf214d1eb37d1bcd346c3a008755e1326a; normalization=trailing-tex-control-space-empty-group-v1; transformations=control-space:0. -->

<a id="technical-references"></a>

## References


[1] John Irving and Mohamed Omar. Revisiting the Rédei-Berge Symmetric Functions via Matrix Algebra. The Electronic Journal of Combinatorics 32(4) (2025), Paper P4.43, 23 pp. [DOI: 10.37236/13841](https://doi.org/10.37236/13841).

[2] Noga Alon. The Maximum Number of Hamiltonian Paths in Tournaments. Combinatorica 10(4) (1990), 319–324. [DOI: 10.1007/BF02128667](https://doi.org/10.1007/BF02128667).

[3] Yanjun Han and Jonathan Niles-Weed. Approximate independence of permutation mixtures. The Annals of Statistics, to appear ([author's publication list](https://yanjunhan2021.github.io/publication.html)). [arXiv:2408.09341v2](https://arxiv.org/html/2408.09341v2) (9 September 2024); the lemma numbers cited in the text refer to this version.

[4] Bo Deng, Xueliang Li, Bryan Shader and Wasin So. On the Maximum Skew Spectral Radius and Minimum Skew Energy of Tournaments. Linear and Multilinear Algebra 66(7) (2018), 1434–1441. [DOI: 10.1080/03081087.2017.1357676](https://doi.org/10.1080/03081087.2017.1357676).

[5] Peter McCullagh. An asymptotic approximation for the permanent of a doubly stochastic matrix. Journal of Statistical Computation and Simulation 84(2) (2014), 404–414. [DOI: 10.1080/00949655.2012.712122](https://doi.org/10.1080/00949655.2012.712122). [arXiv:1205.5723](https://arxiv.org/abs/1205.5723).

[6] N. C. Wormald. Tournaments with many Hamilton cycles. arXiv:2610.16245v1 (2026). [Version](https://arxiv.org/html/2610.16245v1).

[7] Ehud Friedgut and Jeff Kahn. On the Number of Hamiltonian Cycles in a Tournament. Combinatorics, Probability and Computing 14(5–6) (2005), 769–781. [DOI: 10.1017/S0963548305006863](https://doi.org/10.1017/S0963548305006863).

[8] Eric Li. The Godsil–McKay Asymptotic for Latin Rectangles in the Sublinear Range of Erdős Problem 725. [arXiv:2608.01671v1](https://arxiv.org/html/2608.01671v1) (2026).

[9] Ilan Adler, Noga Alon and Sheldon M. Ross. On the Maximum Number of Hamiltonian Paths in Tournaments. Random Structures & Algorithms 18(3) (2001), 291–296. [DOI: 10.1002/rsa.1010](https://doi.org/10.1002/rsa.1010).

[10] Tibor Szele. Kombinatorikai vizsgálatok az irányított teljes gráffal kapcsolatban. Matematikai és Fizikai Lapok 50 (1943), 223–256. [Original volume archive](https://real-j.mtak.hu/7300/).

[11] Yijia Fang and Hao Huang. Maximizing directed cycles in tournaments. arXiv:2608.06238v1 (2026). [arXiv version](https://arxiv.org/html/2608.06238v1#S3).

[12] Alexander Divoux and Shouda Wang. The maximum number of Hamiltonian cycles in tournaments. arXiv:2610.23755v1 (2026). [arXiv version](https://arxiv.org/html/2610.23755v1).

[13] Deep Bhattacharjee. *Two conjectures of Wormald on Hamilton cycles in tournaments*. Hexagon preprint 2610.00460v2 (2026). [Version](https://hexagonmath.org/2610.00460v2).



[14] Xingchen Liu. *Constant-factor bounds for Hamiltonian paths in tournaments*, v1.0 (8 October 2026). [Version DOI: 10.5281/zenodo.23233166](https://doi.org/10.5281/zenodo.23233166). Later archive: v1.2, [10.5281/zenodo.23288896](https://doi.org/10.5281/zenodo.23288896).

[15] Xingchen Liu and Xiangyu Ye. Wormald tournament project, manuscript revision `2fd6a2c30260b826feef71049d7d593527fd7a42` (19 October 2026). [Fixed manuscript](https://github.com/LStar404/wormald-tournament-conjectures/blob/2fd6a2c30260b826feef71049d7d593527fd7a42/docs/paper.zh.md).

[16] Deep Bhattacharjee. *Two conjectures of Wormald on Hamilton cycles in tournaments*, release v1.0.0 (14 October 2026). [Release and source archive](https://github.com/creelie/Breakthrough-problems-1/releases/tag/v1.0.0).

[17] Liu--Ye. *Tournament Hamiltonian counts*: source and formal-coverage snapshot `c678e9ee24fb304cad755a27c99f511c8640f75e`. [Fixed repository revision](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/tree/c678e9ee24fb304cad755a27c99f511c8640f75e).
