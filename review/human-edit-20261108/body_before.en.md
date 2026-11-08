## 2. Preliminaries and notation

### 2.1 The random baseline and error conventions


Let $\mathfrak S_n$ be the symmetric group on $[n]$, and let $I_\pi$ indicate that the consecutive edges of $\pi$ all point forward. Each ordering uses $n-1$ distinct undirected edges, so

$$
H(T)=\sum_{\pi\in\mathfrak S_n}I_\pi(T),\qquad
\mathbb E I_\pi=\prod_{j=1}^{n-1}\frac12=2^{-(n-1)},
$$

$$
\mathbb EH(T)=\sum_{\pi\in\mathfrak S_n}\mathbb EI_\pi
=n!2^{-(n-1)}=\mu_n.
$$

The maximum is at least the mean, so $P(n)\ge\mu_n$. Let $\mathcal T_n$ denote all tournaments with vertex labels $[n]$. In this paper, a uniform $O(n^{-1})$ error means

$$
\exists K<\infty\ \exists n_0\ \forall n\ge n_0\ \forall T\in\mathcal T_n:
\quad |\mathrm{error}(n,T)|\le K/n.
$$

The constants $K,n_0$ are uniform over tournaments and deletion sets. They may depend on additional fixed parameters $b,A_0,B_0$, when present.



### 2.2 Sign matrices and spectral factors


**Definition 2.1 (Sign matrices and scores).**

The adjacency matrix $A$ has zero diagonal and $A_{ij}=1$ precisely when $i\to j$. Define

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1.
$$

Here $I$ is the identity matrix in the current dimension, $J=\mathbf1\mathbf1^{\mathsf T}$, and $\mathbf1$ is the all-ones column vector. In $I_p,J_p,\mathbf1_p$, the subscript explicitly specifies the dimension $p$. The superscript $\mathsf T$ denotes transpose. If $d_i^+$ is the outdegree, then $s_i=2d_i^+-(n-1)$ and $\sum_i s_i=0$. The Euclidean and maximum vector norms are

$$
\|x\|_2=\left(\sum_i|x_i|^2\right)^{1/2},\quad
\|x\|_\infty=\max_i|x_i|.
$$

We use the notation

$$
\mathcal E=\|s\|_2^2,\qquad d=\|s\|_\infty,\qquad
a=\frac{s}{n-1},\qquad \tau=\|a\|_2^2.
$$

The normalized scores $a$ and $\tau$ are defined for $n\ge2$. An odd-order tournament is regular when every vertex has outdegree $(n-1)/2$, equivalently $s=0$. An even-order tournament is balanced when every outdegree is $n/2$ or $n/2-1$, equivalently $s_i\in\{-1,1\}$. Thus $d$ measures the largest vertex imbalance, whereas $\tau$ measures the total squared imbalance after normalization.


**Definition 2.2 (Submatrices and permanents).**

For a vertex set $U$, the notation $A[U]=A[U,U]$ denotes the principal submatrix. For possibly different row and column sets $R,C$, the submatrix $A[R,C]$ selects those rows and columns, always in increasing original vertex-label order. The same convention applies to a general matrix $M[R,C]$. The complement $U^c$ is taken in the current full vertex set. Empty sums equal zero and empty products equal one; both the determinant and the permanent of the empty matrix equal one. For a square matrix of order $m$, denoted by $M$, the permanent is

$$
\operatorname{per}M=\sum_{\pi\in\mathfrak S_m}\prod_{i=1}^m M_{i,\pi(i)}.
$$


**Definition 2.3 (Frequencies and spectral factors).**

The singular values of a real matrix $M$ are the nonnegative square roots of the eigenvalues of $M^{\mathsf T}M$. The operator norm $\|M\|_{\rm op}=\sup_{\|x\|_2=1}\|Mx\|_2$ equals the largest singular value. The square of the Frobenius norm $\|M\|_F=(\sum_{i,j}|M_{ij}|^2)^{1/2}$ is the sum of the squared singular values. For the skew-symmetric matrix $S$, write $\pm i\lambda_j$ for its nonzero eigenvalue pairs, where $i^2=-1$ and $\lambda_j>0$, adding zero frequencies when needed. Each $\lambda_j$ occurs twice among the singular values. Define

$$
x_j=\frac{\lambda_j^2}{n^2},\qquad
D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2},
$$

$$
\rho_n(S)=D_n(S)\det(I+S/n)=\prod_j\frac{1+x_j}{1-x_j}.
$$


The skew-symmetric singular values occur in pairs, and $\|S\|_F^2=n(n-1)$, so

$$
\sum_jx_j=\frac{n-1}{2n},\qquad \|S/n\|_{\rm op}^2\le\frac{n-1}{2n}<\frac12.
$$

Therefore $D_n$ and $\rho_n$ are positive and bounded by absolute constants. In particular,

$$
D_n(S)=\det(I+iS/n)^{-1}.
$$


For every $i$,

$$
s_i=\sum_{j\ne i}(A_{ij}-A_{ji})
=d_i^+-[(n-1)-d_i^+]=2d_i^+-(n-1),
$$

$$
\sum_i s_i=\sum_{i<j}(S_{ij}+S_{ji})=0,\qquad
\|S\|_F^2=\sum_{i\ne j}1=n(n-1).
$$

In a real orthonormal basis, a real skew-symmetric matrix becomes a direct sum of blocks $\left(\begin{smallmatrix}0&\lambda_j\\-\lambda_j&0\end{smallmatrix}\right)$ and zero blocks. Consequently,

$$
\det(I+S/n)=\prod_j(1+\lambda_j^2/n^2)=\prod_j(1+x_j),
$$

$$
\begin{aligned}
\det(I-S^{\mathsf T}S/n^2)&=\prod_j(1-x_j)^2,\\
D_n(S)&=\prod_j(1-x_j)^{-1},\\
\det(I+iS/n)&=\prod_j(1-\lambda_j/n)(1+\lambda_j/n)
=\prod_j(1-x_j),\\
\rho_n(S)&=\prod_j\frac{1+x_j}{1-x_j}.
\end{aligned}
$$

Each frequency occurs twice in the squared Frobenius norm, so

$$
2\sum_j\lambda_j^2=n(n-1),\qquad
\sum_jx_j=\frac{n-1}{2n},\qquad
\|S/n\|_{\rm op}^2\le\sum_jx_j<\frac12.
$$

For $n=1$, we have $S=[0]$, the frequency sum is empty, and $D_1(S)=\rho_1(S)=1$.

Every $\log$ below is a natural logarithm. Using $-\log(1-x)=\int_0^x(1-u)^{-1}\,du\le2x$ for $0\le x\le1/2$, we obtain

$$
0\le\log D_n(S)\le2\sum_jx_j<1,\qquad 1\le D_n(S)<e.
$$

Similarly, $\log(1+x)\le x$ gives $\log\rho_n(S)<3/2$. Multiplication by $D_n(S)$ or $\rho_n(S)$ therefore preserves the order of the error. Lemma 6.1 gives a sharper bound.

## 3. A uniform permanent approximation

The counting argument needs a permanent estimate uniform under scaling and logarithmically many independent row and column deletions. We state the analytic theorem with its exact parameters; its full coefficient proof is in **Detailed proof companion, §§3.2–3.6**, retaining the original numbering. This section gives the proof structure and the estimates that close it. The supplement forms an integral part of the proof.

McCullagh [5] obtained the determinant main term under moderate-deviation assumptions. The argument retained here comes from the earlier path project [14]. It allows signed inputs, although Sections 4–8 use only the nonnegative case. Divoux–Wang [12] give a related nonnegative theorem with an $o(1)$ error; extracting the $O(n^{-1})$ rate uses the uniform coefficient and tail estimates recorded below.

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

**Proof with the coefficient estimates delegated to the supplement.** Choose fixed $1<\sigma<R<1/q$ (omit the upper restriction if $q=0$), and put

$$
f(z)=\frac{\operatorname{per}(J_n+zE)}{n!},\qquad
G(z)=\det(I-z^2BB^{\mathsf T})^{-1/2},\qquad
\Gamma(r)=\exp\!\left(\frac{C^2r^2}{2(1-q^2r^2)}\right).
$$

Since $\|B\|_F^2\le C^2$, $1\le G(1)\le\Gamma(1)$ and $|G(z)|\le\Gamma(|z|)$ on the fixed disk. The positive square-root branch is determined at zero.

Separate inclusion–exclusion for row and column indices expresses coefficients as bipartite multigraph sums. Double centering eliminates degree-one vertices. Degree-two components are exactly the Gaussian pairings and sum to $G$. For the remaining components, contract degree-two chains **before taking absolute values**: the alternating products of $B,B^{\mathsf T}$ retain the spectral gap. A chain of length $\ell\ge2$ has contraction bounded by $C^2q^{\ell-2}/n$. The residual core is classified by excess (edges minus vertices), giving one factor $n^{-1}$ per excess. The exact labeling compensation and the core activity bound are proved in supplement §§3.2–3.3. This order of contraction preserves the operator-norm control.

For some fixed $\alpha>0$, set $M=\lfloor\alpha n\rfloor$. The finite coefficient window, including restoration of $n^k/(n)_k$, has error $K_1/n+K_2/n^2$ (supplement §3.4). Its deviation is of order $k^2/n$, and the Gaussian coefficients are summed with a fixed radius greater than one to absorb this weight. Permanent polarization and the positive-semidefinite permanent estimate give $\max_{|z|=R}|f(z)|\le\exp(\beta\sqrt n)$, up to a fixed factor, where $\beta=RC/(1-Rq)$; Cauchy's estimate then controls the coefficients above $M$ (supplement §3.5). Together these bounds yield

$$
|f(1)-G(1)|\le\frac{K_1}{n}+\frac{K_2}{n^2}
+K_3e^{\beta\sqrt n-\alpha n\log R}
+K_4e^{-\alpha n\log\sigma}.
$$

Every constant and the threshold depend only on $C,q$ and the radii fixed from them. Both exponential terms are $o(n^{-1})$. Finitely many smaller orders are covered using $|f(1)|\le(1+C)^n$ and $G(1)\le\Gamma(1)$. This proves the uniform absolute bound; $G(1)\ge1$ gives the relative form. $\square$

The supplement also records the signed example with fixed parameters at arbitrarily large orders and the two estimates needed to quantify the nonnegative proof of [12]. The applications use the stated nonnegative specialization.

## 4. Scaling and nonprincipal submatrices

Write $a=S\mathbf1/(n-1)$, $\tau=\sum a_i^2$, $P_p=J_p/p$ and $\Pi_p=I_p-P_p$. For a matrix $X$ of order $p$, let $\mathfrak m(X)=\sum X_{ij}$ and $g(X)=(X\mathbf1-\mathbf1,X^{\mathsf T}\mathbf1-\mathbf1)$. The normalization $C=2A/(n-1)$ has marginals $\mathbf1+a$ and $\mathbf1-a$. The three estimates below control balancing, its logarithmic cost, and the Gaussian factor. Their parameter dependence is the input to the uniform bounds in Lemmas 4.4–4.5.

### 4.1 Scaling and Gaussian factors

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

**Proof mechanism.** Fix the gauge $\sum x_i=\sum y_j$. The reference matrix $\mathsf H_0$ has diagonal blocks $I$ and off-diagonal blocks $X_0,X_0^{\mathsf T}$, while the actual linearization $\mathsf H_X$ has diagonal blocks $\operatorname{diag}(X\mathbf1),\operatorname{diag}(X^{\mathsf T}\mathbf1)$ and off-diagonal blocks $X,X^{\mathsf T}$. Put $u=(\mathbf1,-\mathbf1)$ and $N=uu^{\mathsf T}/(2p)$ to fix the gauge. On the zero-sum subspaces, the inverse of $\mathsf H_0+N$ is expressed through $(I-EE^{\mathsf T})^{-1}$ and $(I-E^{\mathsf T}E)^{-1}$. The dense entry bound and operator gap give its induced $1$- and $\infty$-norms at most $L_0$. Both corresponding norms of $\mathsf H_X-\mathsf H_0$ are at most $3\varepsilon$; hence the Neumann series bounds the inverse of $\mathsf H_X+N$ by $2L_0$. The stated threshold then makes the nonlinear map a contraction in the radius $4L_0\varepsilon$ ball. This proves existence and the stated entry and spectral bounds. The block inverse and contraction estimates are supplied in Detailed proof companion §4.1.

For nonnegative $X$, apply this construction to the convex potential

$$
\Phi_X(x,y)=\sum_{ij}X_{ij}e^{x_i+y_j}-\sum x_i-\sum y_j.
$$

Along the segment to the balanced point, its Hessian on the gauge subspace has a positive lower bound depending only on the fixed parameters. Integration gives the two-norm bound, and the entry bound gives the Frobenius displacement. Comparing the potential at zero and at its minimum gives $0\le\theta_X\le K\|g(X)\|_2^2$. Scalar normalization proves the general-mass identity and $-\theta_X\le\kappa$. In particular, the nonnegativity of the potential cost is used at total mass $p$; the general-mass argument uses the one-sided bound $-\theta_X\le\kappa$.

Define $\mathcal G(Z)=\det(I-Z^{\mathsf T}Z)^{-1/2}$ for $\|Z\|_{\rm op}<1$; zero padding and changing to $ZZ^{\mathsf T}$ preserve its value.

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

**Proof.** Integrate the derivative of $-\tfrac12\log\det(I-H)$ along the positive-semidefinite Gram loss caused by deleting rows. Its trace is the sum of the deleted squared row norms. Switch Gram sides for column deletion and apply the same argument to the constant-direction projections. The stability inequality follows along the Gram segment from $\|U^{\mathsf T}U-V^{\mathsf T}V\|_*\le(\|U\|_F+\|V\|_F)\|U-V\|_F$. $\square$

### 4.2 Uniform deletion bounds

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


**Proof.** Use $n=N$ and $m=n-t$. Perform paired score correction and mass normalization:

$$
\begin{aligned}
C&=\frac{2A}{n-1}, & C'&=\operatorname{diag}(\ell)C\operatorname{diag}(r),\\
\nu&=\mathfrak m(C')-n, & \widehat C&=\frac{nC'}{n+\nu},\\
X&=\frac nm\widehat C[R,T], & \kappa&=\mathfrak m(X)-m.
\end{aligned}
$$

Put $v_i=a_i/(1-a_i^2)$, $w_i=a_i^2/(1-a_i^2)$, $V=\sum v_i$, $W=\sum w_i$. The cancellation of the first-order mass change is recorded by the exact identity

$$
\nu=\frac{W^2-V^2+W+2w^{\mathsf T}Sv}{n-1},\qquad |\nu|\le K\mathcal M_\tau.
$$

If $e,f$ are the marginal errors of $\widehat C$, deleting the independent row and column sets gives

<a id="eq-deletion-mass"></a>

$$
\kappa=\frac nm\left[-\sum_{i\in I}e_i-\sum_{j\in J}f_j
+\sum_{i\in I,j\in J}\widehat C_{ij}-\frac{t^2}{n}\right].\tag{4.1}
$$

Normalize $\widetilde X=mX/(m+\kappa)$. The preprocessing estimates in Detailed proof companion §4.3 give, uniformly,

$$
|\kappa|\le K(t\sqrt{\tau/n}+t^2/n),\quad
\|g(\widetilde X)\|_\infty\le K(\sqrt{\tau/n}+t/n),\quad
\|g(\widetilde X)\|_2\le K(\sqrt\tau+t/\sqrt n).
$$

The entries of $\widetilde X$ lie in $[0,K/m]$ and its doubly centered kernel has operator norm at most $1/\sqrt2+o(1)$. Fixing the gap $q=3/4$ therefore makes Lemma 4.1 applicable above a common threshold. Its scaling $B_X$ has entries $O(1/m)$, with centered norm eventually at most $4/5$. Lemmas 4.2–4.3 and the same preprocessing give

$$
-\theta_X\le\kappa,\qquad
\log\mathcal G(B_X-P_m)\le\log D_n(S)+K\bigl(\sqrt{\tau/n}+(t+1)/n\bigr).
$$

The exact restoration is

<a id="eq-exact-restoration"></a>

$$
\operatorname{per}A[R,T]=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j
\left[\frac{m(n-1)(n+\nu)}{2n^2}\right]^m
 e^{-\theta_X}\operatorname{per}B_X.\tag{4.2}
$$

Theorem 3.1 gives $\operatorname{per}B_X=(m!/m^m)\mathcal G(B_X-P_m)(1+O(m^{-1}))$. The remaining scalar is $(m!/2^m)(1-1/n)^m(1+\nu/n)^m$, whose logarithmic deviation from $e^{-1}m!/2^m$ is $O((t+1)/n+|\nu|)$. Combining these bounds proves the displayed error exponent. All gaps, densities and thresholds were fixed from $b,A_0,B_0$, which establishes the stated uniform quantifiers. $\square$

**Lemma 4.5 (Permanent approximation for small scores).**

Suppose $d=\|S\mathbf 1_n\|_\infty=o(\sqrt n)$. Fix $0<B_0<\infty$, delete any $t\le B_0\log n$ rows and $t$ columns, and write $m=n-t$. Uniformly over these choices,

<a id="eq-small-score-permanent"></a>

$$
\operatorname{per}A[R,T]=e^{-1}D_n(S)\frac{m!}{2^m}\left[1+O_{B_0}\left(\frac{(d+t+1)^2}{n}\right)\right].
\tag{4.3}
$$

More precisely, for fixed $B_0>0$ there are constants $C_{\mathrm{err}},\delta>0$ and an integer $N_0\ge4$ such that the following holds uniformly for $n\ge N_0$. Let $S$ be a tournament sign matrix and let $I,J\subseteq[n]$ satisfy $|I|=|J|=t\le B_0\log n$. Put $d=\|S\mathbf1_n\|_\infty$ and $\eta=(d+t+1)^2/n$. If $\eta\le\delta$, the absolute relative error in [equation (4.3)](#eq-small-score-permanent) is at most $C_{\mathrm{err}}\eta$. Here $R=[n]\setminus I$, $T=[n]\setminus J$, and $m=n-t$; the two deleted sets may be chosen independently. In the asymptotic range of the lemma, $\eta\to0$.

**Proof.** Take $X=(n/m)C[R,T]$ directly, without paired score correction. Equation (4.1) and the marginal identities give

$$
|\kappa|=O(t(d+t)/n),\quad
\|g(X)\|_\infty=O((d+t)/n),\quad
\|g(X)\|_2=O((d+t)/\sqrt n).
$$

After normalizing to mass $m$, Lemmas 4.1–4.2 give $|\theta_X|=O((d+t)^2/n)$ and scaling displacement $O((d+t)/n)$. To compare the full Gaussian factors, set $Y=(S-I)/(n-1)$ and use skew-symmetry to obtain

$$
Y^{\mathsf T}Y=\frac{S^{\mathsf T}S+I}{(n-1)^2},\qquad
Y^{\mathsf T}Y-\frac{S^{\mathsf T}S}{n^2}\succeq0.
$$

The last positive-semidefinite difference has trace $O(n^{-1})$, since $\operatorname{tr}(S^{\mathsf T}S)=n(n-1)$. Integrating the log-determinant derivative across this Gram difference, with a fixed spectral gap, gives $|\log\mathcal G(Y)-\log D_n(S)|=O(n^{-1})$. Thus the $O(n^{-1})$ comparison concerns the logarithmic Gaussian factors. Combining it with Lemma 4.3, deletion, centering and scalar normalization gives

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|=O(\eta).
$$

The restoration identity is now $\operatorname{per}A[R,T]=[m(n-1)/(2n)]^m e^{-\theta_X}\operatorname{per}B_X$. Insert Theorem 3.1 and $(1-1/n)^m=e^{-1}\exp(O((t+1)/n))$. The normalized ratio is $e^u(1+v)$ with $|u|\le K\eta$, $|v|\le K/n\le K\eta$. Choose a fixed sufficiently small $\delta$ and use $|e^u-1|\le e^{|u|}|u|$ to obtain the claimed finite, uniform relative-error bound. $\square$

## 5. Path convolution and a determinant representation

### 5.1 Positive path convolution


**Lemma 5.1 (Path convolution).**

For every tournament,

<a id="eq-path-convolution"></a>

$$
H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}A[U^c].
\tag{5.1}
$$


**Proof.**

The permanent of the adjacency matrix counts directed cycle covers. The convolution [equation (5.1)](#eq-path-convolution) converts cycle-cover counts on complementary vertex sets into the path count. It is the tournament specialization of Proposition 2 of Irving and Omar [1], where the complementary adjacency matrix is $\overline A=J-A=I+A^{\mathsf T}$ and includes the diagonal entries.

The identity can also be checked directly using generating functions. Set $X=\operatorname{diag}(z_1,\ldots,z_n)$, the diagonal matrix with diagonal entries $z_1,\ldots,z_n$ and zero off-diagonal entries. More generally, $\operatorname{diag}(v)$ has the entries of the vector $v$ on its diagonal. Multiplying by the corresponding variable whenever a vertex is visited gives the generating function for all walks:

$$
1+\mathbf1^{\mathsf T}(I-XA)^{-1}X\mathbf1
=\frac{\det(I+X\overline A)}{\det(I-XA)}.
$$

The equality follows from the rank-one determinant lemma. Extracting the coefficient of $z_1\cdots z_n$ selects exactly the Hamiltonian paths. The trace of a matrix is the sum of its diagonal entries,

$$
\operatorname{tr}M=\sum_iM_{ii}.
$$

For the denominator, the formal identity $\det(I-XA)^{-1}=\exp(\sum_{r\ge1}\operatorname{tr}((XA)^r)/r)$ shows that the coefficients of squarefree monomials, in which each variable has exponent zero or one, count disjoint directed cycle covers and thus equal permanents. Combining this with the principal-minor expansion of the numerator gives

$$
H(T)=\sum_U\det\overline A[U]\operatorname{per}A[U^c].
$$

Substituting $\overline A[U]=I+A[U]^{\mathsf T}$ proves the identity.

Write $T[U]$ for the subtournament induced by the vertex set $U$, and let $k=|U|$. The symmetric part of $I+A[U]$ is the positive definite matrix $(I+J)/2$. Thus its real eigenvalues are positive, its nonreal eigenvalues occur in conjugate pairs, and its determinant is positive. The squared row norms are $1+d_i^+(T[U])$, whose mean is $(k+1)/2$. Hadamard's inequality and the arithmetic–geometric mean inequality give

$$
0<\det(I+A[U])\le h_k,\qquad h_k=\left(\frac{k+1}{2}\right)^{k/2}.
$$

This proves the convolution and positivity claims. $\square$

Set $h_0=1$ and define

$$
w_k=\frac{2^k h_k}{k!}.
$$


**Lemma 5.1a (Fixed moments and a uniform tail).** For every fixed $c>0$ and integer $r\ge0$,

$$
\sum_{k\ge0}(k+1)^r c^kw_k<\infty.
$$

For sufficiently large $n$, put $k_n=\lceil4\log n/\log\log n\rceil$. There is an absolute constant $C$ such that the normalized contribution of $|U|>k_n$ to (5.1) is bounded uniformly by

$$
B_n:=\frac C2\sqrt{n+1}\sum_{k>k_n}w_k
=n^{-3/2+o(1)}=o(n^{-1}).
$$

**Proof.** Stirling's formula gives $\log(c^kw_k)=-(k/2)\log k+O_c(k)$, and the exact ratio of successive terms is at most $K_c/\sqrt{k+1}$. Hence every fixed moment converges and $\sum_{k>k_n}c^kw_k=n^{-2+o(1)}$. Brégman's bound and degree balancing [2, Lemma 2.1 and Corollary 2.3] give $\operatorname{per}A_T\le C\sqrt{m+1}m!/2^m$ for every tournament of order $m$; enlarge $C$ to include $m=0$. Consequently, the normalized convolution terms of size $k$ are at most

$$
\frac{\binom nk h_k C\sqrt{n-k+1}(n-k)!2^{-(n-k)}}{n!2^{-(n-1)}}
\le\frac C2\sqrt{n+1}\,w_k.
$$

Summing proves the assertion. $\square$

We call $|U|\le k_n$ the short terms. In the error estimates below, retaining the fixed moments of $c^kw_k$ instead of bounding $k$ by $k_n$ avoids logarithmic losses.

### 5.2 The emergence of the spectral factor

First suppose $d=o(\sqrt n)$. By Lemma 4.5, for $|U|=k\le k_n$ we have

$$
\operatorname{per}A[U^c]
=e^{-1}D_n(S)\frac{(n-k)!}{2^{n-k}}
\left(1+O\left(\frac{(d+k+1)^2}{n}\right)\right).
$$

For integers $0\le k\le n$, define the falling factorial by

$$
(n)_k=\prod_{h=0}^{k-1}(n-h),
$$

Thus $(n)_0=1$, and $(n)_k>0$ in this range. The normalization satisfies $((n-k)!/2^{n-k})/\mu_n=2^{k-1}/(n)_k$. Substituting the leading term into Lemma 5.1 therefore gives the normalized sum

$$
\frac{e^{-1}D_n(S)}2
\sum_{|U|\le k_n}\frac{2^{|U|}}{(n)_{|U|}}\det(I+A[U]),
$$

The relative error is uniform over tournaments and sets $|U|\le k_n$. Replacing $(n)_k$ by $n^k$ in the short sum and adding the tail yields the principal-minor identity below; Section 8.1 estimates the resulting errors.

$$
\sum_U(2/n)^{|U|}\det(I+A[U])
=\det\left(I+\frac2n(I+A)\right).
$$

Since $2A=J-I+S$, the rank-one term $J$ asymptotically contributes a factor of two, while the scalar term contributes $e$. More precisely, the small-score assumption gives

$$
\det\left(I+\frac2n(I+A)\right)
=2e\det(I+S/n)\left(1+O(n^{-1}+d^2/n^2)\right).
$$

The factor $e^{-1}$ in the permanent estimate comes from restoring $(1-1/n)^{n-k}$ and reflects the zero diagonal. The factor $1/2$ comes from the path normalization above. They cancel the factor $2e$ in the generating determinant, leaving $D_n(S)\det(I+S/n)=\rho_n(S)$. The two determinants have separate origins: the first approximates cycle-cover counts, and the second sums the weights in the path convolution. Theorem 8.1 will complete the error summation and prove

$$
\frac{H(T)}{\mu_n}=\rho_n(S)+O((d+1)^2/n)
\qquad\text{when }d=o(\sqrt n).
$$

To obtain an upper bound for all tournaments, Section 7 separately handles large score variance and extreme degrees, retaining the score penalty in the remaining class. The next lemma controls this same spectral factor for every tournament.

## 6. The spectral bound and equality

The spectral-ratio bound in this section is due to Divoux and Wang [12, Proposition 7.1], using the comparison of Fang and Huang [11]. The determinant polynomial and the carousel switching are also in [12, Section 7 and Lemma 9.1]. We give the details and follow the equality conditions needed for the fixed-base corollary.


### 6.1 The spectral radius and an elementary uniform bound

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

**Historical remark.** Combining the stronger cap $x_j\le4/\pi^2$ with $\sum_jx_j\le1/2$ gives the earlier constant

$$
C_* =\frac{3\pi^4+4\pi^2-32}{\pi^4+4\pi^2-32}>L.
$$

It is the relaxed convex maximum attained at $4/\pi^2,1/2-4/\pi^2,0,\ldots$. The present proof uses the elementary bound $\rho_n<3$ to exclude exceptional vertices and the all-order sharp comparison in Proposition 6.6 for the final upper bound.

### 6.2 Product comparison and equality

**Theorem 6.2 (Fang–Huang).**

We use the following form of [Fang–Huang, Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3). Define the comparison matrix $K_d$ by

$$
(K_d)_{ij}=\begin{cases}
1,&i+j\le d,\\
0,&i+j=d+1,\\
(-1)^{i+j-d-2},&i+j\ge d+2.
\end{cases}
$$

Let $p\ge1$, let $x\in\mathbb R^d$, and let $S_1,\ldots,S_p$ be tournament sign matrices of order $d$. Write $x^*$ for the vector obtained by arranging the absolute values of the coordinates of $x$ in decreasing order. Then

$$
(S_1\cdots S_p x)^*\prec_w K_d^p x^*.
$$

The right-hand side is a nonnegative decreasing vector. Weak majorization $u\prec_w v$ means

$$
\sum_{i=1}^r u_i\le\sum_{i=1}^r v_i
\quad(1\le r\le d).
$$

Moreover, vector equality in the outermost comparison implies equality for every suffix product. To apply this to Frobenius norms, we first record the squared-norm inequality under weak majorization, including its equality case.


**Lemma 6.3 (Truncated sums under weak majorization).**

Write $(a-t)_+=\max(a-t,0)$. For nonnegative decreasing vectors satisfying $u\prec_w v$ and $t\ge0$,

$$
\sum_{i=1}^d(u_i-t)_+
=\max_{0\le r\le d}\left(\sum_{i=1}^r u_i-rt\right)
\le\max_{0\le r\le d}\left(\sum_{i=1}^r v_i-rt\right)
=\sum_{i=1}^d(v_i-t)_+.
$$


**Proof.**

The first equality follows by taking $r=\#\{i:u_i>t\}$: adding coordinates at most $t$, or removing coordinates greater than $t$, cannot increase the sum. For $a\ge0$, we also have

$$
2\int_0^\infty(a-t)_+\,dt
=2\int_0^a(a-t)\,dt
=2[at-t^2/2]_0^a=a^2.
$$

Integrating coordinate by coordinate gives

$$
\|u\|_2^2
=2\int_0^\infty\sum_i(u_i-t)_+\,dt
\le2\int_0^\infty\sum_i(v_i-t)_+\,dt
=\|v\|_2^2.
$$

Suppose the squared norms are equal. The function $g(t)=\sum_i(v_i-t)_+-\sum_i(u_i-t)_+$ is continuous and nonnegative, with integral zero. If $g(t_0)>0$, then $g(t)>g(t_0)/2$ on an interval of positive length, a contradiction. Thus $g\equiv0$. Comparing right derivatives gives

$$
\#\{i:u_i>t\}=\#\{i:v_i>t\}=:N(t).
$$

For coordinate $j$,

$$
u_j=\int_0^\infty
\mathbf1_{\{\#\{i:u_i>t\}\ge j\}}\,dt
=\int_0^\infty\mathbf1_{\{N(t)\ge j\}}\,dt=v_j.
$$

Equality of squared norms therefore forces $u=v$. Taking $x=e_j$ and using $e_j^*=e_1$ yields

$$
\|S^pe_j\|_2^2\le\|K_d^pe_1\|_2^2.
$$

Equality also forces $(S^pe_j)^*=K_d^pe_1$.


### 6.3 Moments of the comparison matrix

Write $\operatorname{tr}M=\sum_jM_{jj}$.

Let $T_d$ be the transitive tournament sign matrix, with all entries above the diagonal equal to $1$. Let $R_0$ be the reversal permutation matrix and $D_0=\operatorname{diag}(1,-1,\ldots)$. By the definition of $K_d$,

$$
(D_0K_dR_0)_{ij}
=(-1)^{i-1}(K_d)_{i,d+1-j}
=\begin{cases}
(-1)^{i-1},&i<j,\\
0,&i=j,\\
(-1)^j,&i>j.
\end{cases}
$$

Here $R_0e_j=e_{d+1-j}$ and $(D_0)_{jj}=(-1)^{j-1}$. Since $(K_d)_{ij}$ depends only on $i+j$, we have $K_d^T=K_d$.

Write the sequence of increasing odd indices followed by decreasing even indices as

$$
(\ell_1,\ldots,\ell_d)=(1,3,\ldots,d,d-1,d-3,\ldots,2),
\qquad \Lambda e_j=e_{\ell_j}.
$$

Each index occurs once. Hence $\Lambda^T\Lambda=\Lambda\Lambda^T=I$, and $\ell_1=1$.

Permute the rows and columns in this order. Odd indices are increasing, so the corresponding upper-triangular entries are $(-1)^{i-1}=1$; even indices are decreasing, so those entries are $(-1)^j=1$. An odd index precedes an even index, and the corresponding entry is $(-1)^{i-1}$ if $i<j$, or $(-1)^j$ if $i>j$, again equal to $1$. Hence

$$
T_d=\Lambda^TD_0K_dR_0\Lambda.
$$

Set $U=D_0\Lambda$. Since $R_0R_0^T=I$, $\Lambda\Lambda^T=I$ and $K_d^T=K_d$, multiplication gives

$$
\begin{aligned}
T_dT_d^T
&=\Lambda^TD_0K_dR_0\Lambda
\Lambda^TR_0^TK_dD_0\Lambda\\
&=\Lambda^TD_0K_d^2D_0\Lambda=U^TK_d^2U.
\end{aligned}
$$

The first index in this ordering is 1, so $Ue_1=e_1$. Also $T_d^T=-T_d$, hence

$$
T_d^2=-U^TK_d^2U,\qquad
T_d^{2p}=(-1)^pU^TK_d^{2p}U
$$

because each adjacent pair $UU^T$ in the product equals $I$. Consequently,

$$
(-1)^p(T_d^{2p})_{11}
=e_1^TK_d^{2p}e_1
=(K_d^pe_1)^T(K_d^pe_1)
=\|K_d^pe_1\|_2^2.
$$

The signed cyclic shift $Z$ in the proof companion, Appendix A.2 satisfies $Z^TT_dZ=T_d$, and therefore $Z^TT_d^{2p}Z=T_d^{2p}$. Comparing diagonal entries gives $(T_d^{2p})_{j+1,j+1}=(T_d^{2p})_{jj}$ for $j<d$. At $j=d$, the two signs cancel and give $(T_d^{2p})_{11}=(T_d^{2p})_{dd}$. Thus all diagonal entries agree, and

$$
\begin{aligned}
\|T_d^p\|_F^2
&=\operatorname{tr}((T_d^p)^TT_d^p)
=(-1)^p\operatorname{tr}T_d^{2p}\\
&=d(-1)^p(T_d^{2p})_{11}
=d\|K_d^pe_1\|_2^2.
\end{aligned}
$$

Sum the $d$ column inequalities from the preceding section:

$$
\|S^p\|_F^2
=\sum_{j=1}^d\|S^pe_j\|_2^2
\le d\|K_d^pe_1\|_2^2
=\|T_d^p\|_F^2\qquad(p\ge1).
$$

In particular, the inequality holds for every odd $p$, as required in the next section.

### 6.4 The extremum of the spectral ratio

Let $S$ be any tournament sign matrix of order $d$, with nonzero eigenvalues $\pm i\lambda_j$, where $\lambda_j>0$, and put $x_j=\lambda_j^2/d^2$. Since $2\sum_j\lambda_j^2=\|S\|_F^2=d(d-1)$, we have $x_j\le(d-1)/(2d)<1/2$. In the skew-symmetric canonical form, a zero block contributes $1$ to both determinants, while a nonzero two-dimensional block contributes $1+x_j$ and $1-x_j$, respectively. Hence

$$
\det(I+S/d)=\prod_j(1+x_j),\qquad
\det(I+iS/d)=\prod_j(1-x_j)>0.
$$

For $0\le x<1$, integrate the geometric series:

$$
\begin{aligned}
\log\frac{1+x}{1-x}
&=\int_0^x\left(\frac1{1+t}+\frac1{1-t}\right)\,dt\\
&=2\int_0^x\frac{dt}{1-t^2}
=2\sum_{r=0}^\infty\int_0^x t^{2r}\,dt
=2\sum_{r=0}^\infty\frac{x^{2r+1}}{2r+1}.
\end{aligned}
$$

The interchange follows from uniform convergence of the geometric series on $[0,x]$. The skew-symmetric canonical form also gives $\|S^p\|_F^2=2\sum_j\lambda_j^{2p}$. Substituting term by term yields

$$
\begin{aligned}
\log\rho_d(S)
&=2\sum_j\sum_{r=0}^\infty
\frac{\lambda_j^{4r+2}}{(2r+1)d^{4r+2}}\\
&=\sum_{r=0}^\infty
\frac{\|S^{2r+1}\|_F^2}{(2r+1)d^{4r+2}}
\le\sum_{r=0}^\infty
\frac{\|T_d^{2r+1}\|_F^2}{(2r+1)d^{4r+2}}
=\log\rho_d(T_d).
\end{aligned}
$$

Put $r_d=\rho_d(T_d)$. If equality holds above, every nonnegative difference in the series vanishes. The term $r=1$ gives $\|S^3\|_F^2=\|T_d^3\|_F^2$. Since this difference is itself the sum of the nonnegative column differences, equality holds in each column. The equality criterion of Section 6.2 and the suffix equality in Fang–Huang's theorem then give

$$
(S^3e_j)^*=K_d^3e_1,\qquad
(S^2e_j)^*=K_d^2e_1.
$$

Take squared norms in the second identity and sum over $j$:

$$
\operatorname{tr}S^4=\|S^2\|_F^2
=d\|K_d^2e_1\|_2^2
=\|T_d^2\|_F^2=\operatorname{tr}T_d^4.
$$

By the proof companion, Appendix A.3, equality of the fourth moments is equivalent to $S=\Omega^TT_d\Omega$ for a signed permutation matrix $\Omega$. Conversely, $\Omega^T\Omega=I$ implies

$$
I+tS=\Omega^T(I+tT_d)\Omega,\qquad
\det(I+tS)=(\det \Omega)^2\det(I+tT_d)=\det(I+tT_d).
$$

**Lemma 6.4 (The spectral ratio and equality).**

Take $t=1/d$ and $t=i/d$ separately to obtain $\rho_d(S)=r_d$. Thus

$$
\rho_d(S)\le r_d,
\quad\text{with equality if and only if }S=\Omega^TT_d\Omega.
$$


**Proof (Ordinary isomorphism in the regular case).**

Write $\Omega=D_{\varepsilon}P$, where $P$ is a permutation matrix and $D_{\varepsilon}=\operatorname{diag}(\varepsilon_1,\ldots,\varepsilon_d)$ with $\varepsilon_i\in\{-1,1\}$. Put $\varepsilon=(\varepsilon_1,\ldots,\varepsilon_d)^T$. Then

$$
S=P^TD_{\varepsilon}T_dD_{\varepsilon}P,\qquad PSP^T=D_{\varepsilon}T_dD_{\varepsilon}.
$$

Relabel by $P$ and continue to write $S$ for the resulting matrix. If the tournament is regular, then $S\mathbf1=0$, and $D_{\varepsilon}^2=I$ gives

$$
D_{\varepsilon}T_d\varepsilon=0,\qquad T_d\varepsilon=0.
$$

The difference between rows $i$ and $i+1$ has entry 1 in each of columns $i,i+1$ and zero elsewhere. Therefore

$$
0=(T_d\varepsilon)_i-(T_d\varepsilon)_{i+1}=\varepsilon_i+\varepsilon_{i+1}.
$$

It follows that $\varepsilon_i=(-1)^{i-1}\varepsilon_1$. The common sign $\varepsilon_1$ cancels in $D_{\varepsilon}T_dD_{\varepsilon}$, leaving the alternating switching. the proof companion, Appendix A.2 identifies this tournament with $\mathrm{Car}_d$. Thus, among regular tournaments, equality holds only for the carousel, up to isomorphism.


### 6.5 A gap from the sixth moment


![Reversing all arcs between $U=\{1,2\}$ and its complement in $\mathrm{Car}_5$ gives the transitive order $(3,1,4,2,0)$. Circled vertices belong to $U$. This switching conjugates the sign matrix as $S\mapsto DSD$ and preserves the spectral ratio; it need not preserve the Hamiltonian path count.](figures/carousel_switching.png){width=94%}


**Lemma 6.5 (Strict sixth-moment deficit).**

If regular $S$ is not ordinarily isomorphic to the carousel, the preceding equality argument gives

$$
\Delta_3:=\|T_d^3\|_F^2-\|S^3\|_F^2>0.
$$


**Proof.**

Modulo 2, $S\equiv J+I$. Since $J^2=dJ$ and $J^3=d^2J$,

$$
S^3\equiv(J+I)^3
=I+3J+3dJ+d^2J
\equiv I+(1+d+d^2)J\equiv I+J\pmod2.
$$

The last step uses that $d(d+1)$ is even. Also $(S^3)^T=-S^3$, so its diagonal entries vanish and its off-diagonal entries are odd. If $z=2k+1$,

$$
z^2=4k(k+1)+1\equiv1\pmod8.
$$

Pair the skew-symmetric positions in the squared norm:

$$
\|S^3\|_F^2=2\sum_{i<j}((S^3)_{ij})^2
\equiv2\binom d2=d(d-1)\pmod{16}.
$$

This also applies to $T_d$. Thus $\Delta_3$ is a positive multiple of 16, and $\Delta_3\ge16$. Retaining just term $r=1$ in the logarithmic series gives

$$
\log\frac{r_d}{\rho_d(S)}
\ge\frac{\Delta_3}{3d^6}\ge\frac{16}{3d^6}.
$$

Exponentiate and rearrange:

$$
\rho_d(S)\le r_de^{-16/(3d^6)},\qquad
r_d-\rho_d(S)\ge r_d(1-e^{-16/(3d^6)})>0.
$$


The gap depends on the base order $d$. Section 11.2 obtains a corresponding block threshold by comparing the limits.

### 6.6 The sharp comparison at every order

**Proposition 6.6 (All-order spectral comparison).** For every tournament sign matrix $S$ of order $n$, $\rho_n(S)\le r_n$, where $r_n=L+O(n^{-1})$ is the explicit quotient below. The $O(n^{-1})$ constant is absolute and uniform over tournaments.

**Proof.**

For $n=1$ the ratio equals one. The regular equality classification in Section 6 concerns odd orders, but the preceding spectral inequality does not require regularity. To make its use at every order explicit, let $n\ge2$ and write the permutation in Section 6.3 as all odd indices in increasing order followed by all even indices in decreasing order. At odd order this is the original permutation. At even order it is $(1,3,\ldots,n-1,n,n-2,\ldots,2)$. The same entrywise computation gives

$$
T_n=\Lambda^TD_0K_nR_0\Lambda,\qquad
T_n^2=-U^TK_n^2U,\qquad U=D_0\Lambda,
\qquad Ue_1=e_1.
$$

The signed wrap-around shift satisfies $Z^TT_nZ=T_n$ at either parity. Consequently, all diagonal entries of $T_n^{2p}$ coincide. For every integer $p\ge1$, the columnwise Fang–Huang comparison and these identities give

$$
\|S^p\|_F^2\le n\|K_n^pe_1\|_2^2=\|T_n^p\|_F^2.
$$

Substitution into the absolutely convergent logarithmic series of Section 6.4 yields, at every order,

$$
\log\rho_n(S)
=\sum_{r\ge0}\frac{\|S^{2r+1}\|_F^2}{(2r+1)n^{4r+2}}
\le\log\rho_n(T_n).
$$

The determinant polynomial in Lemma 6.1 also holds at both parities. Hence

$$
\rho_n(S)\le r_n
=\frac{(1+1/n)^n+(1-1/n)^n}
{(1+i/n)^n+(1-i/n)^n}
=L+O(n^{-1}).
$$

For the last step, the Taylor estimate for the logarithm gives, for $z\in\{1,-1,i,-i\}$, $n\log(1+z/n)=z+O(n^{-1})$, while the denominator tends to $2\cos1>0$. The quotient therefore has an $O(n^{-1})$ error. These estimates depend on the order alone, not on the tournament. $\square$

## 7. The upper bound for arbitrary tournaments

Write $V_{\rm deg}(T)$ for degree variance, reserving $V(T)$ for the vertex set:

$$
V_{\rm deg}(T)=\sum_i\left(d_i^+-\frac{n-1}{2}\right)^2
=\frac14\|S\mathbf1\|_2^2,
\qquad
\tau=\frac{4V_{\rm deg}(T)}{(n-1)^2}.
$$

The proof has three cases. If $V_{\rm deg}(T)\ge16n^2\log n$, the variance penalty in Brégman's inequality makes the path count negligible. Otherwise, vertices with degrees outside $[(n-1)/20,19(n-1)/20]$ number at most $O(\log n)$. If any such vertices exist, separating them from the rest gives a path count below the random expectation. In the remaining tournaments, normalized scores stay a fixed distance from $\pm1$, and $\tau=O(\log n)$. For them, the permanent estimate below retains the factor $e^{-\tau}$ and controls the final error by $O(n^{-1})$.

The constant $K$ in this section may increase from one occurrence to the next; after the degree thresholds above are fixed, it is absolute. Section 5.1 has already bounded the long terms by $o(n^{-1})\mu_n$, so here we estimate only short terms $|U|\le k_n$.

The three cases require different precision: the high-variance class contributes $o(n^{-1})$ after normalization; the exceptional-vertex class only needs a fixed gap below the baseline $1$; the remaining class carries the sharp $O(n^{-1})$ estimate. All constants in the local scaling lemmas are fixed before taking the common large-order threshold.

**Proposition 7.1 (Uniform sharp upper bound).** There are absolute constants $K,n_0$ such that every tournament $T$ of order $n\ge n_0$ satisfies

$$
H(T)\le (L+K/n)\mu_n.
$$

### 7.1 Applying the nonprincipal permanent estimate

The estimate of Lemma 4.4 allows different deleted row and column sets. We use it below to control edges between the exceptional set and the core. When the deleted sets agree, the score product is retained outside the path convolution.

### 7.2 Large score variance


**Lemma 7.2 (Permanent bound with a variance penalty).**

There is an absolute constant $K$ such that, for every order $m\ge1$, a tournament $Q$ with outdegrees $d_i$ and degree variance $V_{\rm deg}(Q)=\sum_i(d_i-(m-1)/2)^2$ satisfies

$$
\operatorname{per}A_Q\le
K\sqrt{m+1}\frac{m!}{2^m}\exp\left(-\frac{V_{\rm deg}(Q)}{8m^2}\right).
$$


**Proof.**

Concavity of the row-degree factor strengthens the Brégman bound [2]. If some $d_i=0$, the adjacency matrix has a zero row and its permanent is zero. Otherwise, define $f(k)=\log(k!)/k$ for positive integers. Direct calculation gives, for $k\ge2$,

$$
2f(k)-f(k-1)-f(k+1)
=\frac{2[\log k-f(k-1)]-k\log(1+1/k)}{k(k+1)}.
$$

Applying the arithmetic–geometric mean inequality to $1,\ldots,k-1$ gives $\log k-f(k-1)\ge\log2$. Also, $(1+1/k)^k<e<3$, so the numerator is at least $\log(4/3)\ge1/4$. Consequently, on the degree interval $[1,m-1]$, the piecewise linear interpolation of the integer-point function $f(k)+k^2/(8m^2)$ is concave. Jensen's inequality at the mean $\eta=(m-1)/2$ gives

$$
\sum_i f(d_i)
\le m\widetilde f(\eta)-\frac{V_{\rm deg}(Q)}{8m^2}+\frac{1}{32m},
$$

Here $\widetilde f$ is the linear interpolation. The last term handles a half-integer mean and can be omitted when the mean is an integer. Stirling's formula gives

$$
\exp(m\widetilde f(\eta))\le K\sqrt{m+1}\frac{m!}{2^m}.
$$

Combining this with Brégman's row-degree bound proves the variance estimate.

We apply this bound to the tournament associated with each short deleted set. We must therefore check that its variance remains sufficiently large after deletion.

After deleting a size-$k$ set $U$, each remaining centered degree changes by at most $k/2$, and the sum of the original squared deviations at deleted vertices is at most $kn^2/4$. Applying Cauchy–Schwarz to the cross term gives

$$
V_{\rm deg}(T-U)\ge V_{\rm deg}(T)-\frac{kn^2}{4}-k\sqrt{nV_{\rm deg}(T)}.
$$

If $V_{\rm deg}(T)\ge16n^2\log n$, then uniformly for every $k\le k_n$,

$$
V_{\rm deg}(T-U)\ge(1-o(1))V_{\rm deg}(T).
$$

Thus the variance penalty in every short permanent is at most $n^{-2+o(1)}$, absorbing the preceding $\sqrt n$ factor. Summation with the summable determinant weights bounds the total normalized short contribution by $n^{-3/2+o(1)}$. Adding the long-deletion tail gives, uniformly over this graph class,

$$
V_{\rm deg}(T)\ge16n^2\log n\quad\Longrightarrow\quad
H(T)/\mu_n=o(1/n).
$$


Write $L_k=\log(k!)$. Then

$$
\begin{aligned}
2f(k)-f(k-1)-f(k+1)
&=\frac{2(L_{k-1}+\log k)}k-\frac{L_{k-1}}{k-1}
-\frac{L_{k-1}+\log k+\log(k+1)}{k+1}\\
&=\frac{2\log k-2L_{k-1}/(k-1)-k\log(1+1/k)}{k(k+1)}.
\end{aligned}
$$

AM–GM gives

$$
((k-1)!)^{1/(k-1)}\le\frac{1+\cdots+(k-1)}{k-1}=k/2,
$$

Hence $\log k-f(k-1)\ge\log2$. Also, $k\log(1+1/k)<1<\log3$, and

$$
\log(4/3)=\int_1^{4/3}\frac{du}{u}\ge\frac{1/3}{4/3}=\frac14.
$$

The second difference is therefore at least $1/[4k(k+1)]\ge1/(4m^2)$. Set $h(k)=f(k)+k^2/(8m^2)$. Then

$$
2h(k)-h(k-1)-h(k+1)
\ge\frac1{4m^2}-\frac2{8m^2}=0.
$$

If $\eta$ is an integer, $\widetilde h(\eta)=\widetilde f(\eta)+\eta^2/(8m^2)$. If $\eta=k+1/2$, then

$$
\frac{k^2+(k+1)^2}{2}=\eta^2+\frac14,
\quad
\widetilde h(\eta)=\widetilde f(\eta)+\frac{\eta^2+1/4}{8m^2}.
$$

Jensen's inequality therefore gives

$$
\begin{aligned}
\sum_i f(d_i)+\frac{\sum_i d_i^2}{8m^2}
&=\sum_i h(d_i)\le m\widetilde h(\eta)\\
&\le m\widetilde f(\eta)+\frac{m\eta^2}{8m^2}+\frac1{32m},\\
\sum_i f(d_i)&\le m\widetilde f(\eta)
-\frac{\sum_i(d_i-\eta)^2}{8m^2}+\frac1{32m}.
\end{aligned}
$$

For $m=2r+1$, the logarithmic form of Stirling's formula gives

$$
m f(r)=\frac{2r+1}{r}\left[r\log r-r+\tfrac12\log(2\pi r)+O(1/r)\right],
$$

$$
\log(m!/2^m)=m\log(m/2)-m+\tfrac12\log(2\pi m)+O(1/m).
$$

Subtracting and using $r=(m-1)/2$ gives $\tfrac12\log m+O(1)$. For $m=2r$, $\widetilde f(\eta)=[f(r-1)+f(r)]/2$; applying the same formula to each term gives the same difference. Exponentiating therefore yields $K\sqrt{m+1}$. The cases $m=1,2$ are incorporated directly into the constant.


Write $b_i=d_i^+-(n-1)/2$. For a retained vertex, let $e_i$ count its outgoing edges to $U$. Then

$$
b_i'=d_i^+-e_i-(n-k-1)/2=b_i+\delta_i,
\qquad\delta_i=k/2-e_i,\quad |\delta_i|\le k/2.
$$

Thus

$$
\begin{aligned}
V_{\rm deg}(T-U)&=\sum_{i\notin U}(b_i+\delta_i)^2\\
&\ge V_{\rm deg}(T)-\sum_{i\in U}b_i^2-2\left|\sum_{i\notin U}b_i\delta_i\right|\\
&\ge V_{\rm deg}(T)-kn^2/4-k\sum_{i\notin U}|b_i|\\
&\ge V_{\rm deg}(T)-kn^2/4-k\sqrt{nV_{\rm deg}(T)}.
\end{aligned}
$$

When $V\ge16n^2\log n$, the relative losses are respectively at most

$$
\frac{k}{64\log n}=o(1),\qquad
k\sqrt{n/V}\le\frac{k}{4\sqrt{n\log n}}=o(1).
$$

It follows that $V_{\rm deg}(T-U)/(8(n-k)^2)\ge(2-o(1))\log n$, so the penalty is $n^{-2+o(1)}$. Multiplying by $\sqrt n$ and $\sum_kw_k<\infty$ gives $n^{-3/2+o(1)}$.


To estimate the factorial factor in the variance bound, apply the Stirling formula from the proof companion, Appendix B.3. With $c$ denoting its constant,

$$
f(r)=\log r-1+\frac{\log r}{2r}+\frac cr+O(r^{-2}).
$$

First take $m=2r+1$, so that the average outdegree is the integer $r$. Multiplication by $m$ gives

$$
mf(r)=m\log r-m+\left(1+\frac1{2r}\right)\log r
+2c+\frac cr+O(r^{-1}).
$$

The logarithm of the natural scale is

$$
\log(m!/2^m)=m\log(m/2)-m+\frac12\log m+c+O(m^{-1}).
$$

Denote their difference by $\Delta_m$:

$$
\begin{aligned}
\Delta_m
&=m\log\frac{2r}{m}+\log r-\frac12\log m
+c+O(\log m/m)\\
&=m\log(1-1/m)+\frac12\log m-\log2
+\log(1-1/m)+c+O(\log m/m).
\end{aligned}
$$

Since $m\log(1-1/m)=-1+O(1/m)$ and all other terms except $\frac12\log m$ are uniformly bounded, $\Delta_m\le\frac12\log m+K$.

Next take $m=2r$ with $r\ge2$. The mean is $r-1/2$, and linear interpolation gives

$$
m\widetilde f((m-1)/2)=r[f(r-1)+f(r)].
$$

Substitution term by term yields

$$
\begin{aligned}
r[f(r-1)+f(r)]
={}&r\log(r-1)+r\log r-2r\\
&+\frac r{2(r-1)}\log(r-1)+\frac12\log r\\
&+c\frac r{r-1}+c+O(r^{-1}).
\end{aligned}
$$

Subtracting $\log((2r)!/2^{2r})=2r\log r-2r+\frac12\log(2r)+c+O(r^{-1})$ gives

$$
\begin{aligned}
\Delta_{2r}
={}&r\log(1-1/r)
+\frac r{2(r-1)}\log(r-1)\\
&-\frac12\log2+c\frac r{r-1}+O(r^{-1}).
\end{aligned}
$$

The first term is nonpositive. The second satisfies

$$
\frac r{2(r-1)}\log(r-1)
\le\frac12\log r+\frac{\log r}{2(r-1)}
\le\frac12\log r+\frac12,
$$

Here $\log r\le r-1$. The constant term $c r/(r-1)$ has absolute value at most $2|c|$. Thus again $\Delta_m\le\frac12\log m+K$. Exponentiating in both parity cases gives

$$
\exp(m\widetilde f((m-1)/2))\le e^K\sqrt m\,m!/2^m.
$$

The finitely many values of $m$ outside the expansion range are covered by increasing the same $K$. $\square$

### 7.3 Exceptional vertices


![A directed five-cycle in a permanent term and its row-column matching. Shaded vertices form the exceptional set $F=\{f_1,f_2\}$. Cross-block arcs occupy core rows $I=\{x_2,x_3\}$ and core columns $J=\{x_1,x_3\}$, leaving the nonprincipal entry $A[x_1,x_2]$ shown in bold. Only the arcs of this permanent term are drawn.](figures/nonprincipal_matching.png){width=94%}


Assume from now on that $V_{\rm deg}(T)<16n^2\log n$. Define the exceptional set

$$
F=\left\{i:\frac{d_i^+}{n-1}\notin[1/20,19/20]\right\},
\qquad f=|F|,\qquad M=T-F,\qquad N=n-f.
$$

Each exceptional vertex contributes to $V_{\rm deg}(T)$ at least a fixed positive multiple of $n^2$, so $f=O(\log n)$. A nonexceptional vertex originally has absolute score at most $0.9(n-1)$, and deleting $F$ changes its score by at most $f$. Consequently, uniformly for all sufficiently large $n$,

$$
\max_i|(S_M\mathbf1)_i/(N-1)|<0.95,\qquad
\tau_M=O(\log n).
$$

For the squared score sum, use $\|S_M\mathbf1\|_2\le\|S\mathbf1\|_2+f\sqrt N$ and divide by $N-1$. The same argument remains valid after further deleting a short core subset. Throughout these deletions the original exceptional set $F$ is retained, allowing the constants to be chosen uniformly.

First classify cycle covers according to their connections between $F$ and the core $M$, thereby estimating $\operatorname{per}A_T$. An exceptional vertex has few neighbors in one direction. A cycle cover must use edges in both directions unless that vertex is matched within $F$, and the latter choice incurs a cost of order $1/N$. Use the paired core weights $\ell,r$ from Lemma 4.4, whose total deviation satisfies

$$
\sum_{i\in M}|\ell_i-1|+\sum_{i\in M}|r_i-1|
\le K\sqrt{N\log n}.
$$

For $x\in F$, write $q_x=N^{-1}|\{j\in M:x\to j\}|$. Its distance from $[0,1/20]\cup[19/20,1]$ is $O(f/n)$. The weighted sums of cross-edge neighbors on the two sides are bounded by $N(q_x+\beta)$ and $N(1-q_x+\beta)$, where $\beta=O(\sqrt{\log n/n})$. Set

$$
u_x=2(q_x+\beta),\qquad v_x=2(1-q_x+\beta).
$$

Uniformly for every $x$, we may choose

$$
u_xv_x\le c_n=19/100+o(1),\qquad
u_x,v_x\le L_n=2+o(1).
$$

Decompose the permanent according to the permutation edges lying inside $F$. If there are $s$ internal edges, their row set $R$ and column set $C$ both have size $s$, and there are exactly $t=f-s$ cross edges in each direction. The deleted core row and column sets $I,J$ both have size $t$, but need not coincide. The exact four-block expansion is

$$
\operatorname{per}A_T
=\sum_{s=0}^{f}
\sum_{\substack{R,C\subseteq F\\|R|=|C|=s}}
\sum_{\substack{I,J\subseteq M\\|I|=|J|=f-s}}
\operatorname{per}A[R,C]\,
\operatorname{per}A[F\setminus R,J]\,
\operatorname{per}A[I,F\setminus C]\,
\operatorname{per}A[M\setminus I,M\setminus J].
$$

Every contributing permutation belongs to exactly one class. First apply the uniform bound of Lemma 4.4 to the core permanent and then separate the two cross-edge sums. Deleting a core row contributes $\ell_i$, and deleting a core column contributes $r_j$. For fixed $R,C$, the outgoing cross-edge sum is exactly

$$
\begin{aligned}
&\sum_{\substack{J\subseteq M\\|J|=t}}
\operatorname{per}A[F\setminus R,J]\prod_{j\in J}r_j\\
&=\sum_{\phi:F\setminus R\hookrightarrow M}
\prod_{x\in F\setminus R}A_{x,\phi(x)}r_{\phi(x)}
\le\prod_{x\in F\setminus R}\sum_{j\in M}A_{xj}r_j.
\end{aligned}
$$

Independently, the incoming cross-edge sum is

$$
\begin{aligned}
&\sum_{\substack{I\subseteq M\\|I|=t}}
\operatorname{per}A[I,F\setminus C]\prod_{i\in I}\ell_i\\
&=\sum_{\psi:F\setminus C\hookrightarrow M}
\prod_{y\in F\setminus C}A_{\psi(y),y}\ell_{\psi(y)}
\le\prod_{y\in F\setminus C}\sum_{i\in M}A_{iy}\ell_i.
\end{aligned}
$$

Here $\hookrightarrow$ means an injection. Each injection is counted exactly once by its image set and its corresponding permanent term, with no extra factor $t!$. The image sets $I,J$ need neither coincide nor be disjoint: they belong to the row and column copies of the core, respectively. Since every factor is nonnegative, the injectivity restrictions may be dropped. The product of the two upper bounds is

$$
N^{2t}2^{-2t}
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right).
$$

The permanent inside the exceptional set is at most $s!$. After division by $n!/2^n$, the full factor restoring factorials and powers of two is

$$
2^sN^{2t}\frac{(N-t)!}{(N+f)!}
=\left(\frac2N\right)^s\exp(O(f^2/N)).
$$

Here $N+f-(N-t)=f+t=2f-s$, so the factorial ratio contributes $N^{-(2f-s)}\exp(O(f^2/N))$. Multiplication by $N^{2t}$ leaves exactly $N^{-s}$.

Let $h=|R\cap C|$. The paired product satisfies

$$
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right)
\le c_n^{f-2s}L_n^{2s}(c_n/L_n^2)^h
\le c_n^{f-2s}L_n^{2s}.
$$

The first inequality follows by counting vertices carrying two factors, one factor or no factor; it remains valid even when $f-2s$ is negative. For $t\le f=O(\log n)$, the error in Lemma 4.4 is uniformly $o(1)$, and its factor $\Gamma\le1$ may be discarded. Using $\binom fs^2s!\le f^{2s}/s!$, the full sum gives

$$
\frac{\operatorname{per}A_T}{n!/2^n}
\le(1+o(1))e^{-1}D_N(S_M)c_n^f
\exp(O(f^2/N))
\exp\left(\frac{2L_n^2f^2}{c_n^2N}\right).
$$

All additional exponents here are $o(1)$. More explicitly, after deleting a short core subset $U$, the core order is $N'=n-f-|U|\sim n$, meaning $N'/n\to1$, while the exceptional set remains the original $F$. The normalized core scores are still eventually at most $0.95$, their squared sum is $O(\log n)$, and the cross-edge deletion size is $t\le f=O(\log n)$. Hence the error exponent in Lemma 4.4 is

$$
O\!\left(\frac{(\log n)^{3/2}}{\sqrt n}+\frac{(\log n)^2}{n}\right)=o(1),
$$

The constants are independent of $U,I,J$. The cross-edge neighbor proportions change from those in the original graph by only $O((f+|U|)/n)$, and the total one-norm deviation of the weights remains $O(\sqrt{n\log n})$. Thus the cross-edge sum estimates above also hold uniformly. The core Gaussian factor becomes $\exp(O(|U|/n))$ times the original one: applying the Gaussian row-and-column deletion lemma to $S_M/N$ gives logarithmic loss $O(|U|/n)$, and changing the normalization scale from $N$ to $N-|U|$ has the same order of cost.

In the path convolution, the proportion of size-$k$ subsets intersecting $F$ is at most $fk/n$. The general permanent bound therefore bounds their full normalized short contribution by

$$
K\frac f{\sqrt n}\sum_k kw_k=o(1).
$$

For subsets contained in the core, restore the falling factorial and sum the positive principal minors. For every core order $N\le n$, the rank-one determinant identity gives

$$
\det\left(I_N+\frac2n(I_N+A_M)\right)
\le2e\det(I_N+S_M/N).
$$

To prove this, first factor out $(1+1/n)^N\le e$. The remaining all-ones rank-one factor is at most $1+N/(n+1)<2$, because the real quadratic form of the inverse of $I+S_M/(n+1)$ is at most the squared vector norm. Finally, the skew-frequency determinant product increases monotonically as the scale increases from $1/(n+1)$ to $1/N$.

Restoring the falling factorial for short subsets contributes $\exp(O(k_n^2/n))=1+o(1)$. Since eventually $c_n<1/4$, the uniform estimates above give

$$
\frac{H(T)}{\mu_n}
\le(1/4)^f\rho_N(S_M)+o(1)
\le 3/4+o(1)<1,\qquad f\ge1.
$$

Since $P(n)\ge\mu_n$, every maximizing tournament of sufficiently large order has no exceptional vertex. A weaker bound for short convolution terms avoiding $F$ is $(10/3)4^{-f}(1+\varepsilon_n)$. Denote the combined contribution of the other short terms and the long terms by $\delta_n$. Then

<a id="eq-exceptional-bound"></a>

$$
\frac{H(T)}{\mu_n}\le\frac{10}{3}4^{-f}(1+\varepsilon_n)+\delta_n,
\qquad \varepsilon_n,\delta_n\longrightarrow0.
\tag{7.1}
$$

Both errors tend to zero uniformly over the low-variance class. Take $n$ large enough that $1+\varepsilon_n\le21/20$ and that the short terms meeting $F$ and the long terms each contribute at most $1/25$. For $f\ge1$, [equation (7.1)](#eq-exceptional-bound) gives

$$
\frac{10}{3}\cdot\frac14\cdot\frac{21}{20}+\frac1{25}+\frac1{25}
=\frac{191}{200}<1.
$$

Either choice leaves the final upper-bound constant unchanged.


An exceptional vertex satisfies

$$
|d_i^+-(n-1)/2|>\frac9{20}(n-1),\quad
f\frac{81}{400}(n-1)^2\le V_{\rm deg}(T)<16n^2\log n,
$$

Hence $f<(6400/81)(n/(n-1))^2\log n$. For the core,

$$
\max_i|s_i^M|\le0.9(n-1)+f,
\quad \frac{0.9(n-1)+f}{n-f-1}\longrightarrow0.9,
$$

$$
\tau_M\le\frac{2\|s\|_2^2+2f^2N}{(N-1)^2}
=O(\log n)+O((\log n)^2/n)=O(\log n).
$$

Since $|\ell_i-1|\le|a_i|/(1-b)$ and $|r_i-1|\le|a_i|/(1-b)$,

$$
\sum_i(|\ell_i-1|+|r_i-1|)
\le\frac2{1-b}\sum_i|a_i|
\le\frac2{1-b}\sqrt{N\tau_M}=O(\sqrt{N\log n}).
$$

This bounds the difference between the weighted and unweighted count of any neighbor subset by the total deviation above. Specifically,

$$
\sum_jA_{xj}r_j\le Nq_x+K\sqrt{N\log n},\quad
\sum_iA_{ix}\ell_i\le N(1-q_x)+K\sqrt{N\log n}.
$$

For $q\in[0,1/20]\cup[19/20,1]$, we have $4q(1-q)\le4(1/20)(19/20)=19/100$. The $O(f/n)$ perturbation of the neighbor proportion and the perturbation $\beta=o(1)$ together give $u_xv_x\le19/100+o(1)$.

In the four-block expansion, $t=f-s$. There are $s$ edges within the exceptional set, $t$ from the exceptional set to the core, $t$ from the core to the exceptional set, and $N-t$ within the core. Their total is

$$
s+t+t+(N-t)=N+f=n.
$$

There are no signs in a permanent expansion, and each permutation occurs once after classification. The full powers-of-two and factorial factor is

$$
\frac{[(N-t)!/2^{N-t}]\,[N^{2t}/2^{2t}]}{(N+f)!/2^{N+f}}
=2^{f-t}N^{2t}\frac{(N-t)!}{(N+f)!}
=2^sN^{2t}\frac{(N-t)!}{(N+f)!}.
$$

Since

$$
\frac{(N-t)!}{(N+f)!}=\prod_{h=-t+1}^{f}\frac1{N+h}
=N^{-(f+t)}\exp\left(-\sum_{h=-t+1}^{f}\log(1+h/N)\right),
$$

and $\sum|h|/N=O(f^2/N)$, this becomes

$$
2^sN^{2t-(f+t)}e^{O(f^2/N)}=(2/N)^se^{O(f^2/N)}.
$$

If $h=|R\cap C|$, the vertices carrying both $u,v$ number $f-2s+h$, and those carrying just one factor number $2s-2h$. Consequently,

$$
c_n^{f-2s+h}L_n^{2s-2h}
=c_n^{f-2s}L_n^{2s}(c_n/L_n^2)^h
\le c_n^{f-2s}L_n^{2s}.
$$

Summing over all choices of internal edges gives

$$
\begin{aligned}
\sum_{s=0}^f\binom fs^2s!(2/N)^sc_n^{f-2s}L_n^{2s}
&\le c_n^f\sum_{s=0}^f\frac1{s!}
\left(\frac{2L_n^2f^2}{c_n^2N}\right)^s\\
&\le c_n^f\exp\left(\frac{2L_n^2f^2}{c_n^2N}\right).
\end{aligned}
$$

Below, $\#E$ and $|E|$ both denote the cardinality of a finite set $E$. When $k=0$, the deleted set avoids the exceptional set, and the proportion is zero. For $1\le k\le n$, the proportion satisfies

$$
\frac{\#\{U:|U|=k,U\cap F\ne\varnothing\}}{\binom nk}
\le\sum_{x\in F}\frac{\binom{n-1}{k-1}}{\binom nk}=fk/n.
$$

After multiplication by the general convolution weight $K\sqrt n\,w_k$, the total is $Kf\sum_kkw_k/\sqrt n=o(1)$.


Set $Q=S_M/(n+1)$ and $v=\mathbf1_N$. Then

$$
\begin{aligned}
\det\left(I_N+\frac2n(I_N+A_M)\right)
&=(1+1/n)^N\det(I_N+Q)
\left[1+\frac1{n+1}v^{\mathsf T}(I_N+Q)^{-1}v\right].
\end{aligned}
$$

Using $(I+Q)^{-1}=(I-Q)(I-Q^2)^{-1}$ and the vanishing of a skew-symmetric quadratic form,

$$
v^{\mathsf T}(I+Q)^{-1}v=v^{\mathsf T}(I+Q^{\mathsf T}Q)^{-1}v\le\|v\|_2^2=N.
$$

Also, $(1+1/n)^N\le e^{N/n}\le e$, and

$$
\det(I+S_M/(n+1))=\prod_j\left(1+\frac{\lambda_j^2}{(n+1)^2}\right)
\le\prod_j\left(1+\frac{\lambda_j^2}{N^2}\right).
$$

The three factors are at most $e$, $\det(I+S_M/N)$, and $2$, respectively. Multiplication by the permanent factor $e^{-1}/2$ leaves $\rho_N(S_M)$. The constants in the exceptional-set estimate satisfy

$$
\frac{10}{3}\frac14\frac{21}{20}=\frac78=\frac{175}{200},\qquad
\frac1{25}+\frac1{25}=\frac{16}{200},\qquad
\frac{175+16}{200}=\frac{191}{200}.
$$


Suppose that, after deleting the exceptional vertices and a short set, the distance of every exceptional vertex's core-neighbor proportion from $[0,1/20]\cup[19/20,1]$ is at most $\epsilon_n$, where $\epsilon_n=O((f+k_n)/n)$. On $q\in[0,1]$, the derivative of $q(1-q)$ has absolute value at most one. Thus

$$
q_x(1-q_x)\le\frac{19}{400}+\epsilon_n.
$$

Using the same nonnegative weight deviation $\beta_n=O(\sqrt{\log n/n})$,

$$
\begin{aligned}
u_xv_x
&=4(q_x+\beta_n)(1-q_x+\beta_n)\\
&=4q_x(1-q_x)+4\beta_n+4\beta_n^2\\
&\le\frac{19}{100}+4\epsilon_n+4\beta_n+4\beta_n^2=:c_n.
\end{aligned}
$$

Moreover, $u_x,v_x\le2+2\beta_n=:L_n$. Since $\epsilon_n,\beta_n\to0$, choose a uniform threshold such that

$$
4\epsilon_n+4\beta_n+4\beta_n^2<\frac6{100},\qquad c_n<\frac14.
$$

Each term in the additional exponent above also tends to zero:

$$
\frac{f^2}{N}=O((\log n)^2/n)\to0,
\quad
\frac{2L_n^2f^2}{c_n^2N}=O((\log n)^2/n)\to0.
$$

For $\tau\le A\log n,t\le B\log n$, the error terms in Lemma 4.4 are bounded respectively by constant multiples of

$$
\frac{\log n+(\log n)^2}{n},\quad
\frac{(\log n)^{3/2}}{\sqrt n},\quad
\sqrt{\frac{\log n}{n}},\quad
\frac{\log n+1}{n},\quad
\frac{(\log n)^{3/2}}{\sqrt n},\quad
\frac{(\log n)^2}{n}.
$$

The constants are independent of the tournament and deletion sets, so the resulting $o(1)$ error is uniform.

### 7.4 The score penalty in the remaining class

**Proposition 7.3 (Uniform score-sensitive bound).** Fix $K_0>0$. There are constants $K,N$ depending only on $K_0$ such that, for $n\ge N$, every tournament with $a=S\mathbf1/(n-1)$, $\|a\|_\infty\le0.9$, and $\tau=\sum_i a_i^2\le K_0\log n$ satisfies

$$
\frac{H(T)}{\mu_n}\le\rho_n(S)\exp\left(-\frac\tau2+\frac K n\right)+B_n,
$$

where $B_n\ge0$ is the graph-independent tail from Lemma 5.1a and $B_n=o(n^{-1})$.

**Proof.**

The remaining tournaments satisfy

$$
\max_i|a_i|\le0.9,\qquad
a=s/(n-1),\qquad \tau=\sum_i a_i^2\le K\log n.
$$

For the fixed $K_0$ in the statement, all subsequent constants may depend on $K_0$. The paired product satisfies

$$
\Gamma=\prod_i(1-a_i^2)\le e^{-\tau}.
$$

Apply Lemma 4.4 to the whole tournament. The score product is common to every short term. Retaining it outside the sum absorbs errors that, individually, may exceed $1/n$.

For a principal deleted set of size $k\le k_n$, denoted by $U$, Lemma 4.4 gives

$$
\operatorname{per}A[U^c]\le
e^{-1}D_n(S)\Gamma
\left(\prod_{i\in U}g_i\right)
\frac{(n-k)!}{2^{n-k}}\exp(R_\tau+R_{\tau,k}),
$$

$$
g_i=(1-a_i^2)^{-1}\le G:=100/19,
$$

$$
R_\tau\le K[\mathcal M_\tau+\sqrt{\tau/n}+1/n],\qquad
R_{\tau,k}\le K[k\sqrt{\tau/n}+(k+k^2)/n].
$$

When accumulating errors, we must retain the common factor $\Gamma$. Define the nonnegative coefficients

$$
c_k=(2/n)^k\sum_{|U|=k}\det(I+A[U])\prod_{i\in U}g_i.
$$

They satisfy $c_0=1$ and $c_k\le G^kw_k$. Restoring the falling factorial produces

$$
\log\frac{n^k}{(n)_k}=O(k^2/n),\qquad k\le k_n.
$$

Set $\delta_n=\sqrt{\tau/n}+1/n$ and $r_k=R_{\tau,k}+\log(n^k/(n)_k)$. Taking a nonnegative error bound, uniformly for $\tau\le K_0\log n$ we have $0\le r_k\le K\delta_n(k+k^2)$ and $\max_{k\le k_n}r_k=o(1)$. Therefore

$$
\sum_{k\le k_n}c_ke^{r_k}
\le\sum_{k=0}^{n}c_k+
K\delta_n\sum_{k\ge0}G^kw_k(k+k^2)
\le\left(\sum_{k=0}^{n}c_k\right)e^{K\delta_n}.
$$

The last step uses $\sum_kc_k\ge1$ and convergence of the corresponding fixed moments. The normalized short path sum is consequently at most

$$
\frac{e^{-1}D_n(S)\Gamma}{2}
e^{R_\tau+K\delta_n}
\det\left(I+\frac2n\operatorname{diag}(g)(I+A)\right).
$$

Summing the error against the finite moments of $G^kw_k$ preserves the stated rate without a logarithmic loss.

We now remove the weights while preserving the score penalty. Set $W=I+(2/n)(I+A)$ and $\Delta=(2/n)\operatorname{diag}(g-1)(I+A)$. The symmetric part of $W$ is at least $I$, so $\|W^{-1}\|_{\rm op}\le1$. Each row of $I+A$ has Euclidean norm at most $\sqrt n$, and $\sum_i(g_i-1)\le K\tau$. Decomposing $\Delta$ as a sum of rank-one row matrices therefore controls its trace norm, the sum of its singular values. Using $\|uv^{\mathsf T}\|_*=\|u\|_2\|v\|_2$, we obtain

$$
\|\Delta\|_*\le K\tau/\sqrt n.
$$

The determinant inequality $|\det(I+E)|\le\exp(\|E\|_*)$ gives

$$
\det(W+\Delta)\le\det(W)e^{K\tau/\sqrt n}.
$$

Both determinants are positive: the symmetric part of $W$ is positive definite, and the weighted determinant has a principal-minor expansion with positive coefficients. The unweighted rank-one bound of Section 7.3, with $N=n$, is $\det(W)\le2e\det(I+S/n)$.

Combining the factors above and adding only the long-deletion tail at the end yields the uniform score-sensitive upper bound

<a id="eq-score-penalty"></a>

$$
\frac{H(T)}{\mu_n}\le
\rho_n(S)\exp\left\{-\tau+
K\left[\frac{1+\tau+\tau^2}{n}
+\frac{\tau^{3/2}+\tau}{\sqrt n}+\sqrt{\tau/n}\right]\right\}
+B_n.
\tag{7.2}
$$

For $\tau\le K_0\log n$ and sufficiently large order, the polynomial error terms other than the constant $1/n$ consume at most $\tau/4$ in total. Young's inequality controls the remaining square-root term:

$$
K\sqrt{\tau/n}\le\tau/4+K^2/n.
$$

The total exponent in [equation (7.2)](#eq-score-penalty) is therefore at most $-\tau/2+K/n$. Applying Proposition 6.6 gives

$$
H(T)/\mu_n\le r_ne^{K/n}+B_n=L+O(1/n).
$$

This proves Proposition 7.3 and the sharp bound in the remaining class. $\square$


### 7.5 Completion of the upper bound

The three classes cover all tournaments. High-variance tournaments have normalized path count $o(1/n)$; low-variance tournaments containing exceptional vertices have count strictly below one; and every remaining tournament satisfies the bound $L+O(1/n)$ just proved. Hence

$$
{P(n)\le\bigl(L+O(1/n)\bigr)\mu_n.}
$$

The threshold in each case is independent of the particular tournament. Taking a common threshold proves the upper bound in Proposition 7.1.

## 8. The small-score formula and the lower bound


**Theorem 8.1 (Small-score path approximation).**

There is an absolute constant $C$ with the following property. For every nonnegative function satisfying $d(n)/\sqrt n\to0$, denoted by $d=d(n)$, there is a threshold $n_0(d)$ such that every tournament of order $n\ge n_0(d)$ with $\|S\mathbf1\|_\infty\le d(n)$ satisfies

$$
\left|\frac{H(T)}{\mu_n}-\rho_n(S)\right|\le C\frac{(d(n)+1)^2}{n}.
$$


### 8.1 Proof of the small-score approximation

**Proof.**

Write $d=d(n)$. Apply Lemma 4.5 to every principal deleted set $|U|=k\le k_n$. Since $d+k_n+1=o(\sqrt n)$, it applies uniformly over all these subsets. After restoring the falling factorial $(n)_k$, the positive path convolution gives

$$
\frac{H(T)}{\mu_n}
=\frac{e^{-1}D_n(S)}2
\sum_{k\le k_n}\left(\frac2n\right)^k
\sum_{|U|=k}\det(I+A[U])
+O\left(\frac{(d+1)^2}{n}\right).
$$

This error rate has no extra logarithmic factor, because the error is at most a fixed constant times

$$
\frac1n\sum_{k\ge0}w_k(d+k+1)^2
=O\left(\frac{(d+1)^2}{n}\right).
$$

Restoring the falling factorial contributes $O(n^{-1}\sum k^2w_k)$, and Section 5.1 bounds the terms with large deleted sets by $o(n^{-1})$. Extending the short generating sum above to all $k$ costs $n^{-2+o(1)}$, because its coefficients are bounded by $w_k$. Thus

$$
\frac{H(T)}{\mu_n}
=\frac{e^{-1}D_n(S)}2
\det\left(I+\frac2n(I+A)\right)
+O\left(\frac{(d+1)^2}{n}\right).
$$

Set $u=\mathbf1/\sqrt n$ and $Q=S/(n+1)$. The rank-one determinant lemma gives

$$
\det\left(I+\frac2n(I+A)\right)
=(1+1/n)^n\det(I+Q)
\left(1+\frac n{n+1}u^{\mathsf T}(I+Q)^{-1}u\right).
$$

Skew-symmetry gives

$$
u^{\mathsf T}(I+Q)^{-1}u=u^{\mathsf T}(I-Q^2)^{-1}u,
$$

The absolute difference of this quantity from one is at most

$$
\|Qu\|_2^2\le\frac{d^2}{(n+1)^2}.
$$

Also, $(1+1/n)^n=e(1+O(n^{-1}))$. Replacing $S/(n+1)$ by $S/n$ incurs a logarithmic determinant error $O(n^{-1})$, by the bounded sum of the squared normalized frequencies. Consequently,

$$
\det\left(I+\frac2n(I+A)\right)
=2e\det(I+S/n)\left(1+O(n^{-1}+d^2/n^2)\right).
$$

Substitution proves the theorem. All estimates use the same absolute constant; only the threshold beyond which the small-score condition holds depends on $d$.


For every $k$, using $d+k+1\le(d+1)(k+1)$ gives

$$
\frac1n\sum_kw_k(d+k+1)^2
\le\frac{(d+1)^2}{n}\sum_kw_k(k+1)^2.
$$

Thus using $k_n$ as a replacement for $k$ is unnecessary, and no $\log n$ loss occurs. For $Q^{\mathsf T}=-Q$,

$$
(I+Q)^{-1}=(I-Q)(I-Q^2)^{-1},\qquad
Q(I-Q^2)^{-1}\text{ is skew-symmetric},
$$

$$
\begin{aligned}
1-u^{\mathsf T}(I+Q)^{-1}u
&=u^{\mathsf T}[I-(I+Q^{\mathsf T}Q)^{-1}]u\\
&=(Qu)^{\mathsf T}(I+QQ^{\mathsf T})^{-1}(Qu)
\le\|Qu\|_2^2.
\end{aligned}
$$

Since $Qu=s/[(n+1)\sqrt n]$,

$$
\|Qu\|_2^2=\frac{\sum_i s_i^2}{n(n+1)^2}\le\frac{d^2}{(n+1)^2}.
$$

The determinant error from changing the normalization satisfies

$$
\begin{aligned}
0&\le\log\det(I+S/n)-\log\det(I+S/(n+1))\\
&=\sum_j\int_{\lambda_j^2/(n+1)^2}^{\lambda_j^2/n^2}\frac{du}{1+u}\\
&\le\sum_j\lambda_j^2\left(\frac1{n^2}-\frac1{(n+1)^2}\right)\\
&=\frac{n(n-1)}2\frac{2n+1}{n^2(n+1)^2}=O(n^{-1}).
\end{aligned}
$$

and

$$
0\le1-n\log(1+1/n)
=n\int_0^{1/n}\frac{u}{1+u}\,du\le\frac1{2n}.
$$

The difference between the rank-one factor and two is

$$
\left|1+\frac n{n+1}u^{\mathsf T}(I+Q)^{-1}u-2\right|
\le\frac1{n+1}+\frac{d^2}{(n+1)^2}.
$$

Multiplying in order and using $D_n(S)\det(I+S/n)<3$ gives the absolute error in Theorem 8.1. $\square$

### 8.2 Carousel tournaments


**Corollary 8.2 (Carousel lower bound).**

For the odd-order carousel tournaments and even-order one-vertex-deletion constructions defined below,

$$
H(\mathrm{Car}_n)/\mu_n=L+O(n^{-1}).
$$


**Proof.**

For odd $n$, take the residue classes modulo $n$ and define the carousel tournament $\mathrm{Car}_n$ as follows: for $1\le j\le(n-1)/2$, direct $i\to i+j$. It is regular, so $d=0$. For even $n$, let $\mathrm{Car}_n$ be obtained by deleting one vertex from $\mathrm{Car}_{n+1}$. Then $d=1$.

The sign matrix of an odd-order carousel is similar to $T_n^0$ by a signed permutation. Explicitly, use the diagonal signs $(-1)^i$, $0\le i<n$, to conjugate $T_n^0$, and reorder the indices as $0,2,\ldots,n-1,1,3,\ldots,n-2$. When two indices have the same parity, the switched edge follows increasing index order; when they have different parities, its direction is reversed. Reading indices in the stated cyclic order gives the carousel orientation. Restricting the inverse signed conjugation and reordering after a one-vertex deletion gives $T_n^0$ on the remaining ordered indices. Thus the same signed spectral calculation remains valid after any one vertex is deleted, and both parity cases satisfy

$$
\rho_n(S_{\mathrm{Car}_n})
=r_n:=\frac{(n+1)^n+(n-1)^n}{(n+i)^n+(n-i)^n}.
$$

Divide numerator and denominator by $n^n$. At each fixed $z=1,-1,i,-i$, use the Taylor expansion of $(1+z/n)^n$. This gives

$$
r_n=\frac{\cosh1}{\cos1}+O(n^{-1})=L+O(n^{-1}).
$$

Both parities therefore have $H(\mathrm{Car}_n)/\mu_n=L+O(n^{-1})$, and hence

$$
P(n)\ge(L-O(n^{-1}))\mu_n.
$$

The transition from signed similarity to the path count uses Theorem 8.1, with $d=0$ and $d=1$, respectively. Let the constants and thresholds for the lower and upper bounds be $K_l,N_l$ and $K_u,N_u$. Taking $K=\max(K_l,K_u)$ and $n_0=\max(N_l,N_u,2)$ completes Theorem 1.1.


Write $n=2m+1$, with original indices $i=0,\ldots,2m$. Let $D_{ii}=(-1)^i$. For $i<j$,

$$
(DT_n^0D)_{ij}=(-1)^{i+j}.
$$

Use the reordering $p_k=2k\pmod n$, represented in $0,\ldots,n-1$. It gives the sequence $0,2,\ldots,2m,1,3,\ldots,2m-1$. If $i,j$ have the same parity and their positive difference is $2h$, then

$$
2^{-1}(j-i)\pmod n=h\in\{1,\ldots,m\}.
$$

If their parities differ and $i<j$, write $j-i=2h+1$. Then

$$
2^{-1}(j-i)\pmod n=h+m+1\in\{m+1,\ldots,2m\}.
$$

In the new indices, edges with differences $1,\ldots,m$ point forward, and those with differences $m+1,\ldots,2m$ point backward, exactly as in the carousel tournament. A one-vertex deletion selects the corresponding principal submatrix. The restricted $D$ is still a diagonal sign matrix, and the transitive principal submatrix on the remaining ordered indices is still $T_n^0$. This identifies the spectrum of both parity constructions. Their path counts are then estimated separately by Theorem 8.1.

By $D_n(S)=\det(I+iS/n)^{-1}$ and the principal-minor polynomial,

$$
\begin{aligned}
\rho_n(S)&=\frac{\det(I+S/n)}{\det(I+iS/n)}\\
&=\frac{(1+1/n)^n+(1-1/n)^n}
{(1+i/n)^n+(1-i/n)^n}=r_n.
\end{aligned}
$$

For $z\in\{1,-1,i,-i\}$ and $n\ge2$, the power series for the principal logarithm on $|w|<1$ gives

$$
\begin{aligned}
n\log(1+z/n)&=z-\frac{z^2}{2n}+R_{n,z},\\
|R_{n,z}|&\le\sum_{h=3}^{\infty}\frac1{h n^{h-1}}
\le\frac1{3n^2(1-1/n)}\le\frac2{3n^2}.
\end{aligned}
$$

Exponentiating yields $(1+z/n)^n=e^z(1-z^2/(2n)+O(n^{-2}))$. Adding the terms in pairs gives

$$
\begin{aligned}
(1+1/n)^n+(1-1/n)^n&=2\cosh1\,[1-1/(2n)+O(n^{-2})],\\
(1+i/n)^n+(1-i/n)^n&=2\cos1\,[1+1/(2n)+O(n^{-2})].
\end{aligned}
$$

Because $\cos1>0$, the denominator is bounded below by a fixed positive constant for all sufficiently large $n$. Using

$$
\frac1{1+u}=1-u+\frac{u^2}{1+u},
$$

we obtain the more precise spectral ratio

$$
r_n=L[1-1/n+O(n^{-2})].
$$

The term $-L/n$ is the first correction to the spectral ratio. Identifying the corresponding coefficient for the path count requires an error smaller than the $O(n^{-1})$ estimate in Theorem 8.1. Finally,

$$
H(\mathrm{Car}_n)/\mu_n=r_n+O(n^{-1})=L+O(n^{-1}),
$$

there is therefore a fixed $K_l$ such that $P(n)\ge(L-K_l/n)\mu_n$. $\square$


### 8.3 Degree stability near the maximum

**Corollary 8.2a (Degree-variance stability).** There are absolute constants $C,N$ such that, for $n\ge N$ and $0\le\varepsilon\le(L-1)/2$, any tournament satisfying $H(T)/\mu_n\ge L-\varepsilon$ has

$$
\tau(T)\le C(\varepsilon+n^{-1}),\qquad
V_{\rm deg}(T)\le C(\varepsilon n^2+n).
$$

In particular, every tournament maximizing $H(T)$ has $V_{\rm deg}(T)=O(n)$.

**Proof.** The assumption gives $H(T)/\mu_n\ge(L+1)/2>1$. The first two classes of Section 7 are therefore excluded by a uniform threshold. Proposition 7.3 and Proposition 6.6 give

$$
L-\varepsilon-B_n\le(L+K_r/n)\exp(-\tau/2+K/n).
$$

For sufficiently large $n$, $B_n\le1/n$ and the left-hand side is bounded below by $(L+1)/4$. Taking logarithms and using $\log(1+x)\le x$ proves $\tau\le C(\varepsilon+1/n)$. Multiply by $(n-1)^2/4$ for the variance estimate. After enlarging the threshold so that $K_l/n\le(L-1)/2$, Corollary 8.2 permits $\varepsilon=K_l/n$ for an exact maximizer. $\square$

The conclusion controls mean square degree deviation and gives a maximum single-vertex deviation of order $\sqrt n$. Eventual regularity, carousel uniqueness, edit-distance stability, and the $o(\sqrt n)$ condition in Theorem 8.1 each require further arguments.

