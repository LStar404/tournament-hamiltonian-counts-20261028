# 竞赛图 Hamilton 路径的定量渐近与 Wormald 角 Hessian

刘星辰、叶祥宇

2026年11月7日

## 摘要

本文证明 $n$ 阶竞赛图中有向 Hamilton 路径的最大数目满足

$$
P(n)=\left(\frac{\cosh1}{\cos1}+O(n^{-1})\right)\frac{n!}{2^{n-1}}.
$$

证明以我们早期的常数因子计数框架为基础，将统一永久式估计、非主子阵局部对角缩放和保留度差惩罚的路径估计与 Fang–Huang 谱比较结合。Divoux–Wang 已确定圈与路径的尖锐首项常数。我们另从 Wormald 随机吹胀公式的原角函数独立推导完整 Hessian，证明其对每个正则基图正定，并明确说明与 Bhattacharjee 结果的重合。对每个固定奇数基阶数，本文证明圆环基图最终唯一最大化两个吹胀模型的路径与圈期望，并证明正则内部块常数严格单调。

## 1. 引言

竞赛图是完全图的一个定向。记 $H(T)$ 为竞赛图 $T$ 中有向 Hamilton 路径的数目，$C(T)$ 为有向 Hamilton 圈的数目。路径按顶点顺序计数，圈则不区分循环起点。令

$$
P(n)=\max_{|V(T)|=n}H(T),\qquad
\mu_n=\frac{n!}{2^{n-1}},\qquad
\nu_n=\frac{(n-1)!}{2^n}.
$$

Szele [10] 用期望的线性性给出了这个问题的第一个下界。在均匀随机竞赛图中，一个给定的顶点排列以概率 $2^{-(n-1)}$ 形成有向路径，故路径数的期望为 $\mu_n$，从而 $P(n)\ge\mu_n$。对 $n\ge3$，同样的计算给出圈数期望 $\nu_n$。Szele 还证明了上界 $P(n)=O(n!2^{-3n/4})$，并猜想 $(P(n)/n!)^{1/n}$ 趋于 $1/2$。因此，最初的问题是确定路径数的指数增长率。

Alon [2] 通过永久式解决了这一问题。邻接矩阵 $A$ 的永久式等于覆盖全部顶点的互不相交有向圈族的数目，因而是 Hamilton 圈数的上界。将 Brégman 不等式用于 $\operatorname{per}A$，再利用出度之和为 $\binom n2$，可以证明所得上界在出度尽可能均匀时最大。由圈数上界加上一个新顶点的构造，Alon 得到 $P(n)=O(n^{3/2}\mu_n)$。Friedgut–Kahn [7] 以熵方法细化了这一类计数，将圈数上界改进为 $O(n^\alpha\nu_n)$，其中 $\alpha\approx1.249$；相应的路径上界具有同样的多项式因子。这些结果确定了指数增长率，但上、下界之间仍相差一个随 $n$ 增长的多项式。

提高下界则需要改变边的随机定向方式。Adler、Alon 和 Ross [9] 在完全图中选取近乎覆盖全部边的边不交三角形族，再将各三角形独立、均匀地定向为有向三圈。若一个顶点排列中有某个三角形连续出现，该排列形成有向路径的概率便比独立定向模型更大。对均匀随机的顶点排列，他们用 Brun 筛证明这类连续出现的次数趋于均值为一的 Poisson 分布，由此得到下界 $(e-o(1))\mu_n$；同一构造也改进了圈数下界。Wormald [6] 进一步考虑固定基图的随机吹胀：块间方向由基图决定，块内分别取均匀随机竞赛图或随机正则竞赛图。沿一个无穷阶数序列，圆环基图给出的圈数下界常数超过 $2.85588$，其数值计算又预示了约为 $2.855958$ 的极限常数。这些构造给出了下界；匹配的全局上界需要另一条论证。

Divoux–Wang [12] 确定了这个常数，证明全体竞赛图的最大圈数为 $(L+o(1))\nu_n$，最大路径数为 $(L+o(1))\mu_n$，其中 $L=\cosh1/\cos1$。他们仍从永久式出发，但保留了仅由度数给出的上界无法反映的矩阵信息。对于圈数至少达到随机期望的竞赛图，Brégman 不等式先限制其度差平方和；删去少量度差过大的顶点后，剩余邻接矩阵经标量归一化后接近双随机矩阵。为计入被删顶点，他们按 Hamilton 圈在这些顶点上形成的有向路段分类，将每类路段及其连接端点编码为核心上的加权矩阵。随后利用 Sinkhorn 缩放、McCullagh 型永久式近似以及 Liu 的行列式—永久式恒等式，将圈数归结为反对称矩阵的行列式比值。Fang–Huang [11] 的矩阵比较定理给出该比值的上界，圆环图及其偶阶删点图达到相同的渐近值。路径结论再由增添顶点的论证得到。

第一作者于 2026 年 10 月 8 日公开存档的路径计数稿 [14] 已证明 $(L-O(n^{-1}))\mu_n\le P(n)\le(C_*+O(n^{-1}))\mu_n$，并给出下文使用的主要分析框架。它消除了多项式间隙，但两侧首项常数仍满足 $L<C_*$。该稿包含正路径卷积、统一永久式估计、非主子阵缩放及异常顶点分析，早于 [12] 于 10 月 16 日提交 arXiv v1。本文将这一框架与 Fang–Huang [11] 的谱矩比较结合，得到尖锐的全局定量估计，细化 [12, 定理 1.4] 的首项渐近式；重点在于删点、缩放与求和后仍保留统一的 $O(n^{-1})$ 误差。本文没有证明这一误差阶不可改进。

**定理 1.1。** 存在绝对常数 $K',n_1$，使所有整数 $n\ge n_1$ 满足

$$
(L-K'/n)\mu_n\le P(n)\le(L+K'/n)\mu_n.
$$

奇阶圆环图 $\mathrm{Car}_n$ 的顶点集为 $\mathbb Z/n\mathbb Z$，其中 $i\to j$ 当且仅当 $j-i$ 的模 $n$ 代表元属于 $\{1,\ldots,(n-1)/2\}$。定理的下界由奇阶圆环图，以及从 $\mathrm{Car}_{n+1}$ 删除一个顶点所得的偶阶图达到，误差为 $O(\mu_n/n)$。

![圆环图 $\mathrm{Car}_7$ 及删除顶点 $0$ 后的偶阶图。左图每个顶点的出度均为 $3$；右图各顶点的出度为 $2$ 或 $3$。两图均画出全部边。](figures/carousel_deletion.png){width=94%}


本文的另一部分研究 Wormald 的随机吹胀模型。固定奇数 $d\ge3$ 及一个 $d$ 阶基图 $T^*$，将每个顶点替换为 $m$ 个顶点，块间所有边的方向由 $T^*$ 决定。若各内部块独立取均匀随机竞赛图，记所得模型为 $\mathcal T(T^*,m)$；若各块独立取均匀随机正则竞赛图，记为 $\mathcal R(T^*,m)$，此时要求 $m$ 为奇数。总阶数为 $N=dm$。以下圈数和路径数分别以 $\nu_N$ 和 $\mu_N$ 归一化。

![有向三圈的吹胀示例。每个内部块在图中均选为有向三圈，块间粗箭头表示相应方向的全部 $9$ 条边。在随机模型中，内部块按规定的分布独立抽取。](figures/triangle_blowup.png){width=78%}


Wormald [6] 的定理 4 以角 Hessian 的行列式非零为条件，给出正则基图的期望渐近式。他对若干小阶基图作了计算，并猜想这一条件总成立。我们证明该矩阵正定，并对每个正则基图求出其行列式。

**定理 1.2。** 设 $T^*$ 为正则竞赛图，$A$ 为其邻接矩阵。令 $S=A-A^T$、$C=S/d$ 及 $E=(e_1-e_d,\ldots,e_{d-1}-e_d)$。Wormald 角函数在原点的 Hessian $\mathbf H$ 为正定矩阵，且

$$
\mathbf H=E^T(I+C^2)(I-C^2)^{-1}E,\qquad
\mathcal H=d\,\frac{\det(I+C^2)}{\det(I-C^2)}>0,
$$
$$
\sqrt{d/\mathcal H}=\rho_d(S)
:=\frac{\det(I+S/d)}{\det(I+iS/d)}\in\mathbb Q_{>0}.
$$

这里 $\mathcal H=\det\mathbf H$，平方根取正值。角函数的定义见第 9 节。结合 Wormald [6] 的定理 1、4、5，固定 $d$ 后，模型 $\mathcal T(T^*,m)$ 的归一化圈、路径期望均趋于 $\rho_d(S)$，模型 $\mathcal R(T^*,m)$ 的相应极限均为 $e^{1/d}\rho_d(S)$。

模型常数也可直接由 Divoux–Wang [12, 命题 5.1] 得出，无须经过 Hessian 计算；第 10.1 节另写出这一推导。其命题 7.1、引理 9.1 已给出谱比值上界和圆环取等。下面结合这些结论、Fang–Huang [11] 的等号条件，以及正则基图的零行和条件，确定取等基图；非正则情形则另作估计。

**推论 1.3。** 对每个固定奇数 $d\ge3$，存在 $M_d$，使所有 $m\ge M_d$ 时，$\mathrm{Car}_d$ 在同构意义下唯一最大化两个模型的 Hamilton 圈数和路径数期望。对于 $\mathcal R(T^*,m)$，只考虑奇数 $m$。

下式中的 $r_d$ 是 Divoux–Wang [12, 第 7 节及引理 9.1] 已给出的二项式闭式，正则块因子 $e^{1/d}$ 来自 Wormald [6, 定理 1]。由 Fang–Huang [11, 引理 4.2] 所列显式频率，还可推出如下单调性。

**推论 1.4。** 置

$$
r_d=\frac{(1+1/d)^d+(1-1/d)^d}{(1+i/d)^d+(1-i/d)^d},
\qquad \mathfrak r_d=e^{1/d}r_d.
$$

沿奇数 $d\ge3$，$\mathfrak r_d$ 严格递增并趋于 $L$。

定理 1.2 直接证明 Wormald [6] 关于原 Hessian 的猜想 6。推论 1.3 结合已有计数与谱比较，补入等号分析及非正则基图估计。猜想 2 的极限存在性由 [12] 的闭式及 Wormald 的 $e^{1/d}$ 因子即得，推论 1.4 则补充严格单调性。第 10 节保留直至 $d^{-5}$ 项、余项为 $O(d^{-6})$ 的展开，作为该闭式的进一步计算。

Bhattacharjee [13, 定理 1.1、1.3，命题 3.1，引理 3.2 及推论 3.3] 也处理 Wormald 的猜想 2 和 6。原角 Hessian、正定性、行列式／有理平方公式和圆环极限由我们的 Wormald 项目 [15] 与其工作独立得到。本文保留直接推导，并明确记录重合。10 月 8 日路径存档 [14] 属于本文的另一条主线，不用于确定 Hessian 的日期。Bhattacharjee 于 10 月 14 日公开发布的版本 [16] 已有完整 Hessian；[15] 所引本方固定稿件提交日期为 10 月 19 日。Git 提交时间与公开发行时间含义不同，这些记录不支持本方 Hessian 更早的主张。

各项内容的定位和依赖如下。

| 内容 | 范围与已有工作的关系 |
|---|---|
| 常数因子路径框架 | 独立存档于 [14]；当时上界常数为 $C_*>L$。 |
| 尖锐全局路径估计 | 计数误差控制与 [11] 结合，给出最终统一 $O(n^{-1})$ 误差；尖锐首项渐近见 [12]。 |
| 有符号永久式估计 | 保留 [14] 的独立证明；图论计数应用使用其非负特例。 |
| 原角 Hessian 与圆环极限 | 与 [13,16] 重合的独立推导；早期路径档案不支持该部分的先后主张。 |
| 固定基图期望极值 | 谱等号分析、非正则基衰减及有限图类比较给出最终唯一性。 |
| 正则块常数单调性 | 已知圆环谱的严格单调性推论。 |

推论 1.3 先固定基阶数 $d$。此时基图只有有限多个同构类；正则非圆环基有严格极限间隙，非正则基的归一化期望趋于零。因此可对全部基图及四种期望取共同阈值。该结论比较期望，正则内部块模型仅允许奇数 $m$。

### 1.1 永久式估计与路径计数

McCullagh [5] 已在适度偏离条件下给出行列式近似及 $O(n^{-1})$ 相对误差。Divoux–Wang [12, 命题 3.1] 对非负双随机矩阵证明了对矩阵类一致的 $1+o(1)$ 版本；细化其系数估计及 Gamma 平均，也可在这一情形保留 $O(n^{-1})$。第 3 节采用固定元素界和算子范数界，给出后文所需的形式与详细证明。定理 1.1 的定量结论在于经过删点、缩放和求和后，最终路径数仍具有同阶误差。

证明从永久式的系数展开出发，对行指标和列指标的互异性分别作容斥。双中心化使含一度顶点的项消失；二度分量的总和由高斯配对计算，得到行列式主项。其余分量先收缩二度链，再按边数与顶点数之差估计。这样可以控制随矩阵阶数增长的一段系数。尾项另作估计：先用永久式极化化为半正定情形，再用 Han–Niles-Weed [3, 引理 4.3–4.4] 所用的复高斯矩与 AM–GM 估计控制其模，最后应用 Cauchy 系数估计。两部分合起来给出所需误差，不必将形式级数代入未经证明的收敛区域。

路径部分采用 Irving–Omar [1] 所讨论的行列式—永久式恒等式的竞赛图特例：

$$
H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}A[U^c].
$$

右端各项均非负，因而可以直接估计每个永久式，再对删集求和。大删集的总贡献由阶乘尾界控制；对其余删集，永久式估计还须经过对角缩放，才能用于原来的邻接矩阵。求和时保留删集大小的原权重，并利用其各阶固定矩可求和的性质；若一律用最大的删集大小代入，就会产生额外的对数因子。

少量度差很大的顶点使这一步较为复杂。我们按异常顶点集及其补集将矩阵分为四块，再按跨块匹配展开永久式。一个匹配在剩余部分占用的行、列可能具有不同的指标，因此只估计主子矩阵不够。第 4 节同时处理不同的行删集与列删集，并估计对角缩放因子和高斯行列式因子的变化。这与 Divoux–Wang 对圈在异常集内形成的有向路径段分类有所区别：这里的求和对象是永久式展开中的行列匹配。

为了得到对所有竞赛图成立的路径上界，只需考虑 $H(T)\ge\mu_n$ 的图。Brégman 不等式先限制出度的离差平方和；该量过大时可直接给出充分小的上界。若仍有异常顶点，则利用上述跨块展开估计。其余图的缩放计算中，度差产生一个负指数因子。中间某些误差为平方根量级，单独取绝对值会丢失所需精度；将它们与负指数合并估计，最终仍只损失 $O(n^{-1})$。此时主项为

$$
\rho_n(S)=\frac{\det(I+S/n)}{\det(I+iS/n)},\qquad S=A-A^T.
$$

和 [12] 一样，我们用 Fang–Huang [11] 的矩阵比较将其控制在传递竞赛图的相应比值以下。后者可显式计算，等于 $L+O(n^{-1})$。下界由小度差图的双侧路径估计得到：奇阶圆环图的度差为零，其偶阶删点图的度差绝对值为一。命题 6.6 给出全阶数谱比较，命题 7.3 集中陈述统一的度差惩罚；第 7、8 节直接完成定理 1.1，推论 8.2a 再给出近极值者的度数方差稳定性。

### 1.2 随机吹胀中的 Hessian 与等号条件

Wormald [6] 将 Hamilton 圈投影为基图上的闭游走；圈在每个内部块留下覆盖该块的有向路径森林。将闭游走与块内路径的计数写成生成函数后，期望问题化为多元有理函数的系数渐近。对正则基图，其公式中的常数取决于一个由隐式方程定义的角 Hessian，并以该 Hessian 的非退化性为条件。于是，计算这个矩阵既能去掉渐近公式中的条件，也能用来比较不同基图。

本文从原隐式方程求导，得到定理 1.2 的完整矩阵恒等式及正定性，从而直接验证 Wormald 渐近式所要求的非退化条件。恒等式 $\sqrt{d/\det\mathbf H}=\rho_d(S)$ 又把该 Hessian 与已有谱理论联系起来。模型极限 $\rho_d(S)$ 也可由 [12, 命题 5.1] 直接推出。本文先独立验证 Hessian 非退化，再应用 Wormald 的计数公式。

在正则基图中，我们沿用 [12] 的比较，并接入 Fang–Huang [11] 的等号分类。带符号相似再加零行和条件，即确定圆环基图。非正则基图另用 Brégman 不等式估计。固定阶数的基图只有有限多个同构类，严格的极限差因而给出推论 1.3。推论 1.4 采用显式谱的短证明；另保留高阶展开的计算。上述模型极限始终先固定基图阶数，再令块阶趋于无穷。

### 1.3 进一步问题与本文安排

各有限阶数的路径最大图和首个修正项的系数仍是开放问题。另一个问题是估计阈值 $M_d$ 随 $d$ 的增长。若令基图阶数与块阶数同时趋于无穷，还需要对基图阶数一致的误差估计。

第 2 节统一记号；第 3、4 节给出永久式和非主子阵缩放估计的精确条件与证明路线；第 5、6 节建立路径卷积和全阶数谱比较；第 7、8 节证明尖锐路径界及度差稳定性；第 9—11 节处理原角 Hessian 和固定基阶数的模型极值。详细证明伴随稿保留原有章节、公式编号，供核查长技术估计和辅助代数。主文在所引用估计的准确条件下展开计数与模型论证。

## 2. 预备知识与记号

### 2.1 随机基准与误差约定


记 $\mathfrak S_n$ 为 $[n]$ 的置换群。对 $\pi\in\mathfrak S_n$，以 $I_\pi$ 表示其相邻边全部顺向的示性函数。每个排列使用 $n-1$ 条互异的无向边，因而

$$
H(T)=\sum_{\pi\in\mathfrak S_n}I_\pi(T),\qquad
\mathbb E I_\pi=\prod_{j=1}^{n-1}\frac12=2^{-(n-1)},
$$

$$
\mathbb EH(T)=\sum_{\pi\in\mathfrak S_n}\mathbb EI_\pi
=n!2^{-(n-1)}=\mu_n.
$$

最大值至少等于平均值，所以 $P(n)\ge\mu_n$。以 $\mathcal T_n$ 表示顶点标号为 $[n]$ 的全部竞赛图，本文中“统一 $O(n^{-1})$”的含义是

$$
\exists K<\infty\ \exists n_0\ \forall n\ge n_0\ \forall T\in\mathcal T_n:
\quad |\mathrm{error}(n,T)|\le K/n.
$$

常数 $K,n_0$ 对竞赛图及删集一致；若另有预先固定的参数 $b,A_0,B_0$，则允许依赖这些参数。

### 2.2 符号矩阵与谱因子


**定义 2.1（符号矩阵与度差）。**

邻接矩阵 $A$ 的对角元为零，且 $A_{ij}=1$ 当且仅当 $i\to j$。定义

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1.
$$

其中 $I$ 为同阶单位矩阵，$J=\mathbf1\mathbf1^{\mathsf T}$，$\mathbf1$ 为全一列向量；写成 $I_p,J_p,\mathbf1_p$ 时下标表示维数 $p$。上标 $\mathsf T$ 表示转置。若 $d_i^+$ 为出度，则 $s_i=2d_i^+-(n-1)$ 且 $\sum_i s_i=0$。向量的二范数和最大范数分别为

$$
\|x\|_2=\left(\sum_i|x_i|^2\right)^{1/2},\quad
\|x\|_\infty=\max_i|x_i|.
$$

使用记号

$$
\mathcal E=\|s\|_2^2,\qquad d=\|s\|_\infty,\qquad
a=\frac{s}{n-1},\qquad \tau=\|a\|_2^2.
$$

标准化度差 $a$ 与 $\tau$ 在 $n\ge2$ 时定义。奇阶正则图指每个顶点的出度都为 $(n-1)/2$，等价于 $s=0$；偶阶平衡图指每个顶点的出度均为 $n/2$ 或 $n/2-1$，等价于 $s_i\in\{-1,1\}$。因此，$d$ 衡量最大的顶点不平衡程度，$\tau$ 则衡量归一化后的不平衡平方总量。


**定义 2.2（子矩阵与永久式）。**

对顶点集 $U$，$A[U]=A[U,U]$ 表示主子矩阵。对可能不同的行、列集 $R,C$，$A[R,C]$ 取这些行与列，并始终按原顶点标号递增排列。一般矩阵 $M[R,C]$ 采用相同约定。$U^c$ 表示相对于当前顶点全集的补集。空和为零、空积为一，空矩阵的行列式和永久式均为一。对 $m$ 阶方阵 $M$，永久式定义为

$$
\operatorname{per}M=\sum_{\pi\in\mathfrak S_m}\prod_{i=1}^m M_{i,\pi(i)}.
$$


**定义 2.3（频率与谱因子）。**

实矩阵 $M$ 的奇异值是 $M^{\mathsf T}M$ 的特征值的非负平方根。算子范数 $\|M\|_{\rm op}=\sup_{\|x\|_2=1}\|Mx\|_2$ 等于最大奇异值；Frobenius 范数 $\|M\|_F=(\sum_{i,j}|M_{ij}|^2)^{1/2}$ 的平方等于奇异值平方之和。对反对称矩阵 $S$，记其非零成对特征值为 $\pm i\lambda_j$（$i^2=-1$），其中 $\lambda_j>0$，必要时补零频率。每个 $\lambda_j$ 在奇异值中出现两次。定义

$$
x_j=\frac{\lambda_j^2}{n^2},\qquad
D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2},
$$

$$
\rho_n(S)=D_n(S)\det(I+S/n)=\prod_j\frac{1+x_j}{1-x_j}.
$$


反对称奇异值成对出现，且 $\|S\|_F^2=n(n-1)$，故

$$
\sum_jx_j=\frac{n-1}{2n},\qquad \|S/n\|_{\rm op}^2\le\frac{n-1}{2n}<\frac12.
$$

因此 $D_n$ 与 $\rho_n$ 都为正，且有绝对常数上界。特别地，

$$
D_n(S)=\det(I+iS/n)^{-1}.
$$


以下 $\log$ 均为自然对数。由 $-\log(1-x)=\int_0^x(1-u)^{-1}\,du\le2x$（$0\le x\le1/2$），得到

$$
0\le\log D_n(S)\le2\sum_jx_j<1,\qquad 1\le D_n(S)<e.
$$

同理由 $\log(1+x)\le x$ 得 $\log\rho_n(S)<3/2$。因此，乘以 $D_n(S)$ 或 $\rho_n(S)$ 不改变误差的阶。引理 6.1 将给出更精确的上界。

## 3. 永久式的一致渐近估计

计数论证需要一个在缩放及对数多个行、列独立删除下一致有效的永久式估计。以下保留定理的精确参数，完整系数证明移入**详细证明伴随稿材料 §§3.2–3.6**，沿用原编号。本节给出证明结构及闭合误差所需的估计。补充材料构成证明的完整组成部分。

McCullagh [5] 在中等偏差条件下得到行列式主项；这里保留的论证来自早期路径项目 [14]，允许有符号输入，而 §§4–8 只使用非负特例。Divoux–Wang [12] 的相关非负版本陈述 $o(1)$ 误差；得到 $O(n^{-1})$ 还须核对一致的系数与尾项估计，相关估计列于下文。

**定理 3.1（永久式的一致渐近估计）。**

 固定 $0\le C<\infty$ 和 $0\le q<1$。设 $n\ge1$，$E\in\mathbb R^{n\times n}$ 满足

$$
E\mathbf1=E^{\mathsf T}\mathbf1=0,\qquad
\max_{i,j}|E_{ij}|\le C,\qquad
\|E/n\|_{\mathrm{op}}\le q.
$$

 令 $B=E/n$。对所有满足上述条件的矩阵，一致地有

<a id="eq-uniform-permanent"></a>

$$
\frac{\operatorname{per}(J_n+E)}{n!}
=\det(I-BB^{\mathsf T})^{-1/2}+O_{C,q}(n^{-1}).
\tag{3.1}
$$

[式 (3.1)](#eq-uniform-permanent)也可写成行列式因子乘以相对误差 $1+O_{C,q}(n^{-1})$。下标 $C,q$ 表示误差常数和起始阶数可依赖这两个预先固定的参数，但须同时适用于所有满足条件的矩阵。

**证明（系数估计详见补充材料）。** 固定选取 $1<\sigma<R<1/q$（$q=0$ 时省略上限），置

$$
f(z)=\frac{\operatorname{per}(J_n+zE)}{n!},\qquad
G(z)=\det(I-z^2BB^{\mathsf T})^{-1/2},\qquad
\Gamma(r)=\exp\!\left(\frac{C^2r^2}{2(1-q^2r^2)}\right).
$$

由 $\|B\|_F^2\le C^2$，在固定圆盘内有 $|G(z)|\le\Gamma(|z|)$，且 $1\le G(1)\le\Gamma(1)$。平方根取在零点确定的分支，实区间上取正值。

分别对行、列指标作容斥，系数成为二部多重图之和。双中心化消去一度顶点；二度分量恰为高斯配对，总和为 $G$。对于其余分量，必须**先收缩二度链，再取绝对值**：交替乘积 $B,B^{\mathsf T}$ 才能保留谱隙。长度 $\ell\ge2$ 的链收缩至多为 $C^2q^{\ell-2}/n$。余下核心按超额（边数减顶点数）分类，每单位超额贡献一个 $n^{-1}$。标号补偿的精确恒等式及核心活动量界见补充材料 §§3.2–3.3；这一收缩次序保留算子范数控制。

取只依赖固定参数的 $\alpha>0$，令 $M=\lfloor\alpha n\rfloor$。补充材料 §3.4 证明有限系数窗口的总误差为 $K_1/n+K_2/n^2$，其中已经恢复因子 $n^k/(n)_k$。其偏差为 $k^2/n$ 量级，须在大于一的固定半径上对高斯系数求和吸收。永久式极化及半正定永久式估计给出 $\max_{|z|=R}|f(z)|\le\exp(\beta\sqrt n)$（允许固定乘法常数），其中 $\beta=RC/(1-Rq)$；Cauchy 估计于是控制次数大于 $M$ 的部分，详见补充材料 §3.5。合并得

$$
|f(1)-G(1)|\le\frac{K_1}{n}+\frac{K_2}{n^2}
+K_3e^{\beta\sqrt n-\alpha n\log R}
+K_4e^{-\alpha n\log\sigma}.
$$

全部常数及起始阶数只依赖预先固定的 $C,q$ 和据此选取的半径。两项指数余量均为 $o(n^{-1})$；有限多个小阶数可用 $|f(1)|\le(1+C)^n$、$G(1)\le\Gamma(1)$ 统一覆盖。由 $G(1)\ge1$，绝对误差又给出相对误差。$\square$

补充材料另保留任意大阶数、固定参数的有符号例子，以及从 [12] 的非负证明提取定量误差所需的两个估计；图论应用使用已陈述的非负特例。

## 4. 缩放与非主子阵

记 $a=S\mathbf1/(n-1)$、$\tau=\sum a_i^2$、$P_p=J_p/p$、$\Pi_p=I_p-P_p$。对 $p$ 阶矩阵 $X$，置 $\mathfrak m(X)=\sum X_{ij}$ 和 $g(X)=(X\mathbf1-\mathbf1,X^{\mathsf T}\mathbf1-\mathbf1)$。归一化矩阵 $C=2A/(n-1)$ 的行、列边际分别为 $\mathbf1+a$、$\mathbf1-a$。以下三个估计依次控制平衡缩放、对数代价及高斯因子，其参数依赖保证引理 4.4–4.5 的一致性。

### 4.1 缩放与高斯因子

**引理 4.1（局部缩放）。**

 设 $p\ge1$，$X$ 为总质量等于 $p$ 的实 $p\times p$ 矩阵。记

$$
\alpha=X\mathbf 1_p-\mathbf 1_p,\qquad \beta=X^{\mathsf T}\mathbf 1_p-\mathbf 1_p,\qquad \varepsilon=\max(\|\alpha\|_\infty,\|\beta\|_\infty).
$$

假设 $|X_{ij}|\le C/p$，每行和每列的绝对值之和至多为 $2$，并且

$$
X_0=X-\frac{\alpha\mathbf 1_p^{\mathsf T}+\mathbf 1_p\beta^{\mathsf T}}p,\qquad E=X_0-P_p
$$

满足 $|E_{ij}|\le C_0/p$ 和 $\|E\|_{\rm op}\le q<1$，其中 $C,C_0\ge0$、$0\le q<1$ 为固定参数。定义

$$
L_0=\frac32+C_0+\frac{C_0^2}{1-q},
$$

$$
\varepsilon_0=\min\left\{\frac1{256L_0^2},\frac{1-q}{2(32L_0+2)}\right\}.
$$

 若 $\varepsilon\le\varepsilon_0$，则存在满足 $\sum_i x_i=\sum_j y_j$ 的有限实向量 $x,y$，使 $B=\operatorname{diag}(e^x)X\operatorname{diag}(e^y)$ 的每行和每列之和均为 $1$。此外，

$$
\|(x,y)\|_\infty\le4L_0\varepsilon,\qquad |B_{ij}|\le2C/p,\qquad \|B-P_p\|_{\rm op}\le(1+q)/2.
$$

若 $X$ 逐元素非负，则 $B$ 为双随机矩阵，且与 $X$ 具有相同的零支撑。

**引理 4.2（位移与容量）。**

在上述假设下，再设 $X\ge0$。以 $\theta_X=\sum_i x_i+\sum_j y_j$ 表示总缩放势。存在仅依赖固定稠密度与谱隙参数的常数，使

$$
\|(x,y)\|_2\le K\|(\alpha,\beta)\|_2,\qquad \|B-X\|_F\le\frac K{\sqrt p}\|(\alpha,\beta)\|_2,
$$

$$
0\le\theta_X\le K\|(\alpha,\beta)\|_2^2.
$$

**一般质量。** 对于总质量为任意正数的非负矩阵 $X$，假设 $\widetilde X=pX/\mathfrak m(X)$ 满足引理 4.1 的条件，再对 $\widetilde X$ 应用以上结论。若 $B$ 为其缩放，则有精确恒等式

$$
\theta_X=\theta_{\widetilde X}+p\log\frac p{\mathfrak m(X)},\qquad \operatorname{per}X=e^{-\theta_X}\operatorname{per}B.
$$

特别地，若 $\kappa=\mathfrak m(X)-p$，则 $\operatorname{per}X\le e^\kappa\operatorname{per}B$。当质量不等于 $p$ 时，$\theta_X$ 本身不必非负。

**证明机制。** 固定规范 $\sum x_i=\sum y_j$。参考矩阵 $\mathsf H_0$ 的对角块为 $I$，非对角块为 $X_0,X_0^{\mathsf T}$；实际线性化 $\mathsf H_X$ 的对角块为 $\operatorname{diag}(X\mathbf1),\operatorname{diag}(X^{\mathsf T}\mathbf1)$，非对角块为 $X,X^{\mathsf T}$。置 $u=(\mathbf1,-\mathbf1)$、$N=uu^{\mathsf T}/(2p)$ 以固定规范。在零和子空间上，$\mathsf H_0+N$ 的逆可由 $(I-EE^{\mathsf T})^{-1}$、$(I-E^{\mathsf T}E)^{-1}$ 表示；稠密条目界与算子谱隙使其诱导 $1$-范数与 $\infty$-范数均至多为 $L_0$。$\mathsf H_X-\mathsf H_0$ 的这两个范数均至多为 $3\varepsilon$，因此 Neumann 级数将 $\mathsf H_X+N$ 的逆控制在 $2L_0$ 以内。给定阈值随后使非线性映射在半径 $4L_0\varepsilon$ 的球上成为压缩映射，从而得到存在性、条目界和谱界。块逆公式及压缩估计详见详细证明伴随稿材料 §4.1。

对于非负 $X$，考虑凸势函数

$$
\Phi_X(x,y)=\sum_{ij}X_{ij}e^{x_i+y_j}-\sum x_i-\sum y_j.
$$

从零点到平衡点的线段上，Hessian 在规范子空间上的下界为只依赖固定参数的正常数。积分得到二范数界，再用条目界得到 Frobenius 位移。比较零点及极小点的势函数值，得 $0\le\theta_X\le K\|g(X)\|_2^2$。标量归一化给出一般质量恒等式及 $-\theta_X\le\kappa$。因此，代价的非负性用于总质量恰为 $p$ 的情形，一般质量情形使用单侧界 $-\theta_X\le\kappa$。

当 $\|Z\|_{\rm op}<1$ 时，定义 $\mathcal G(Z)=\det(I-Z^{\mathsf T}Z)^{-1/2}$；添零行列或改用 $ZZ^{\mathsf T}$ 均保持其值。

**引理 4.3（Gram 删除与稳定性）。**

设 $\|Z\|_{\rm op}\le q_*<1$。删除行集 $I$ 和列集 $J$，剩余集合为 $R,T$，则

$$
0\le\log\mathcal G(Z)-\log\mathcal G(Z[R,T])\le\frac{\sum_{i\in I}\|Z_{i,\cdot}\|_2^2+\sum_{j\in J}\|Z_{\cdot,j}\|_2^2}{2(1-q_*^2)}.
$$

**双侧中心化。** 对阶数为 $m\ge1$ 且满足 $\|W\|_{\rm op}\le q_*$ 的方形余矩阵 $W$，置 $u=\mathbf 1_m/\sqrt m$，则

$$
0\le\log\mathcal G(W)-\log\mathcal G(\Pi_mW\Pi_m)\le\frac{\|W^{\mathsf T}u\|_2^2+\|Wu\|_2^2}{2(1-q_*^2)}.
$$

**稳定性。** 对于维数相同、算子范数均至多为 $q_*$ 的两个实矩阵，另有

$$
|\log\mathcal G(U)-\log\mathcal G(V)|\le\frac{\|U\|_F+\|V\|_F}{2(1-q_*^2)}\|U-V\|_F.
$$

**证明。** 沿删除行产生的半正定 Gram 损失积分 $-\tfrac12\log\det(I-H)$ 的导数，其迹等于被删行范数平方和。换到另一侧 Gram 矩阵处理列删除，对常数方向投影同样处理。稳定性由 Gram 线段上的积分及 $\|U^{\mathsf T}U-V^{\mathsf T}V\|_*\le(\|U\|_F+\|V\|_F)\|U-V\|_F$ 得到。$\square$

### 4.2 一致删除估计

**引理 4.4（非主永久式界）。**

 固定 $0\le b<1$ 及正常数 $A_0,B_0$。对 $N\ge2$ 阶竞赛图核心，置 $a=S\mathbf1/(N-1)$，$\tau=\sum_i a_i^2$。令 $I,J\subseteq[N]$ 分别为行、列删集；此处 $I,J$ 为集合，和单位矩阵、全一矩阵的记号由下文的集合运算区分。假设

$$
\max_i|a_i|\le b,\qquad
\tau\le A_0\log N,\qquad
|I|=|J|=t\le B_0\log N.
$$

定义 $\ell_i=(1+a_i)^{-1}$、$r_i=(1-a_i)^{-1}$，以及

$$
\Gamma=\prod_i(1-a_i^2),\qquad
\mathcal M_\tau=\frac{\tau+\tau^2}{N}+\frac{\tau^{3/2}}{\sqrt N}.
$$

 令 $R=[N]\setminus I$、$T=[N]\setminus J$ 分别为保留行、列集；本式的 $T$ 是列指标集。则有

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

对所有充分大的 $N$，该估计对每个满足条件的竞赛图及每对 $I,J$ 同时成立。常数 $K$ 和起始阶数仅依赖 $b,A_0,B_0$。


**证明。** 取 $n=N$、$m=n-t$，先作配对度差校正及质量归一化：

$$
\begin{aligned}
C&=\frac{2A}{n-1}, & C'&=\operatorname{diag}(\ell)C\operatorname{diag}(r),\\
\nu&=\mathfrak m(C')-n, & \widehat C&=\frac{nC'}{n+\nu},\\
X&=\frac nm\widehat C[R,T], & \kappa&=\mathfrak m(X)-m.
\end{aligned}
$$

置 $v_i=a_i/(1-a_i^2)$、$w_i=a_i^2/(1-a_i^2)$、$V=\sum v_i$、$W=\sum w_i$。一阶质量变化抵消后的精确恒等式为

$$
\nu=\frac{W^2-V^2+W+2w^{\mathsf T}Sv}{n-1},\qquad |\nu|\le K\mathcal M_\tau.
$$

设 $e,f$ 为 $\widehat C$ 的边际误差。独立删除行、列集合后，有

<a id="eq-deletion-mass"></a>

$$
\kappa=\frac nm\left[-\sum_{i\in I}e_i-\sum_{j\in J}f_j
+\sum_{i\in I,j\in J}\widehat C_{ij}-\frac{t^2}{n}\right].\tag{4.1}
$$

归一化为 $\widetilde X=mX/(m+\kappa)$。详细证明伴随稿材料 §4.3 的预处理估计一致给出

$$
|\kappa|\le K(t\sqrt{\tau/n}+t^2/n),\quad
\|g(\widetilde X)\|_\infty\le K(\sqrt{\tau/n}+t/n),\quad
\|g(\widetilde X)\|_2\le K(\sqrt\tau+t/\sqrt n).
$$

$\widetilde X$ 的条目位于 $[0,K/m]$，其双中心化核的算子范数至多为 $1/\sqrt2+o(1)$。固定谱隙参数 $q=3/4$ 后，引理 4.1 在共同阈值以上适用。缩放 $B_X$ 的条目为 $O(1/m)$，中心化范数最终至多为 $4/5$。引理 4.2–4.3 及同一预处理给出

$$
-\theta_X\le\kappa,\qquad
\log\mathcal G(B_X-P_m)\le\log D_n(S)+K\bigl(\sqrt{\tau/n}+(t+1)/n\bigr).
$$

精确恢复恒等式为

<a id="eq-exact-restoration"></a>

$$
\operatorname{per}A[R,T]=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j
\left[\frac{m(n-1)(n+\nu)}{2n^2}\right]^m
 e^{-\theta_X}\operatorname{per}B_X.\tag{4.2}
$$

定理 3.1 给出 $\operatorname{per}B_X=(m!/m^m)\mathcal G(B_X-P_m)(1+O(m^{-1}))$。余下标量为 $(m!/2^m)(1-1/n)^m(1+\nu/n)^m$，相对 $e^{-1}m!/2^m$ 的对数偏差为 $O((t+1)/n+|\nu|)$。合并即得所列误差指数。全部谱隙、稠密度及阈值均由 $b,A_0,B_0$ 固定，保证陈述中的一致量词。$\square$

**引理 4.5（小度差永久式近似）。**

设 $d=\|S\mathbf 1_n\|_\infty=o(\sqrt n)$。固定 $0<B_0<\infty$，任删 $t\le B_0\log n$ 行与 $t$ 列，记 $m=n-t$。对这些选择一致地有

<a id="eq-small-score-permanent"></a>

$$
\operatorname{per}A[R,T]=e^{-1}D_n(S)\frac{m!}{2^m}\left[1+O_{B_0}\left(\frac{(d+t+1)^2}{n}\right)\right].
\tag{4.3}
$$

更具体地，固定 $B_0>0$ 后，存在常数 $C_{\mathrm{err}},\delta>0$ 和整数 $N_0\ge4$，使下述结论对所有 $n\ge N_0$ 一致成立。设 $S$ 为竞赛符号矩阵，$I,J\subseteq[n]$ 且 $|I|=|J|=t\le B_0\log n$；置 $d=\|S\mathbf1_n\|_\infty$、$\eta=(d+t+1)^2/n$。若 $\eta\le\delta$，则[式 (4.3)](#eq-small-score-permanent)的相对误差绝对值不超过 $C_{\mathrm{err}}\eta$。这里 $R=[n]\setminus I$、$T=[n]\setminus J$、$m=n-t$，两个删集可独立选取。在引理所述渐近范围内，$\eta\to0$。

**证明。** 直接取 $X=(n/m)C[R,T]$。式 (4.1) 及边际恒等式给出

$$
|\kappa|=O(t(d+t)/n),\quad
\|g(X)\|_\infty=O((d+t)/n),\quad
\|g(X)\|_2=O((d+t)/\sqrt n).
$$

将质量归一化为 $m$ 后，引理 4.1–4.2 给出 $|\theta_X|=O((d+t)^2/n)$，缩放位移为 $O((d+t)/n)$。为比较全阶高斯因子，置 $Y=(S-I)/(n-1)$，由反对称性得

$$
Y^{\mathsf T}Y=\frac{S^{\mathsf T}S+I}{(n-1)^2},\qquad
Y^{\mathsf T}Y-\frac{S^{\mathsf T}S}{n^2}\succeq0.
$$

由 $\operatorname{tr}(S^{\mathsf T}S)=n(n-1)$，上式半正定差的迹为 $O(n^{-1})$。在固定谱隙下，沿该 Gram 差积分对数行列式的导数，得到 $|\log\mathcal G(Y)-\log D_n(S)|=O(n^{-1})$。这里的 $O(n^{-1})$ 比较针对高斯因子的对数。再结合引理 4.3、删除、中心化及标量归一化，得到

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|=O(\eta).
$$

此时恢复恒等式为 $\operatorname{per}A[R,T]=[m(n-1)/(2n)]^m e^{-\theta_X}\operatorname{per}B_X$。代入定理 3.1 及 $(1-1/n)^m=e^{-1}\exp(O((t+1)/n))$，归一化比值写成 $e^u(1+v)$，其中 $|u|\le K\eta$、$|v|\le K/n\le K\eta$。固定充分小的 $\delta$，利用 $|e^u-1|\le e^{|u|}|u|$，便得所述有限且一致的相对误差界。$\square$

## 5. 路径卷积与行列式表示

### 5.1 正路径卷积


**引理 5.1（路径卷积）。**

对任意竞赛图，

<a id="eq-path-convolution"></a>

$$
H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}A[U^c].
\tag{5.1}
$$


**证明。**


邻接矩阵的永久式计算有向圈覆盖数。卷积[式 (5.1)](#eq-path-convolution)把互补顶点集上的圈覆盖数转换成路径数。它是 Irving 与 Omar 的 Proposition 2 [1] 在竞赛图上的特化，其中补邻接矩阵为 $\overline A=J-A=I+A^{\mathsf T}$，包含对角元。

也可用生成函数直接核对。令 $X=\operatorname{diag}(z_1,\ldots,z_n)$，即对角元依次为 $z_1,\ldots,z_n$、其余元素为零的对角矩阵；一般的 $\operatorname{diag}(v)$ 同样由向量 $v$ 的元素组成对角线。每次访问一个顶点即乘上对应变量，则全部游走的生成函数为

$$
1+\mathbf1^{\mathsf T}(I-XA)^{-1}X\mathbf1
=\frac{\det(I+X\overline A)}{\det(I-XA)}.
$$

等号来自秩一行列式引理。取 $z_1\cdots z_n$ 的系数，恰选出全部 Hamilton 路径。对分母，形式恒等式 $\det(I-XA)^{-1}=\exp(\sum_{r\ge1}\operatorname{tr}((XA)^r)/r)$ 表明，其无平方因子单项式（每个变量的指数均为零或一）的系数计算不交有向圈覆盖数，因而等于永久式。再结合分子的主子式展开，得到

$$
H(T)=\sum_U\det\overline A[U]\operatorname{per}A[U^c].
$$

代入 $\overline A[U]=I+A[U]^{\mathsf T}$ 即得结论。

以 $T[U]$ 表示由顶点集 $U$ 诱导的子竞赛图，令 $k=|U|$。矩阵 $I+A[U]$ 的对称部分为正定矩阵 $(I+J)/2$，故实特征值均为正，非实特征值共轭成对，从而行列式为正。各行平方范数为 $1+d_i^+(T[U])$，平均值为 $(k+1)/2$。由 Hadamard 不等式及算术—几何平均不等式得

$$
0<\det(I+A[U])\le h_k,\qquad h_k=\left(\frac{k+1}{2}\right)^{k/2}.
$$

以上证明也说明：迹级数中的 $1/r$ 消去有向圈的起点选择，指数展开中的 $1/h!$ 消去互不相交圈的排列；相交圈产生平方变量，不贡献无平方因子系数。$\square$

**引理 5.1a（固定矩与统一尾界）。** 约定 $h_0=1$，并令

$$
w_k=\frac{2^k h_k}{k!}.
$$

对任意固定 $c>0$ 和非负整数 $r$，

$$
\sum_{k\ge0}(k+1)^r c^k w_k<\infty.
$$

**证明。** Stirling 公式给出 $\log(c^kw_k)=-(k/2)\log k+O_c(k)$，其中下标 $c$ 表示隐含常数可依赖预先固定的 $c$。记 $\lceil x\rceil$ 为不小于 $x$ 的最小整数，对充分大 $n$ 取

$$
k_n=\left\lceil\frac{4\log n}{\log\log n}\right\rceil,
$$

又由连续项比 $c w_{k+1}/w_k=O_c(k^{-1/2})$，尾和由首项的固定倍数控制，故 $\sum_{k>k_n}c^kw_k=n^{-2+o(1)}$。

使用 [2, Lemma 2.1] 所述的 Brégman 界及 [2, Corollary 2.3] 的度数平衡化，再结合 Stirling 公式，给出统一常数 $C$，使任意 $m$ 阶竞赛图满足

$$
\operatorname{per}A_T\le C\sqrt{m+1}\,\frac{m!}{2^m}.
$$

增大 $C$ 后也覆盖 $m=0$。引理 7.2 将证明含方差修正因子的版本。于是路径卷积中 $|U|>k_n$ 的贡献除以 $\mu_n$ 后，至多为

$$
B_n:=\frac C2\sqrt{n+1}\sum_{k>k_n}w_k
=n^{-3/2+o(1)}=o(n^{-1}).
$$

常数 $C$ 绝对，故 $B_n$ 只依赖 $n$，该界对所有竞赛图一致。$\square$

称 $|U|\le k_n$ 的项为短项；路径卷积中的永久式只需在这些项上精确估计。


### 5.2 谱因子的出现

先设 $d=o(\sqrt n)$。由引理 4.5，对 $|U|=k\le k_n$ 有

$$
\operatorname{per}A[U^c]
=e^{-1}D_n(S)\frac{(n-k)!}{2^{n-k}}
\left(1+O\left(\frac{(d+k+1)^2}{n}\right)\right).
$$

对整数 $0\le k\le n$，下降阶乘定义为

$$
(n)_k=\prod_{h=0}^{k-1}(n-h),
$$

故 $(n)_0=1$，且此范围内 $(n)_k>0$。归一化满足 $((n-k)!/2^{n-k})/\mu_n=2^{k-1}/(n)_k$。因此，将主项代入引理 5.1，所得归一化总和为

$$
\frac{e^{-1}D_n(S)}2
\sum_{|U|\le k_n}\frac{2^{|U|}}{(n)_{|U|}}\det(I+A[U]),
$$

这里的相对误差对竞赛图和 $|U|\le k_n$ 一致。将短和中的 $(n)_k$ 换成 $n^k$，再补入尾项，得到下述主子式恒等式；相应误差将在第 8.1 节估计。

$$
\sum_U(2/n)^{|U|}\det(I+A[U])
=\det\left(I+\frac2n(I+A)\right).
$$

由 $2A=J-I+S$，秩一项 $J$ 渐近贡献因子二，标量项贡献 $e$。更确切地，小度差假设给出

$$
\det\left(I+\frac2n(I+A)\right)
=2e\det(I+S/n)\left(1+O(n^{-1}+d^2/n^2)\right).
$$

永久式估计中的 $e^{-1}$ 来自恢复 $(1-1/n)^{n-k}$，对应零对角线的影响；$1/2$ 则来自上述路径归一化。它们与生成行列式中的 $2e$ 抵消，留下 $D_n(S)\det(I+S/n)=\rho_n(S)$。两个行列式各有来源：前者近似圈覆盖数，后者对路径卷积的权重求和。定理 8.1 将完成误差求和，证明

$$
\frac{H(T)}{\mu_n}=\rho_n(S)+O((d+1)^2/n)
\qquad\text{当 }d=o(\sqrt n).
$$

为得到全体竞赛图的上界，第 7 节另行处理较大的出度离差平方和及极端度数，并在剩余图类中保留度差修正因子。下面的引理则对每个竞赛图控制同一个谱因子。

## 6. 谱因子的上界与等号

本节的谱比值上界由 Divoux–Wang [12, 命题 7.1] 根据 Fang–Huang [11] 的比较得到。行列式多项式及圆环切换亦见 [12, 第 7 节及引理 9.1]。下面保留详细推导，并追踪固定基图推论所需的等号条件。


### 6.1 谱半径与统一粗界

**引理 6.1（谱上限）。** 任意 $n$ 阶竞赛符号矩阵满足

$$
\|S\|_{\rm op}\le\cot\frac{\pi}{2n}<\frac{2n}{\pi},\qquad
\rho_n(S)\le\frac{3n-1}{n+1}<3.
$$

**证明。** $iS$ 为 Hermitian 矩阵。对任意复向量 $z$，同时对 $S,z$ 作带符号置换，使非零坐标相位落在 $[0,\pi)$ 且递增。于是 $c_{ij}=\operatorname{Im}(\overline z_i z_j)\ge0$（$i<j$）。若 $T_n^0$ 是上三角全一的传递符号矩阵，则

$$
z^*iSz=-2\sum_{i<j}S_{ij}c_{ij}\le2\sum_{i<j}c_{ij}=z^*(-iT_n^0)z.
$$

取 Rayleigh 商得 $\|S\|_{\rm op}\le\|T_n^0\|_{\rm op}$。相邻行的特征方程给出 $(\lambda-1)v_i=(\lambda+1)v_{i+1}$，几何比 $r=(\lambda-1)/(\lambda+1)$ 满足 $r^n=-1$。全部特征值因而为 $i\cot((2j-1)\pi/(2n))$，$1\le j\le n$，得到所述算子界；$n=1$ 直接验证。

令 $x_j=\lambda_j^2/n^2$，则 $\sum_jx_j=(n-1)/(2n)$。函数 $\phi(x)=\log((1+x)/(1-x))$ 满足 $\phi(0)=0$，且 $\phi'$ 在 $[0,1)$ 递增，故当 $a,b\ge0$、$a+b<1$ 时，$\phi(a)+\phi(b)\le\phi(a+b)$。迭代即得

$$
\log\rho_n(S)=\sum_j\phi(x_j)\le\phi\left(\frac{n-1}{2n}\right),
$$

取指数得到粗界。它不使用后面的 Fang–Huang 比较。

传递矩阵的同一特征值计算给出全部偶阶主子式为一、奇阶主子式为零（偶阶正频率按互补角配对，其乘积为一）。因此

$$
\det(I+zT_n^0)=\sum_{h=0}^{\lfloor n/2\rfloor}\binom n{2h}z^{2h}
=\frac{(1+z)^n+(1-z)^n}{2}.
$$

$\square$

**历史说明。** 早期路径稿以更弱的谱信息得到常数
$C_*=(3\pi^4+4\pi^2-32)/(\pi^4+4\pi^2-32)>L$。本稿的异常点排除只需上述 $\rho_n<3$；最终上界直接使用命题 6.6 的锐比较，不再以 $C_*$ 作为中间主定理。

### 6.2 乘积比较与等号条件

**定理 6.2 (Fang–Huang).**

我们使用 [Fang–Huang, Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3) 的以下形式。令比较矩阵 $K_d$ 为

$$
(K_d)_{ij}=\begin{cases}
1,&i+j\le d,\\
0,&i+j=d+1,\\
(-1)^{i+j-d-2},&i+j\ge d+2.
\end{cases}
$$

设 $p\ge1$，$x\in\mathbb R^d$，$S_1,\ldots,S_p$ 为 $d$ 阶竞赛符号矩阵。用 $x^*$ 表示将 $x$ 的坐标绝对值按降序排列所得的向量，则

$$
(S_1\cdots S_p x)^*\prec_w K_d^p x^*.
$$

右端是非负降序向量。弱主序$u\prec_w v$的含义是

$$
\sum_{i=1}^r u_i\le\sum_{i=1}^r v_i
\quad(1\le r\le d).
$$

此外，最外层比较取向量等号时，每个后缀乘积的比较也取向量等号。为将这一结论用于矩阵的 Frobenius 范数，我们先说明弱主序下的平方和比较及其取等条件。


**引理 6.3 (弱主序的截断和比较).**

记$(a-t)_+=\max(a-t,0)$。对于满足$u\prec_w v$的降序非负向量及$t\ge0$，

$$
\sum_{i=1}^d(u_i-t)_+
=\max_{0\le r\le d}\left(\sum_{i=1}^r u_i-rt\right)
\le\max_{0\le r\le d}\left(\sum_{i=1}^r v_i-rt\right)
=\sum_{i=1}^d(v_i-t)_+.
$$


**证明。**

取 $r=\#\{i:u_i>t\}$ 即得第一个等号：加入不大于 $t$ 的坐标或删去大于 $t$ 的坐标，均不能增大该和。又对 $a\ge0$，

$$
2\int_0^\infty(a-t)_+\,dt
=2\int_0^a(a-t)\,dt
=2[at-t^2/2]_0^a=a^2.
$$

逐坐标积分得到

$$
\|u\|_2^2
=2\int_0^\infty\sum_i(u_i-t)_+\,dt
\le2\int_0^\infty\sum_i(v_i-t)_+\,dt
=\|v\|_2^2.
$$

若平方和相等，函数 $g(t)=\sum_i(v_i-t)_+-\sum_i(u_i-t)_+$ 连续、非负且积分为零。若某处 $g(t_0)>0$，则在 $t_0$ 的一个正长度邻域内有 $g(t)>g(t_0)/2$，与积分为零矛盾。因此 $g\equiv0$。以下 $\#U$ 表示有限集 $U$ 的基数，$\mathbf1_{\mathcal E}$ 表示条件 $\mathcal E$ 的指示函数。比较两边的右导数可得

$$
\#\{i:u_i>t\}=\#\{i:v_i>t\}=:N(t).
$$

对第$j$个坐标，

$$
u_j=\int_0^\infty
\mathbf1_{\{\#\{i:u_i>t\}\ge j\}}\,dt
=\int_0^\infty\mathbf1_{\{N(t)\ge j\}}\,dt=v_j.
$$

因而平方和取等强制$u=v$。取$x=e_j$，由于$e_j^*=e_1$，得到

$$
\|S^pe_j\|_2^2\le\|K_d^pe_1\|_2^2.
$$

并且取等时$(S^pe_j)^*=K_d^pe_1$。


### 6.3 比较矩阵的矩

记$\operatorname{tr}M=\sum_jM_{jj}$。

令 $T_d$ 为传递竞赛图的符号矩阵，其上三角元为 $1$。令 $R_0$ 为反序置换矩阵，$D_0=\operatorname{diag}(1,-1,\ldots)$。由 $K_d$ 的定义，

$$
(D_0K_dR_0)_{ij}
=(-1)^{i-1}(K_d)_{i,d+1-j}
=\begin{cases}
(-1)^{i-1},&i<j,\\
0,&i=j,\\
(-1)^j,&i>j.
\end{cases}
$$

这里 $R_0e_j=e_{d+1-j}$，$(D_0)_{jj}=(-1)^{j-1}$。由于 $(K_d)_{ij}$ 只依赖于 $i+j$，有 $K_d^T=K_d$。

把奇指标升序、偶指标降序所得序列记为

$$
(\ell_1,\ldots,\ell_d)=(1,3,\ldots,d,d-1,d-3,\ldots,2),
\qquad \Lambda e_j=e_{\ell_j}.
$$

这些指标各出现一次，所以$\Lambda^T\Lambda=\Lambda\Lambda^T=I$，而$\ell_1=1$。

按这一顺序排列行、列。两个奇指标按升序排列，故相应上三角元为 $(-1)^{i-1}=1$；两个偶指标按降序排列，故相应上三角元为 $(-1)^j=1$。奇指标总在偶指标之前，此时无论原指标满足 $i<j$ 还是 $i>j$，相应元素分别为 $(-1)^{i-1}$ 或 $(-1)^j$，仍等于 $1$。因此

$$
T_d=\Lambda^TD_0K_dR_0\Lambda.
$$

置$U=D_0\Lambda$。由于$R_0R_0^T=I$、$\Lambda\Lambda^T=I$、$K_d^T=K_d$，矩阵乘积给

$$
\begin{aligned}
T_dT_d^T
&=\Lambda^TD_0K_dR_0\Lambda
\Lambda^TR_0^TK_dD_0\Lambda\\
&=\Lambda^TD_0K_d^2D_0\Lambda=U^TK_d^2U.
\end{aligned}
$$

第一项指标是1，故$Ue_1=e_1$。又$T_d^T=-T_d$，所以

$$
T_d^2=-U^TK_d^2U,\qquad
T_d^{2p}=(-1)^pU^TK_d^{2p}U
$$

（相乘时每两个邻接的$UU^T$都等于$I$）。于是

$$
(-1)^p(T_d^{2p})_{11}
=e_1^TK_d^{2p}e_1
=(K_d^pe_1)^T(K_d^pe_1)
=\|K_d^pe_1\|_2^2.
$$

详细证明稿附录 A.2 给出的带符号循环移位 $Z$ 满足 $Z^TT_dZ=T_d$，从而 $Z^TT_d^{2p}Z=T_d^{2p}$。比较对角元，当 $j<d$ 时有 $(T_d^{2p})_{j+1,j+1}=(T_d^{2p})_{jj}$；当 $j=d$ 时，绕回的两个负号抵消，得到 $(T_d^{2p})_{11}=(T_d^{2p})_{dd}$。于是所有对角元相同，且

$$
\begin{aligned}
\|T_d^p\|_F^2
&=\operatorname{tr}((T_d^p)^TT_d^p)
=(-1)^p\operatorname{tr}T_d^{2p}\\
&=d(-1)^p(T_d^{2p})_{11}
=d\|K_d^pe_1\|_2^2.
\end{aligned}
$$

现在对上一节的$d$个列不等式求和：

$$
\|S^p\|_F^2
=\sum_{j=1}^d\|S^pe_j\|_2^2
\le d\|K_d^pe_1\|_2^2
=\|T_d^p\|_F^2\qquad(p\ge1).
$$

特别地，该不等式对下一节所需的每个奇数 $p$ 都成立。

### 6.4 谱比值的极值

设 $S$ 为任意 $d$ 阶竞赛符号矩阵，其非零特征值为 $\pm i\lambda_j$，其中 $\lambda_j>0$，并令 $x_j=\lambda_j^2/d^2$。由 $2\sum_j\lambda_j^2=\|S\|_F^2=d(d-1)$，有 $x_j\le(d-1)/(2d)<1/2$。在反对称标准形中，零块对两个行列式均贡献 $1$，非零二维块分别贡献 $1+x_j$ 和 $1-x_j$。因此

$$
\det(I+S/d)=\prod_j(1+x_j),\qquad
\det(I+iS/d)=\prod_j(1-x_j)>0.
$$

在$0\le x<1$上，将几何级数积分，

$$
\begin{aligned}
\log\frac{1+x}{1-x}
&=\int_0^x\left(\frac1{1+t}+\frac1{1-t}\right)\,dt\\
&=2\int_0^x\frac{dt}{1-t^2}
=2\sum_{r=0}^\infty\int_0^x t^{2r}\,dt
=2\sum_{r=0}^\infty\frac{x^{2r+1}}{2r+1}.
\end{aligned}
$$

积分交换可由$[0,x]$上几何级数的一致收敛保证。反对称标准形还给$\|S^p\|_F^2=2\sum_j\lambda_j^{2p}$。逐项代入，

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

令 $r_d=\rho_d(T_d)$。若上述不等式取等，则各项的非负差均为零。取 $r=1$，得到 $\|S^3\|_F^2=\|T_d^3\|_F^2$。又因为这一差等于各列非负差之和，每一列也取等。由第 6.2 节的取等条件及 Fang–Huang 的后缀等号结论，

$$
(S^3e_j)^*=K_d^3e_1,\qquad
(S^2e_j)^*=K_d^2e_1.
$$

对后一式求平方和并按$j$求和，

$$
\operatorname{tr}S^4=\|S^2\|_F^2
=d\|K_d^2e_1\|_2^2
=\|T_d^2\|_F^2=\operatorname{tr}T_d^4.
$$

由详细证明稿附录 A.3，四次矩取等当且仅当 $S=\Omega^TT_d\Omega$，其中 $\Omega$ 为带符号置换矩阵。反之，由 $\Omega^T\Omega=I$ 可得

$$
I+tS=\Omega^T(I+tT_d)\Omega,\qquad
\det(I+tS)=(\det \Omega)^2\det(I+tT_d)=\det(I+tT_d).
$$

**引理 6.4 (谱比值及等号条件).**

分别取$t=1/d$和$t=i/d$，得到$\rho_d(S)=r_d$。因此

$$
\rho_d(S)\le r_d,
\quad\text{等号当且仅当 }S=\Omega^TT_d\Omega.
$$


**证明 (正则情形的普通同构分类).**

写 $\Omega=D_{\varepsilon}P$，其中 $P$ 为置换矩阵，$D_{\varepsilon}=\operatorname{diag}(\varepsilon_1,\ldots,\varepsilon_d)$，$\varepsilon_i\in\{-1,1\}$。记 $\varepsilon=(\varepsilon_1,\ldots,\varepsilon_d)^T$，则

$$
S=P^TD_{\varepsilon}T_dD_{\varepsilon}P,\qquad PSP^T=D_{\varepsilon}T_dD_{\varepsilon}.
$$

用 $P$ 重编号后，仍记所得矩阵为 $S$。正则性给出 $S\mathbf1=0$，再由 $D_{\varepsilon}^2=I$ 得

$$
D_{\varepsilon}T_d\varepsilon=0,\qquad T_d\varepsilon=0.
$$

第$i$行与第$i+1$行的差只有第$i,i+1$列各为1，因此

$$
0=(T_d\varepsilon)_i-(T_d\varepsilon)_{i+1}=\varepsilon_i+\varepsilon_{i+1}.
$$

因此 $\varepsilon_i=(-1)^{i-1}\varepsilon_1$。整体符号 $\varepsilon_1$ 在 $D_{\varepsilon}T_dD_{\varepsilon}$ 中抵消，所得矩阵恰为交替切换。详细证明稿附录 A.2 证明它与 $\mathrm{Car}_d$ 同构，故正则图中仅圆环图取等。


### 6.5 六次矩的严格间隙


![将 $\mathrm{Car}_5$ 中集合 $U=\{1,2\}$ 与其补集之间的边全部反向，得到传递次序 $(3,1,4,2,0)$。圈出的顶点属于 $U$。这一切换对应符号矩阵的共轭 $S\mapsto DSD$，因而保持谱比值；它一般不保持 Hamilton 路径数。](figures/carousel_switching.png){width=94%}


$\binom nk=n!/(k!(n-k)!)$，$k>n$时为0。

**引理 6.5 (六次矩的严格亏损).**

若正则$S$不普通同构于圆环，上一节的等号推演给

$$
\Delta_3:=\|T_d^3\|_F^2-\|S^3\|_F^2>0.
$$


**证明。**

在模2意义下$S\equiv J+I$，并且$J^2=dJ$、$J^3=d^2J$，所以

$$
S^3\equiv(J+I)^3
=I+3J+3dJ+d^2J
\equiv I+(1+d+d^2)J\equiv I+J\pmod2.
$$

最后一步使用$d(d+1)$为偶数。又$(S^3)^T=-S^3$，故其对角为0、非对角为奇数。若$z=2k+1$，

$$
z^2=4k(k+1)+1\equiv1\pmod8.
$$

将反对称位置成对求和，

$$
\|S^3\|_F^2=2\sum_{i<j}((S^3)_{ij})^2
\equiv2\binom d2=d(d-1)\pmod{16}.
$$

此式也适用于$T_d$。因此$\Delta_3$是正的16的整数倍，$\Delta_3\ge16$。在对数级数中只保留$r=1$项，

$$
\log\frac{r_d}{\rho_d(S)}
\ge\frac{\Delta_3}{3d^6}\ge\frac{16}{3d^6}.
$$

两边取指数，再移项，

$$
\rho_d(S)\le r_de^{-16/(3d^6)},\qquad
r_d-\rho_d(S)\ge r_d(1-e^{-16/(3d^6)})>0.
$$


这个间隙取决于基图阶数 $d$；相应的块阶阈值将在第 11.2 节由极限比较得到。

### 6.6 全阶数谱比较

**命题 6.6。** 对每个 $n\ge2$ 及每个 $n$ 阶竞赛符号矩阵，$\rho_n(S)\le r_n=L+O(n^{-1})$，其中隐含常数为绝对常数。

**证明。**

第 6 节的正则等号分类只涉及奇阶图，但在它之前的谱不等式不要求正则性。为使全阶数应用明确，令 $n\ge2$，将第 6.3 节的排列写为“全部奇指标递增，再接全部偶指标递减”。奇阶时这是原排列；偶阶时则为 $(1,3,\ldots,n-1,n,n-2,\ldots,2)$。相应逐元素等式仍给出

$$
T_n=\Lambda^TD_0K_nR_0\Lambda,\qquad
T_n^2=-U^TK_n^2U,\qquad U=D_0\Lambda,
\qquad Ue_1=e_1.
$$

带负绕回移位满足 $Z^TT_nZ=T_n$，也不依赖奇偶性。因此 $T_n^{2p}$ 的全部对角元相同。对任意整数 $p\ge1$，Fang–Huang 的逐列比较与这些恒等式给出

$$
\|S^p\|_F^2\le n\|K_n^pe_1\|_2^2=\|T_n^p\|_F^2.
$$

将它代入第 6.4 节绝对收敛的对数级数，即得对每个阶数

$$
\log\rho_n(S)
=\sum_{r\ge0}\frac{\|S^{2r+1}\|_F^2}{(2r+1)n^{4r+2}}
\le\log\rho_n(T_n).
$$

详细证明稿附录 A.1 的行列式多项式对奇偶阶数同样成立，所以

$$
\rho_n(S)\le r_n
=\frac{(1+1/n)^n+(1-1/n)^n}
{(1+i/n)^n+(1-i/n)^n}
=L+O(n^{-1}).
$$

最后一步可由第 8.2 节的复指数估计直接得到：对 $z\in\{1,-1,i,-i\}$，$n\log(1+z/n)=z+O(n^{-1})$，分母趋于 $2\cos1>0$，故商的误差也是 $O(n^{-1})$。这些估计只含阶数 $n$，不含图的选择。

$\square$

## 7. 全体竞赛图的路径上界

使用度数方差记号

$$
V_{\rm deg}(T)=\sum_i\left(d_i^+-\frac{n-1}{2}\right)^2
=\frac14\|S\mathbf1\|_2^2,
\qquad
\tau=\frac{4V_{\rm deg}(T)}{(n-1)^2}.
$$

证明分为三种情形。若 $V_{\rm deg}(T)\ge16n^2\log n$，Brégman 不等式中的方差修正因子使路径数可以忽略。否则，度数落在 $[(n-1)/20,19(n-1)/20]$ 之外的顶点至多有 $O(\log n)$ 个。若存在这样的顶点，将它们与其余部分分离后，可得路径数低于随机期望。剩余竞赛图的归一化度差与 $\pm1$ 保持固定距离，且 $\tau=O(\log n)$。对它们，下面的永久式估计保留因子 $e^{-\tau}$，从而将最终误差控制到 $O(n^{-1})$。

本节中的 $K$ 可以在不同位置增大；固定上述度数阈值后，它是绝对常数。第 5.1 节已将长项控制为 $o(n^{-1})\mu_n$，故这里只估计短项 $|U|\le k_n$。

**命题 7.1（统一路径上界）。** 存在绝对常数 $K,n_0$，使任意 $n\ge n_0$ 及 $n$ 阶竞赛图 $T$ 满足

$$
H(T)\le(L+K/n)\mu_n.
$$

三类图所需精度不同：高方差类只需 $o(n^{-1})$，异常点类只需低于随机基线 $1$，剩余类才承担统一的 $L+O(n^{-1})$。以下依次实现这三个目标。

### 7.1 非主永久式估计的应用

引理 4.4 的非主永久式界适用于不同的行、列删集。以下用它控制异常顶点与核心之间的跨边；当两删集相同时，所得度差乘积将保留在路径卷积之外。

### 7.2 较大的出度离差平方和


**引理 7.2（含方差修正因子的永久式界）。**

存在绝对常数 $K$，使每个 $m\ge1$ 阶竞赛图 $Q$，若其出度为 $d_i$，度数方差为 $V_{\rm deg}(Q)=\sum_i(d_i-(m-1)/2)^2$，则满足

$$
\operatorname{per}A_Q\le
K\sqrt{m+1}\frac{m!}{2^m}\exp\left(-\frac{V_{\rm deg}(Q)}{8m^2}\right).
$$


**证明。**

利用行度数因子的凹性，可以加强 Brégman 界 [2]。若某个 $d_i=0$，上界显然成立。否则，对正整数定义 $f(k)=\log(k!)/k$。直接计算得，对 $k\ge2$，

$$
2f(k)-f(k-1)-f(k+1)
=\frac{2[\log k-f(k-1)]-k\log(1+1/k)}{k(k+1)}.
$$

对 $1,\ldots,k-1$ 使用算术—几何平均不等式，得到 $\log k-f(k-1)\ge\log2$。又有 $(1+1/k)^k<e<3$，故分子至少为 $\log(4/3)\ge1/4$。因此，在度数区间 $[1,m-1]$ 上，整数点函数 $f(k)+k^2/(8m^2)$ 的分段线性插值是凹函数。对平均值 $\eta=(m-1)/2$ 使用 Jensen 不等式得

$$
\sum_i f(d_i)
\le m\widetilde f(\eta)-\frac{V_{\rm deg}(Q)}{8m^2}+\frac{1}{32m},
$$

其中 $\widetilde f$ 为线性插值。最后一项处理半整数均值；整数均值时可省去。Stirling 公式给出

$$
\exp(m\widetilde f(\eta))\le K\sqrt{m+1}\frac{m!}{2^m}.
$$

结合 Brégman 的行度数上界，即得方差估计。

下面将此界用于每个短删集对应的竞赛图。为此，需要确认删点后方差仍然足够大。

删去大小为 $k$ 的集合 $U$ 后，每个剩余顶点的中心化度数改变至多 $k/2$；被删除的原平方偏差之和至多为 $kn^2/4$。对交叉项使用 Cauchy–Schwarz 不等式，得到

$$
V(T-U)\ge V_{\rm deg}(T)-\frac{kn^2}{4}-k\sqrt{nV_{\rm deg}(T)}.
$$

若 $V_{\rm deg}(T)\ge16n^2\log n$，则对所有 $k\le k_n$ 一致有

$$
V(T-U)\ge(1-o(1))V_{\rm deg}(T).
$$

于是每个短永久式的方差修正因子至多为 $n^{-2+o(1)}$；前面的 $\sqrt n$ 因子可被吸收。按可求和的行列式权重求和，归一化短项总贡献至多为 $n^{-3/2+o(1)}$。加上长删集尾项，得到对该类图统一成立的结论

$$
V_{\rm deg}(T)\ge16n^2\log n\quad\Longrightarrow\quad
H(T)/\mu_n=o(1/n).
$$


记 $L_k=\log(k!)$，则

$$
\begin{aligned}
2f(k)-f(k-1)-f(k+1)
&=\frac{2(L_{k-1}+\log k)}k-\frac{L_{k-1}}{k-1}
-\frac{L_{k-1}+\log k+\log(k+1)}{k+1}\\
&=\frac{2\log k-2L_{k-1}/(k-1)-k\log(1+1/k)}{k(k+1)}.
\end{aligned}
$$

AM–GM 给出

$$
((k-1)!)^{1/(k-1)}\le\frac{1+\cdots+(k-1)}{k-1}=k/2,
$$

因此 $\log k-f(k-1)\ge\log2$。又 $k\log(1+1/k)<1<\log3$，以及

$$
\log(4/3)=\int_1^{4/3}\frac{du}{u}\ge\frac{1/3}{4/3}=\frac14.
$$

故二阶差至少为 $1/[4k(k+1)]\ge1/(4m^2)$。令 $h(k)=f(k)+k^2/(8m^2)$，则

$$
2h(k)-h(k-1)-h(k+1)
\ge\frac1{4m^2}-\frac2{8m^2}=0.
$$

若 $\eta$ 为整数，$\widetilde h(\eta)=\widetilde f(\eta)+\eta^2/(8m^2)$；若 $\eta=k+1/2$，则

$$
\frac{k^2+(k+1)^2}{2}=\eta^2+\frac14,
\quad
\widetilde h(\eta)=\widetilde f(\eta)+\frac{\eta^2+1/4}{8m^2}.
$$

因此 Jensen 不等式给出

$$
\begin{aligned}
\sum_i f(d_i)+\frac{\sum_i d_i^2}{8m^2}
&=\sum_i h(d_i)\le m\widetilde h(\eta)\\
&\le m\widetilde f(\eta)+\frac{m\eta^2}{8m^2}+\frac1{32m},\\
\sum_i f(d_i)&\le m\widetilde f(\eta)
-\frac{\sum_i(d_i-\eta)^2}{8m^2}+\frac1{32m}.
\end{aligned}
$$

对于 $m=2r+1$，Stirling 的对数形式给出

$$
m f(r)=\frac{2r+1}{r}\left[r\log r-r+\tfrac12\log(2\pi r)+O(1/r)\right],
$$

$$
\log(m!/2^m)=m\log(m/2)-m+\tfrac12\log(2\pi m)+O(1/m).
$$

相减并用 $r=(m-1)/2$，得到 $\tfrac12\log m+O(1)$。对于 $m=2r$，
$\widetilde f(\eta)=[f(r-1)+f(r)]/2$，分别使用同一公式得到相同差值。故指数化后得到 $K\sqrt{m+1}$。有 $d_i=0$ 时永久式每项均有零因子；$m=1,2$ 直接并入常数。


写 $b_i=d_i^+-(n-1)/2$。对保留顶点，令 $e_i$ 为其指向 $U$ 的边数，则

$$
b_i'=d_i^+-e_i-(n-k-1)/2=b_i+\delta_i,
\qquad\delta_i=k/2-e_i,\quad |\delta_i|\le k/2.
$$

所以

$$
\begin{aligned}
V(T-U)&=\sum_{i\notin U}(b_i+\delta_i)^2\\
&\ge V_{\rm deg}(T)-\sum_{i\in U}b_i^2-2\left|\sum_{i\notin U}b_i\delta_i\right|\\
&\ge V_{\rm deg}(T)-kn^2/4-k\sum_{i\notin U}|b_i|\\
&\ge V_{\rm deg}(T)-kn^2/4-k\sqrt{nV_{\rm deg}(T)}.
\end{aligned}
$$

在 $V\ge16n^2\log n$ 时，相对损失分别至多为

$$
\frac{k}{64\log n}=o(1),\qquad
k\sqrt{n/V}\le\frac{k}{4\sqrt{n\log n}}=o(1).
$$

于是 $V(T-U)/(8(n-k)^2)\ge(2-o(1))\log n$，罚项为 $n^{-2+o(1)}$，再乘 $\sqrt n$ 及 $\sum_kw_k<\infty$ 即得 $n^{-3/2+o(1)}$。


为估计方差界中的阶乘因子，使用详细证明稿附录 B.3 的 Stirling 公式。记其中的常数为 $c$，则

$$
f(r)=\log r-1+\frac{\log r}{2r}+\frac cr+O(r^{-2}).
$$

先取 $m=2r+1$，平均出度为整数 $r$。乘以 $m$：

$$
mf(r)=m\log r-m+\left(1+\frac1{2r}\right)\log r
+2c+\frac cr+O(r^{-1}).
$$

自然尺度的对数为

$$
\log(m!/2^m)=m\log(m/2)-m+\frac12\log m+c+O(m^{-1}).
$$

相减后记作 $\Delta_m$：

$$
\begin{aligned}
\Delta_m
&=m\log\frac{2r}{m}+\log r-\frac12\log m
+c+O(\log m/m)\\
&=m\log(1-1/m)+\frac12\log m-\log2
+\log(1-1/m)+c+O(\log m/m).
\end{aligned}
$$

$m\log(1-1/m)=-1+O(1/m)$，其余未含 $\frac12\log m$ 的项一致有界，故 $\Delta_m\le\frac12\log m+K$。

再取 $m=2r$、$r\ge2$，平均为 $r-1/2$，线性插值得

$$
m\widetilde f((m-1)/2)=r[f(r-1)+f(r)].
$$

逐项代入：

$$
\begin{aligned}
r[f(r-1)+f(r)]
={}&r\log(r-1)+r\log r-2r\\
&+\frac r{2(r-1)}\log(r-1)+\frac12\log r\\
&+c\frac r{r-1}+c+O(r^{-1}).
\end{aligned}
$$

减去 $\log((2r)!/2^{2r})=2r\log r-2r+\frac12\log(2r)+c+O(r^{-1})$，得

$$
\begin{aligned}
\Delta_{2r}
={}&r\log(1-1/r)
+\frac r{2(r-1)}\log(r-1)\\
&-\frac12\log2+c\frac r{r-1}+O(r^{-1}).
\end{aligned}
$$

第一项不大于零。第二项满足

$$
\frac r{2(r-1)}\log(r-1)
\le\frac12\log r+\frac{\log r}{2(r-1)}
\le\frac12\log r+\frac12,
$$

其中 $\log r\le r-1$。常数项 $c r/(r-1)$ 绝对值至多 $2|c|$。所以仍有 $\Delta_m\le\frac12\log m+K$。两类均指数化得到

$$
\exp(m\widetilde f((m-1)/2))\le e^K\sqrt m\,m!/2^m.
$$

有限个不在展开范围内的 $m$ 由增大同一个 $K$ 覆盖。 $\square$

### 7.3 异常顶点


![一个永久式项中的有向五圈及其行列匹配。灰色顶点组成异常集 $F=\{f_1,f_2\}$。跨块边占用核心行 $I=\{x_2,x_3\}$ 和核心列 $J=\{x_1,x_3\}$，留下粗边所示的非主子矩阵项 $A[x_1,x_2]$。图中只画出这个永久式项的边。](figures/nonprincipal_matching.png){width=94%}


下面假设 $V_{\rm deg}(T)<16n^2\log n$。定义异常集

$$
F=\left\{i:\frac{d_i^+}{n-1}\notin[1/20,19/20]\right\},
\qquad f=|F|,\qquad M=T-F,\qquad N=n-f.
$$

每个异常顶点向 $V_{\rm deg}(T)$ 贡献至少某个固定正倍数的 $n^2$，故 $f=O(\log n)$。非异常顶点的原度差绝对值至多为 $0.9(n-1)$；删去 $F$ 改变它至多 $f$。因此，对所有充分大的 $n$ 一致有

$$
\max_i|(S_M\mathbf1)_i/(N-1)|<0.95,\qquad
\tau_M=O(\log n).
$$

对度差平方和，使用 $\|S_M\mathbf1\|_2\le\|S\mathbf1\|_2+f\sqrt N$，再除以 $N-1$。进一步删除短核心子集后，同一论证仍然适用。在这些删除中始终保留原异常集 $F$，因此常数可以统一选取。

先按圈覆盖在 $F$ 与核心 $M$ 之间的连接方式估计 $\operatorname{per}A_T$。异常顶点在某个方向上的邻居很少。圈覆盖需要使用两个方向的边，除非将该顶点匹配到 $F$ 内部；后一种选择会产生 $1/N$ 量级的代价。使用引理 4.4 的核心成对权重 $\ell,r$，它们的总偏移满足

$$
\sum_{i\in M}|\ell_i-1|+\sum_{i\in M}|r_i-1|
\le K\sqrt{N\log n}.
$$

对 $x\in F$，记 $q_x=N^{-1}|\{j\in M:x\to j\}|$。它到 $[0,1/20]\cup[19/20,1]$ 的距离为 $O(f/n)$。两侧带权跨边邻居之和分别由 $N(q_x+\beta)$ 和 $N(1-q_x+\beta)$ 控制，其中 $\beta=O(\sqrt{\log n/n})$。置

$$
u_x=2(q_x+\beta),\qquad v_x=2(1-q_x+\beta).
$$

可对全部 $x$ 统一选取

$$
u_xv_x\le c_n=19/100+o(1),\qquad
u_x,v_x\le L_n=2+o(1).
$$

按排列在 $F$ 内部使用的边分解永久式。若内部有 $s$ 条边，其行集 $R$ 和列集 $C$ 均有 $s$ 个点；每个跨边方向恰有 $t=f-s$ 条边。核心行、列删集 $I,J$ 均有 $t$ 个点，但不必相同。精确四块展开为

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

每个有贡献的排列被唯一分类。先对核心永久式使用引理 4.4 的一致上界，再分离两个跨边求和。删除核心行产生 $\ell_i$，删除核心列产生 $r_j$。固定 $R,C$，向外跨边求和精确等于

$$
\begin{aligned}
&\sum_{\substack{J\subseteq M\\|J|=t}}
\operatorname{per}A[F\setminus R,J]\prod_{j\in J}r_j\\
&=\sum_{\phi:F\setminus R\hookrightarrow M}
\prod_{x\in F\setminus R}A_{x,\phi(x)}r_{\phi(x)}
\le\prod_{x\in F\setminus R}\sum_{j\in M}A_{xj}r_j.
\end{aligned}
$$

独立地，向内跨边求和为

$$
\begin{aligned}
&\sum_{\substack{I\subseteq M\\|I|=t}}
\operatorname{per}A[I,F\setminus C]\prod_{i\in I}\ell_i\\
&=\sum_{\psi:F\setminus C\hookrightarrow M}
\prod_{y\in F\setminus C}A_{\psi(y),y}\ell_{\psi(y)}
\le\prod_{y\in F\setminus C}\sum_{i\in M}A_{iy}\ell_i.
\end{aligned}
$$

其中 $\hookrightarrow$ 表示单射。每个单射由其像集及相应永久式项恰好计数一次，没有额外的 $t!$ 因子。像集 $I,J$ 不必相等，也不必不交，因为它们分别属于核心的行、列副本。所有因子非负，故可去掉单射限制。两个上界的乘积为

$$
N^{2t}2^{-2t}
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right).
$$

异常内部永久式至多为 $s!$。除以 $n!/2^n$ 后，阶乘与二的幂合并为

$$
2^sN^{2t}\frac{(N-t)!}{(N+f)!}
=\left(\frac2N\right)^s\exp(O(f^2/N)).
$$

这里 $N+f-(N-t)=f+t=2f-s$，故阶乘比贡献 $N^{-(2f-s)}\exp(O(f^2/N))$，再乘 $N^{2t}$ 后恰留下 $N^{-s}$。

令 $h=|R\cap C|$。成对乘积满足

$$
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right)
\le c_n^{f-2s}L_n^{2s}(c_n/L_n^2)^h
\le c_n^{f-2s}L_n^{2s}.
$$

第一个不等式由分别统计出现两个、一个及零个因子的顶点数得到；即使 $f-2s$ 为负，它仍正确。引理 4.4 的误差在 $t\le f=O(\log n)$ 内统一为 $o(1)$，其因子 $\Gamma\le1$ 可舍去。由 $\binom fs^2s!\le f^{2s}/s!$，求和可得

$$
\frac{\operatorname{per}A_T}{n!/2^n}
\le(1+o(1))e^{-1}D_N(S_M)c_n^f
\exp(O(f^2/N))
\exp\left(\frac{2L_n^2f^2}{c_n^2N}\right).
$$

其中额外指数均为 $o(1)$。具体地，删除短核心子集 $U$ 后，核心阶数为 $N'=n-f-|U|\sim n$（即 $N'/n\to1$），异常集合仍取原来的 $F$。核心的归一化度差最终仍不超过 $0.95$，归一化度差平方和为 $O(\log n)$，而跨边删集大小为 $t\le f=O(\log n)$。因此引理 4.4 中的误差指数为

$$
O\!\left(\frac{(\log n)^{3/2}}{\sqrt n}+\frac{(\log n)^2}{n}\right)=o(1),
$$

其中常数与 $U,I,J$ 无关。跨边邻点比例相较于原始全图仅改变 $O((f+|U|)/n)$，权重的一范数位移仍为 $O(\sqrt{n\log n})$，故前述跨边求和估计也一致成立。此时核心高斯因子改变为原来的 $\exp(O(|U|/n))$ 倍：对 $S_M/N$ 使用高斯删行列引理，对数损失为 $O(|U|/n)$；将归一化尺度从 $N$ 改为 $N-|U|$ 也产生同阶误差。

在路径卷积中，大小为 $k$ 且与 $F$ 相交的子集占比至多为 $fk/n$。通用永久式界因而使其全部归一化短项贡献至多为

$$
K\frac f{\sqrt n}\sum_k kw_k=o(1).
$$

对包含于核心的子集，恢复下降阶乘后，对正主子式求和。任意核心阶数 $N\le n$ 均满足由秩一行列式恒等式给出的界

$$
\det\left(I_N+\frac2n(I_N+A_M)\right)
\le2e\det(I_N+S_M/N).
$$

证明时先提出 $(1+1/n)^N\le e$。剩余全一秩一因子至多为 $1+N/(n+1)<2$，因为 $I+S_M/(n+1)$ 的逆矩阵的实二次型至多为向量范数的平方。最后，反对称频率行列式乘积在尺度从 $1/(n+1)$ 增至 $1/N$ 时单调增大。

短子集的下降阶乘恢复带来 $\exp(O(k_n^2/n))=1+o(1)$。由于最终 $c_n<1/4$，上述统一估计给出

$$
\frac{H(T)}{\mu_n}
\le(1/4)^f\rho_N(S_M)+o(1)
\le 3/4+o(1)<1,\qquad f\ge1.
$$

由于 $P(n)\ge\mu_n$，充分大阶数的极值图均无异常顶点。还可将上界放宽为 $(10/3)4^{-f}(1+\varepsilon_n)$：这里计入的是删集与 $F$ 不相交的短卷积项；其余短项和长项合计记为 $\delta_n$。于是

<a id="eq-exceptional-bound"></a>

$$
\frac{H(T)}{\mu_n}\le\frac{10}{3}4^{-f}(1+\varepsilon_n)+\delta_n,
\qquad \varepsilon_n,\delta_n\longrightarrow0.
\tag{7.1}
$$

两个误差均在上述低方差图类上一致趋于零。取 $n$ 充分大，使 $1+\varepsilon_n\le21/20$，并使与 $F$ 相交的短项及长项各不超过 $1/25$。当 $f\ge1$ 时，[式 (7.1)](#eq-exceptional-bound)给出

$$
\frac{10}{3}\cdot\frac14\cdot\frac{21}{20}+\frac1{25}+\frac1{25}
=\frac{191}{200}<1.
$$

两种选择均不影响最终上界常数。


异常点满足

$$
|d_i^+-(n-1)/2|>\frac9{20}(n-1),\quad
f\frac{81}{400}(n-1)^2\le V_{\rm deg}(T)<16n^2\log n,
$$

故 $f<(6400/81)(n/(n-1))^2\log n$。对核心，

$$
\max_i|s_i^M|\le0.9(n-1)+f,
\quad \frac{0.9(n-1)+f}{n-f-1}\longrightarrow0.9,
$$

$$
\tau_M\le\frac{2\|s\|_2^2+2f^2N}{(N-1)^2}
=O(\log n)+O((\log n)^2/n)=O(\log n).
$$

因为 $|\ell_i-1|\le|a_i|/(1-b)$、$|r_i-1|\le|a_i|/(1-b)$，

$$
\sum_i(|\ell_i-1|+|r_i-1|)
\le\frac2{1-b}\sum_i|a_i|
\le\frac2{1-b}\sqrt{N\tau_M}=O(\sqrt{N\log n}).
$$

这使任意邻居子集的加权计数与普通计数相差至多上述总偏移。具体地，

$$
\sum_jA_{xj}r_j\le Nq_x+K\sqrt{N\log n},\quad
\sum_iA_{ix}\ell_i\le N(1-q_x)+K\sqrt{N\log n}.
$$

当 $q\in[0,1/20]\cup[19/20,1]$ 时，$4q(1-q)\le4(1/20)(19/20)=19/100$；邻居比例的 $O(f/n)$ 扰动与 $\beta=o(1)$ 扰动共同给出 $u_xv_x\le19/100+o(1)$。

四块展开中 $t=f-s$；依次取异常内部 $s$ 条边、异常到核心 $t$ 条边、核心到异常 $t$ 条边、核心内部 $N-t$ 条边，总数

$$
s+t+t+(N-t)=N+f=n.
$$

永久式展开没有符号，分类后每个排列只出现一次。全部二次幂及阶乘因子为

$$
\frac{[(N-t)!/2^{N-t}]\,[N^{2t}/2^{2t}]}{(N+f)!/2^{N+f}}
=2^{f-t}N^{2t}\frac{(N-t)!}{(N+f)!}
=2^sN^{2t}\frac{(N-t)!}{(N+f)!}.
$$

由于

$$
\frac{(N-t)!}{(N+f)!}=\prod_{h=-t+1}^{f}\frac1{N+h}
=N^{-(f+t)}\exp\left(-\sum_{h=-t+1}^{f}\log(1+h/N)\right),
$$

且 $\sum|h|/N=O(f^2/N)$，上式变为

$$
2^sN^{2t-(f+t)}e^{O(f^2/N)}=(2/N)^se^{O(f^2/N)}.
$$

若 $h=|R\cap C|$，同时出现 $u,v$ 两因子的顶点数为 $f-2s+h$，只出现一个因子的顶点数为 $2s-2h$；于是

$$
c_n^{f-2s+h}L_n^{2s-2h}
=c_n^{f-2s}L_n^{2s}(c_n/L_n^2)^h
\le c_n^{f-2s}L_n^{2s}.
$$

全部内部边选择的求和为

$$
\begin{aligned}
\sum_{s=0}^f\binom fs^2s!(2/N)^sc_n^{f-2s}L_n^{2s}
&\le c_n^f\sum_{s=0}^f\frac1{s!}
\left(\frac{2L_n^2f^2}{c_n^2N}\right)^s\\
&\le c_n^f\exp\left(\frac{2L_n^2f^2}{c_n^2N}\right).
\end{aligned}
$$

以下 $\#E$ 与 $|E|$ 均表示有限集合 $E$ 的元素数。$k=0$ 时删集不与异常集相交，所占比例为零；对 $1\le k\le n$，该比例满足

$$
\frac{\#\{U:|U|=k,U\cap F\ne\varnothing\}}{\binom nk}
\le\sum_{x\in F}\frac{\binom{n-1}{k-1}}{\binom nk}=fk/n.
$$

乘通用卷积权重 $K\sqrt n\,w_k$ 后总和为 $Kf\sum_kkw_k/\sqrt n=o(1)$。


令 $Q=S_M/(n+1)$，$v=\mathbf1_N$，则

$$
\begin{aligned}
\det\left(I_N+\frac2n(I_N+A_M)\right)
&=(1+1/n)^N\det(I_N+Q)
\left[1+\frac1{n+1}v^{\mathsf T}(I_N+Q)^{-1}v\right].
\end{aligned}
$$

利用 $(I+Q)^{-1}=(I-Q)(I-Q^2)^{-1}$ 及反对称二次型为零，

$$
v^{\mathsf T}(I+Q)^{-1}v=v^{\mathsf T}(I+Q^{\mathsf T}Q)^{-1}v\le\|v\|_2^2=N.
$$

又 $(1+1/n)^N\le e^{N/n}\le e$，并且

$$
\det(I+S_M/(n+1))=\prod_j\left(1+\frac{\lambda_j^2}{(n+1)^2}\right)
\le\prod_j\left(1+\frac{\lambda_j^2}{N^2}\right).
$$

三项分别由 $e$、$\det(I+S_M/N)$ 和 $2$ 控制。再乘永久式中的 $e^{-1}/2$，得到 $\rho_N(S_M)$。上述异常集估计中的常数满足

$$
\frac{10}{3}\frac14\frac{21}{20}=\frac78=\frac{175}{200},\qquad
\frac1{25}+\frac1{25}=\frac{16}{200},\qquad
\frac{175+16}{200}=\frac{191}{200}.
$$


设删去异常点和短集后，每个异常点的核心邻居比例距 $[0,1/20]\cup[19/20,1]$ 至多为 $\epsilon_n$，其中 $\epsilon_n=O((f+k_n)/n)$。对 $q\in[0,1]$，函数 $q(1-q)$ 的导数绝对值至多一。因此

$$
q_x(1-q_x)\le\frac{19}{400}+\epsilon_n.
$$

用同一个非负权重偏移 $\beta_n=O(\sqrt{\log n/n})$，

$$
\begin{aligned}
u_xv_x
&=4(q_x+\beta_n)(1-q_x+\beta_n)\\
&=4q_x(1-q_x)+4\beta_n+4\beta_n^2\\
&\le\frac{19}{100}+4\epsilon_n+4\beta_n+4\beta_n^2=:c_n.
\end{aligned}
$$

而 $u_x,v_x\le2+2\beta_n=:L_n$。因 $\epsilon_n,\beta_n\to0$，可先选统一阈值使

$$
4\epsilon_n+4\beta_n+4\beta_n^2<\frac6{100},\qquad c_n<\frac14.
$$

上述额外指数的每一项也都趋于零：

$$
\frac{f^2}{N}=O((\log n)^2/n)\to0,
\quad
\frac{2L_n^2f^2}{c_n^2N}=O((\log n)^2/n)\to0.
$$

引理 4.4 的误差项在 $\tau\le A\log n,t\le B\log n$ 时分别至多为常数乘

$$
\frac{\log n+(\log n)^2}{n},\quad
\frac{(\log n)^{3/2}}{\sqrt n},\quad
\sqrt{\frac{\log n}{n}},\quad
\frac{\log n+1}{n},\quad
\frac{(\log n)^{3/2}}{\sqrt n},\quad
\frac{(\log n)^2}{n}.
$$

上述常数均与竞赛图及删集无关，故所得 $o(1)$ 误差也是一致的。

### 7.4 剩余图类中的度差修正因子

**命题 7.3（度差敏感的统一计数界）。** 固定绝对常数 $K_0$。存在常数 $K_1,n_0$（只依赖 $K_0$），使每个 $n\ge n_0$ 及满足 $\|a\|_\infty\le0.9$、$\tau\le K_0\log n$ 的竞赛图都有

$$
\frac{H(T)}{\mu_n}\le\rho_n(S)\exp(-\tau/2+K_1/n)+B_n,
$$

其中 $B_n$ 是引理 5.1a 中不依赖具体图的尾界，$B_n=o(n^{-1})$。全局应用先固定三类划分所需的 $K_0$，故其中常数为绝对常数。

**证明。** 剩余竞赛图满足

$$
\max_i|a_i|\le0.9,\qquad
a=s/(n-1),\qquad \tau=\sum_i a_i^2\le K\log n.
$$

以下固定一个绝对常数 $K_0$，使 $\tau\le K_0\log n$。其成对乘积满足

$$
\Gamma=\prod_i(1-a_i^2)\le e^{-\tau}.
$$

现在对整个竞赛图应用引理 4.4。度差乘积是所有短项共有的因子；将它保持在总和之外，可以吸收那些单独看来比 $1/n$ 更大的误差。

对大小为 $k\le k_n$ 的主删集 $U$，引理 4.4 给出

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

在累计误差时，必须保留公共因子 $\Gamma$。定义非负系数

$$
c_k=(2/n)^k\sum_{|U|=k}\det(I+A[U])\prod_{i\in U}g_i.
$$

它们满足 $c_0=1$、$c_k\le G^kw_k$。下降阶乘的恢复产生

$$
\log\frac{n^k}{(n)_k}=O(k^2/n),\qquad k\le k_n.
$$

令 $\delta_n=\sqrt{\tau/n}+1/n$，$r_k=R_{\tau,k}+\log(n^k/(n)_k)$。将误差上界选为非负值后，对 $\tau\le K_0\log n$ 一致有 $0\le r_k\le K\delta_n(k+k^2)$，且 $\max_{k\le k_n}r_k=o(1)$。因此

$$
\sum_{k\le k_n}c_ke^{r_k}
\le\sum_{k=0}^{n}c_k+
K\delta_n\sum_{k\ge0}G^kw_k(k+k^2)
\le\left(\sum_{k=0}^{n}c_k\right)e^{K\delta_n}.
$$

最后一步使用 $\sum_kc_k\ge1$ 以及相应固定矩的收敛性。归一化短路径总和因而至多为

$$
\frac{e^{-1}D_n(S)\Gamma}{2}
e^{R_\tau+K\delta_n}
\det\left(I+\frac2n\operatorname{diag}(g)(I+A)\right).
$$

误差总和由 $G^kw_k$ 的有限矩控制，而非由最大删集大小 $k_n$ 控制。这避免了在最终误差中引入额外的对数因子。

下面去除权重，同时保持度差修正因子。令 $W=I+(2/n)(I+A)$、$\Delta=(2/n)\operatorname{diag}(g-1)(I+A)$。$W$ 的对称部分至少为 $I$，故 $\|W^{-1}\|_{\rm op}\le1$。由于 $I+A$ 每行的二范数至多为 $\sqrt n$，且 $\sum_i(g_i-1)\le K\tau$，将 $\Delta$ 分解为秩一行矩阵之和，可以控制其迹范数，即奇异值之和。由 $\|uv^{\mathsf T}\|_*=\|u\|_2\|v\|_2$，得到

$$
\|\Delta\|_*\le K\tau/\sqrt n.
$$

由行列式不等式 $|\det(I+E)|\le\exp(\|E\|_*)$，可得

$$
\det(W+\Delta)\le\det(W)e^{K\tau/\sqrt n}.
$$

两个行列式均为正：$W$ 的对称部分正定；加权行列式的主子式展开系数为正。第 7.3 节的无权秩一界在 $N=n$ 时为 $\det(W)\le2e\det(I+S/n)$。

合并上述各因子，最后仅加入引理 5.1a 的长删集尾项，得到保留度差修正因子的一致上界

<a id="eq-score-penalty"></a>

$$
\frac{H(T)}{\mu_n}\le
\rho_n(S)\exp\left\{-\tau+
K\left[\frac{1+\tau+\tau^2}{n}
+\frac{\tau^{3/2}+\tau}{\sqrt n}+\sqrt{\tau/n}\right]\right\}
+B_n.
\tag{7.2}
$$

当 $\tau\le K_0\log n$ 时，除常数 $1/n$ 外的多项式误差项，在充分大阶数总共至多消耗 $\tau/4$。剩余平方根项由 Young 不等式控制：

$$
K\sqrt{\tau/n}\le\tau/4+K^2/n.
$$

[式 (7.2)](#eq-score-penalty)中的总指数因此至多为 $-\tau/2+K/n$。这就证明命题 7.3。再由命题 6.6，得到

$$
H(T)/\mu_n\le r_ne^{K/n}+B_n=L+O(1/n).
$$


$\square$

### 7.5 完成上界

三类图覆盖全部竞赛图。高方差图的归一化路径数为 $o(1/n)$；低方差但含异常点的图严格低于一；所有剩余图满足刚才的 $L+O(1/n)$ 上界。因此

$$
{P(n)\le\bigl(L+O(1/n)\bigr)\mu_n.}
$$

三种情形中的起始阶数均不依赖具体竞赛图，因此取一个共同阈值便得到命题 7.1 的上界。

## 8. 小度差公式与路径下界


**定理 8.1（小度差路径近似）。**

存在绝对常数 $C$，具有如下性质：对每个满足 $d(n)/\sqrt n\to0$ 的非负函数 $d=d(n)$，存在阈值 $n_0(d)$，使每个阶数为 $n\ge n_0(d)$ 且 $\|S\mathbf1\|_\infty\le d(n)$ 的竞赛图都满足

$$
\left|\frac{H(T)}{\mu_n}-\rho_n(S)\right|\le C\frac{(d(n)+1)^2}{n}.
$$


### 8.1 小度差近似的证明

**证明。**

以下记 $d=d(n)$。对每个主删集 $|U|=k\le k_n$，应用引理 4.5。因 $d+k_n+1=o(\sqrt n)$，其适用性对全部这些子集一致。恢复下降阶乘 $(n)_k$ 后，由正路径卷积得到

$$
\frac{H(T)}{\mu_n}
=\frac{e^{-1}D_n(S)}2
\sum_{k\le k_n}\left(\frac2n\right)^k
\sum_{|U|=k}\det(I+A[U])
+O\left(\frac{(d+1)^2}{n}\right).
$$

此误差率没有额外对数因子，因为误差至多为固定常数乘上

$$
\frac1n\sum_{k\ge0}w_k(d+k+1)^2
=O\left(\frac{(d+1)^2}{n}\right).
$$

下降阶乘恢复误差贡献 $O(n^{-1}\sum k^2w_k)$；大删集对应的项由第 5.1 节控制为 $o(n^{-1})$。将上式短生成和扩展到全部 $k$ 的代价为 $n^{-2+o(1)}$，因为系数被 $w_k$ 控制。于是

$$
\frac{H(T)}{\mu_n}
=\frac{e^{-1}D_n(S)}2
\det\left(I+\frac2n(I+A)\right)
+O\left(\frac{(d+1)^2}{n}\right).
$$

令 $u=\mathbf1/\sqrt n$，$Q=S/(n+1)$。秩一行列式引理给出

$$
\det\left(I+\frac2n(I+A)\right)
=(1+1/n)^n\det(I+Q)
\left(1+\frac n{n+1}u^{\mathsf T}(I+Q)^{-1}u\right).
$$

反对称性给出

$$
u^{\mathsf T}(I+Q)^{-1}u=u^{\mathsf T}(I-Q^2)^{-1}u,
$$

该量与一的差的绝对值不超过

$$
\|Qu\|_2^2\le\frac{d^2}{(n+1)^2}.
$$

又有 $(1+1/n)^n=e(1+O(n^{-1}))$；将 $S/(n+1)$ 换为 $S/n$ 的对数行列式误差为 $O(n^{-1})$，这是由归一化频率平方的有界总和得到的。因此

$$
\det\left(I+\frac2n(I+A)\right)
=2e\det(I+S/n)\left(1+O(n^{-1}+d^2/n^2)\right).
$$

代回即得定理。各估计使用同一个绝对常数；只有小度差条件开始成立的阶数依赖函数 $d$。


对每个 $k$，由
$d+k+1\le(d+1)(k+1)$，

$$
\frac1n\sum_kw_k(d+k+1)^2
\le\frac{(d+1)^2}{n}\sum_kw_k(k+1)^2.
$$

因此无需用 $k_n$ 替代 $k$，也不会产生 $\log n$ 损失。对 $Q^{\mathsf T}=-Q$，

$$
(I+Q)^{-1}=(I-Q)(I-Q^2)^{-1},\qquad
Q(I-Q^2)^{-1}\text{ 为反对称矩阵},
$$

$$
\begin{aligned}
1-u^{\mathsf T}(I+Q)^{-1}u
&=u^{\mathsf T}[I-(I+Q^{\mathsf T}Q)^{-1}]u\\
&=(Qu)^{\mathsf T}(I+QQ^{\mathsf T})^{-1}(Qu)
\le\|Qu\|_2^2.
\end{aligned}
$$

由于 $Qu=s/[(n+1)\sqrt n]$，

$$
\|Qu\|_2^2=\frac{\sum_i s_i^2}{n(n+1)^2}\le\frac{d^2}{(n+1)^2}.
$$

改变归一化尺度产生的行列式误差满足

$$
\begin{aligned}
0&\le\log\det(I+S/n)-\log\det(I+S/(n+1))\\
&=\sum_j\int_{\lambda_j^2/(n+1)^2}^{\lambda_j^2/n^2}\frac{du}{1+u}\\
&\le\sum_j\lambda_j^2\left(\frac1{n^2}-\frac1{(n+1)^2}\right)\\
&=\frac{n(n-1)}2\frac{2n+1}{n^2(n+1)^2}=O(n^{-1}).
\end{aligned}
$$

且

$$
0\le1-n\log(1+1/n)
=n\int_0^{1/n}\frac{u}{1+u}\,du\le\frac1{2n}.
$$

秩一因子与二的差为

$$
\left|1+\frac n{n+1}u^{\mathsf T}(I+Q)^{-1}u-2\right|
\le\frac1{n+1}+\frac{d^2}{(n+1)^2}.
$$

依次相乘并用 $D_n(S)\det(I+S/n)<3$，即得到定理 8.1 的绝对误差。 $\square$

### 8.2 圆环竞赛图


**推论 8.2（圆环图下界）。**

对下面定义的奇阶圆环图及偶阶一点删除构造，

$$
H(\mathrm{Car}_n)/\mu_n=L+O(n^{-1}).
$$


**证明。**

对奇数 $n$，在模 $n$ 的剩余类上定义圆环竞赛图 $\mathrm{Car}_n$：当 $1\le j\le(n-1)/2$ 时，令 $i\to i+j$。该图正则，故 $d=0$。对偶数 $n$，令 $\mathrm{Car}_n$ 为 $\mathrm{Car}_{n+1}$ 删去一个顶点所得的图，此时 $d=1$。

奇阶圆环符号矩阵与 $T_n^0$ 带符号置换相似。一个显式构造是：用对角符号 $(-1)^i$，$0\le i<n$，共轭 $T_n^0$，再按 $0,2,\ldots,n-1,1,3,\ldots,n-2$ 重排指标；两个指标同奇偶时，切换后的边沿指标递增方向；异奇偶时方向相反。按上述循环顺序读取指标，即得到圆环方向。将逆向的带符号共轭和重排限制到偶阶的一点删除后，变换所得的矩阵为剩余有序指标上的 $T_n^0$。因此，删除任意一个顶点后，同一带符号谱计算仍然适用，奇偶两类均满足

$$
\rho_n(S_{\mathrm{Car}_n})
=r_n:=\frac{(n+1)^n+(n-1)^n}{(n+i)^n+(n-i)^n}.
$$

分子、分母均除以 $n^n$，并对四个固定值 $z=1,-1,i,-i$ 使用 $(1+z/n)^n$ 的 Taylor 展开，得到

$$
r_n=\frac{\cosh1}{\cos1}+O(n^{-1})=L+O(n^{-1}).
$$

故奇偶两类都有 $H(\mathrm{Car}_n)/\mu_n=L+O(n^{-1})$，于是

$$
P(n)\ge(L-O(n^{-1}))\mu_n.
$$

从带符号相似过渡到路径数，使用的是定理 8.1，分别对应 $d=0$ 和 $d=1$。设下界与上界的常数和阈值分别为 $K_l,N_l$ 与 $K_u,N_u$。取 $K=K_l+K_u$、$n_0=\max(N_l,N_u,2)$，即得命题 7.1。


写 $n=2m+1$，原指标 $i=0,\ldots,2m$。令 $D_{ii}=(-1)^i$，则对 $i<j$，

$$
(DT_n^0D)_{ij}=(-1)^{i+j}.
$$

取重排 $p_k=2k\pmod n$（取 $0,\ldots,n-1$ 的代表元），它依次为 $0,2,\ldots,2m,1,3,\ldots,2m-1$。若 $i,j$ 同奇偶，正向差为偶数 $2h$，则

$$
2^{-1}(j-i)\pmod n=h\in\{1,\ldots,m\}.
$$

若异奇偶且 $i<j$，写 $j-i=2h+1$，则

$$
2^{-1}(j-i)\pmod n=h+m+1\in\{m+1,\ldots,2m\}.
$$

所以在新指标下，差 $1,\ldots,m$ 的边顺向，差 $m+1,\ldots,2m$ 的边逆向，正好是圆环图。删一点时取对应主子矩阵；限制后的 $D$ 仍为符号对角矩阵，而传递矩阵在保留有序指标上的主子矩阵仍为 $T_n^0$。这证明奇偶构造都具有上述谱，不声称带符号变换保持路径数。

由 $D_n(S)=\det(I+iS/n)^{-1}$ 及主子式多项式，

$$
\begin{aligned}
\rho_n(S)&=\frac{\det(I+S/n)}{\det(I+iS/n)}\\
&=\frac{(1+1/n)^n+(1-1/n)^n}
{(1+i/n)^n+(1-i/n)^n}=r_n.
\end{aligned}
$$

对 $z\in\{1,-1,i,-i\}$、$n\ge2$，在主值对数的 $|w|<1$ 级数中，

$$
\begin{aligned}
n\log(1+z/n)&=z-\frac{z^2}{2n}+R_{n,z},\\
|R_{n,z}|&\le\sum_{h=3}^{\infty}\frac1{h n^{h-1}}
\le\frac1{3n^2(1-1/n)}\le\frac2{3n^2}.
\end{aligned}
$$

指数化得 $(1+z/n)^n=e^z(1-z^2/(2n)+O(n^{-2}))$。分别相加：

$$
\begin{aligned}
(1+1/n)^n+(1-1/n)^n&=2\cosh1\,[1-1/(2n)+O(n^{-2})],\\
(1+i/n)^n+(1-i/n)^n&=2\cos1\,[1+1/(2n)+O(n^{-2})].
\end{aligned}
$$

因为 $\cos1>0$，分母对充分大 $n$ 有固定正下界。利用

$$
\frac1{1+u}=1-u+\frac{u^2}{1+u},
$$

得到更精细的谱比值

$$
r_n=L[1-1/n+O(n^{-2})].
$$

这里的 $-L/n$ 是谱比值的修正项；路径数的相应系数仍需精度高于定理 8.1 中 $O(n^{-1})$ 的估计。最后

$$
H(\mathrm{Car}_n)/\mu_n=r_n+O(n^{-1})=L+O(n^{-1}),
$$

从而存在固定 $K_l$ 使 $P(n)\ge(L-K_l/n)\mu_n$。 $\square$

**推论 8.2a（近极值者的度数方差）。** 令 $\varepsilon_0=(L-1)/2$。存在绝对常数 $C,N$，使任意 $n\ge N$、$0\le\varepsilon\le\varepsilon_0$ 和满足 $H(T)/\mu_n\ge L-\varepsilon$ 的竞赛图都有

$$
\tau(T)\le C(\varepsilon+n^{-1}),\qquad
V_{\rm deg}(T)\le C(\varepsilon n^2+n).
$$

特别地，路径计数最大化者满足 $V_{\rm deg}(T)=O(n)$。

**证明。** 假设给出 $H(T)/\mu_n\ge(L+1)/2>1$，故第 7.2、7.3 节的两类图在统一大阶阈值后均被排除。由命题 7.3 和 6.6，

$$
L-\varepsilon-B_n\le(L+K_r/n)e^{-\tau/2+K_1/n}.
$$

增大阈值使 $0\le B_n\le1/n$ 且左端至少为 $(L+1)/4$，取对数并用 $\log(1+x)\le x$ 即得 $\tau\le C(\varepsilon+1/n)$。乘以 $(n-1)^2/4$ 得方差界。再增大阈值使 $K_\ell/n\le(L-1)/2$，对最大化者使用本节下界并取 $\varepsilon=K_\ell/n$。$\square$

该结论控制平均平方度差，并给出最大单点度差 $O(\sqrt n)$。正则性、圆环同构、编辑距离稳定性以及定理 8.1 所需的 $o(\sqrt n)$ 条件均需要进一步论证。

## 9. 原角函数的 Hessian

设 $A$ 为奇数阶 $d\ge3$ 正则竞赛图的邻接矩阵，记

$$
S=2A+I-J,\quad C=S/d,\quad P_0=J/d,\quad z=2/d.
$$

于是 $C^T=-C$ 且 $C\mathbf1=0$。定义

$$
B(y)=I-(A+\tfrac12I)\operatorname{diag}(y),\qquad K(y)=\det B(y).
$$

在 $z\mathbf1$ 附近，从 $K(y)=0$ 中解出 $y_d=h(y_1,\ldots,y_{d-1})$。取基点值为 $\log z$ 的局部对数支，定义角函数

$$
\widetilde f(\theta)=\log h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}}).
$$

**定理 9.2（原角 Hessian）.** 上述消元函数和对数支在基点附近解析。令 $E=(e_1-e_d,\ldots,e_{d-1}-e_d)$，则

$$
\mathbf H:=\nabla^2\widetilde f(0)=E^TQE\succ0,\qquad
Q=(I+C^2)(I-C^2)^{-1}.
$$

特别地，记 $\mathcal H=\det\mathbf H$，有

$$
\mathcal H=d\frac{\det(I+C^2)}{\det(I-C^2)},\qquad
\sqrt{d/\mathcal H}=\frac{\det(I+C)}{\det(I+iC)}=\rho_d(S)\in\mathbb Q_{>0}.
$$

**证明.** 令 $u=\mathbf1/\sqrt d$，取 $u^\perp$ 的标准正交基作为 $V$ 的列。$C$ 的每个非零频率 $\lambda$ 满足

$$
\lambda^2\le\tfrac12\|C\|_F^2=\frac{d-1}{2d}<\frac12.
$$

置 $P=(2A+I)/d=P_0+C$，引入 $y_j=ze^{t_j}$。在标准正交基 $(u,V)$ 下写成

$$
(u,V)^T[I-P\operatorname{diag}(e^t)](u,V)
=\begin{pmatrix}a&b\\c&D\end{pmatrix}.
$$

在零点 $a=b=c=0$，且 $D(0)=V^T(I-C)V$ 可逆。因此解析 Schur 补

$$
\psi(t)=a(t)-b(t)D(t)^{-1}c(t)
$$

与 $K(ze^t)$ 具有相同的局部零点集。置 $U=(I-C)^{-1}$。零点处的导数为

$$
a_j=-1/d,\quad a_{jk}=-\delta_{jk}/d,\quad
b_j=-e_j^TV/\sqrt d,\quad c_k=-V^TCe_k/\sqrt d.
$$

由于 $b=c=0$，$bD^{-1}c$ 的二阶导数仅余 $b_jD^{-1}c_k+b_kD^{-1}c_j$。利用 $VD(0)^{-1}V^TC=UC$，得到

$$
\psi_j(0)=-1/d,\qquad
\psi_{jk}(0)=-\frac{\delta_{jk}+(UC)_{jk}+(UC)_{kj}}d=-Q_{jk}/d,
$$

其中 $I+UC+(UC)^T=(I+C^2)(I-C^2)^{-1}$。又记 $q=\det(I-C)>0$，则

$$
K_{y_d}(z\mathbf1)=-q/(dz)=-q/2\ne0.
$$

解析隐函数定理给出 $h$，且 $h(z,\ldots,z)=z$。选取局部对数支并令

$$
g(t')=\log[h(ze^{t'})/z],\qquad \psi(t',g(t'))=0.
$$

隐式求导给出 $g_j(0)=-1$ 以及

$$
g_{jk}(0)=-(Q_{jk}-Q_{jd}-Q_{dk}+Q_{dd}).
$$

由 $\widetilde f(\theta)=\log z+g(i\theta)$，角变量的二阶导数带来 $i^2=-1$，故 $\mathbf H=-\nabla^2g(0)=E^TQE$。

在频率为 $\lambda$ 的斜对称块上，$Q$ 的作用为正数 $(1-\lambda^2)/(1+\lambda^2)$，且 $Qu=u$。于是 $Q\succ0$，进而 $E^TQE\succ0$。坐标矩阵 $E$ 的 Gram 矩阵为 $E^TE=I_{d-1}+J_{d-1}$，其行列式为 $d$，因此

$$
\det(E^TQE)=d\det_{u^\perp}Q=d\det Q.
$$

最后，$\det(I+C^2)=\det(I+iC)^2$，$\det(I-C^2)=\det(I+C)^2$。未平方的两个行列式均为正，分别由各块上的 $1-\lambda^2>0$ 和 $1+\lambda^2>0$ 得出。有理斜对称矩阵 $C$ 的奇数阶主子式为零，故 $\det(I+iC)$ 为有理数，结论得证。$\square$

上述计算确定了原角坐标下的完整 Hessian。Schur 补的展开计算和显式局部消元保留于《详细证明伴随稿》§9。

## 10. 模型极限与 carousel 常数

### 10.1 四种固定基图极限

固定奇数阶 $d\ge3$ 的正则基图。每个基点替换为独立均匀标号 $m$ 阶竞赛图，得到模型 $\mathcal T$；替换为独立均匀标号正则 $m$ 阶竞赛图，得到模型 $\mathcal R$，后者要求 $m$ 为奇数。块间边遵循基图。记 $N=dm$，分别用

$$
\nu_N=(N-1)!/2^N,\qquad \mu_N=N!/2^{N-1}
$$

归一化圈与路径的期望。

**推论 10.2.** 固定 $d$ 时，模型 $\mathcal T$ 的两个极限均为 $\rho_d(S)$，模型 $\mathcal R$ 的两个极限均为 $e^{1/d}\rho_d(S)$：

$$
\frac{\mathbb EC_{\mathcal T}}{\nu_N},\ 
\frac{\mathbb EH_{\mathcal T}}{\mu_N}\longrightarrow\rho_d(S),
\qquad
\frac{\mathbb EC_{\mathcal R}}{\nu_N},\ 
\frac{\mathbb EH_{\mathcal R}}{\mu_N}\longrightarrow e^{1/d}\rho_d(S).
$$

正则块极限沿奇数 $m$ 取值。

**证明.** Wormald 定理 4 在 $\mathcal H\ne0$ 时给出第一个圈极限 $\sqrt{d/\mathcal H}$，其条件及数值已由定理 9.2 确定。他的定理 5 将结论转为路径情形，定理 1 和定理 5 给出正则块因子 $e^{1/d}$。$\square$

作为对照，Divoux–Wang [12, Proposition 5.1] 可直接给出同一组常数。令 $W=(J_N-I_N+S\otimes J_m)/2$，$D=2W/(N-1)$，$B=D-J_N/N$。在常数方向、块常数零和子空间、各块内零和子空间上，$B$ 分别作用为

$$
0,\qquad B_0=\left.\frac{mS-I_d}{N-1}\right|_{\mathbf1_d^\perp},\qquad -I/(N-1).
$$

因此其算子范数保持小于一，计数公式中的行列式比满足

$$
R_N=\frac{\det(I-B)}{\sqrt{\det(I-B^TB)}}\longrightarrow e\rho_d(S).
$$

从 $D$ 缩放回 $W$ 贡献因子 $((N-1)/N)^N\to e^{-1}$。他们的辅助顶点构造给出 $\operatorname{path}(D)=(1+o(1))N^2\operatorname{cyc}(D)$，Wormald 的比较再为正则块补上 $e^{1/d}$。《详细证明伴随稿》§10.1 保留行列式各因子及辅助顶点的归一化计算。定理 9.2 进一步确定了原角函数本身的 Hessian。

### 10.2 闭式与单调性

**命题 10.3.** 对奇数 $d\ge3$，记 $r_d=\rho_d(\mathrm{Car}_d)$，$\mathfrak r_d=e^{1/d}r_d$，则

$$
r_d=\frac{(1+1/d)^d+(1-1/d)^d}
{(1+i/d)^d+(1-i/d)^d}.
$$

事实上，carousel 符号矩阵经带符号置换相似于传递竞赛图符号矩阵 $T_d$，且

$$
\det(I+tT_d)=\frac{(1+t)^d+(1-t)^d}{2}.
$$

代入 $t=1/d$ 和 $i/d$ 即得公式。这些行列式求值来自 [12, Section 7 and Lemma 9.1]；初等计算收于《详细证明伴随稿》附录 A.1–A.2。

**推论 10.5.** 沿奇数 $d\ge3$，数列 $\mathfrak r_d$ 严格递增并趋于 $L=\cosh1/\cos1$。

**证明.** $T_d/d$ 的正频率为 [11, Lemma 4.2]

$$
a_{j,d}=d^{-1}\cot\frac{(2j-1)\pi}{2d},\qquad 1\le j\le(d-1)/2.
$$

展开行列式比的对数，并用 $2\sum_j a_{j,d}^2=1-1/d$，得到

$$
\log\mathfrak r_d
=1+2\sum_{j=1}^{(d-1)/2}\sum_{r\ge1}\frac{a_{j,d}^{4r+2}}{2r+1}.
$$

固定 $j$，$a_{j,d}$ 随 $d$ 增大：令 $c_j=(2j-1)\pi/2$，$x=c_j/d$，则 $a_{j,d}=x\cot x/c_j$，而

$$
(x\cot x)'=\frac{\sin x\cos x-x}{\sin^2x}<0\quad(0<x<\pi/2).
$$

从 $d$ 增至 $d+2$ 时，原有频率全部增大，并增加一个正频率。上式为正系数收敛级数，故严格递增。闭式直接给出极限 $L$。$\square$

高阶展开为

$$
\mathfrak r_d=L\left[1+\frac{a_2}{d^2}+\frac{a_4}{d^4}-\frac1{3d^5}+O(d^{-6})\right],
$$

$$
a_2=\frac{\tanh1-\tan1}{3},\qquad
a_4=\frac{\tanh1+\tan1}{5}+\frac{2+\tan^21-\tanh^21}{18}+\frac{a_2^2}{2}.
$$

在 $x=1/d=0$ 处展开闭式即可得到此式；一致 Taylor 余项界保留于《详细证明伴随稿》§10.4。此处先在固定 $d$ 下取块极限，再令 $d\to\infty$。

## 11. 固定基图阶数下的唯一期望极值

现将 §10 的两个模型推广到固定奇数阶 $d\ge3$ 的所有竞赛图基图，归一化保持不变。

**推论 11.2.** 存在阈值 $M_d$，使每个 $m\ge M_d$ 时，carousel 基图都在四种期望计数（$\mathcal T$ 与 $\mathcal R$ 中的圈与路径）中唯一达到最大值，等号按普通竞赛图同构分类。在 $\mathcal R$ 中只取可容许的奇数 $m$。

该结论比较期望计数。阈值依赖 $d$，但对该阶所有基图及四种可容许比较共同有效。

### 11.1 非正则基图的归一化期望指数衰减

设基图出度为 $d_i$，定义

$$
b_i=d_i+\tfrac12,\quad a_i=2b_i/d=1+s_i/d,\quad
s_i=2d_i-(d-1),\quad \kappa=(\prod_i a_i)^{1/d}.
$$

这里 $0<a_i<2$，$\sum_i a_i=d$。利用 $(0,2)$ 上的界 $\log a\le a-1-(a-1)^2/8$，有

$$
\log\kappa\le-\frac{\sum_i s_i^2}{8d^3}.
$$

非正则时，零和偶整数 $s_i$ 的平方和至少为 $8$，因此 $\kappa<1$ 且 $\kappa^N\le e^{-N/d^3}$。

在模型 $\mathcal T$ 中，期望邻接矩阵 $W$ 的每个 $i$ 型行之行和为 $r_i=mb_i-1/2$。Hamilton 圈使用互异无序顶点对，内部边的独立性给出 $\mathbb EC_{\mathcal T}=C(W)\le\operatorname{per}W$。

对元素属于 $[0,1]$ 的矩阵，逐行线性优化可将永久式放大到行和向上取整的零一矩阵：先增加该行至目标整数行和，再在相应的超单纯形上最大化关于此行的线性永久式函数，其最大值可在零一顶点取得。逐行实施后，Brégman 不等式给出

$$
\operatorname{per}W\le\prod_{i=1}^d(R_i!)^{m/R_i},
\qquad R_i=\lceil mb_i-\tfrac12\rceil.
$$

固定 $d$ 时，$R_i=mb_i+O(1)$，且 $m\ge2$ 时 $R_i\ge m/4$。由 Stirling 界，

$$
\log\frac{\operatorname{per}W}{N!/2^N}
\le N\log\kappa+O_d(\log N).
$$

于是 $\mathbb EC_{\mathcal T}/\nu_N\le N^{O_d(1)}\kappa^N\to0$。在模型 $\mathcal R$ 中，每个样本的 $i$ 型行和恰为 $mb_i-1/2$；对样本邻接矩阵逐个应用 Brégman 不等式，再取期望，得到同一界。显式常数收于《详细证明伴随稿》§§11.4–11.5。

对于路径，加入一个新顶点，其与原顶点的边独立均匀定向。对每个 $N\ge2$ 阶竞赛图 $G$，有

$$
\mathbb E[C_{\rm aug}\mid G]=H(G)/4,\qquad 4\nu_{N+1}=\mu_N.
$$

闭合路径所需的两条新边互异，故概率恰为 $1/4$。$\mathcal T$ 的增广期望矩阵中，原有行和为 $mb_i$；$\mathcal R$ 的每个增广样本中，原有行和至多为 $mb_i+1/2$。统一选取 $R_i'=\lceil mb_i+1/2\rceil=mb_i+O(1)$，并为新行选目标行和 $N$，再次应用 Brégman 不等式。归一化后，原有行贡献 $N\log\kappa+O_d(\log N)$，新增一行仅改变多项式因子。因此

$$
\frac{\mathbb EH_{\mathcal T}}{\mu_N},\quad
\frac{\mathbb EH_{\mathcal R}}{\mu_N}
\le (N+1)^{O_d(1)}\kappa^N\longrightarrow0.
$$

增广界的显式归一化计算见《详细证明伴随稿》§11.6。上述出度界覆盖所有非正则基图。

### 11.2 严格比较与共同阈值

对于正则基图，推论 10.2 和 §6 的等号分类表明，carousel 的极限常数严格大于所有与其不同构的正则基图。正则类中的等号分类给出普通同构，正是吹胀模型所需的等价关系。非正则基图由 §11.1 得到零极限，carousel 极限 $r_d$ 和 $e^{1/d}r_d$ 则为正。

固定 $d$ 的基图数有限。对每个非 carousel 基图以及四种期望，极限的严格分离给出最终严格不等式。对这有限多个阈值取最大值即得 $M_d$；其中 $\mathcal R$ 沿奇数 $m$ 比较。最后，基图同构仅重新标记各块，保持内部块的独立同分布以及所有路径、圈计数。因此与 carousel 同构的基图恰好取得等号，推论 11.2 得证。$\square$

## 作者说明

本文合并两条独立发展的研究主线。路径框架及其 $L/C_*$ 界见固定版本存档 [14]；Wormald 项目与 [13,16] 的关系见引言。叶祥宇完成了早期路径界的配套 Lean 形式化，精确陈述见[早期仓库固定版本](https://github.com/LStar404/tournament-hamiltonian-paths/blob/a01680d39647bc4fa2f88d56b4e01a4b8dc98d48/formalization/VERIFICATION.md)。

仓库快照 [17] 记录了修订前稿件 30 个编号结果的 Lean 端点，包括尖锐路径界、原角 Hessian、路径卷积、谱比较及固定基图期望极值。[固定覆盖表](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/c678e9ee24fb304cad755a27c99f511c8640f75e/formal/COVERAGE.zh.md) 说明对象、假设、量词和覆盖边界；配套[复现说明](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/c678e9ee24fb304cad755a27c99f511c8640f75e/formal/README.zh.md) 给出工具链和审计步骤。

本次修订调整论证组织，并加入明确标出的推论。Lean 覆盖和源码哈希对应上述历史快照。固定工程的本轮复跑日志和范围说明随修订版提供；精炼稿的新端点映射仍待完成。AI 用于表述和部分证明检查。吹胀期望极值的阈值是固定奇数基阶数下的存在性结论，不包含可计算阈值或对增长基阶数的一致性。

## 参考文献


[1] John Irving and Mohamed Omar. Revisiting the Rédei-Berge Symmetric Functions via Matrix Algebra. The Electronic Journal of Combinatorics 32(4) (2025), Paper P4.43, 23 pp. [DOI: 10.37236/13841](https://doi.org/10.37236/13841).

[2] Noga Alon. The Maximum Number of Hamiltonian Paths in Tournaments. Combinatorica 10(4) (1990), 319–324. [DOI: 10.1007/BF02128667](https://doi.org/10.1007/BF02128667).

[3] Yanjun Han and Jonathan Niles-Weed. Approximate independence of permutation mixtures. The Annals of Statistics, to appear（[作者发表目录](https://yanjunhan2021.github.io/publication.html)）。[arXiv:2408.09341v2](https://arxiv.org/html/2408.09341v2)（2024年9月9日）；正文所引引理编号对应这一版本。

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
