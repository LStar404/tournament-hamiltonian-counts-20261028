# 论文—Lean 证明对应与覆盖边界

本目录形式化了**原角函数的 Hessian 公式、正定性、行列式及正有理平方根结论**，并验证若干有限组合与代数引理。
**这不等于整篇论文已经形式化：全局 Hamilton 路径渐近定理及其永久式分析尚未覆盖。**

论文基准提交为 `d3ae4d7692c23985c1aba21f5846a49b13721b92`；文本快照与哈希见 [`SOURCE.json`](SOURCE.json)。
下表的“条件”是 Lean 陈述中的实质性输入，不能将这些输入本身误称为已经证明的论文结论。

## 已形式化的结果

| 论文位置／结果 | 导出的 Lean 端点 | 精确覆盖与条件 |
|---|---|---|
| §5.1：精确有限 Hamilton 路径卷积 | `TournamentPaths.pathCount_eq_positive_convolution`；`pathCountFinite_eq_pathConvolutionSum` | 对真实 Boolean 竞赛图及真实排列路径计数证明 `H(T)=∑_U det(I+A[U]) per(A[Uᶜ])`，无正则性或额外数学假设。复用旧工程的循环消去证明，并证明竞赛图类型、路径谓词、计数、邻接矩阵及主子矩阵的桥接。`pathCountFinite` 对 `Fin n` 的所有阶数成立；在 `Fin (n+1)` 上与原 `pathCount` 严格相等。零阶和单顶点路径数及卷积均为 1，边界端点已检查。此项不包含永久式渐近或现稿定理 1.1 的全局定量结论。来源和本轮证据见 `CONVOLUTION_SOURCE.json`、`CONVOLUTION_MIGRATION.zh.md`。 |
| 合并稿定理 1.2、9.2；`04_wormald.zh.md` 定理 3.2：原角函数 Hessian | `Tournament.wormald_original_angle_hessian` | 对实际 `Fin (n+1)` 竞赛图，唯一额外假设是**各点出度正则**。证明实际角函数的两次实 Fréchet 导数等于 `Eᵀ(I+C²)(I−C²)⁻¹E` 的复数嵌入，给出实正定矩阵、严格正的行列式、精确行列式商，以及等于正平方根的正有理数。论文的奇数 `d≥3` 范围全部包含。**没有把 Hessian 定义成目标矩阵，也没有将目标二阶导数公式当作前提。** |
| §9.5–9.6：原分支存在、唯一性与局部解析性 | `Tournament.OriginalCoordinates.regular_original_branch_analytic`；`regular_original_branch_local_unique`；`regular_original_rawLog_analytic`；`regular_original_rawLog_exp_analytic` | 对实际非空正则竞赛图，从图结构证明原基点行列式为零、选定坐标系数非零；原消元分支在基点局部解析且唯一，其未经归一化的对数和指数坐标下的对数也局部解析。没有将隐式函数的非退化条件留作额外假设。 |
| 同上：实际函数与矩阵表达式的等同性 | `Tournament.HessianMain.angleHessian_eq_compressedResolvent`；`original_angle_second` | `originalAngle` 使用原行列式 `det(I−(A+I/2)diag y)` 的显式消元分支，在 `y_j=(2/d)exp(iθ_j)` 上取对数；只有 `d−1` 个实角变量。保留导数完整的复数值，再证明其为实矩阵，未预先取实部。 |
| §9.4–9.6：导数、消元与坐标桥接 | `Tournament.ScalarTwoJet.iterated_fderiv_phi_zero_real_skew`；`Tournament.OriginalCoordinates.original_branch_expCoordinates`；`Tournament.HessianMain.originalAngle_eventually_eq` | 从真实逆矩阵函数计算标量约束的两阶导数；证明原矩阵/基点与归一化矩阵/基点的精确缩放；最终建立**邻域上的对数函数相等**，而不只是指数相等或模 `2πi` 相等。泛型中间引理的解析性、逆、两阶导数假设均在主端点中得到具体实例化。 |
| §2.2、9.2：符号矩阵与正则性 | `TournamentPaths.signMatrix_row_sum`；`regular_normalizedSign_mulVec_one`；`tournament_normalizedSign_frobeniusSq` | 从实际 Boolean 边方向构造邻接矩阵与 `S=A−Aᵀ`，证明度差公式、正则时零行和及 `‖S/d‖F²=(d−1)/d`。足以证明正定性的 Frobenius 界已覆盖；不另宣称证明原文更强的成对谱界。 |
| §9.7：候选矩阵的代数与正有理比值 | `TournamentPaths.regular_tournament_algebraicHessian_det`；`regular_tournament_positive_rational_sqrt` | 针对实际正则竞赛图证明维数因子 `d`、行列式比值、有理性和正号。正平方根由正性选定，不是仅靠平方相等。它们经上面的实际导数等式接入完整 Hessian 端点。 |
| §11.6 引理 11.5：随机增点的 `H/4` 恒等式 | `TournamentPaths.augmentation_count_identity`；`augmentation_average` | 旧图有 **至少两个顶点**，所有新增边方向遍历等权 Boolean 函数空间。路径是所有旧顶点的排列；圈以唯一新增顶点为规范起点。证明精确整数计数式与有理数有限平均式，没有多计循环起点。 |
| §4.3 式 (4.1)：删集质量及边际 | `Tournament.deletion_mass`；`deletion_row_marginal`；`deletion_column_marginal` | 独立行删集、列删集；质量式要求总质量为 `n`、两删集大小均为 `t`，并明确要求 `n≠0`、`n−t≠0`。这是精确有限和恒等式，不是永久式误差估计。 |
| §4.4：度差因子的精确恢复 | `Tournament.score_factor_restoration` | `1+a_i` 与 `1−a_i` 均非零时，证明保留行列因子与全乘积、删除因子逆元之间的等式。未由此推出缩放或永久式上界。 |
| §7.4：平方根误差吸收 | `Tournament.sqrt_error_absorption`；`total_error_absorption` | 在 `τ≥0`、`n>0` 下证明 `K√(τ/n)≤τ/4+K²/n`。后一结果另假设非平方根误差满足指定上界；该前提在对数窗口上的统一证明尚未覆盖。 |
| 附录 A.6：有限族极限比较 | `Tournament.finite_eventual_unique_max` | **条件定理**：给定有限比较族、各函数极限以及严格极限差，推出共同的最终严格比较。没有因此证明竞赛图模型的极限、严格谱差、同构等号类或四种模型/计数的共同数值阈值。 |

## 两个容易混淆的边界

1. **增点公式的最小阶数。** 单个旧顶点有一条空边路径，却不能产生有向二圈；文件中的 `one_vertex_average_not_quarter` 明确验证该反例。原引理独立引用时应注明 `N≥2`。论文固定 `d≥3` 的吹胀应用不受影响。这里的“期望”采用有限等权平均；没有另建测度论条件期望或证明 `μ_N,ν_{N+1}` 的概率归一化桥接。
2. **一般滤子不是已获得的整数阈值。** 有限族比较引理允许任意滤子和空比较集；实际极值应用仍须实例化为正确的非圆环同构类、自然数或无限奇数子序列，并提供相应计数极限及严格差。泛型引理本身不替代这些主要数学输入。

## 尚未形式化的论文内容

- 全图最大 Hamilton 路径数的统一渐近界、`O(n⁻¹)` 误差、圆环下界与上下界常数比较。
- 统一永久式估计、Sinkhorn/对角缩放、删集的解析误差与尾项、度差分类及其合并。
- 谱比较及等号同构分类、Wormald 的计数渐近定理、四个随机吹胀模型/计数极限，以及由它们得到的唯一期望极值。
- 文中其余未在上表明确列出的命题。不能从单个辅助恒等式通过检查推断这些内容也已通过检查。

## 证据类型与信任边界

Lean 使用固定工具链和精确依赖版本；最终构建与公理审计应针对相同源码运行。
标准基础依赖 `propext`、`Classical.choice`、`Quot.sound` 如被使用，会在公理审计中列明；
`sorryAx`、新增未证明数学公理及未经内核验证的计算均不被接受。
官方 mathlib 编译缓存属于依赖供应链信任，不代表独立重建了全部上游库。

SymPy 的小阶精确有理数检查是**回归测试**，不是一般定理的证明，也不是任何上述 Lean 主定理的假设。

