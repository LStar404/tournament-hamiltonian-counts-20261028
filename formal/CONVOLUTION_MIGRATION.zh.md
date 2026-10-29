# 精确有限 Hamilton 路径卷积迁移

目标基准：`LStar404/tournament-hamiltonian-counts-20261028@20fc92ae3a64d559d2aeaf6c5d30856dd5c438d8`。
旧证明：`LStar404/tournament-hamiltonian-paths@a01680d39647bc4fa2f88d56b4e01a4b8dc98d48`。

## 数学端点

`TournamentPaths.pathCount_eq_positive_convolution` 对真实 `Tournament (Fin (n+1))` 证明

$$H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}(A[U^c]).$$

它只接受 `T`，不要求正则性、阶数为奇数、永久式估计或任何额外数学前提。
`pathCountFinite_eq_pathConvolutionSum` 使用独立定义的真实排列路径计数，适用于所有 `Fin n`，包括 `n=0`。
`pathCountFinite_eq_pathCount` 证明非空情形与现有 `pathCount` 的自然数值严格相同。
`empty_path_count`、`empty_path_convolution` 和 `singleton_path_convolution` 明列零阶和单点值均为 1。
原增点 `H/4` 恒等式仍要求至少两个旧顶点；这与精确卷积在零阶、单点成立并不矛盾。

## 复用与桥接

从旧端点 `TournamentHamiltonian.pathCount_eq_pathConvolutionSum` 取八文件完整本地 import 闭包：
`Packing`、`Definitions`、`PositiveDeterminant`、`Hadamard`、`Orientation`、
`PathConvolution`、`PathConvolutionCoefficients`、`PathConvolutionGenerating`。
没有重写循环消去证明，也未导入旧工程的永久式渐近或全局主界证明。

新桥接逐项证明：

1. `toLegacy` 保留 Boolean 边函数和两个竞赛图结构条件。
2. 独立的全阶数相邻位置谓词与旧 `IsHamiltonian` 相同；借旧 `isHamiltonian_iff_consecutive` 与新 `IsHamiltonPath` 等价。
3. 在自然数中将旧 `filter.card` 与排列指标和相等，再将计数转换到实数；不把卷积定义成路径计数。
4. 两个邻接矩阵逐项相同，`pathPrincipalMatrix` 就是 `I+A[U]`，补集主子矩阵和永久式使用同一有限索引类型；全 `Finset` 求和保持一致。

旧工具链为 Lean 4.34.1，新工程仍使用原锁定的 Lean 4.35.0 和 mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`，没有更换目标依赖版本。
旧八文件只增加 `module`、公开导入及 `@[expose] public section`；去掉这些可见性标记后，定理陈述和证明正文与旧 checkout 逐字相同。
目标 `Paths.lean` 仅给 `IsHamiltonPath`、`pathCount` 加 `@[expose]`，以便跨模块证明定义等价，正文不变。
来源许可为 CC BY 4.0；作者、依赖图、原 Git blob 哈希和本地移植文件哈希见 `CONVOLUTION_SOURCE.json`，完整许可见 `TournamentHamiltonian/LICENSE`。

## 实际验证与复现

本轮 `lake build Tournament.PathConvolution` 已成功（3332 jobs）。
独立 `#print axioms` 审计的 14 个桥接/边界/复用端点只使用
`propext`、`Classical.choice`、`Quot.sound`；`#check` 确认主端点没有额外数学前提。
`verification/convolution/` 保存原运行的构建、14 端点专项审计、`theorems.json` 中 258 个登记定理的传递公理审计、回归结果及源码哈希。
258 是明确登记的定理端点数，不是所有迁入模块公开声明的完整枚举；对登记端点执行的 `#print axioms` 仍检查其实际证明的传递依赖。
这 258 项登记审计通过，只出现 `propext`、`Classical.choice`、`Quot.sound`；构建和审计成功状态指原本地物化源码运行，不是本次元数据校正新跑的结果。

在 `formal/` 中运行：

```text
lake exe cache get
python scripts/check_sources.py
lake build
python scripts/audit_axioms.py
python scripts/check_convolution_examples.py
```

Windows 本轮使用工作目录内的 `ELAN_HOME` 与 `MATHLIB_CACHE_DIR`，并设置
`PYTHONUTF8=1`、`PYTHONIOENCODING=utf-8`。官方 Lean 版本输出为 4.35.0，编译器提交
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。
上游 mathlib 使用官方匹配缓存，未声称独立从源码重建全部上游库。

两次中间失败均来自模块可见性：旧文件不是 `module`；现有两个定义正文未暴露。
对应日志另存，均通过格式/可见性调整解决，没有加入 `sorry`、`admit` 或新数学公理。

标准库 Python 枚举对 0 至 5 阶全部 1100 个标号竞赛图通过；这是独立精确整数回归，不替代 Lean 的全阶数证明。

## 历史运行字节与 Git 规范字节

`verification/convolution/source_hashes.json` 保留原运行记录的全部 38 个哈希，原值和文件字节均未由本次校正改写；旧构建、公理与回归日志也不改写。
新增 `verification/convolution/source_hashes.provenance.json` 分别列出 `local_materialized_sha256` 与 `canonical_git_sha256`，后者固定到合并后的 Git 快照 `5d528bc2b962ea3d2ada921fbcae0ddf49afe481`。
38 个规范源文件的 Git blob 标识均已核对：16 项两组哈希直接相同，另 22 项满足“规范 Git 文件字节末尾再附加一个 LF 字节”后的 SHA-256 等于原记录。
这是可逐项复算的哈希映射；本次没有重新读取原工作站构建时的文件，不把映射解释为重新观察了历史运行，也不以规范哈希替换历史运行哈希。
完整方法和复核命令见 `verification/convolution/SOURCE_HASHES.zh.md`。

**本次仅修正文档与证据元数据，不改 Lean 证明正文，不重新运行构建或公理审计；尚未针对上述 canonical Git 字节快照新跑 Lean 编译。**
不能把补充的规范 Git 哈希当作一次新的、逐字节相同的已完成构建。原运行的构建结果与标准基础公理结果保持其原有证据范围。

## 覆盖限制

本次精确有限卷积没有剩余数学证明义务。统一永久式渐近、缩放/删集误差、谱极值与现稿定理 1.1 的锐常数量化渐近仍未由本次迁移认证。
旧路径工程另有上界首项常数 `C_*>L` 的无条件主界；不能将其与现稿锐上界混同，也不能抹去其已有成果。
稿件四项来源/边界修订另作独立提交；本机无 TeX 编译器，尚未重建外发 PDF。
