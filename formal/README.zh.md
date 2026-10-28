# 竞赛图 Hamilton 计数：Lean 形式化

本目录包含 Wormald 原角函数 Hessian 主定理的 Lean 机器证明，以及路径增点计数、删集恒等式和有限族极限比较的形式化。全局 Hamilton 路径计数的定量渐近定理尚未形式化，具体覆盖范围见 `COVERAGE.zh.md`。

核对的论文快照与源文件哈希见 `SOURCE.json`。原论文的编号在该快照中固定；后续正文修订需要重新核对对应关系。

## 从哪里读

- `Tournament/HessianTheorem.lean`：完整 Hessian 主结论，入口是 `Tournament.wormald_original_angle_hessian`。
- `Tournament/HessianMain.lean`：原角函数与其实际二阶导数的定义，以及 Hessian 等于矩阵公式的证明。
- `Tournament/OriginalCoordinates.lean`：原论文的 `A+I/2`、`z=2/d` 与归一化计算之间的精确连接。
- `Tournament/Paths.lean`：真正的有限路径、圈与随机增点计数模型。
- `COVERAGE.zh.md`：原文编号、机器定理与未覆盖部分的对应表。

主定理只要求一个实际竞赛图及其正则性。局部函数存在、非退化、导数公式、正定性以及正有理平方根均由证明导出，没有把需要证明的 Hessian 公式当作假设。原角函数的 Hessian 先保留复数值，再证明它等于实矩阵的复化。

## 验证结果的含义

1. **无额外数学假设的形式化定理。** Lean 中写清对象、结构和适用范围，证明使用 Lean 与 mathlib 的既有基础。证明项不含 `sorry`，不增加未证明的公理。
2. **条件形式化定理。** 例如，已知一组函数具有指定极限且极限严格比较，可以推出共同的最终比较阈值。这只验证由假设到结论的推理，不能替代这些极限的证明。
3. **有限算例或普通审读。** 它们可以发现错误、核对翻译和边界，但不能代替一般性机器证明。数值结果不作为形式化定理的前提。

Lean 的 `Classical.choice`、`propext` 与 `Quot.sound` 是常见基础依赖；验收记录需要列明。`sorryAx`、临时增加的数学公理以及未经内核验证的计算结果均不作为合格证明。

## 与其余论文结果的关系

论文定理 1.1 的全局路径计数误差依赖统一永久式估计、对角缩放、删集求和、度差分类以及谱比较。若只验证删集中的有限求和恒等式，不能宣称该全局渐近定理已经形式化。

论文定理 9.2 的对象是原隐式角函数的 Hessian。本目录贯通了原局部函数、对数分支、二阶导数、矩阵表达式、正定性、行列式和正有理平方根；并非只对预先定义的矩阵检验正定性。

论文附录 A.6 的有限基图共同阈值原理可以在任意滤子上表达，因此能够同时处理所有块大小与仅取奇数块大小的情形。形式化该原理不会自动证明 Wormald 的计数极限或谱比较的等号分类。

## 开发约定

- 固定 Lean 与 mathlib 版本，不依赖浮动 `master`。
- 证明、编译结果、信任依赖与原文对应表一起验收。
- 所有未完成义务明确列出，不用 `axiom` 或 `sorry` 填补空白。
- 不改动论文的结论来迎合可证明的较弱命题；较弱命题单独命名和说明。
- 本目录的构建不需要用户密钥、模型 API、远程付费服务或任何论文以外的私人数据。

## 复现

固定 Lean 4.35.0；mathlib 固定提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`，其他依赖提交写在 `lake-manifest.json`。

已有匹配 Lean/Lake 的环境，在本目录运行：

```bash
lake exe cache get
bash scripts/verify.sh
```

Linux x86_64 可先运行 `bash scripts/setup-local-lean.sh`。它从 Lean 官方发布页下载固定版本，核对 SHA-256，仅安装到本目录的 `.toolchain`，并打印应在当前 shell 设置的环境变量。Windows/macOS 可使用官方 Lean 工具链管理器安装 `lean-toolchain` 中的版本，再运行相同 Lake 命令。

`verify.sh` 依次检查本地证明占位符、构建整个模块集合，并对 `theorems.json` 中的公开定理逐项执行 `#print axioms`。允许的基础依赖只有 `propext`、`Classical.choice`、`Quot.sound`。输出在 `.lake/verification`；任何编译错误、缺失定理或额外公理都会使脚本返回非零状态。

mathlib 使用官方已编译缓存，并固定其源代码版本。这不等于独立从源代码重建、审计所有上游基础库；编译器与依赖缓存属于复现时需要信任的软件供应链。

可选回归检查：安装 SymPy 后运行 `python3 scripts/check_hessian_examples.py`。它对几个指定正则图，从原隐式行列式直接计算有理二阶导数并与矩阵公式比较。这些有限例子用于检查实现，不参与 Lean 主定理证明。

仓库附带的 GitHub Actions 工作流只允许手动启动，不会因推送或拉取请求自动运行。
