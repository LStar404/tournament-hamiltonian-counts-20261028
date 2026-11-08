> **2026-11-07运行更新：** 固定工程fresh构建与审计已实际通过，完整日志见[本轮报告](../review/lean-rerun-20261107/README.zh.md)。精炼稿新增结论及旧编号差异见[范围说明](../review/compact-20261107/lean_scope.md)。下列既有发布记录对应其原快照；文档状态校正不改变Lean证明源码。

# Lean 形式化验证与复现

> 固定版本：609 个生产模块、3067 个登记端点，及覆盖表中 30 个编号数学结论。生产源已在隔离目录从零本项目编译产物开始构建；固定上游缓存复用。登记数不是论文定理数，也不是所有辅助声明的数量。精确运行时间、命令退出码、关键类型与公理记录见 [实验结果](verification/release/RESULTS.json)。

## 范围

本工程以真实竞赛图、Hamilton 路径/圈计数、原始矩阵和归一化为对象。具体编号与 Lean 完整名称、前提及量词对应以最终 `COVERAGE.zh.md` 为准；不要仅凭相似定理名推断覆盖。谱 signed-permutation 等号分类和正则奇阶普通圆环同构分类不同；谱等同不推出 Hamilton 计数不变。

“四种计数期望”指两种块内抽样方式（uniform / regular）×路径/圈两种计数。计数期望不是样本级或几乎必然结论。吹胀期望的最终极值比较使用固定奇数基图阶；不宣称给出数值最小阈值或对增长基图阶的一致性。全局锐常数主定理按其自身量词陈述，不受这一吹胀限定替代。这也不是全文逐句、所有替代证明或全部外部文献背景的形式化。

## 复现

固定配置是 `lean-toolchain`、`lakefile.toml` 和 `lake-manifest.json`：Lean 4.35.0，mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`，其余依赖按 manifest 中的 **rev**，不以 `inputRev` 的标签代替锁定 revision。

在可用的固定官方工具链与依赖缓存环境内，从本目录运行：

```bash
python3 scripts/check_release_manifest.py
python3 scripts/verify_release.py
```

从没有本项目编译产物的新目录进行 production fresh 验证：

```bash
python3 scripts/verify_release.py --fresh --width 2
```

`--fresh` 拒绝已有 `.lake/build`，不会自行删除文件。它先以最多两个拓扑就绪项目目标从源编译全部生产模块，再运行无目标参数的默认 `lake build`；随后源扫描、全部登记端点递归公理审计、关键完整类型及真实定义打印。日志明确区分从零项目编译与后续 aggregate root 检查。固定 mathlib/其他上游缓存可以复用，**这不等于冷重建全部上游库**。

所有新运行结果写入 `.lake/verification/release-runs/`，不会改生产源。`verification/release/` 保存发布时固定输入和结果，新的运行不会覆盖它。源扫描是辅助检查，不能代替 Lean 内核和递归公理审计。允许的基础公理仅为 `propext`、`Classical.choice`、`Quot.sound`。

若只有最小核心环境，也可运行原来的 `bash scripts/verify.sh`；它执行源扫描、默认构建和全登记公理检查，但不代替发布 manifest 与关键类型门。依赖准备时应保持 manifest 锁定，不运行会浮动版本的更新流程。

## 历史与来源

此候选是以 main `cd8a0e1cf99165263167865c1201fc8b2c94cc01` 为基准的文件白名单增量，不替换未列出的既存文稿、来源记录或历史失败证据。历史 Hessian / 卷积来源和核验说明继续描述各自版本，不改写其哈希或历史结论。当前发布结果另行保存；旧日志中的宿主路径不复制进新的实验记录。

保留 `TournamentHamiltonian/LICENSE` 中的来源许可。机器认证支持的是明确的数学陈述，不改变文稿中的学术来源、作者信用及辅助工具披露。

## 构建诊断的解释

“production fresh”指起始没有本项目 `.olean` / `.ilean`，不表示没有旧 linter 警告。原有 deprecated import、unused tactic 等警告如实记录，不为消除警告修改冻结证明。默认根汇总检查与从零项目模块编译分开记时；允许复用的仅为锁定上游依赖缓存。

原核心公理脚本及其 JSON 中的历史字段名 `theorem_count` 按 `theorems.json` 的登记声明计数；本说明统一称登记端点，不将定义或辅助声明冒称论文定理。

