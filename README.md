# 竞赛图 Hamilton 计数：论文、导读与复核记录

这份材料收录刘星辰、叶祥宇关于竞赛图 Hamilton 路径计数与 Wormald 随机吹胀模型的稿件。论文保留详细推导，另附面向初学者的中文导读、一页思路说明，以及本轮公式、来源和排版复核记录。

## 精炼修订版

本分支保留主分支作为基线，供审查此次论文修订。

- [中文主文](manuscripts/01_combined.zh.pdf)：37页。
- [英文主文](manuscripts/02_combined.en.pdf)：41页。
- [中文详细证明伴随稿](manuscripts/07_detailed_proof.zh.pdf)：精炼前94页详细论证，保留原编号；作者说明同步本轮运行状态。
- [英文详细证明伴随稿](manuscripts/08_detailed_proof.en.pdf)：精炼前98页详细论证，保留原编号；作者说明同步本轮运行状态。

每份文稿另有同名 `.md` 与 `.tex` 源文件。主文重写了永久式、局部缩放和模型论证，长技术估计按明确位置引用详细伴随稿；压缩指主文阅读篇幅，不声称合计页数同步下降。专题稿和旧导读保留其原版本。

三轮自审逐轮发现、实际修改及核验记录见 `review/compact-20261107/self-review/`。本轮改写、独立审查、版式和编译记录见 `review/compact-20261107/`。Lean固定工程的本轮执行日志、结果及与新稿的范围区别见 `review/lean-rerun-20261107/` 和 `review/compact-20261107/lean_scope.md`。新增陈述没有自动获得历史端点认证。

## 结果与已有工作的关系

第一作者的早期路径稿于 2026 年 10 月 8 日公开存档，已给出 $L/C_*$ 常数界及正路径卷积、统一永久式估计、非主子阵缩放和异常点处理框架。该具体首版作者为 Xingchen Liu，版本 DOI 为 [10.5281/zenodo.23233166](https://doi.org/10.5281/zenodo.23233166)。它没有确定两侧共同尖锐常数，也不含 Wormald 原角 Hessian。

当前合稿将上述计数框架与 Fang–Huang 谱比较结合，得到对所有阶数统一的 $O(n^{-1})$ 误差。Divoux–Wang 已确定圈和路径的尖锐首项常数。完整原角 Hessian 等结果与 Bhattacharjee 独立取得；正文准确记录重合及固定版本，不用早期路径存档为 Hessian 主张先后。严格单调性、等号分类、非正则基衰减和固定阶期望唯一性分别说明其依赖。

## 目录

- `manuscripts/`：各套 PDF、TeX 和 Markdown。
- `manuscripts/figures/`：六幅图的 PDF、SVG、PNG，以及记录边方向的 `graph_figure_data.json`。
- `guide_parts/`：导读的分节源文件。
- `review/`：研究定位、数学审阅、来源核对、公式保留及排版记录。
- `tools/`：本仓库的 TeX 编译脚本和图形生成源码。
- `fonts/`：中文排版使用的随附字体及相应许可说明。

第三方论文全文不在材料中；参考文献及其链接列在正文末尾。复核记录说明检查过什么、采用了哪些有限检验，也保留检查范围的限制。它们不能替代一般证明或完整的形式化验证。历史记录中的稿件编号和哈希对应各自快照，阅读前请先看 [review/README.md](review/README.md)。

## 编译 TeX

使用 Python 3.9 或更新版本，以及已安装的 XeLaTeX 或 Tectonic。脚本只调用系统 `PATH` 中的编译器，不下载编译器、宏包或字体。若使用 Tectonic，其需要的资源须已在本机缓存中；脚本启用 `--only-cached`，缺少缓存时会报告失败。

在仓库根目录运行：

```text
python tools/compile_tex.py --check
python tools/compile_tex.py
python tools/compile_tex.py --engine xelatex 01_combined.zh
```

默认编译 `manuscripts/` 中全部 TeX。XeLaTeX 运行两遍，以处理交叉引用；Tectonic 使用自身的重跑机制。新 PDF 与日志写入 `build/pdf/`，保留 `manuscripts/` 中已经审阅的 PDF。任何一份失败都会使脚本返回非零状态，并给出对应日志位置。

脚本始终从 `manuscripts/` 目录启动编译，所以正文中的 `figures/...` 和导言中的 `../fonts/...` 均按相对路径查找。直接调用编译器时也请先进入这个目录。宏包依赖以各 TeX 导言为准，包括 `fontspec`、AMS 数学宏包、`geometry`、`graphicx`、`booktabs`、`longtable`、`enumitem`、`needspace`、`hyperref`、`bookmark`、`fancyhdr` 等；中文字体设置另涉及 `xeCJK`。缺失字体或宏包时，应先按编译器日志补齐本机环境。

中文稿通过 `xeCJK` 和相对路径 `../fonts/` 读取 `NotoSerifSC-Regular.ttf`（字重 400，正文）与 `NotoSansSC-SemiBold.ttf`（字重 600，标题及粗体），无需另行安装这两种中文字体。它们由官方变量字体固定字重生成，相应许可分别见 `fonts/OFL-NotoSerifSC.txt`、`fonts/OFL-NotoSansSC.txt`。拉丁文字仍使用系统中的 Times New Roman、Arial、Consolas；数学使用 TeX 字体，扩展拉丁字符使用 `lmroman10-regular.otf`。这些字体依赖以各 TeX 导言为准。替换字体会改变行宽、分页和公式附近留白，应重新检查输出。

这里提供的是直接编译 TeX 的脚本。它不承担 Markdown 到 TeX 的转换，也没有收录原工作区依赖本机环境的 `build.py`。修改 Markdown 后，需要同步修改或重新转换 TeX，再进行编译与排版检查。

## 重新生成图

`tools/create_graph_figures.py` 需要 NumPy 和 Matplotlib。依赖已安装后运行：

```text
python tools/create_graph_figures.py
```

该脚本根据明确的顶点、边及切换排列生成四幅图，覆盖 `manuscripts/figures/` 内对应的 PDF、SVG、PNG 和图数据 JSON。TeX 引用 PDF，Markdown 引用 PNG，SVG 用于继续编辑。图中文字使用 DejaVu Serif。不同 Matplotlib 或字体版本可能改变文字位置，重新生成后应核对图形及正文分页。

导读新增的三顶点图与 Hessian 二次型图由 `python tools/create_guide_figures.py` 生成。这个脚本需要 NumPy 和 Matplotlib，仅重绘这两幅图；导读其余三幅图与论文共用。

## Lean 形式化验证

原固定快照对[覆盖表](formal/COVERAGE.zh.md)所列的 30 个编号结果提供与修订前原文对象、前提和量词对应的 Lean 端点，涵盖全局锐常数量化渐近、实际原角 Hessian、精确路径卷积、谱比较及等号分类，以及四种吹胀计数期望的极限和极值。吹胀期望的最终极值比较覆盖每个固定奇数阶 $d\ge3$ 的全部基图，不限于正则基图。

本轮已对固定 Lean 工程完成 fresh 构建及审计：609个生产模块、3067个登记端点和223个关键端点类型检查通过，318条命令均退出0；实际日志见 `review/lean-rerun-20261107/`。新加的引理5.1a、命题6.6、命题7.3、推论8.2a及改写后的编号仍待建立新的形式化对应。原有范围不是全文逐句认证，也不表示全部替代证明或完整的 SVD、矩形矩阵核范数背景均已形式化。仅对吹胀期望极值而言，阈值是固定基图阶 $d$ 下的存在性结论；不宣称给出可计算或最小数值阈值，或对增长 $d$ 的一致结论。上述固定基图阶的限定只涉及吹胀期望极值；全局锐常数主定理按其自身量词陈述。期望结果也不等于样本级或几乎必然结果。

各编号结果的精确对应、完整类型和核验版本见[覆盖表](formal/COVERAGE.zh.md)；工具链、构建及递归公理审计步骤见[复现说明](formal/README.zh.md#复现)。旧 Hessian 核验及[卷积迁移记录](formal/CONVOLUTION_MIGRATION.zh.md)仍只描述各自版本，历史记录和来源哈希不改写。

GitHub Actions 检查为手动触发，不会因推送或拉取请求自动运行。


