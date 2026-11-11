# 竞赛图 Hamilton 计数：论文、导读与复核记录

这份材料收录刘星辰、叶祥宇关于竞赛图 Hamilton 路径计数与 Wormald 随机吹胀模型的稿件。论文保留详细推导，另附面向初学者的中文导读、一页思路说明，以及本轮公式、来源和排版复核记录。

## 2026年11月11日 Gemini 意见核对修订

本轮明确全局路径界与固定基图吹胀极限的不同范围，补充 Hessian 的广义谱与正下界、历史界比较表，并在导言说明连续分析的 Lean 覆盖边界。具体采纳与未采纳意见见[本轮复核记录](review/gemini-20261111/README.md)，准确声明与源码锚点见[英文形式化证据索引](review/gemini-20261111/formal_anchors.en.md)。

上一轮最终编辑仅在中英文主文的作者声明中增加固定版本的英文覆盖摘要直链，并压缩摘要中的永久式定位措辞。数学内容、必要技术附录和历史形式化记录不变；源稿、生成 TeX 与 PDF 同步检查，见[最终编辑记录](review/final-editorial-20261111/README.md)。

第二轮修订补全摘要中 $0\le\varepsilon\le(L-1)/2$ 的适用范围及 $L,\mu_n$ 的定义，增加偶数阶精确极值图度方差为 $\Theta(n)$ 的观察，以及相对于实际最大值的稳定性推论 8.4。必要技术附录已统一记号与引用，并新增[英文形式化覆盖摘要](review/revision-20261111-round2/lean_coverage.en.md)。

本轮把全局 $O(n^{-1})$ 路径计数和度方差稳定性作为论文主线。永久式定理明确定位为有独立定量证明的分析工具，不主张首次得到 $O(n^{-1})$ 永久式近似，也不把有符号输入或类一致性本身当作创新区别。

唯一的英文投稿组合为（英文为研究投稿主版本，中文为同步对照）：

- [英文正文](manuscripts/02_combined.en.pdf)，主题为定量路径计数与度稳定性。
- [英文必要技术附录](manuscripts/09_technical_appendix.en.pdf)，收录永久式、非主子阵缩放与恢复、必要谱等号辅助证明。

[中文正文](manuscripts/01_combined.zh.pdf)和[中文技术附录](manuscripts/10_technical_appendix.zh.pdf)是同一组合的中文对照。每份均有同名 Markdown 和 TeX 源文件。技术附录保留原章节及公式编号以便核查。

可用 `python tools/package_submission.py` 生成仅含两份英文 PDF 的[审阅包](submission/README.md)，并以 `--check` 检查其清单和哈希。包内不包含中文稿、初学者导读或历史审计记录；这不改变它们在本仓库中的保留位置，也不代表已经向期刊提交。

原[英文详细证明伴随稿](manuscripts/08_detailed_proof.en.pdf)和[中文详细证明伴随稿](manuscripts/07_detailed_proof.zh.pdf)、专题稿及导读保留为独立展开阅读材料，不与新正文并列作为投稿版本。主要结论所需的长证明已收入技术附录；旧稿的额外初等计算和高阶展开属于可选阅读。

第二轮修改和实际检查见 [review/revision-20261111-round2/](review/revision-20261111-round2/README.md)，上一轮记录保留在 [review/revision-20261111/](review/revision-20261111/README.md)。[英文覆盖摘要](review/revision-20261111-round2/lean_coverage.en.md)补充本次新增陈述；[详细对应表](review/revision-20261111/lean_correspondence.md)继续区分旧端点已覆盖的结论、新书面证明链及无新增端点的结果。本轮未改变 Lean 生产源码，也不把历史构建记录写作本次重新编译。

历史精炼、来源和形式化复跑记录继续保留，版本边界见 [review/README.md](review/README.md)。

## 结果与已有工作的关系

第一作者的早期路径稿于 2026 年 10 月 8 日公开存档，已给出 $L/C_*$ 常数界及正路径卷积、统一永久式估计、非主子阵缩放和异常点处理框架。该具体首版作者为 Xingchen Liu，版本 DOI 为 [10.5281/zenodo.23233166](https://doi.org/10.5281/zenodo.23233166)。它没有确定两侧共同尖锐常数，也不含 Wormald 原角 Hessian。

当前合稿将上述计数框架与 Fang–Huang 谱比较结合，得到对所有阶数统一的 $O(n^{-1})$ 误差，并推出近极值图的度方差界 $V_{\rm deg}=O(\varepsilon n^2+n)$，特别是精确极值图 $V_{\rm deg}=O(n)$。Divoux–Wang 已确定圈和路径的尖锐首项常数。完整原角 Hessian 等结果与 Bhattacharjee 独立取得；正文准确记录重合及固定版本，不用早期路径存档为 Hessian 主张先后。严格单调性、等号分类、非正则基衰减和固定阶期望唯一性分别说明其依赖。

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

`python tools/render_compact_main.py` 根据主文 Markdown 重建两个主文的 TeX 正文，并保留各自导言。`python tools/build_technical_appendix.py` 从冻结的详细稿按明确记录的记号、引用及文献表述变换，生成两个必要技术附录；它校验原始段落和变换后段落的哈希，不修改历史原稿。修改后应先运行相应转换，再编译并检查 PDF。编译器缺少原字体时，可用 `python tools/compile_portable_pdfs.py --documents 01_combined.zh 02_combined.en 09_technical_appendix.en 10_technical_appendix.zh` 在独立目录以已安装的替代字体构建；字体变化会影响分页。

## 重新生成图

`tools/create_graph_figures.py` 需要 NumPy 和 Matplotlib。依赖已安装后运行：

```text
python tools/create_graph_figures.py
```

该脚本根据明确的顶点、边及切换排列生成四幅图，覆盖 `manuscripts/figures/` 内对应的 PDF、SVG、PNG 和图数据 JSON。TeX 引用 PDF，Markdown 引用 PNG，SVG 用于继续编辑。图中文字使用 DejaVu Serif。不同 Matplotlib 或字体版本可能改变文字位置，重新生成后应核对图形及正文分页。

导读新增的三顶点图与 Hessian 二次型图由 `python tools/create_guide_figures.py` 生成。这个脚本需要 NumPy 和 Matplotlib，仅重绘这两幅图；导读其余三幅图与论文共用。

## Lean 形式化验证

原固定快照对[覆盖表](formal/COVERAGE.zh.md)所列的 30 个编号结果提供与修订前原文对象、前提和量词对应的 Lean 端点，涵盖全局锐常数量化渐近、实际原角 Hessian、精确路径卷积、谱比较及等号分类，以及四种吹胀计数期望的极限和极值。吹胀期望的最终极值比较覆盖每个固定奇数阶 $d\ge3$ 的全部基图，不限于正则基图。

2026年11月7日的历史复跑对固定 Lean 工程完成 fresh 构建及审计：609个生产模块、3067个登记端点和223个关键端点类型检查通过，318条命令均退出0；实际日志见 `review/lean-rerun-20261107/`。当前引理5.2（原5.1a）、命题6.6、命题7.3、定理1.2／推论8.3（原8.2a）没有新增组合端点；具体差别和现有结论覆盖见本轮对应表。原有范围不是全文逐句认证，也不表示全部替代证明或完整的 SVD、矩形矩阵核范数背景均已形式化。仅对吹胀期望极值而言，阈值是固定基图阶 $d$ 下的存在性结论；不宣称给出可计算或最小数值阈值，或对增长 $d$ 的一致结论。上述固定基图阶的限定只涉及吹胀期望极值；全局锐常数主定理按其自身量词陈述。期望结果也不等于样本级或几乎必然结果。

各编号结果的精确对应、完整类型和核验版本见[覆盖表](formal/COVERAGE.zh.md)；工具链、构建及递归公理审计步骤见[复现说明](formal/README.zh.md#复现)。旧 Hessian 核验及[卷积迁移记录](formal/CONVOLUTION_MIGRATION.zh.md)仍只描述各自版本，历史记录和来源哈希不改写。

GitHub Actions 检查为手动触发，不会因推送或拉取请求自动运行。



