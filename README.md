# 竞赛图 Hamilton 计数：论文、导读与复核记录

这份材料收录刘星辰、叶祥宇关于竞赛图 Hamilton 路径计数与 Wormald 随机吹胀模型的稿件。论文保留详细推导，另附面向初学者的中文导读、一页思路说明，以及本轮公式、来源和排版复核记录。

## 从哪里开始读

建议先读[大一新生导读](manuscripts/06_freshman_guide.zh.pdf)，再用[一页思路说明](manuscripts/05_proof_idea.zh.pdf)回看证明的主要步骤。需要核对完整论证时，读[中文合稿](manuscripts/01_combined.zh.pdf)或[英文合稿](manuscripts/02_combined.en.pdf)。两个专题文件分别展开路径估计和原角 Hessian 的计算。

| 文件 | 内容 |
|---|---|
| `06_freshman_guide.zh` | 33 页：从三角形开始，5 幅图，10 道练习及完整答案 |
| `05_proof_idea.zh` | 一页证明思路 |
| `01_combined.zh` | 中文合稿，包含完整推导及结果来源说明 |
| `02_combined.en` | 与中文合稿对应的英文版本 |
| `03_constant_factor.zh` | 路径计数的永久式估计，定位为技术补充 |
| `04_wormald.zh` | Wormald 原角 Hessian、模型极限与相关推论 |

各套文件均提供 PDF、TeX 和 Markdown。PDF 适合连续阅读；TeX 保留排版设置；Markdown 便于改写和比较文字。目录名中的旧文件标识 `constant_factor` 仅用于保持文件链接稳定，该稿的现标题与定位已是技术补充。

## 结果与已有工作的关系

全体竞赛图 Hamilton 路径和圈极值的首项常数

$$L=\frac{\cosh1}{\cos1}$$

由 Divoux–Wang 确定。合稿的路径部分在这一首项基础上证明对全体竞赛图统一的 $O(n^{-1})$ 归一化误差，细化永久式、删除、对角缩放及删集求和中的误差控制。局部永久式的 $O(n^{-1})$ 误差阶已有 McCullagh 的工作，也可从 Divoux–Wang 的非负双随机矩阵证明中进一步提取；本文的全局误差结论需要后续计数步骤共同成立。

另一项主结果直接计算 Wormald 原角函数的完整 Hessian，证明它的正定性，并求出行列式。固定正则基图的模型常数也可以直接从 Divoux–Wang 的加权圈公式得到。正则内部块因子与路径转换仍调用 Wormald 的计数定理；谱比较及其等号分类承接 Fang–Huang、Divoux–Wang。稿件在相应位置明确这些依赖，再补充等号分析、非正则基图估计及固定阶图类的比较。

原 $C_*>L$ 常数因子上界已被已有首项结论涵盖，因此保留为辅助估计。圆环闭式及其极限同样注明已有来源；严格单调性和高阶展开作为这些公式的进一步推论与计算呈现。完整对照见[研究定位说明](review/研究定位说明.txt)。

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
