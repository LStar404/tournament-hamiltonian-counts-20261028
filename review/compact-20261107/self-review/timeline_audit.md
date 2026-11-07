# 第三轮：版本时间线独立核对

## 本轮检查范围

直接复核当前中英文引言与书目[14–17]、`priority_audit/findings.md`、Zenodo三个版本的原始JSON，以及v1.0实际英文TeX的作者、摘要、定理和§7.2。Bhattacharjee与Divoux–Wang的固定版本事实采用前轮已经核验并留存来源的证据，本轮没有将Git时间解释成首次公开时间。

## 实质发现与处理建议

书目[14]的首版作者为Xingchen Liu，紧接“Later archive: v1.2”容易把后版也读成单作者。原始Zenodo元数据显示后版v1.1/v1.2的作者为Xingchen Liu、Xiangyu Ye。建议[14]仅保留确已核验全文的v1.0，或明确把v1.2写成两作者条目。

v1.2的`publication_date`为2026-10-11，记录`created`为2026-10-10T22:46:58.701722+00:00。v1.1分别为2026-10-09与2026-10-08T22:38:29.672234+00:00。两类字段应并列说明，不按记录创建时间自动推断首次公开日期。后两版的内容增量不由元数据单独确定。

## 可核验时间线

| 时间 | 记录类型 | 作者/版本 | 该记录支撑的内容 |
|---|---|---|---|
| 2026-10-08 08:00 UTC | Zenodo记录创建，DataCite紧随注册且findable；publication_date=10-08 | Xingchen Liu，v1.0，DOI 10.5281/zenodo.23233166 | 已核全文：L/C*两常数界、正路径卷积、永久式展开、非主子阵缩放、异常顶点处理；§7.2保留尖锐L上界问题；该包无Lean |
| 2026-10-09（元数据publication_date） | 后续Zenodo版本；created=10-08 22:38 UTC | Xingchen Liu、Xiangyu Ye，v1.1，DOI 10.5281/zenodo.23249802 | 本轮核作者及日期字段；不以元数据声称具体新增定理 |
| 2026-10-11（元数据publication_date） | 后续Zenodo版本；created=10-10 22:46 UTC | Xingchen Liu、Xiangyu Ye，v1.2，DOI 10.5281/zenodo.23288896 | 本轮核作者及日期字段；当前[14]应避免把后版归作首版单作者 |
| 2026-10-14 | GitHub公开release v1.0.0 | Deep Bhattacharjee，固定commit 82f66b1cc6c495e6623e0d412b66ab09efdb3a43 | 前轮已核固定源码具有完整原角Hessian矩阵公式，不只行列式 |
| 2026-10-16 17:00:14 UTC | arXiv v1 submission | Alexander Divoux、Shouda Wang，2610.23755v1 | 尖锐圈/路径首项渐近；提交时间用于版本排序，不用于推断研究完成时间 |
| 2026-10-19 | 所引Git稿件revision日期 | Xingchen Liu、Xiangyu Ye，2fd6a2c30260b826feef71049d7d593527fd7a42 | Wormald项目固定稿，支持读者复查该版推导；Git revision日期本身不是首次公开时间的独立证明 |
| 2026-10-30 | 固定仓库合并commit | Liu–Ye，c678e9ee24fb304cad755a27c99f511c8640f75e | 后续合稿与形式化覆盖快照；与10月8日路径包及本轮11月7日fresh重跑分别记录 |

## 可直接采用的中英文字

中文：

Bhattacharjee 于2026年10月14日公开的版本[16]已给出原角Hessian的完整矩阵公式、正定性及相关行列式结论。本方Wormald项目在[15]固定至10月19日的Liu–Ye Git稿件版本；[13]的后续版本也注明了双方的独立工作。本文保留直接推导，并逐项说明重合结果。这里分别记录公开发行日期和Git稿件版本日期；10月8日的单作者路径存档[14]则对应前述L/C*计数框架。

English:

Bhattacharjee's public release of 14 October 2026 [16] contains the full original angular Hessian, its positive definiteness, and the associated determinant results. Our Wormald project is cited through the Liu--Ye Git manuscript revision dated 19 October [15]; the later version [13] also acknowledges the independent work. We retain a direct derivation and identify the overlapping results. These records distinguish a public release date from a Git manuscript revision date. The separate single-author path archive of 8 October [14] concerns the L/C* counting framework described above.

书目[14]的建议最短形式：

[14] Xingchen Liu. *Constant-factor bounds for Hamiltonian paths in tournaments*, v1.0 (8 October 2026). [Version DOI: 10.5281/zenodo.23233166](https://doi.org/10.5281/zenodo.23233166).

若保留后版链接，应追加：Subsequent joint version: Xingchen Liu and Xiangyu Ye, v1.2 (publication-date metadata: 11 October 2026), DOI 10.5281/zenodo.23288896.

## 来源

https://zenodo.org/records/23233166
https://api.datacite.org/dois/10.5281/zenodo.23233166
https://zenodo.org/records/23249802
https://zenodo.org/records/23288896
https://arxiv.org/abs/2610.23755v1
https://github.com/creelie/Breakthrough-problems-1/releases/tag/v1.0.0
https://github.com/creelie/Breakthrough-problems-1/blob/82f66b1cc6c495e6623e0d412b66ab09efdb3a43/preprint/main.tex
https://hexagonmath.org/pdf/2610.00460v2
https://github.com/LStar404/wormald-tournament-conjectures/blob/2fd6a2c30260b826feef71049d7d593527fd7a42/docs/paper.zh.md

## 已落实

第三轮已采用上述双语时间线段落；主文书目[14]仅保留单作者v1.0，后续两作者版本及日期字段区别留在本记录中。最终主文由37页中文、41页英文构成。
