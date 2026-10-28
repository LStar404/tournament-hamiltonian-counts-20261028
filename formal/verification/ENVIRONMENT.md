# 验证环境

- Lean 4.35.0，发布提交 eb6cafb7290e8bd5f2937522d8d804f58f02bafc。
- Lake 5.0.0，随同一 Lean 官方发行版。
- Linux x86_64 官方编译器归档 SHA-256：7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d。
- mathlib 固定提交 56a005855ea17e0b0958f73ec801ae140b0a1679；其他依赖见 lake-manifest.json。
- 官方 mathlib 缓存已使用。标准基础公理和具体依赖见 axioms.json。
- Python 3.12 / SymPy 1.14.0 用于独立有限回归，不参与 Lean 定理证明。
- 构建日期：2026-10-28 UTC。源码哈希见 source_hashes.json。

复现命令：在 formal 目录执行 bash scripts/verify.sh。
所附构建和公理记录针对本包源码；覆盖范围见 COVERAGE.zh.md。
