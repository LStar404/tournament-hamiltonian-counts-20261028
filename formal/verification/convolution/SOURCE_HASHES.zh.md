> **历史记录提示（2026-11-07）：** 下文记载当时的哈希校正，旧“未运行”状态仅限该阶段。后续固定工程的实际fresh运行见[2026-11-07报告](../../../review/lean-rerun-20261107/README.zh.md)。原哈希、日期和结论保持历史含义。

# 路径卷积验证：历史物化字节与规范 Git 字节

本说明只校正证据范围，不改变 Lean 证明正文、原构建/公理/回归日志或 `source_hashes.json` 的任一字节和哈希原值。

## 两组哈希分别表示什么

- `source_hashes.json`：原运行记录的 38 项本地物化输入 SHA-256，保留不动。不要把这份历史记录重命名为一次新的规范 Git 构建结果。
- `source_hashes.provenance.json` 的 `local_materialized_sha256`：逐项复制上述原记录，提供明确的语义标签。
- 同文件的 `canonical_git_sha256`：固定 Git 快照 `5d528bc2b962ea3d2ada921fbcae0ddf49afe481` 中对应 38 个文件的原始 blob 字节 SHA-256。路径均相对于仓库 `formal/`。
- `canonical_git_blob_sha1`：同一快照的 Git blob 标识。38 项均用 `SHA1("blob " + 字节数 + NUL + 文件字节)` 核对，以排除读取时换行规范化造成的伪差异。

两组 SHA-256 不应互相覆盖。规范哈希是供读者核对固定 Git 快照的补充材料，不是本次新构建的产物。

## 可核验的末尾换行映射

`canonical_to_historical_hash_mapping` 为每个文件给出以下一种规则：

| 规则 | 项数 | 精确含义 |
|---|---:|---|
| `identity` | 16 | 规范 Git 原始字节的 SHA-256 与原记录相同。 |
| `append_one_lf` | 22 | 在规范 Git 原始字节末尾再附加 **一个** `0x0A` 字节，其 SHA-256 与原记录相同。 |

这里没有执行 CRLF/LF 规范化，也没有删除已有末尾换行。22 项差异是再增加一个 LF；新桥文件、有可见性修改的 `Paths.lean` 和迁入的 8 个证明源文件属于直接匹配组。

该映射是从规范 Git 字节与已保留历史哈希计算出的确定等式。本次没有重新读取原工作站当时的本地文件，也没有重新执行旧运行；因此不把“哈希等式已核验”写成“历史运行文件已重新观察”。原记录与规范字节在这些项目上只差末尾空行的解释，与哈希等式一致；它不构成数学内容变化。

## 不扩大历史构建结论

- 原记录的构建与公理成功状态仍只说明原本地物化源码运行。
- 本次只修正文档/元数据；没有改写原日志、没有以新哈希追改原运行来源。
- **本次没有重新运行 Lean build 或 `#print axioms`，尚未对上述 canonical Git 字节快照新跑 Lean 编译。**
- 新增此文件和 provenance JSON 不能被计作一次新的逐字节可复现构建。匹配官方缓存的原有供应链范围也没有扩大。

## 仅复核哈希的命令（不编译 Lean）

在含有上述固定提交的仓库根目录运行以下 Python。源文件和旧哈希文件的逐字节比较均读取 Git blob，避免工作树换行转换；另对工作树旧哈希文件只检查 JSON 原值。

```python
import hashlib
import json
from pathlib import Path
import subprocess

root = Path("formal/verification/convolution")
p = json.loads((root / "source_hashes.provenance.json").read_text())
h = lambda b: hashlib.sha256(b).hexdigest()
commit = p["canonical_git_snapshot_commit"]
old_path = "formal/verification/convolution/source_hashes.json"
old_bytes = subprocess.check_output(["git", "show", f"{commit}:{old_path}"])
assert h(old_bytes) == p["historical_record"]["file_sha256"]
assert json.loads(old_bytes) == p["local_materialized_sha256"]
assert subprocess.check_output(["git", "show", f"HEAD:{old_path}"]) == old_bytes
assert json.loads((root / "source_hashes.json").read_text()) == p["local_materialized_sha256"]
for path, expected in p["canonical_git_sha256"].items():
    raw = subprocess.check_output(["git", "show", f"{commit}:formal/{path}"])
    assert h(raw) == expected, path
    blob = b"blob " + str(len(raw)).encode() + b"\0" + raw
    assert hashlib.sha1(blob).hexdigest() == p["canonical_git_blob_sha1"][path], path
    rule = p["canonical_to_historical_hash_mapping"][path]
    assert rule in ("identity", "append_one_lf"), path
    mapped = raw if rule == "identity" else raw + b"\n"
    assert h(mapped) == p["local_materialized_sha256"][path], path
assert len(p["canonical_git_sha256"]) == 38
assert list(p["canonical_to_historical_hash_mapping"].values()).count("identity") == 16
assert list(p["canonical_to_historical_hash_mapping"].values()).count("append_one_lf") == 22
print("38 pinned Git blobs and historical hash mappings verified; no Lean build run.")
```

若在后续提交修改这 38 个受记录文件中的任一个，应另行产生对应新快照的证据；不要静默更新此固定历史快照的哈希。

