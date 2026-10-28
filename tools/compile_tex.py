#!/usr/bin/env python3
"""Compile repository TeX sources with an already installed, offline engine.

Run from any directory. Inputs are manuscripts/*.tex; new PDFs and logs go to
build/pdf by default, leaving the reviewed PDFs in manuscripts untouched.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
MANUSCRIPTS = ROOT / "manuscripts"


def find_engine(requested: str) -> tuple[str, str]:
    candidates = ("xelatex", "tectonic") if requested == "auto" else (requested,)
    for name in candidates:
        executable = shutil.which(name)
        if executable:
            return name, executable
    raise RuntimeError(
        "未在 PATH 中找到可用编译器。请先自行安装 XeLaTeX 或 Tectonic，"
        "并确认相应命令可以运行；本脚本不会下载工具或宏包。"
    )


def select_documents(names: list[str]) -> list[Path]:
    if not names:
        documents = sorted(MANUSCRIPTS.glob("*.tex"))
        if not documents:
            raise RuntimeError("manuscripts/ 中没有 TeX 文件。")
        return documents
    documents = []
    for name in names:
        if Path(name).name != name or name in {".", ".."}:
            raise RuntimeError("请只给出 manuscripts/ 内的文件名或不含扩展名的名称。")
        source = MANUSCRIPTS / (name if name.endswith(".tex") else name + ".tex")
        if not source.is_file():
            raise RuntimeError(f"找不到稿件：{source.name}")
        if source not in documents:
            documents.append(source)
    return documents


def check_local_figures(source: Path) -> None:
    text = source.read_text(encoding="utf-8")
    figures = re.findall(r"\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}", text)
    for figure in figures:
        target = MANUSCRIPTS / figure
        if not target.is_file():
            raise RuntimeError(f"{source.name} 引用的图片不存在：{figure}")


def engine_arguments(name: str, executable: str, version: str, source: Path,
                     output: Path) -> list[str]:
    if name == "tectonic":
        return [executable, "--only-cached", "--keep-logs", "--keep-intermediates",
                "--outdir", str(output), source.name]
    command = [executable, "-interaction=nonstopmode", "-halt-on-error",
               "-file-line-error", "-no-shell-escape",
               "-output-directory=" + str(output)]
    if "miktex" in version.lower():
        command.append("--disable-installer")
    return command + [source.name]


def compile_document(source: Path, name: str, executable: str, version: str,
                     destination: Path, timeout: int) -> bool:
    passes = 2 if name == "xelatex" else 1
    console_log = destination / (source.stem + ".build.log")
    environment = os.environ.copy()
    environment["MIKTEX_ENABLE_INSTALLER"] = "0"
    transcripts = []
    with tempfile.TemporaryDirectory(prefix=".compile-", dir=destination) as temp:
        temporary = Path(temp)
        command = engine_arguments(name, executable, version, source, temporary)
        succeeded = True
        for number in range(1, passes + 1):
            print(f"编译 {source.name}：第 {number}/{passes} 遍", flush=True)
            try:
                result = subprocess.run(
                    command, cwd=MANUSCRIPTS, env=environment,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, encoding="utf-8", errors="replace", timeout=timeout,
                    check=False,
                )
                transcripts.append(f"=== Pass {number} ===\n" + result.stdout)
                if result.returncode != 0:
                    transcripts.append(f"\nExit code: {result.returncode}\n")
                    succeeded = False
                    break
            except (OSError, subprocess.TimeoutExpired) as error:
                transcripts.append(f"\n编译未完成：{error}\n")
                succeeded = False
                break
        console_log.write_text("\n".join(transcripts), encoding="utf-8")
        tex_log = temporary / (source.stem + ".log")
        if tex_log.is_file():
            shutil.copy2(tex_log, destination / tex_log.name)
        pdf = temporary / (source.stem + ".pdf")
        if succeeded and not pdf.is_file():
            transcripts.append("编译器返回成功，但没有生成预期 PDF。")
            console_log.write_text("\n".join(transcripts), encoding="utf-8")
            succeeded = False
        if succeeded:
            shutil.copy2(pdf, destination / pdf.name)
            print(f"完成：{destination / pdf.name}", flush=True)
        else:
            print(f"失败：{source.name}。完整记录：{console_log}", file=sys.stderr)
            print("\n".join("\n".join(transcripts).splitlines()[-25:]), file=sys.stderr)
        return succeeded


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("documents", nargs="*", help="稿件文件名或名称；默认全部 TeX")
    parser.add_argument("--engine", choices=("auto", "xelatex", "tectonic"),
                        default="auto", help="auto 优先使用 XeLaTeX")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "build" / "pdf",
                        help="输出目录；相对路径相对于仓库根目录")
    parser.add_argument("--timeout", type=int, default=600,
                        help="每遍编译最多等待的秒数，默认 600")
    parser.add_argument("--check", action="store_true",
                        help="只检查工具、输入及图片是否存在，不编译")
    args = parser.parse_args()
    try:
        if args.timeout <= 0:
            raise RuntimeError("--timeout 必须为正整数。")
        documents = select_documents(args.documents)
        for source in documents:
            check_local_figures(source)
        name, executable = find_engine(args.engine)
        result = subprocess.run(
            [executable, "--version"], stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace",
            check=False, timeout=30,
        )
        if result.returncode != 0:
            raise RuntimeError(f"{name} --version 执行失败：{result.stdout.strip()}")
        version = result.stdout
        print(f"使用编译器：{name}\n稿件数量：{len(documents)}")
        if args.check:
            print("工具与输入检查通过；字体及宏包的完整性仍须实际编译确认。")
            return 0
        destination = args.output_dir
        if not destination.is_absolute():
            destination = ROOT / destination
        destination = destination.resolve()
        if destination == MANUSCRIPTS.resolve():
            raise RuntimeError("请把输出放到 build/pdf 等目录，以保留 manuscripts/ 内的审阅版 PDF。")
        destination.mkdir(parents=True, exist_ok=True)
        failures = 0
        for source in documents:
            if not compile_document(source, name, executable, version, destination, args.timeout):
                failures += 1
        if failures:
            print(f"{failures} 份稿件编译失败；请检查对应日志。", file=sys.stderr)
            return 1
        print("全部编译完成。")
        return 0
    except (RuntimeError, OSError, subprocess.TimeoutExpired) as error:
        print(f"错误：{error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
