#!/usr/bin/env python3
"""Offline, source-preserving portable-font XeLaTeX builder.

Requires XeLaTeX with xeCJK and longtable 4.23-compatible unnumbered tables,
fontconfig, Python fontTools, Liberation Serif/Sans, DejaVu Sans Mono,
and the system Noto Serif/Sans CJK SC font collections. Installs nothing.
"""
from __future__ import annotations
import argparse, hashlib, json, re, shutil, subprocess
from pathlib import Path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def exact_font(family):
    result = subprocess.run(['fc-match', '-f', '%{family}|%{file}|%{index}', family], check=True, capture_output=True, text=True).stdout
    actual, path, index = result.split('|')
    if family not in actual.split(','):
        raise RuntimeError(f'Required font unavailable: {family}; fontconfig returned {actual}')
    return Path(path), int(index or 0)


def extract_sc(source, destination, want):
    from fontTools.ttLib import TTFont
    path, index = source
    font = TTFont(path, fontNumber=index, recalcTimestamp=False)
    if font['name'].getDebugName(1) != want:
        raise RuntimeError(f'Wrong collection face: {font["name"].getDebugName(1)}')
    font.save(destination)
    return {'source':str(path),'collection_index':index,'source_sha256':digest(path.read_bytes()),'output_sha256':digest(destination.read_bytes())}


def prepare(source, destination, fonts):
    original = source.read_bytes().decode('utf-8')
    preamble, delimiter, body = original.partition('\\begin{document}')
    if not delimiter:
        raise RuntimeError(f'Missing document boundary: {source}')
    preamble = preamble.replace('{Times New Roman}', '{Liberation Serif}').replace('{Arial}', '{Liberation Sans}').replace('{Consolas}', '{DejaVu Sans Mono}')
    if '\\setCJKmainfont' in preamble:
        a = preamble.index('\\setCJKmainfont'); b = preamble.index('\\xeCJKsetup', a)
        fp = fonts.as_posix() + '/'
        replacement = ('\\setCJKmainfont[Path='+fp+',\n  BoldFont=NotoSansCJKsc-Bold.otf,\n  ItalicFont=NotoSerifCJKsc-Regular.otf]{NotoSerifCJKsc-Regular.otf}\n'
            '\\setCJKsansfont[Path='+fp+',\n  BoldFont=NotoSansCJKsc-Bold.otf]{NotoSansCJKsc-Bold.otf}\n'
            '\\setCJKmonofont[Path='+fp+']{NotoSansCJKsc-Bold.otf}\n')
        preamble = preamble[:a] + replacement + preamble[b:]
    shims=[]
    if r'\def\LTcaptype{none}' in body and r'\begin{longtable}' in body:
        preamble += r'''
% Local TeX-version compatibility only: preserve Pandoc's unnumbered tables.
\ExplSyntaxOn
\AddToHook{env/longtable/before}{\str_if_eq:eeT{\LTcaptype}{none}{\stepcounter{LT@tables}\cs_set:Npn\LTcaptype{}}}
\ExplSyntaxOff
'''
        shims.append('longtable LTcaptype=none mapped to empty with unique internal LT@tables counter')
    result = preamble + delimiter + body
    assert result.partition(delimiter)[2].encode() == body.encode()
    destination.write_bytes(result.encode())
    return {'file':source.name,'source_sha256':digest(source.read_bytes()),'working_sha256':digest(result.encode()),'body_sha256':digest(body.encode()),'body_unchanged':True,'preamble_compatibility_shims':shims}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--output',type=Path)
    p.add_argument('--documents',nargs='*')
    p.add_argument('--prepare-only',action='store_true')
    args=p.parse_args();root=args.root.resolve();out=(args.output or root/'build/portable-pdf').resolve()
    if out == root or out == root/'manuscripts':
        raise RuntimeError('Choose a separate output directory; source overwrites are forbidden.')
    tex=out/'tex';fonts=out/'fonts';pdf=out/'pdf'
    for d in (tex,fonts,pdf):d.mkdir(parents=True,exist_ok=True)
    for family in ('Liberation Serif','Liberation Sans','DejaVu Sans Mono'):exact_font(family)
    sf=exact_font('Noto Serif CJK SC');nf=exact_font('Noto Sans CJK SC')
    # Resolve bold via family + fontconfig style, then verify the SC name table.
    result=subprocess.run(['fc-match','-f','%{family}|%{file}|%{index}','Noto Sans CJK SC:weight=bold'],check=True,capture_output=True,text=True).stdout
    family,path,index=result.split('|')
    if 'Noto Sans CJK SC' not in family.split(','):raise RuntimeError('Noto Sans CJK SC Bold unavailable')
    nf=(Path(path),int(index or 0))
    manifest={'source_root':str(root),'font_mode':'documented portable alternatives; not the original Microsoft or bundled Noto SC font bytes','fonts':{},'documents':[]}
    manifest['fonts']['serif']=extract_sc(sf,fonts/'NotoSerifCJKsc-Regular.otf','Noto Serif CJK SC')
    manifest['fonts']['sans_bold']=extract_sc(nf,fonts/'NotoSansCJKsc-Bold.otf','Noto Sans CJK SC')
    shutil.copytree(root/'manuscripts/figures',tex/'figures',dirs_exist_ok=True)
    sources=sorted((root/'manuscripts').glob('*.tex'))
    if args.documents:
        names={x if x.endswith('.tex') else x+'.tex' for x in args.documents}
        if any(Path(x).name!=x for x in names):raise RuntimeError('Documents must be plain filenames')
        sources=[x for x in sources if x.name in names]
        if len(sources)!=len(names):raise RuntimeError('Requested TeX file missing')
    if not sources:raise RuntimeError('No TeX sources found')
    for source in sources:
        record=prepare(source,tex/source.name,fonts);manifest['documents'].append(record)
        if args.prepare_only:continue
        logs=[];stable=False
        for number in range(1,6):
            command=['xelatex','-interaction=nonstopmode','-halt-on-error','-file-line-error','-no-shell-escape','-output-directory='+str(pdf),source.name]
            result=subprocess.run(command,cwd=tex,capture_output=True,text=True,errors='replace',timeout=600)
            logs.append(f'=== Pass {number} ===\n'+result.stdout+result.stderr)
            (pdf/(source.stem+'.build.log')).write_text('\n'.join(logs))
            if result.returncode:raise RuntimeError(f'XeLaTeX failed for {source.name}; see build log')
            log=(pdf/(source.stem+'.log')).read_text(errors='replace')
            if re.search(r'Missing character:|Overfull \\[hv]box',log):raise RuntimeError(f'Missing glyph/overfull box: {source.name}; inspect log')
            rerun=re.search(r'Rerun (?:LaTeX|to get)|Label\(s\) may have changed|There were undefined references|Table widths have changed',log)
            if number>=2 and not rerun:stable=True;record['passes']=number;break
        if not stable:raise RuntimeError(f'References/table widths did not converge for {source.name}')
        record['pdf_sha256']=digest((pdf/(source.stem+'.pdf')).read_bytes())
        record['underfull_count']=len(re.findall(r'Underfull \\[hv]box',log))
        print(source.name,'built in',record['passes'],'passes',flush=True)
    (out/'build-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')

if __name__=='__main__':main()
