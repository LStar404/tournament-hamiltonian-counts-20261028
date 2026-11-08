#!/usr/bin/env python3
"""Regenerate manuscript body and abstract, retaining the approved preamble."""
import re, subprocess
from pathlib import Path
root=Path(__file__).resolve().parent.parent
for stem in ('01_combined.zh','02_combined.en'):
 p=root/'manuscripts'/(stem+'.md'); s=p.read_text()
 abstract=s.split('## ',2)[2].split('\n',1)[1].split('## 1.',1)[0] if False else s[s.index('## 摘要' if '.zh' in stem else '## Abstract'):].split('\n',1)[1].split('## 1.',1)[0]
 body='## 1.'+s.split('## 1.',1)[1]
 def convert(x):
  x=re.sub(r'<a id="([^"]+)"></a>\s*\$\$(.*?)\$\$',lambda m:'\\begin{equation}\n'+m[2].strip()+'\n\\label{'+m[1]+'}\n\\end{equation}',x,flags=re.S)
  out=subprocess.run(['pandoc','-f','markdown+raw_tex','-t','latex','--shift-heading-level-by=-1','--wrap=none'],input=x,text=True,capture_output=True,check=True).stdout
  out=out.replace('.png}', '.pdf}')
  out=re.sub(r'\\texttt\{([0-9a-f]{32,})\}',lambda m:r'\nolinkurl{'+m[1]+'}',out)
  out=re.sub(r',height=[^,\]]+','',out)
  out=re.sub(r'(?m)^(\\(?:sub)*section\*?\{)',lambda m:'\\Needspace{12\\baselineskip}\n'+m[1],out)
  out=out.replace(r'\textbf{推论 1.4。}',r'\Needspace{7\baselineskip}'+ '\n' +r'\textbf{推论 1.4。}')
  return out
 tex=root/'manuscripts'/(stem+'.tex'); old=tex.read_text(); prefix=old.split('\\begin{quote}',1)[0]
 tex.write_text(prefix+'\\begin{quote}\n'+convert(abstract)+'\\end{quote}\n'+convert(body)+'\n\\end{document}\n')
