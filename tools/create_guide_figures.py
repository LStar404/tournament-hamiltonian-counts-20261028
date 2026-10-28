from pathlib import Path
import json, shutil
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch

ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'manuscripts/figures'
OUT.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Serif','font.size':10,
    'mathtext.fontset':'dejavuserif','pdf.fonttype':42,'svg.fonttype':'none'})
data={}
def save(fig,name,record):
    for ext in ('pdf','svg','png'):
        fig.savefig(OUT/f'{name}.{ext}',dpi=220,bbox_inches='tight',pad_inches=.08)
    plt.close(fig);data[name]=record

fig,axs=plt.subplots(1,2,figsize=(6.6,2.85))
pos={1:np.array((0.,1.)),2:np.array((-1.,-.65)),3:np.array((1.,-.65))}
edges=[[(1,2),(1,3),(2,3)],[(1,2),(2,3),(3,1)]]
for ax,es,title in zip(axs,edges,['Transitive triangle','Directed triangle']):
    ax.set_aspect('equal');ax.set_xlim(-1.3,1.3);ax.set_ylim(-1,1.5);ax.axis('off')
    for a,b in es:
        ax.add_patch(FancyArrowPatch(pos[a],pos[b],arrowstyle='-|>',mutation_scale=14,
            shrinkA=11,shrinkB=11,linewidth=1.2,color='.22'))
    for k,p in pos.items():
        ax.add_patch(Circle(p,.11,fc='black',zorder=3))
        ax.text(*p,str(k),color='white',ha='center',va='center',zorder=4)
    ax.text(0,1.35,title,ha='center')
save(fig,'three_vertex_examples',{'left_arcs':edges[0],'right_arcs':edges[1]})

fig,ax=plt.subplots(figsize=(5.3,3.5))
xx=np.linspace(-2,2,400);X,Y=np.meshgrid(xx,xx)
Q=X**2+X*Y+Y**2
ct=ax.contour(X,Y,Q,levels=[.25,.5,1,2,3],colors=['.15']*5,linewidths=.8)
ax.clabel(ct,inline=True,fontsize=8,fmt='%g')
ax.axhline(0,color='.65',lw=.6);ax.axvline(0,color='.65',lw=.6)
ax.set_aspect('equal');ax.set_xlim(-2,2);ax.set_ylim(-1.65,1.65)
ax.set_xlabel('$t_1$');ax.set_ylabel('$t_2$',rotation=0)
ax.set_title(r'$q(t)=t^{\mathsf{T}}Ht=t_1^2+t_1t_2+t_2^2$',fontsize=11)
save(fig,'hessian_quadratic',{'matrix':[[1,.5],[.5,1]],
    'quadratic':'t1^2+t1*t2+t2^2','levels':[.25,.5,1,2,3],
    'meaning':'Contours of the real quadratic form t^T H t, not of the original complex angular function. The Hessian of q/2 is H.'})

(OUT/'guide_figure_data.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
print('Two guide figures generated: PDF, SVG and PNG.')
