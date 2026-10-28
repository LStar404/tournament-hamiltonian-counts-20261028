from pathlib import Path
import json
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, Rectangle

ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'manuscripts/figures'
OUT.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({
    'font.family':'serif', 'font.serif':['DejaVu Serif'],
    'font.size':9, 'mathtext.fontset':'dejavuserif',
    'pdf.fonttype':42, 'ps.fonttype':42, 'svg.fonttype':'none',
    'axes.linewidth':0.6, 'savefig.facecolor':'white',
})
metadata={}

def setup(ax,xlim,ylim):
    ax.set_aspect('equal');ax.set_xlim(*xlim);ax.set_ylim(*ylim);ax.axis('off')

def arrow(ax,a,b,*,curve=0,color='0.25',lw=.75,ms=7,shrink=5,style='-',zorder=1):
    p=FancyArrowPatch(a,b,arrowstyle='-|>',mutation_scale=ms,
      connectionstyle=f'arc3,rad={curve}',shrinkA=shrink,shrinkB=shrink,
      linewidth=lw,color=color,linestyle=style,zorder=zorder)
    ax.add_patch(p)
    return p

def node(ax,p,label,*,radius=.072,ring=False,fontsize=8):
    if ring:ax.add_patch(Circle(p,radius*1.6,fill=False,edgecolor='black',lw=.7,zorder=3))
    ax.add_patch(Circle(p,radius,facecolor='black',edgecolor='black',lw=.4,zorder=4))
    ax.text(*p,label,ha='center',va='center',fontsize=fontsize,color='white',zorder=5)

def circular_positions(n,phase=np.pi/2):
    return {i:np.array((np.cos(phase-2*np.pi*i/n),np.sin(phase-2*np.pi*i/n))) for i in range(n)}

def carousel_edges(n):
    return [(i,j) for i in range(n) for j in range(n) if 1<=(j-i)%n<=(n-1)//2]

def save(fig,name,data):
    for ext in ('pdf','svg','png'):
        fig.savefig(OUT/f'{name}.{ext}',dpi=230,bbox_inches='tight',pad_inches=.055)
    plt.close(fig)
    metadata[name]=data

# All directed edges of the seven-vertex carousel and of its induced deletion.
fig,axs=plt.subplots(1,2,figsize=(6.7,2.95),gridspec_kw={'wspace':.12})
pos=circular_positions(7);edges=carousel_edges(7)
assert len(edges)==21 and len({tuple(sorted(e)) for e in edges})==21
for ax,vertices,title in ((axs[0],list(range(7)),r'$\mathrm{Car}_7$'),
                          (axs[1],list(range(1,7)),r'$\mathrm{Car}_7-\{0\}$')):
    setup(ax,(-1.23,1.23),(-1.12,1.35))
    for i,j in edges:
        if i in vertices and j in vertices:arrow(ax,pos[i],pos[j],lw=.65,ms=6.5,shrink=5.7)
    for i in vertices:node(ax,pos[i],str(i),radius=.075,fontsize=8)
    ax.text(0,1.27,title,ha='center',va='center',fontsize=10)
save(fig,'carousel_deletion',{'vertices_left':list(range(7)),'arcs_left':edges,
 'vertices_right':list(range(1,7)),'arcs_right':[e for e in edges if 0 not in e],
 'meaning':'Right panel is the induced tournament after deleting vertex 0; all remaining arcs are drawn.'})

# Blow-up of a directed triangle. Large arrows denote the nine arcs between blocks.
fig,ax=plt.subplots(figsize=(6.7,3.7));setup(ax,(-2.35,2.35),(-2.05,1.72))
centers={0:np.array((-1.45,.7)),1:np.array((1.45,.7)),2:np.array((0.,-1.35))}
offsets=circular_positions(3)
nodes={}
for k,c in centers.items():
    ax.add_patch(Circle(c,.57,facecolor='0.96',edgecolor='0.58',lw=.6,zorder=0))
    ax.text(c[0],c[1]+.74,rf'$V_{k}$',ha='center',va='center',fontsize=10)
    for i in range(3):nodes[(k,i)]=c+.31*offsets[i]
    for i in range(3):arrow(ax,nodes[(k,i)],nodes[(k,(i+1)%3)],lw=.8,ms=7.5,shrink=3.5)
    for i in range(3):
        p=nodes[(k,i)];ax.add_patch(Circle(p,.031,fc='black',ec='black',zorder=4))
        q=c+.455*offsets[i]
        ax.text(q[0],q[1],rf'$v_{{{k}{i}}}$',ha='center',va='center',fontsize=8.2)
for i,j in ((0,1),(1,2),(2,0)):
    c,d=centers[i],centers[j];v=(d-c)/np.linalg.norm(d-c)
    start=c+.65*v;end=d-.65*v
    arrow(ax,start,end,lw=1,ms=12,shrink=0,color='black')
    perp=np.array((-v[1],v[0]));mid=(start+end)/2+.15*perp
    rotation=np.degrees(np.arctan2(v[1],v[0]))
    if rotation>90:rotation-=180
    if rotation<-90:rotation+=180
    ax.text(mid[0],mid[1],'all 9 arcs',rotation=rotation,ha='center',va='center',fontsize=8.3,
      bbox={'facecolor':'white','edgecolor':'none','pad':.5})
save(fig,'triangle_blowup',{'base_arcs':[(0,1),(1,2),(2,0)],
 'internal_arcs':[((k,i),(k,(i+1)%3)) for k in range(3) for i in range(3)],
 'block_arc_count':9,'meaning':'Each large directed arrow denotes all nine arcs between the displayed three-vertex blocks.'})

# A permanent term as a directed cycle and as a row-column matching.
fig,axs=plt.subplots(1,2,figsize=(6.7,3.6),gridspec_kw={'wspace':.2})
cycle=['f_1','x_1','x_2','f_2','x_3']
arcs=list(zip(cycle,cycle[1:]+cycle[:1]))
exceptional={'f_1','f_2'}
remaining=('x_1','x_2')
ax=axs[0];setup(ax,(-1.35,1.35),(-1.55,1.68))
cp=circular_positions(5);cp={name:cp[k] for k,name in enumerate(cycle)}
for name in exceptional:
    ax.add_patch(Circle(cp[name],.18,fc='0.89',ec='0.65',lw=.6,zorder=0))
for a,b in arcs:
    arrow(ax,cp[a],cp[b],lw=1.7 if (a,b)==remaining else .85,
          color='black' if (a,b)==remaining else '0.35',ms=9,shrink=6.5)
for name in cycle:node(ax,cp[name],'$'+name+'$',radius=.088,fontsize=8)
ax.text(0,1.53,'Directed cycle',ha='center',va='center',fontsize=9.5)
ax.text(0,-1.34,r'$F=\{f_1,f_2\}$',ha='center',va='center',fontsize=9)

ax=axs[1];setup(ax,(-1.35,1.35),(-1.55,1.68))
ordered=['f_1','f_2','x_1','x_2','x_3']
ys={name:1.05-.51*k for k,name in enumerate(ordered)}
left={name:(-.77,ys[name]) for name in ordered}
right={name:(.77,ys[name]) for name in ordered}
for x in (-1.0,.54):
    ax.add_patch(Rectangle((x,.31),.46,.99,fc='0.89',ec='none',zorder=0))
ax.plot([-1.13,1.13],[.285,.285],color='0.65',lw=.6,ls=(0,(3,3)),zorder=0)
for a,b in arcs:
    arrow(ax,left[a],right[b],lw=1.8 if (a,b)==remaining else .85,
          color='black' if (a,b)==remaining else '0.4',ms=9,shrink=6.5)
for name in ordered:
    node(ax,left[name],'$'+name+'$',radius=.088,fontsize=8)
    node(ax,right[name],'$'+name+'$',radius=.088,fontsize=8)
ax.text(-.77,1.53,'Rows',ha='center',va='center',fontsize=9.5)
ax.text(.77,1.53,'Columns',ha='center',va='center',fontsize=9.5)
ax.text(-.77,-1.34,r'$I=\{x_2,x_3\}$',ha='center',va='center',fontsize=8.2)
ax.text(.77,-1.34,r'$J=\{x_1,x_3\}$',ha='center',va='center',fontsize=8.2)
core=set(cycle)-exceptional
deleted_rows={a for a,b in arcs if a in core and b in exceptional}
deleted_cols={b for a,b in arcs if a in exceptional and b in core}
assert deleted_rows=={'x_2','x_3'} and deleted_cols=={'x_1','x_3'}
assert [(a,b) for a,b in arcs if a in core and b in core]==[remaining]
save(fig,'nonprincipal_matching',{'directed_cycle':cycle,'matching_arcs':arcs,
 'row_column_order':ordered,'exceptional_vertices':sorted(exceptional),
 'deleted_core_rows':sorted(deleted_rows),'deleted_core_columns':sorted(deleted_cols),
 'remaining_core_arc':remaining,
 'meaning':'The same permanent term appears as a directed five-cycle and a row-column matching. Only selected cycle arcs are shown, not every tournament edge. Shading marks F in both copies; the bold arc belongs to the remaining core submatrix with different row and column deletion sets.'})

# A concrete switching equivalence: Car_5, switch U={1,2}, then order 3,1,4,2,0.
fig,axs=plt.subplots(1,2,figsize=(6.7,3.0),gridspec_kw={'wspace':.18})
pos=circular_positions(5);edges=carousel_edges(5);U={1,2};order=[3,1,4,2,0]
switched=[(j,i) if ((i in U)!=(j in U)) else (i,j) for i,j in edges]
assert set(switched)=={(order[i],order[j]) for i in range(5) for j in range(i+1,5)}
ax=axs[0];setup(ax,(-1.23,1.23),(-1.26,1.36))
for i,j in edges:arrow(ax,pos[i],pos[j],lw=.75,ms=7,shrink=6)
for i in range(5):node(ax,pos[i],str(i),radius=.076,ring=i in U,fontsize=8)
ax.text(0,1.28,r'$\mathrm{Car}_5$',ha='center',va='center',fontsize=10)
ax.text(0,-1.15,r'$U=\{1,2\}$',ha='center',va='center',fontsize=9)
ax=axs[1];setup(ax,(-1.23,1.23),(-1.26,1.36))
trans={order[k]:np.array((-np.cos(k*np.pi/4),1.8*np.sin(k*np.pi/4)-.9)) for k in range(5)}
for i,j in switched:arrow(ax,trans[i],trans[j],lw=.75,ms=7,shrink=6)
for i in order:node(ax,trans[i],str(i),radius=.076,ring=i in U,fontsize=8)
ax.text(0,1.28,'After switching',ha='center',va='center',fontsize=9)
ax.text(0,-1.15,r'$(3,1,4,2,0)$',ha='center',va='center',fontsize=9)
save(fig,'carousel_switching',{'carousel_arcs':edges,'switching_set':sorted(U),
 'switched_arcs':switched,'transitive_order':order,
 'meaning':'Reverse precisely the arcs with one endpoint in U and one outside. Every switched arc points forward in the displayed transitive order.'})

(OUT/'graph_figure_data.json').write_text(json.dumps(metadata,indent=2),encoding='utf-8')
print('\n'.join(str(OUT/(name+'.pdf')) for name in metadata))
