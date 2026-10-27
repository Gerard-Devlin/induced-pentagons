#!/usr/bin/env python3
"""Regenerate Figure 1 directly from the three formulas in Section 11."""

import _bootstrap  # local CLI module paths only
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def main():
    dest=Path(__file__).resolve().parents[1]/'paper'/'figures'
    dest.mkdir(parents=True,exist_ok=True)
    a=np.linspace(0,1,1201)
    clone=3*a*(1-a)/80
    eigen=(1-a)/80
    optimum=np.minimum(clone,eigen)
    with plt.rc_context({'font.family':'serif','font.size':10,
                         'axes.spines.top':False,'axes.spines.right':False,
                         'pdf.fonttype':42,'ps.fonttype':42}):
        fig,ax=plt.subplots(figsize=(6.2,2.55),layout='constrained')
        ax.plot(a,clone,color='#98a5b4',lw=1.4,ls='--',label='Partial clone')
        ax.plot(a,eigen,color='#6d8796',lw=1.4,ls=':',label='Negative eigenspace')
        ax.plot(a,optimum,color='#233c50',lw=2.1,label=r'Optimal coefficient $f(\alpha)$')
        ax.set(xlim=(0,1),ylim=(0,.0133),xlabel=r'Arithmetic phase $\alpha$',
               ylabel=r'Coefficient of $m^2$')
        ax.set_xticks([0,1/3,2/3,1],['0',r'$1/3$',r'$2/3$','1'])
        ax.set_yticks([0,1/240,1/120,1/80],['0',r'$1/240$',r'$1/120$',r'$1/80$'])
        ax.grid(axis='y',color='#d8dde1',lw=.6,alpha=.65)
        ax.legend(frameon=False,loc='upper right',fontsize=8.4)
        fig.savefig(dest/'arithmetic_phase.pdf')
        fig.savefig(dest/'arithmetic_phase.png',dpi=220)
    print('Regenerated arithmetic phase figure.')

if __name__=='__main__': main()
