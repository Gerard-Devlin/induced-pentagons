#!/usr/bin/env python3
"""Normative finite specification of the formulas in manuscript Sections 2/4.

This is deliberately separate from both the input generator and the saved data.
The independent counter checks that data use these particular mathematical
patterns and normalizations before checking any recorded count. It therefore
does not let a saved JSON file redefine the theorem that is being verified.
"""

import _bootstrap  # local CLI module paths only
from fractions import Fraction as F
from itertools import product
import math

PSTAR=F(5,144)
TAU=F(5,663552)
KAPPA=F(1,9216)
FLAG_SPECIFICATIONS={
    'one_root':(1,4,(),20,140),
    'independent3':(3,5,(),72,1260),
    'edge_isolate':(3,5,((0,1),),72,1260),
    'path3':(3,5,((0,1),(1,2)),72,1260),
    'triangle3':(3,5,((0,1),(0,2),(1,2)),72,1260),
}

def primitive_patterns():
    """Required edges/nonedges in the paper's labelled integral formulas."""
    result=[]
    def add(name,n,edges,nonedges=()):
        clean=lambda es:sorted(tuple(sorted(e)) for e in es)
        edges,nonedges=clean(edges),clean(nonedges)
        if len(set(edges))!=len(edges) or len(set(nonedges))!=len(nonedges):
            raise ValueError('A primitive pattern repeats an edge variable')
        if set(edges)&set(nonedges):raise ValueError('Conflicting requirements')
        if not all(0<=a<b<n for a,b in edges+nonedges):raise ValueError('Invalid labelled vertex')
        result.append({'name':name,'vertices':n,'edges':[list(e) for e in edges],
                       'nonedges':[list(e) for e in nonedges],
                       'denominator':math.factorial(7)//math.factorial(7-n)})
    cycle=[(0,1),(1,2),(2,3),(3,4),(0,4)]
    chords=[(0,2),(0,3),(1,3),(1,4),(2,4)]
    add('p',2,[(0,1)])
    add('theta',5,cycle,chords)
    add('L1',6,cycle+[(0,5)],chords)
    add('L2',7,cycle+[(0,5),(0,6)],chords)
    add('L3',7,cycle+[(0,5),(5,6)],chords)
    add('B1',3,[(0,1),(0,2)])
    add('B2',4,[(0,1),(0,2),(0,3)])
    add('B3',4,[(0,1),(1,2),(2,3)])
    add('L_triangle',7,cycle+[(0,5),(0,6),(5,6)],chords)
    add('B_triangle',4,[(0,1),(0,2),(1,2),(0,3)])
    # W(0,1) times two common-neighbour factors at vertices 2 and 3.
    common=[(0,1),(0,2),(1,2),(0,3),(1,3)]
    # Completion A deletes the root edge; completion B deletes a root chord.
    ae=[(0,4),(4,5),(5,6),(1,6)]
    an=[(0,5),(0,6),(1,4),(1,5),(4,6)]
    be=[(0,4),(1,4),(1,5),(5,6),(0,6)]
    bn=[(0,5),(4,5),(4,6),(1,6)]
    for i in (0,1):
        e=common+([(2,3)] if i else [])
        ne=[] if i else [(2,3)]
        add(f'R{i}',4,e,ne)
        add(f'J{i}_A',7,e+ae,ne+an)
        add(f'J{i}_B',7,e+be,ne+bn)
    # Triangle-weighted profile replacement f=g(1-h), equations (10),(11).
    tri=[(0,1),(0,2),(1,2)]
    path=[(3,4),(4,5),(5,6)];missing=[(3,5),(3,6),(4,6)]
    add('Jdel_Lg',7,tri+path+[(0,3),(0,6)],missing+[(0,4),(0,5)])
    for a,b in product((0,1),repeat=2):
        e=tri+path+[(0,3),(0,6)];ne=missing+[(1,3),(1,6)]
        for vertex,choice in ((4,a),(5,b)):
            if choice:e += [(0,vertex),(1,vertex)]
            else:ne += [(0,vertex)]
        add(f'Jdel_Lf{a}{b}',7,e,ne)
    add('Ddel',4,common)
    return result

def variational_columns():
    columns={'p':{'p':F(1)},'theta':{'theta':F(1)}}
    for j in (1,2,3):columns[f'Phi{j}']={f'L{j}':PSTAR,f'B{j}':-TAU}
    columns['PhiTri']={'L_triangle':PSTAR,'B_triangle':-TAU}
    for i in (0,1):columns[f'Ji{i}']={f'J{i}_A':F(1),f'J{i}_B':F(-1),f'R{i}':-KAPPA}
    columns['Jdel']={'Jdel_Lg':F(1,2),'Ddel':-KAPPA,
                    **{f'Jdel_Lf{a}{b}':F(-1,2) for a,b in product((0,1),repeat=2)}}
    return columns

def verify_specification(metadata,patterns,flags):
    if not __debug__:raise RuntimeError('Proof specification verification refuses disabled assertions.')
    specs=primitive_patterns()
    assert len(specs)==len(metadata['patterns'])==22
    assert [s['name'] for s in specs]==patterns['pattern_names'].tolist()
    for i,(expected,actual) in enumerate(zip(specs,metadata['patterns'])):
        for key,value in expected.items():assert actual[key]==value,(actual['name'],key,'mathematical specification differs')
        assert int(patterns['pattern_denominators'][i])==expected['denominator']
    expected=variational_columns()
    assert len(metadata['columns'])==len(expected)==9
    assert [c['name'] for c in metadata['columns']]==list(expected)==patterns['column_names'].tolist()
    for c in metadata['columns']:
        assert {k:F(v) for k,v in c['terms'].items()}==expected[c['name']],c['name']
    norm=metadata['normalization']
    assert (F(norm['pstar']),F(norm['tau']),F(norm['kappa']))==(PSTAR,TAU,KAPPA)
    assert int(patterns['fixed_density_denominator'])==3024
    assert int(patterns['common_denominator'])==278691840
    for name,(_,_,_,dim,den) in FLAG_SPECIFICATIONS.items():
        assert len(flags['flag_masks_'+name])==dim
        assert flags['C_'+name].shape==(1044,dim,dim)
        assert int(flags['denominator_'+name])==den
    return {'status':'verified_exact','primitive_patterns':22,'named_columns':9,
            'flag_types':5,'source':'Explicit mathematical formulas in Sections 2 and 4',
            'saved_metadata_cannot_redefine_patterns_or_denominators':True}
