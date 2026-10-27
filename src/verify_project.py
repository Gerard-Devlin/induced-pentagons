#!/usr/bin/env python3
"""Recompute the complete finite verification chain, failing if proof data lack.

This command checks the computational dependencies of the manuscript. Its PASS is not a machine formalization of the analytic arguments.
Missing, malformed, or incorrect certificate data always return a nonzero code.
"""

import _bootstrap  # local CLI module paths only
from pathlib import Path
import argparse, hashlib, importlib.metadata, json, os, platform, sys, time, traceback
from release_integrity import VERIFIED_STATUS, fingerprints

ROOT=Path(__file__).resolve().parents[1]
CERTIFICATE_NAMES=[
    'all_graph_exact_certificate.json',
    'all_graph_path3_triangle_domination_span.json',
    'all_graph_tf_degree_codegree_spans.json',
]
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def installed_version(name):
    try: return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        if name == 'python-flint': return None
        raise

def save(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_suffix(path.suffix+'.tmp')
    tmp.write_text(json.dumps(obj,indent=2)+'\n');os.replace(tmp,path)

def main():
    if not __debug__:
        raise RuntimeError('Exact verification requires assertions; run Python without -O and without PYTHONOPTIMIZE.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'results/verification_manifest.json')
    a=parser.parse_args();started=time.time();data=ROOT/'certificates'
    initial_hashes=fingerprints(ROOT)
    report={'schema':'induced-pentagons.project-verification.v2',
            'scope':'Exact computational dependencies; analytic arguments are provided in the manuscript',
            'status':'incomplete','steps':{},'missing_certificates':[],
            'environment':{'python':platform.python_version(), 'implementation':platform.python_implementation(),
                           'assertions_enabled':__debug__,
                           'packages':{name:installed_version(name) for name in
                                       ('numpy','scipy','sympy','python-flint','networkx')}},
            'sha256_scope':'Source, exact data, canonical and flattened paper/PDFs, and documentation; hashes bind bytes, not a machine formalization of the text.'}
    def finish(code):
        report['elapsed_seconds']=time.time()-started
        report['sha256']=fingerprints(ROOT)
        if code==0 and report['sha256']!=initial_hashes:
            report['status']='failed'
            report['error']='A bound source, data, or manuscript file changed during verification. Rerun with a stable project.'
            code=1
        save(a.output,report);print(json.dumps(report,indent=2));return code
    report['missing_certificates']=[n for n in CERTIFICATE_NAMES if not (data/n).exists()]
    if report['missing_certificates']:
        report['reason']='The complete global computational proof cannot be checked until all three certificates exist.'
        return finish(2)
    try:
        from check_manuscript_inventory import build_inventory, render_guide
        inventory=build_inventory(ROOT)
        assert (ROOT/'blueprint/statements.json').read_text()==json.dumps(inventory,indent=2)+'\n', 'Stale manuscript inventory; review changes and run check_manuscript_inventory.py --write'
        assert (ROOT/'blueprint/proof_dependencies.txt').read_text()==render_guide(inventory), 'Stale proof dependency guide'
        report['steps']['manuscript_inventory']={'status':inventory['status'],'counts':inventory['counts'],
            'scope':'Statement/equation completeness and reference resolution, not automatic proof checking'}
        from verify_combinatorial_inputs import verify as verify_inputs
        report['steps']['independent_combinatorial_recount']=verify_inputs(data)
        save(a.output,report)
        from rationalize_certificate import verify_certificate
        report['steps']['global_certificate']=verify_certificate(data/CERTIFICATE_NAMES[0],data)
        from verify_certificate_independent import verify as independent_certificate
        report['steps']['independent_global_certificate']=independent_certificate(data/CERTIFICATE_NAMES[0],data)
        save(a.output,report)
        from generate_equality_spans import verify_spans
        report['steps']['equality_spans']=verify_spans(*(data/n for n in CERTIFICATE_NAMES),data_dir=data)
        from audit_equality_support import audit as support
        support_result=support(data/'graph_atlas_7.json',data/'equality_host_support.json')
        report['steps']['independent_equality_support']={k:support_result[k] for k in
            ('status','host_count','supported_host_count','excluded_host_count',
             'triangle_free_host_count','excluded_triangle_free_host_count','atlas_sha256','support_sha256')}
        from verify_finite import run as finite
        finite_result=finite()
        report['steps']['finite_clebsch']=finite_result
        from verify_profiles import run as profiles
        profile_result=profiles()
        report['steps']['all_boolean_profiles']=profile_result
        save(a.output,report)
        from verify_offsets import run as offsets
        computed=offsets(ROOT/'results/reverified_offset_enumeration.json',True,(-2,-1,0,1,2),False,True)
        report['steps']['fixed_offsets']={
            'status':computed['status'],'presentations':computed['total_candidate_presentations_checked'],
            'actual_graph_checks':computed['actual_graph_checks'],
            'offset_polynomial_records':computed['offset_polynomial_records'],
            'globally_distinct_polynomials':computed['globally_distinct_polynomials'],
            'offsets':{j:{k:r[k] for k in ['lambda','candidate_presentations_checked',
                                        'distinct_polynomials','best_ascending_coefficients']}
                       for j,r in computed['offsets'].items()}}
        from verify_presentation_census import verify as census
        report['steps']['elementary_presentation_census']=census(data)
        from verify_stored_artifacts import verify as stored
        report['steps']['published_artifact_consistency']=stored(data,finite_result,profile_result,computed)
        from verify_sharp_bound import verify as sharp_bound
        matched=sharp_bound(data)
        assert json.loads((ROOT/'results/sharp_bound_verification.json').read_text())==matched, 'Stored sharp-bound equality check differs from fresh computation'
        report['steps']['sharp_target_and_equality']={
            'status':matched['status'],'constants':matched['constants'],
            'squares_exactly_zero':matched['exact_zero_checks']['squares'],
            'conditional_integer_dot_products':matched['exact_zero_checks']['conditional_integer_dot_products'],
            'all_1044_slack_terms_zero':matched['exact_zero_checks']['all_1044_slack_terms_zero'],
            'slope':matched['slope'],'certificate_sha256':matched['certificate_sha256']}
        report['status']=VERIFIED_STATUS
        return finish(0)
    except Exception as exc:
        report['status']='failed';report['error']=f'{type(exc).__name__}: {exc}'
        report['traceback']=traceback.format_exc();return finish(1)

if __name__=='__main__':sys.exit(main())
