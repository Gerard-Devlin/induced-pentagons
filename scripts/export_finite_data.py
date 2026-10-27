#!/usr/bin/env python3
"""Export actual finite objects, not just a summary of their verification."""

import _bootstrap  # local CLI module paths only
import json
from pathlib import Path
from clebsch_core import ADJ, EDGES, CYCLES, PATHS, GENERATORS, all_profile_counts

def main():
    out=Path(__file__).resolve().parents[1]/'certificates';out.mkdir(exist_ok=True)
    graph={'schema_version':1,'labeling':'integers 0..15 represent F_2^4 bit vectors',
           'generators':GENERATORS,'edges':EDGES,'neighborhood_masks':ADJ,
           'induced_C5_vertex_subsets':CYCLES,
           'induced_P4_records':PATHS,
           'P4_record_order':'endpoint1, endpoint2, internal1, internal2'}
    (out/'clebsch_graph.json').write_text(json.dumps(graph,indent=2)+'\n')
    counts=all_profile_counts()
    assert len(counts)==65536 and max(counts)==60
    profiles={'schema_version':1,'mask_convention':'bit i means vertex i belongs to the new-vertex neighborhood',
              'counts_by_mask':counts,
              'definition':'Number of induced P4 subsets whose endpoints are in the neighborhood and whose internal vertices are outside it',
              'verification':'verify_profiles.py independently scans all paths for every mask'}
    (out/'profile_envelope.json').write_text(json.dumps(profiles,separators=(',',':'))+'\n')
    print('Exported Clebsch graph, 192 pentagons, 480 paths, and all 65536 profile counts.')

if __name__=='__main__': main()
