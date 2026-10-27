# Exact proof inputs and discovery data

The three primary exact witness files are:

- `all_graph_exact_certificate.json`: 1,044 host identities, 184 positive
  integer-vector squares with rational weights, and 826 positive host slacks.
- `all_graph_path3_triangle_domination_span.json`: the triangle-domination
  combination of positive path-type square vectors.
- `all_graph_tf_degree_codegree_spans.json`: the degree and codegree span
  combinations used after triangle elimination.

The main JSON certificate stores `constants`, `host_masks`, `free_columns`,
`positive_columns`, `squares`, and `slacks`. Rational coefficients are exact
strings. The verifier validates the schema and signs; floating-point guesses
are never substituted for these coefficients.

`graph_atlas_7.json`, `flag_spaces.json`, `flag_basis.npz`, `pattern_columns.json`,
and `pattern_columns.npz` specify or store finite combinatorial inputs. The
independent recount reconstructs the full-permutation counts and validates
them against the mathematical specification in `src/proof_specification.py`.
`host_masks.txt` and TSV files provide additional inspectable views.

`clebsch_graph.json`, the profile files, and
`eventual_polynomials_small_offsets.json` contain finite construction data.
The offset file records presentations with labeled Clebsch types; it is not a
list of pairwise nonisomorphic extremal graphs. See manuscript Section 14.1.

The `symmetry_blocks*` files are optional numerical discovery aids. They do not
prove the main inequality. See `../docs/COMPUTATIONAL_REPRODUCTION.txt` for the
complete conventions and commands.
