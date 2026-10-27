# Recomputed reports and discovery checkpoint

`verification_manifest.json` records the last full finite verification,
including its exact environment and source/data/manuscript SHA256 map.
`sharp_bound_verification.json` is compared with a fresh equality-model
evaluation during that run. `reverified_offset_enumeration.json` is a generated
view of the stored offset presentations.

Rerun `python src/verify_project.py` after changing any bound source, manuscript,
data, or documentation. An old PASS does not certify a changed repository.
The report is an exact computational verdict, not a proof-assistant verdict on
the analytic arguments.

`sdp_csdp_regularized_solution.npz`, its summary, and `csdp_regularized/` are
optional discovery artifacts. Exact witness verification requires no SDP
solver and does not trust these floating-point outputs.
