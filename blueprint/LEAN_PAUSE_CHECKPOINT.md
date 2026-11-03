# Lean pause checkpoint — 2026-11-03

Work is paused at the user's request after merging completed feature branches.
The status and verification reports describe component proofs, not a complete
formalization of the manuscript.

## Integrated milestones

- Complete primitive and fixed-density tables, atlas coverage and separation.
- All 1,044 stored atlas automorphism orders and orbit sizes, with reproducible
  JSON export and arbitrary seven-vertex graph transfer.
- Full-permutation and joint-sample semantics, normalized density transfer,
  upper-triangular contraction soundness conditional on tensor row checks.
- Actual certificate pentagon target and source Gram quadratic SOS
  nonnegativity, retaining the conditional-product averaging hypothesis.
- Finite weighted compactness, integer/real and blow-up reductions,
  zero-edge boundary and unit-simplex normalization.
- Clebsch spectral identities and pentagon second-order expansion with an
  explicit cubic remainder bound.

## Resume priorities

1. Benchmark and finish the full saved flag-product tensor kernel recounts.
   Generated candidate rows in the tensor worktree are not verified proofs.
2. Complete cached `gramAt` to source `gramEntry` soundness, then the
   independent-sampling/limit bridge for conditional-square nonnegativity.
3. Continue actual weighted variations and the graphon/global-bound proof.
4. Equality classification, stability, phase counting/errors, and eventual
   polynomial arguments remain; see `LEAN_ROADMAP.md` for full scope.

## Preserved unfinished work

Separate worktrees remain intact. `lean/tensor-recount` contains uncommitted
optimization and generated candidate files. `lean/density-identity` contains
an unfinished `CertificateGramSoundness.lean`; `lean/sampling-collision-bound`
contains an unfinished `SamplingCollision.lean`. These were not merged.
The atlas worker's final already-compiled census files were copied into the
integration checkout; its old uncommitted documentation edits were not imported.
No worker should resume until the user explicitly resumes the task.

## Recheck after resuming

Use Lean 4.35.0, preserve the existing dependency caches, and keep
`LEAN_NUM_THREADS=2`. Run `python scripts/verify_lean_paper.py` on stable sources
and `python scripts/verify_lean.py` for the core certificate gate. Read the
latest `results/lean_paper_verification.json`, `results/lean_verification.json`
and `formal/STATUS.md` before reporting progress.
