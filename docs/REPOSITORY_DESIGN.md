# Repository design

The layout follows paper-centered formal mathematics projects: exposition,
a dependency blueprint, checked source, auxiliary scripts, pinned dependencies
and continuous integration. Inspected examples:

- [LeanProject](https://github.com/leanprover-community/LeanProject): source,
  scripts, blueprint/documentation and GitHub workflows.
- [FLT3](https://github.com/pitmonticone/FLT3): separate paper and blueprint,
  explicit build commands and visible CI.
- [Local flag algebras](https://github.com/rossjkang/localflagalgebras):
  certificates, discovery programs and result correspondence.
- [Bodnar supplementary files](https://github.com/bodnalev/supplementary_files):
  inspectable witness fields and independent checking instructions.

Here `src/` contains Python exact-certificate verifiers, `scripts/` contains
generation and search tools, and `paper/`, `blueprint/`, `certificates/` hold
the mathematical artifacts. `formal/` contains the standalone Lean certificate
library and the separate Mathlib mathematical proof layer, with pinned
dependencies, generated candidates, kernel proofs and axiom audits.
`blueprint/trust.md` states their actual checking boundary.

Temporary files and local environments are ignored. `.gitattributes` preserves
literal bytes across Windows and Unix checkouts for integrity verification.
