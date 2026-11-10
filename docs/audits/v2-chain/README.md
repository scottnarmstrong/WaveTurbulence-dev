# Seal audits: Theorem 1.1 for 1/2 < γ < 1 and its chain

Each frozen theorem below was sealed (its placeholder proof replaced by a one-line reference to the formal proof) and
then audited by **two auditors (keys A and B)**, separate AI sessions (the reports that name the model give Claude
Opus 5.5). Each auditor worked separately and did not write the proof. They checked:

- (a) the frozen statement's bytes (only the proof body changed);
- (b) the provider;
- (c) the axioms: standard only;
- (d) hidden hypotheses and vacuity;
- (e) the ABI hashes;
- (f) a replay of the proof in Lean's kernel, in quick mode: 40,618 certificate theorems of `WaveTurbulenceVineParam`
  were checked by statement only (their proofs are kernel-checked by every build), with Mathlib and Lean's core library
  as the trusted base; full mode was not run;
- (g) the status fields;
- (h) a five-bin binder table built from the paper's TeX source. It classifies every hypothesis, and **zero EXCESS**
  (no hypothesis beyond the source, standing assumptions, typing and approved rulings) is required.

A theorem is recorded as PROVED only when both keys pass.

| Theorem | What it is | Seal commit | Key A | Key B | Summary |
|---|---|---|---|---|---|
| `layergardenFlower_v3` | the flower estimate (TARGET `flowerest1`), 1/2 < γ < 1 | `1e51bebf` | [PASS](layergardenFlower_v3-A.md) | [PASS](layergardenFlower_v3-B.md) | [record](Seal-layergardenFlower_v3.md) |
| `fixedpoint_v2` | the fixed-point step, 1/2 < γ < 1 | `f78bcabf` | [PASS](fixedpoint_v2-A.md) | [PASS](fixedpoint_v2-B.md) | [record](Seal-fixedpoint_v2.md) |
| `propansatz_v2` | the ansatz proposition, 1/2 < γ < 1 | `7d98ae17` | [PASS](propansatz_v2-A.md) | [PASS](propansatz_v2-B.md) | [record](Seal-propansatz_v2.md) |
| **`main_v2`** | **Theorem 1.1, 1/2 < γ < 1** | `1987105a` | [PASS](main_v2-A.md) | [PASS](main_v2-B.md) | [record](Seal-main_v2.md) |

The upstream theorem `layergarden_v2` was sealed and audited earlier, in the same way.

These theorems are restricted to 1/2 < γ < 1. The full-range theorem, 0 < γ < 1, uses them for γ > 1/2; its seal
audits are in [`../full-range/`](../full-range/README.md).

The reports are working documents: they mention internal paths and tools of the formalization. Lean names
in them refer to the repository at the time of writing (the commits each report cites); a later clean-up removed some
unused helpers, which remain in the git history at those commits.

Absolute local paths in these records were replaced in November 2026 by placeholders: `<scratch>/` (the project's
private working directory), `<repo>/` (a checkout of this repository), `<worktrees>/` (development checkouts),
`<sources>/` (a local copy of the papers' LaTeX sources and maps) and `<tools>/` (private tooling); none of these is
part of the repository. Internal working records they cite (planning and audit records, working notes kept beside the Lean files, and the
agents' instructions) were removed from the repository at publication; those that were on the main branch
remain in its git history.
