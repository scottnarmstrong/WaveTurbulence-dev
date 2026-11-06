# Campaign plan (wave-turbulence)

Target: Deng–Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2, Theorem 1.1 for
`0 < γ < 1`, square torus, `d ≥ 3` (D2), with everything proved in Lean (D1).

## Phases

| phase | content | status |
|---|---|---|
| P0 | pin sources (target, DH21, DH21-2, DH23, DH19, GIT20), repos, toolchain `wt-throttled` | done 2026-11-03 |
| P1 | paper maps (`~/wave-turbulence/maps/`), then a node-level blueprint/dependency graph | blueprint v2: 275 nodes / 84 packets; exact-anchor/source maintenance continues |
| P2 | **Wave A** exact statements: Theorem 1.1 + every definition it uses (+ Prop `wkelwp`) — audit, author approval, freeze | approved and frozen under D6; `wkelwp` sealed |
| P3 | **Wave B** exact induction gates, combinatorial definitions and principal imported estimates | B1/B2 frozen under D7–D8; five gamma-above-half successors frozen under D10 |
| P4 | prove dependency-ready obligations and integrate on the canonical universe | active: actual vine reduction/norm, LOW counting, flower boundary times and source-provider integration; see HQ and current handoff |
| P5 | seal, audit, errata ledger, public release | 16/26 theorem anchors sealed; 10 drafts; 296 frozen definitions; public release pending |

The active theorem chain is `1/2 < γ < 1`. Seal and independently audit its five successor anchors before starting
the enlarged-vine extension to `0 < γ ≤ 1/2` (D9–D11). Scratch compilation, conditional helper results and library
ports do not seal an anchor. The [HQ README](../../README.md) and [progress ledger](progress.json) distinguish the
weighted work estimate from exact theorem closure; the [current handoff](orch/CODEX-HANDOFF.md) records the active
packets, evidence and remaining gaps.

## Infrastructure packets (route-independent; candidates to start early)

- GAUSS — centered normalized complex Gaussians: moments, Isserlis/Wick for iid families, Wiener-chaos hypercontractivity
  and tail bounds for multilinear Gaussian expressions (DH21 Sec 12 / OT Lemma 2.6). Mine RegularityStructures-dev,
  GlobalPhi43-dev, Critical2DKPZ, DOZZ, Balaban first.
- CUMUL — cumulants (TARGET Def `defcm`), inversion formula, Lemma `propertycm` (Leonov–Shiryaev), cumulants under
  events with gauge/translation symmetry.
- WKE — the collision operator `𝒦` on Schwartz functions: GIT20 trilinear estimates in `Z_s`, Leibniz/weight
  identities (C.6)–(C.7), LWP in `Z_{s,m}`, Prop `wkelwp`, Taylor expansion (`wketaylor`) and bounds (`taylorbound`).
- NLS — Fourier analysis on `𝕋_L^d` (smooth periodic ↔ rapidly decaying coefficients, inversion, Parseval), smooth
  NLS solutions: uniqueness, mass conservation, measurability of the solvability event and of the solution map, the
  gauge/Wick-ordering/time-rescaling reduction to the `a_k` system (TARGET L540–L566).
- COUNT / NT — lattice counting lemmas (TARGET App. A.4, DH23 App. A), number-theory lemmas (Gauss sums, Dirichlet
  approximation, DH23 `NTSP`, `minorarcs`), and the Huxley input question (FINDINGS F3).

## Fleet (D13; supersedes the initial D3 allocation)

- Orchestrator: Codex in `w/orch`, succeeding the quota-interrupted Claude session. Owns source interpretation,
  shared APIs, rulings, manifest, findings and landings.
- Coding workers: Terra-medium subagents; Sol-low fallback if ineffective. Current packets and briefs are in
  [workers.json](workers.json). Independent source reviewers must not have authored the declaration or repair.
- Preserve the existing canonical-world and batch-4b serial builds; inspect their checkpoints before taking over
  work and do not launch duplicate drivers.
- Compile control: toolchain `wt-throttled` (`~/wt-tools/sysroot`): at most 6 project compiles (`WT_CAP`), then the
  shared machine throttle. One targeted niced build per worker/cache at a time; no Mathlib rebuilds. Only the
  orchestrator runs the prescribed root landing gate. The D12 catalogue has its own separate Lean library.
