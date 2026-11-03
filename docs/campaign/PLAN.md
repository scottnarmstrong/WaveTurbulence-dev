# Campaign plan (wave-turbulence)

Target: Deng–Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2, Theorem 1.1 for
`0 < γ < 1`, square torus, `d ≥ 3` (D2), with everything proved in Lean (D1).

## Phases

| phase | content | status |
|---|---|---|
| P0 | pin sources (target, DH21, DH21-2, DH23, DH19, GIT20), repos, toolchain `wt-throttled` | done 2026-11-03 |
| P1 | paper maps (`~/wave-turbulence/maps/`), then a node-level blueprint/dependency graph | maps in progress |
| P2 | **Wave A** exact statements: Theorem 1.1 + every definition it uses (+ Prop `wkelwp`) — audit, author approval, freeze | draft elaborated; audit by wt-orch running |
| P3 | **Wave B** exact statements: induction gates (`propansatz`, `layergarden`, `fixedpoint`), the combinatorial definitions they need (trees, couples, gardens, canonical layering, decorations, `K_G`), and the major imported results (DH21/DH23 regular-couple asymptotics, vine estimates, rigidity theorem, counting lemmas, GIT20 trilinear estimate, Gaussian chaos tails, NLS reduction) | after P1 |
| P4 | provers on the dependency-ready frontier; infrastructure packets that every route needs may start earlier with a recorded reason | infra packets after Wave A freeze |
| P5 | seal, audit, errata ledger, public release | — |

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

## Fleet (D3)

- `wt-orch` — Opus (claude-1): statement audits, blueprint review, seal audits.
- Provers — Claude Code sessions on claude-10/13/14; Codex on codex-3 (codex-1/2 after their resets). Never codex-4.
- Compile control: toolchain `wt-throttled` (`~/wt-tools/sysroot`): at most 6 project compiles (`WT_CAP`), then the
  shared machine throttle. Workers build single modules only, never the library.
