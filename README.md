# WaveTurbulence-dev — campaign HQ

Lean 4 formalization of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024).

<!-- AUTO:updated -->
> **Last updated: 2026-11-03 17:16 UTC** · **estimated completion 13.9 %** (Lean proofs 10.1 %) · frozen theorems sealed: 0 / 2 (+ 13 frozen definitions) · **21,942 lines of Lean on main** (152 files) + 5,329 unlanded on worker branches · blueprint estimate ≈ 273,000 lines
<!-- /AUTO:updated -->

**Scope (D1):** everything proved in Lean, no black boxes. That covers the target paper and the results it uses from
Deng–Hani's earlier papers (DH21, DH23, parts of DH21-2 and DH19), the trilinear estimates of Germain–Ionescu–Tran
(GIT20), smooth-solution theory for cubic NLS on the torus, and the Gaussian/cumulant facts.
**Main theorem (D2):** Theorem 1.1 for `0 < γ < 1` on the square torus `[0,L]^d`, `d ≥ 3`.

## Status

**Phase:** P2 (exact statements) with P4 proofs of route-independent infrastructure running in parallel.
**Wave A frozen (D6):** Theorem 1.1 (`WaveTurbulence.main`) and Prop 3.2 (`WaveTurbulence.wkelwp`) as `DRAFT_SORRY`
anchors in `WaveTurbulence/Frozen/Theorems/`, 13 sealed definitions in `WaveTurbulence/Frozen/Defs/`, manifest
`manifest/frozen.json`. **Wave B** (12 theorems + their definitions): drafting and stage audits in progress.
**Blueprint v2** (after independent topology review): 275 nodes, 84 packets, ≈273k lines, critical path weight 99.
**F32 resolved:** the `wkelwp` blow-up conjunct is provable for all d ≥ 3 (new proof of the general-d L²_s trilinear estimate, audited CORRECT; packet WKE-L2S); no owner decision needed.

```text
DRAFT_ANCHORS: 2 (WaveTurbulence/Frozen/Theorems/Main.lean, WaveTurbulence/Frozen/Theorems/Wkelwp.lean)
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
```

## Progress

<!-- AUTO:progress -->
### Estimated completion: **13.9 %**

`████░░░░░░░░░░░░░░░░░░░░░░░░░░` 13.9 %

| Part of the project | Items | Weight | Done | Completion |
|---|---|---|---|---|
| Sources, paper maps, blueprint (P0–P1) | 1 | 30 | 27.0 | `█████████░` 90 % |
| Exact Lean statements, frozen (P2) | 1 | 20 | 8.0 | `████░░░░░░` 40 % |
| Lean proofs (P4) | 85 | 681 | 68.8 | `█░░░░░░░░░` 10 % |
| Frozen theorems sealed | 2 | 2 | 0.0 | `░░░░░░░░░░` 0 % |
| Release (P5) | 1 | 15 | 0.0 | `░░░░░░░░░░` 0 % |
| **Total** | | 748 | 103.8 | **13.9 %** |

Lean lines: 21,942 on main + 5,329 on branches, of ≈ 273,000 estimated by the blueprint (`██░░░░░░░░░░░░░░░░░░` 10.0 % of the estimate).

<details><summary>All Lean work packets (blueprint §E) with weight and status</summary>

| Packet | Name | Weight | Lines (est.) | Done | Note |
|---|---|---|---|---|---|
| NT1 | GAUSSSUM | 5 | ≈2,100 | ✅ 100 % | landed 59220dc: Dirichlet, sharp interval and log-free smooth Gauss sum bounds |
| R-CUMUL | CUMUL | 13 | ≈3,560 | ✅ 100 % | landed fea3516 |
| R-GAUSS | GAUSS-HC | 4 | ≈2,500 | ✅ 100 % | landed f986d35 (off-route, F34) |
| R-TF | TORUS-FOURIER | 4 | ≈2,500 | ✅ 100 % | landed 5beb902 |
| WA | Wave A definitions | 5 | ≈230 | ✅ 100 % | frozen D6 |
| B1 | NLS-A | 6 | ≈1,600 | 🟡 60 % | Fourier equation, mass conservation, a-system defs landed; reduction in progress (wt-torus) |
| N4 | AN-SOB | 7 | ≈2,700 | 🟡 60 % | Sobolev variants, (10.5) landed; DH21 L10.2 in progress |
| R-NTC | NT-CIRCLE | 6 | ≈3,300 | 🟡 60 % | Euler–Maclaurin + sawtooth; circle 2/3 in progress (wt-nt) |
| R-WKE | WKE | 24 | ≈9,810 | 🟡 50 % | delta reading, slicing, Leibniz, tame trilinear, Schwartz closure, uniqueness landed; existence/τ_max/Taylor in progress (wt-wke) |
| D1 | COMB-CORE | 8 | ≈2,020 | 🟡 30 % | Wave B core carriers drafted; under audit |
| N1 | AN-FOURIER | 9 | ≈3,500 | 🟡 30 % | χ₀ (Gevrey 2, F41) landed; 𝔛 norms in progress |
| N5 | RESONANT | 6 | ≈2,800 | 🟡 30 % | resonant measure parametrization landed; p.v. and DH21 L6.3 in progress |
| D2 | SYS-DEFS | 14 | ≈3,400 | 🟡 25 % | Wave B system objects drafted; under audit |
| NT9 | LINALG | 4 | ≈1,400 | 🟡 20 % | MISC-A started (wt-cumul) |
| B2 | NLS-B | 9 | ≈3,200 | 🟡 15 % | uniqueness of smooth solutions landed |
| NT-EXPSUM | NT-EXPSUM | 14 | ≈5,300 | 🟡 10 % | A-process landed; B-process next (wt-nt) |
| B3 | NLS-C | 10 | ≈3,000 | 🟡 5 % |  |
| C1 | REG-STRUCT | 11 | ≈4,000 | ⬜ 0 % |  |
| C2 | LINKS | 11 | ≈3,000 | ⬜ 0 % |  |
| C3 | SKELETON | 15 | ≈5,200 | ⬜ 0 % |  |
| C4 | LAYERREG | 8 | ≈4,000 | ⬜ 0 % |  |
| C5 | ENHANCED | 9 | ≈3,150 | ⬜ 0 % |  |
| D3 | CANON | 9 | ≈3,950 | ⬜ 0 % |  |
| D4 | REG-DEFS | 8 | ≈2,400 | ⬜ 0 % |  |
| F1 | FINAL-RED | 4 | ≈1,200 | ⬜ 0 % |  |
| F2 | PLG | 12 | ≈4,150 | ⬜ 0 % |  |
| F3 | FINAL-COUNT | 4 | ≈900 | ⬜ 0 % |  |
| G0 | MOLE-COUNT-BASICS | 4 | ≈1,400 | ⬜ 0 % |  |
| G1 | STAGE2-DEF | 10 | ≈2,600 | ⬜ 0 % |  |
| G2 | EXCESS-DH23 | 8 | ≈3,500 | ⬜ 0 % |  |
| G3 | EXCESS-T | 10 | ≈3,500 | ⬜ 0 % |  |
| G4 | APPB-OPS | 8 | ≈4,000 | ⬜ 0 % |  |
| G5 | APPB-ALG | 8 | ≈4,000 | ⬜ 0 % |  |
| G6 | MOLEPROP13 | 6 | ≈2,400 | ⬜ 0 % |  |
| G7 | MOLEPROP4 | 12 | ≈4,500 | ⬜ 0 % |  |
| G8 | RIGID | 10 | ≈4,600 | ⬜ 0 % |  |
| I1 | INDUCT-A | 10 | ≈4,000 | ⬜ 0 % |  |
| I2 | INDUCT-B | 10 | ≈3,050 | ⬜ 0 % |  |
| J1 | BCOEF | 7 | ≈3,800 | ⬜ 0 % |  |
| J2 | CLASSJR2 | 8 | ≈4,000 | ⬜ 0 % |  |
| J3 | MAINCOEF | 4 | ≈3,000 | ⬜ 0 % |  |
| J4 | CANCEL7 | 6 | ≈3,400 | ⬜ 0 % |  |
| J5 | MEXP | 6 | ≈2,700 | ⬜ 0 % |  |
| J6 | WKE-ID | 6 | ≈2,800 | ⬜ 0 % |  |
| J7 | REGCANCEL | 4 | ≈2,000 | ⬜ 0 % |  |
| L1 | PL1A | 7 | ≈2,800 | ⬜ 0 % |  |
| L2 | PL1B | 9 | ≈4,650 | ⬜ 0 % |  |
| L3 | PL23 | 4 | ≈1,700 | ⬜ 0 % |  |
| L4 | PL4 | 4 | ≈2,500 | ⬜ 0 % |  |
| M1 | MOLE | 15 | ≈4,900 | ⬜ 0 % |  |
| M2 | BLOCKS | 6 | ≈1,600 | ⬜ 0 % |  |
| M3 | CLCN | 10 | ≈3,500 | ⬜ 0 % |  |
| M4 | VINES | 10 | ≈3,300 | ⬜ 0 % |  |
| M5 | MOLECPL | 4 | ≈1,500 | ⬜ 0 % |  |
| M6 | TWIST | 8 | ≈2,800 | ⬜ 0 % |  |
| M7 | LFTWIST | 13 | ≈4,200 | ⬜ 0 % |  |
| M8 | LAYERCNT | 6 | ≈2,100 | ⬜ 0 % |  |
| M9 | VINEPARAM | 4 | ≈1,500 | ⬜ 0 % |  |
| N2 | AN-PHASE | 5 | ≈1,700 | ⬜ 0 % |  |
| N3 | AN-HY | 10 | ≈4,500 | ⬜ 0 % |  |
| NT10 | LEMLIN | 4 | ≈1,500 | ⬜ 0 % |  |
| NT11 | LEMCUBIC | 6 | ≈3,000 | ⬜ 0 % |  |
| NT2 | HUA | 8 | ≈3,500 | ⬜ 0 % |  |
| NT3 | MINOR1 | 6 | ≈2,000 | ⬜ 0 % |  |
| NT4 | MINOR2 | 5 | ≈3,200 | ⬜ 0 % |  |
| NT5 | NTSP | 8 | ≈4,300 | ⬜ 0 % |  |
| NT6 | APPROXNT | 12 | ≈6,200 | ⬜ 0 % |  |
| NT7 | COUNT0 | 7 | ≈3,050 | ⬜ 0 % |  |
| NT8 | COUNT | 7 | ≈3,800 | ⬜ 0 % |  |
| RA1 | REGASYMP | 10 | ≈5,800 | ⬜ 0 % |  |
| RA2 | REGREF | 13 | ≈4,100 | ⬜ 0 % |  |
| S1 | STAGE1-COMB | 7 | ≈2,400 | ⬜ 0 % |  |
| S2 | REDSPLICE | 6 | ≈2,400 | ⬜ 0 % |  |
| S2a | REDSPLICE-DEF | 2 | ≈800 | ⬜ 0 % |  |
| S3 | LADDER | 8 | ≈4,200 | ⬜ 0 % |  |
| S4 | SUBPRO | 8 | ≈3,000 | ⬜ 0 % |  |
| V1 | SUMINT-A | 7 | ≈4,200 | ⬜ 0 % |  |
| V2 | SUMINT-B | 5 | ≈2,200 | ⬜ 0 % |  |
| V3 | REGRED | 6 | ≈1,900 | ⬜ 0 % |  |
| V4 | VINEEST-S2 | 4 | ≈2,500 | ⬜ 0 % |  |
| V5 | VINEEST | 13 | ≈5,100 | ⬜ 0 % |  |
| X1 | FLOWER-DEF | 10 | ≈3,100 | ⬜ 0 % |  |
| X2 | FLOWEREST | 16 | ≈8,900 | ⬜ 0 % |  |
| X3 | FIXEDPT | 9 | ≈3,400 | ⬜ 0 % |  |
| Z1 | MAIN | 3 | ≈860 | ⬜ 0 % |  |

</details>

Done fractions last reviewed: **2026-11-03 17:20 UTC**. Source: [`docs/campaign/progress.json`](docs/campaign/progress.json); history: [`docs/campaign/history.csv`](docs/campaign/history.csv).
<!-- /AUTO:progress -->

## Workers

<!-- AUTO:workers -->
| tmux | model / account | packet | branch: last commit | brief |
|---|---|---|---|---|
| wt-orch | Claude Opus / claude-1 | audits (Wave B stage audits; done: freeze check, figure defs, topology review, infra review) | `w/orch`: 9 min ago | [brief](docs/campaign/orch/TASK4.md) |
| wt-gauss-hc | Claude Opus / claude-10 | WAVEB-DRAFT: exact Lean drafts of Wave B (critical path) | `w/waveb-infra`: — | [brief](docs/campaign/briefs/WAVEB-DRAFT.md) |
| wt-torus | Claude Opus / claude-14 | NLS (B1–B3): smooth solutions, reduction to the a-system, measurability | `w/nls`: 1 min ago, 11 unlanded | [brief](docs/campaign/briefs/NLS.md) |
| wt-wke | Claude Opus / claude-13 | WKE-TAYLOR: existence, τ_max (wkelwp 1–2), Taylor bound | `w/wke`: 1 min ago, 11 unlanded | [brief](docs/campaign/briefs/WKE-TAYLOR.md) |
| wt-cumul | GPT-6.1-Sol low / codex-3 | MISC-A: TARGET Lemmas A.6–A.7, DH21 A.4, probability helpers (Hua moved to NT2) | `w/misc-a`: 3 min ago | [brief](docs/campaign/briefs/MISC-A.md) |
| wt-nt | GPT-6.1-Sol low / codex-3 | NT-EXPSUM: circle problem with exponent < 2/3 (van der Corput) | `w/nt-circle`: 0 min ago, 1 unlanded | [brief](docs/campaign/briefs/NT-CIRCLE-v2.md) |
| wt-ansob | GPT-6.1-Sol low / codex-3 | N4 AN-SOB: Sobolev/Morrey, simplex volumes, DH21 Lemma 10.2 | `w/an-sob`: 3 min ago, 1 unlanded | [brief](docs/campaign/briefs/AN-SOB.md) |
| wt-gausssum | GPT-6.1-Sol low / codex-3 | NT2 HUA: Hua L⁴/L⁶, Weyl-sum reduction, L^{3d/2} moments (GAUSSSUM landed) | `w/hua`: — | [brief](docs/campaign/briefs/HUA.md) |
| wt-resonant | GPT-6.1-Sol low / codex-3 | N5 RESONANT: resonant measure, p.v. 1/Ω, DH21 Lemma 6.3 | `w/resonant`: 1 min ago, 1 unlanded | [brief](docs/campaign/briefs/RESONANT.md) |
| wt-anfourier | GPT-6.1-Sol low / codex-3 | N1 AN-FOURIER: Gevrey cutoff χ₀, time-Fourier norms | `w/an-fourier`: 6 min ago | [brief](docs/campaign/briefs/AN-FOURIER.md) |
| wt-l2s | GPT-6.1-Sol low / codex-3 | WKE-L2S: general-d L²_s trilinear estimate (Theorem 7), wkelwp blow-up conjunct | `w/wke-l2s`: 4 min ago, 1 unlanded | [brief](docs/campaign/briefs/WKE-L2S.md) |
<!-- /AUTO:workers -->

## Papers

| key | reference |
|---|---|
| target | Y. Deng, Z. Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082 |
| DH21 | Y. Deng, Z. Hani, *Full derivation of the wave kinetic equation*, Invent. Math. 233 (2023) 543–724, arXiv:2104.11204 |
| DH21-2 | Y. Deng, Z. Hani, *Propagation of chaos and higher order statistics in wave kinetic theory*, JEMS, arXiv:2110.04565 |
| DH23 | Y. Deng, Z. Hani, *Derivation of the wave kinetic equation: full range of scaling laws*, arXiv:2301.07063 |
| DH19 | Y. Deng, Z. Hani, *On the derivation of the wave kinetic equation for NLS*, Forum Math. Pi 9 (2021) e6, arXiv:1912.09518 |
| GIT20 | P. Germain, A. Ionescu, M.-B. Tran, *Optimal local well-posedness theory for the kinetic wave equation*, J. Funct. Anal. (2020), arXiv:1711.05587 |

## Documents

- [docs/DECISIONS.md](docs/DECISIONS.md) — rulings.
- [docs/FINDINGS.md](docs/FINDINGS.md) — source findings and candidate errata.
- [docs/campaign/PLAN.md](docs/campaign/PLAN.md) — phases, infrastructure packets, fleet.
- [docs/blueprint/GRAPH.md](docs/blueprint/GRAPH.md) — node-level dependency graph (v2: 275 nodes, 84 packets, ≈273k lines est.); [docs/blueprint/WAVE-B.md](docs/blueprint/WAVE-B.md) — Wave B proposal.
- [docs/THIRD-PARTY.md](docs/THIRD-PARTY.md) — third-party code (Apache 2.0, attributed).
- [docs/campaign/orch/](docs/campaign/orch/) — independent audits (Wave A, freeze check, figure-only definitions, topology review, infrastructure review).
