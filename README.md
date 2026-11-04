# WaveTurbulence-dev — campaign HQ

Lean 4 formalization of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024).

<!-- AUTO:updated -->
> **Last updated: 2026-11-04 00:40 UTC** · **estimated completion 43.5 %** (Lean proofs 41.7 %) · frozen theorems sealed: 1 / 2 (+ 13 frozen definitions) · **130,634 lines of Lean on main** (1191 files) + 6,383 unlanded on worker branches · blueprint estimate ≈ 273,000 lines
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
### Estimated completion: **43.5 %**

`█████████████░░░░░░░░░░░░░░░░░` 43.5 %

| Part of the project | Items | Weight | Done | Completion |
|---|---|---|---|---|
| Sources, paper maps, blueprint (P0–P1) | 1 | 30 | 27.0 | `█████████░` 90 % |
| Exact Lean statements, frozen (P2) | 1 | 20 | 14.0 | `███████░░░` 70 % |
| Lean proofs (P4) | 85 | 681 | 283.6 | `████░░░░░░` 42 % |
| Frozen theorems sealed | 2 | 2 | 1.0 | `█████░░░░░` 50 % |
| Release (P5) | 1 | 15 | 0.0 | `░░░░░░░░░░` 0 % |
| **Total** | | 748 | 325.6 | **43.5 %** |

Lean lines: 130,634 on main + 6,383 on branches, of ≈ 273,000 estimated by the blueprint (`██████████░░░░░░░░░░` 50.2 % of the estimate).

<details><summary>All Lean work packets (blueprint §E) with weight and status</summary>

| Packet | Name | Weight | Lines (est.) | Done | Note |
|---|---|---|---|---|---|
| B1 | NLS-A | 6 | ≈1,600 | ✅ 100 % | landed: Fourier equation, mass, reduction |
| B2 | NLS-B | 9 | ≈3,200 | ✅ 100 % | done: LWP/persistence, inverse reduction, uniqueness; NLS bridge helpers landed (4639fe2) |
| B3 | NLS-C | 10 | ≈3,000 | ✅ 100 % | done: nlsAkBridge (all 4 conjuncts) proved at the exact snapshot-5 type (scratch, wt-l2s); moves to Foundations at the Wave B freeze |
| J1 | BCOEF | 7 | ≈3,800 | ✅ 100 % | done: time coefficients, class J/R operators, DH21 Lemmas 5.3-5.5 |
| J2 | CLASSJR2 | 8 | ≈4,000 | ✅ 100 % | done: DH21 Lemmas 5.6-5.10 (legal-partition induction, ≤ 2^m expansion); sign F61 open (traced in J3) |
| N1 | AN-FOURIER | 9 | ≈3,500 | ✅ 100 % | landed: χ₀ (Gevrey 2, F41), 𝔛 norms, restriction norms, Fourier-L¹ products |
| N2 | AN-PHASE | 5 | ≈1,700 | ✅ 100 % | landed: Poisson on ℤ_L^d, non-stationary and bilinear stationary phase |
| N3 | AN-HY | 10 | ≈4,500 | ✅ 100 % | done: Hausdorff–Young, phase/time-integral bounds (TARGET A.2, A.3) |
| N4 | AN-SOB | 7 | ≈2,700 | ✅ 100 % | landed: Sobolev variants, (10.5), simplex volumes, DH21 L10.2 |
| N5 | RESONANT | 6 | ≈2,800 | ✅ 100 % | landed: resonant measure, p.v. 1/Ω, DH21 Lemma 6.3 |
| NT-EXPSUM | NT-EXPSUM | 14 | ≈5,300 | ✅ 100 % | landed: circle discrepancy + annulus with exponent 27/41 (B-process, pair (11/30,16/30)); F3 resolved |
| NT1 | GAUSSSUM | 5 | ≈2,100 | ✅ 100 % | landed 59220dc: Dirichlet, sharp interval and log-free smooth Gauss sum bounds |
| NT10 | LEMLIN | 4 | ≈1,500 | ✅ 100 % | landed: lemlin (+F23 second bound), lemcubic0 |
| NT11 | LEMCUBIC | 6 | ≈3,000 | ✅ 100 % | landed: TARGET lemcubic (quadExpSum3 drafted form) |
| NT2 | HUA | 8 | ≈3,500 | ✅ 100 % | landed: Hua L⁴/L⁶, Weyl reduction, L^{3d/2} moments |
| NT3 | MINOR1 | 6 | ≈2,000 | ✅ 100 % | landed: DH23 6.6(1), three-vector count |
| NT4 | MINOR2 | 5 | ≈3,200 | ✅ 100 % | landed: DH23 6.6(2), TARGET Lemma 5.3 (quadExpSum2 drafted form) |
| NT5 | NTSP | 8 | ≈4,300 | ✅ 100 % | landed: TARGET 5.2, DH23 6.5, 6.7 |
| NT6 | APPROXNT | 12 | ≈6,200 | ✅ 100 % | done: DH23 Prop 6.4 with the large-order extension (F33, F54) |
| NT7 | COUNT0 | 7 | ≈3,050 | ✅ 100 % | done: countLemma_bound exactly the audited B1.7 draft (landed f56f6bb) |
| NT8 | COUNT | 7 | ≈3,800 | ✅ 100 % | done: atomCountLemma_bound exactly the audited B1.8 draft + DH23 A.2(2) (landed f56f6bb) |
| NT9 | LINALG | 4 | ≈1,400 | ✅ 100 % | landed: TARGET Lemmas A.6, A.7 (MISC-A) |
| R-CUMUL | CUMUL | 13 | ≈3,560 | ✅ 100 % | landed fea3516 |
| R-GAUSS | GAUSS-HC | 4 | ≈2,500 | ✅ 100 % | landed f986d35 (off-route, F34) |
| R-NTC | NT-CIRCLE | 6 | ≈3,300 | ✅ 100 % | landed: circle 2/3, elementary annulus, estcross |
| R-TF | TORUS-FOURIER | 4 | ≈2,500 | ✅ 100 % | landed 5beb902 |
| R-WKE | WKE | 24 | ≈9,810 | ✅ 100 % | done: WKE LWP, uniqueness, Taylor, general-d L²_s trilinear estimate (Theorem 7), blow-up; frozen wkelwp SEALED 2026-11-03 |
| WA | Wave A definitions | 5 | ≈230 | ✅ 100 % | frozen D6 |
| X1 | FLOWER-DEF | 10 | ≈3,100 | 🟡 95 % | FLOWER-DEF done in scratch: classes, kernels, identities, O-FK; B1.12 final (audited, F1/F2 applied) proposed for the freeze |
| G0 | MOLE-COUNT-BASICS | 4 | ≈1,400 | 🟡 90 % | DEGEN done in scratch (DH21 Lemmas 9.13–9.14, DH23 §10.5, GAP.degenerate.tame, corrected remtame); moves to Foundations after the Wave B freeze |
| M1 | MOLE | 15 | ≈4,900 | 🟡 90 % | MOLE done in scratch: garden molecules, root-compatible decorations, reconstruction (C₀=20736), cuts; moves to Foundations at the freeze |
| M2 | BLOCKS | 6 | ≈1,600 | 🟡 90 % | blocks, hyper-blocks, realizations, overlap classification (connected convention, F57) in scratch |
| D3 | CANON | 9 | ≈3,950 | 🟡 80 % | canonicalCharacterization proved (scratch, pre-freeze) |
| Z1 | MAIN | 3 | ≈860 | 🟡 80 % | main proved from propansatz + nlsAkBridge; nlsAkBridge now proved (scratch) — main rests on propansatz alone |
| D1 | COMB-CORE | 8 | ≈2,020 | 🟡 60 % | COMB-CORE API done (scratch, pre-freeze) |
| D2 | SYS-DEFS | 14 | ≈3,400 | 🟡 50 % | SYS-DEFS API + Duhamel identity (scratch) |
| D4 | REG-DEFS | 8 | ≈2,400 | 🟡 30 % | REG-STRUCT in progress (scratch) |
| X2 | FLOWEREST | 16 | ≈8,900 | 🟡 25 % | X2 moment layer done in scratch (flowerest1/flowerest2 from B1.12, conditional on the named obligation O-X2-EXP = INDUCT graft bijection) |
| C1 | REG-STRUCT | 11 | ≈4,000 | 🟡 15 % | REG-STRUCT in progress |
| I1 | INDUCT-A | 10 | ≈4,000 | 🟡 15 % | INDUCT started (scratch) |
| I2 | INDUCT-B | 10 | ≈3,050 | 🟡 10 % | INDUCT |
| J3 | MAINCOEF | 4 | ≈3,000 | 🟡 5 % | MAINCOEF started (wt-wke): DH21 Prop 5.1 with DH23 weights |
| X3 | FIXEDPT | 9 | ≈3,400 | 🟡 5 % | FIXEDPT started (wt-gauss-hc, /home/scott/wt-scratch/fixedpt) |
| C2 | LINKS | 11 | ≈3,000 | ⬜ 0 % |  |
| C3 | SKELETON | 15 | ≈5,200 | ⬜ 0 % |  |
| C4 | LAYERREG | 8 | ≈4,000 | ⬜ 0 % |  |
| C5 | ENHANCED | 9 | ≈3,150 | ⬜ 0 % |  |
| F1 | FINAL-RED | 4 | ≈1,200 | ⬜ 0 % |  |
| F2 | PLG | 12 | ≈4,150 | ⬜ 0 % |  |
| F3 | FINAL-COUNT | 4 | ≈900 | ⬜ 0 % |  |
| G1 | STAGE2-DEF | 10 | ≈2,600 | ⬜ 0 % |  |
| G2 | EXCESS-DH23 | 8 | ≈3,500 | ⬜ 0 % |  |
| G3 | EXCESS-T | 10 | ≈3,500 | ⬜ 0 % |  |
| G4 | APPB-OPS | 8 | ≈4,000 | ⬜ 0 % |  |
| G5 | APPB-ALG | 8 | ≈4,000 | ⬜ 0 % |  |
| G6 | MOLEPROP13 | 6 | ≈2,400 | ⬜ 0 % |  |
| G7 | MOLEPROP4 | 12 | ≈4,500 | ⬜ 0 % |  |
| G8 | RIGID | 10 | ≈4,600 | ⬜ 0 % |  |
| J4 | CANCEL7 | 6 | ≈3,400 | ⬜ 0 % |  |
| J5 | MEXP | 6 | ≈2,700 | ⬜ 0 % |  |
| J6 | WKE-ID | 6 | ≈2,800 | ⬜ 0 % |  |
| J7 | REGCANCEL | 4 | ≈2,000 | ⬜ 0 % |  |
| L1 | PL1A | 7 | ≈2,800 | ⬜ 0 % |  |
| L2 | PL1B | 9 | ≈4,650 | ⬜ 0 % |  |
| L3 | PL23 | 4 | ≈1,700 | ⬜ 0 % |  |
| L4 | PL4 | 4 | ≈2,500 | ⬜ 0 % |  |
| M3 | CLCN | 10 | ≈3,500 | ⬜ 0 % |  |
| M4 | VINES | 10 | ≈3,300 | ⬜ 0 % |  |
| M5 | MOLECPL | 4 | ≈1,500 | ⬜ 0 % |  |
| M6 | TWIST | 8 | ≈2,800 | ⬜ 0 % |  |
| M7 | LFTWIST | 13 | ≈4,200 | ⬜ 0 % |  |
| M8 | LAYERCNT | 6 | ≈2,100 | ⬜ 0 % |  |
| M9 | VINEPARAM | 4 | ≈1,500 | ⬜ 0 % |  |
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

</details>

Done fractions last reviewed: **2026-11-04 02:25 UTC**. Source: [`docs/campaign/progress.json`](docs/campaign/progress.json); history: [`docs/campaign/history.csv`](docs/campaign/history.csv).
<!-- /AUTO:progress -->

## Workers

<!-- AUTO:workers -->
| tmux | model / account | packet | branch: last commit | brief |
|---|---|---|---|---|
| wt-orch | Claude Opus / claude-1 | Task 19: apply B2 draft fixes (F57 GroupConnected, F58, F59, R15-1/R15-2); done: snapshot-6 audit PASS, MOLE/COUNT/JR-OPS/NLS-BRIDGE/APPROXNT audits | `w/orch`: 3 min ago | [brief](docs/campaign/orch/TASK4.md) |
| wt-gauss-hc | Claude Opus / claude-10 | X2 moment expansion (flowerest1 probabilistic part), then X3 FIXEDPT (pre-freeze); X1 FLOWER, B1.12 final, B2 ladder fix done | `w/waveb-infra`: — | [brief](docs/campaign/briefs/FLOWER.md) |
| wt-torus | Claude Opus / claude-14 | C2 LINKS (pre-freeze): links, coherence, auxlem, treelemma (APPROXNT done) | `w/approxnt`: 0 min ago, 1 unlanded | [brief](docs/campaign/briefs/LINKS.md) |
| wt-wke | Claude Opus / claude-13 | J2 rest (DH21 Lemmas 5.9-5.10) then J3 MAINCOEF (DH21 Prop 5.1); JR-OPS 5.3-5.8 done | `w/jr-ops`: 9 min ago | [brief](docs/campaign/briefs/JR2-MAINCOEF.md) |
| wt-cumul | GPT-6.1-Sol low / codex-3 | I1+I2 INDUCT (pre-freeze, conditional): propansatz from layergarden/fixedpoint/wkeTaylor; main assembly done | `w/norm-bridge`: 4 h ago | [brief](docs/campaign/briefs/INDUCT.md) |
| wt-nt | GPT-6.1-Sol low / codex-3 | M3 CLCN (pre-freeze): (CL)/(CN), blockchainprop, cnblock (MOLE M1+M2 done) | `w/nt-circle`: 33 min ago | [brief](docs/campaign/briefs/CLCN.md) |
| wt-ansob | GPT-6.1-Sol low / codex-3 | G6 MOLEPROP13 (pre-freeze): DH23 Props 10.1, 10.3, then G4 APPB-OPS (DEGEN done) | `w/bproc`: 103 min ago | [brief](docs/campaign/briefs/MOLEPROP13.md) |
| wt-gausssum | GPT-6.1-Sol low / codex-3 | M4 VINES (pre-freeze), then M9 VINEPARAM (COUNT done, landed) | `w/count`: 25 min ago, 4 unlanded | [brief](docs/campaign/briefs/VINES.md) |
| wt-resonant | GPT-6.1-Sol low / codex-3 | D4+C1 REG-STRUCT (pre-freeze): regular chains, DH21 Props 4.5–4.10, structure theorem, counting (COMB-CORE done in scratch) | `w/resonant`: 5 h ago | [brief](docs/campaign/briefs/REG-STRUCT.md) |
| wt-anfourier | GPT-6.1-Sol low / codex-3 | V1+V2 SUMINT (pre-freeze): prove the Wave B statement sumint (N2+N3 done) | `w/an-phase`: 2 h ago | [brief](docs/campaign/briefs/SUMINT.md) |
| wt-l2s | GPT-6.1-Sol low / codex-3 | L1+L2 PL1: TARGET Prop 5.1 proplayer1 (NLS-BRIDGE done: nlsAkBridge proved) | `w/wke-l2s`: 1 min ago, 43 unlanded | [brief](docs/campaign/briefs/PL1.md) |
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
