# WaveTurbulence-dev — campaign HQ

Lean 4 formalization of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024).

<!-- AUTO:updated -->
> **Last updated: 2026-11-05 03:23 UTC** · **estimated completion 86.0 %** (Lean proofs 87.4 %) · frozen theorems sealed: 14 / 26 (+ 296 frozen definitions) · **257,400 lines of Lean on main** (2770 files) + 38,731 unlanded on worker branches · blueprint estimate ≈ 273,000 lines
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
### Estimated completion: **86.0 %**

`██████████████████████████░░░░` 86.0 %

| Part of the project | Items | Weight | Done | Completion |
|---|---|---|---|---|
| Sources, paper maps, blueprint (P0–P1) | 1 | 30 | 27.0 | `█████████░` 90 % |
| Exact Lean statements, frozen (P2) | 1 | 20 | 18.4 | `█████████░` 92 % |
| Lean proofs (P4) | 85 | 681 | 604.2 | `█████████░` 89 % |
| Frozen theorems sealed | 26 | 26 | 14.0 | `█████░░░░░` 54 % |
| Release (P5) | 1 | 15 | 0.0 | `░░░░░░░░░░` 0 % |
| **Total** | | 772 | 663.6 | **86.0 %** |

Lean lines: 257,400 on main + 38,731 on branches, of ≈ 273,000 estimated by the blueprint (`████████████████████` 108.5 % of the estimate).

<details><summary>All Lean work packets (blueprint §E) with weight and status</summary>

| Packet | Name | Weight | Lines (est.) | Done | Note |
|---|---|---|---|---|---|
| B1 | NLS-A | 6 | ≈1,600 | ✅ 100 % | landed: Fourier equation, mass, reduction |
| B2 | NLS-B | 9 | ≈3,200 | ✅ 100 % | done: LWP/persistence, inverse reduction, uniqueness; NLS bridge helpers landed (4639fe2) |
| B3 | NLS-C | 10 | ≈3,000 | ✅ 100 % | done: nlsAkBridge (all 4 conjuncts) proved at the exact snapshot-5 type (scratch, wt-l2s); moves to Foundations at the Wave B freeze |
| D3 | CANON | 9 | ≈3,950 | ✅ 100 % | CANON: canonicalCharacterization sealed and second-key audited PROVED (audits/SEAL-B1-second-key.md) |
| J1 | BCOEF | 7 | ≈3,800 | ✅ 100 % | done: time coefficients, class J/R operators, DH21 Lemmas 5.3-5.5 |
| J2 | CLASSJR2 | 8 | ≈4,000 | ✅ 100 % | done: DH21 Lemmas 5.6-5.10 (legal-partition induction, ≤ 2^m expansion); sign F61 open (traced in J3) |
| J3 | MAINCOEF | 4 | ≈3,000 | ✅ 100 % | MAINCOEF done: DH21 Prop 5.1 for couples and trees (DH23 weights), garden↔code B̃ bridge |
| J4 | CANCEL7 | 6 | ≈3,400 | ✅ 100 % | CANCEL7 done with the F61 correction; BtRec discharged by the B̃ bridge |
| L1 | PL1A | 7 | ≈2,800 | ✅ 100 % | done: B2.2 incoherentDecay proved at the exact type (INCOH-INST, e77e692); seals at the B2 freeze |
| L2 | PL1B | 9 | ≈4,650 | ✅ 100 % | PL1 done: abstract TARGET Prop 5.1 incl. one-clock case (541d4c8); garden instantiation = INCOH-INST |
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
| V1 | SUMINT-A | 7 | ≈4,200 | ✅ 100 % | sumint (B1.6) proved at the exact snapshot-8 type (wt-anfourier, 436 axiom checks); seals at the freeze |
| V2 | SUMINT-B | 5 | ≈2,200 | ✅ 100 % | sumint (B1.6) proved at the exact snapshot-8 type (wt-anfourier, 436 axiom checks); seals at the freeze |
| WA | Wave A definitions | 5 | ≈230 | ✅ 100 % | frozen D6 |
| X3 | FIXEDPT | 9 | ≈3,400 | ✅ 100 % | FIXEDPT closed: fixedpoint_of_closed_gates from B1.12, B1.2, B1.5 only (O-X2-EXP, O-X3-CPL proved) |
| L3 | PL23 | 4 | ≈1,700 | 🟡 98 % | PL23: Props 6.1 (now at the literal 30d norm, PL23-30D) and 6.2 proved; leafwise B2.1 and B2.2 proved (RA1-LEAFWISE, INCOH-LEAFWISE) |
| RA1 | REGASYMP | 10 | ≈5,800 | 🟡 98 % | RA1 done: couples and trees on snapshot 9, plus the leafwise version for per-leaf profiles (RA1-LEAFWISE) |
| G5 | APPB-ALG | 8 | ≈4,000 | 🟡 97 % | APPB-ALG READY: DH23 Prop 10.2 in full (dh23_prop_10_2), fresh 809-module rebuild; GraphOk size deviation recorded |
| I1 | INDUCT-A | 10 | ≈4,000 | 🟡 95 % | INDUCT done in scratch: propansatz_of_gates (from layergarden, fixedpoint, wkeTaylor; 465 modules); port to frozen names after the freeze |
| I2 | INDUCT-B | 10 | ≈3,050 | 🟡 95 % | INDUCT done (see I1) |
| J5 | MEXP | 6 | ≈2,700 | 🟡 95 % | MEXP done: DH21 Props 7.7, 7.8 (corrected weight) |
| J6 | WKE-ID | 6 | ≈2,800 | 🟡 95 % | WKE-ID done: Σ app = 𝒰_n (wke_identity), B2.1 item (4) proved; route avoids DH21 7.9/7.10 |
| J7 | REGCANCEL | 4 | ≈2,000 | 🟡 95 % | REGCANCEL done: DH23 Prop 6.3 (statement form chosen over B2 objects, to audit) |
| M8 | LAYERCNT | 6 | ≈2,100 | 🟡 95 % | LAYERCNT READY: layerlad, layervine (incl. the improved coherent bound) under TARGET's hypotheses; rebase onto the canonical universe pending |
| S3 | LADDER | 8 | ≈4,200 | 🟡 95 % | LADDER: all three spine inputs proved (LadderFourierAt, LadderDecayAt, CoarseSplicedAt); TARGET L2079 gap fixed (errata E5); snapshot-9 rebase pending |
| V4 | VINEEST-S2 | 4 | ≈2,500 | 🟡 95 % | VINEEST-S2 done: vineChain_eq_sumintForm (V4 endpoint, ruling R2), 709-module snapshot-9 rebuild OK; obligations VINEPARAM, SumintSigned |
| X1 | FLOWER-DEF | 10 | ≈3,100 | 🟡 95 % | FLOWER-DEF done in scratch: classes, kernels, identities, O-FK; B1.12 final (audited, F1/F2 applied) proposed for the freeze |
| Z1 | MAIN | 3 | ≈860 | 🟡 95 % | main ⇐ layergarden (B1.2) + layergardenFlower (B1.12) only: all other gates proved (nlsAkBridge, wkeTaylor, propansatz_of_gates, fixedpoint_of_closed_gates) |
| C1 | REG-STRUCT | 11 | ≈4,000 | 🟡 90 % | REG-STRUCT done in scratch: structure theorem with uniqueness, decoding, legal/dominant chains, counts (C₀=12^9); F55 |
| C2 | LINKS | 11 | ≈3,000 | 🟡 90 % | LINKS done in scratch: branchpair, defchoice, linkXY, deflink, defcoh, auxlem, explem, treelemma, incohproof1 (couples); F62-F65 |
| C3 | SKELETON | 15 | ≈5,200 | 🟡 90 % | SKELETON done in scratch: prime skeletons with uniqueness (incl. DH21's omitted E4 argument), 194 declarations |
| C4 | LAYERREG | 8 | ≈4,000 | 🟡 90 % | LAYERREG done in scratch: TARGET Props 4.9 (structure, replacement keeps canonicity) and 4.10 (layering count, stronger) |
| C5 | ENHANCED | 9 | ≈3,150 | 🟡 90 % | ENHANCED done in scratch: dominant couples, special sets, equivalence (DH21 Def 4.18), encoded trees (Props 4.20, 4.23), net signs; + tree incohproof1 |
| D1 | COMB-CORE | 8 | ≈2,020 | 🟡 90 % | COMB-CORE done in scratch; ports at the freeze |
| D2 | SYS-DEFS | 14 | ≈3,400 | 🟡 90 % | SYS-DEFS + Duhamel identity done in scratch; ports at the freeze |
| D4 | REG-DEFS | 8 | ≈2,400 | 🟡 90 % | REG-DEFS done (B2 draft + REG-STRUCT scratch) |
| G0 | MOLE-COUNT-BASICS | 4 | ≈1,400 | 🟡 90 % | DEGEN done in scratch (DH21 Lemmas 9.13–9.14, DH23 §10.5, GAP.degenerate.tame, corrected remtame); moves to Foundations after the Wave B freeze |
| G4 | APPB-OPS | 8 | ≈4,000 | 🟡 90 % | APPB-OPS done in scratch: DH23 App B operations, 73 audited results; figure transcriptions flagged for review; F81 |
| G6 | MOLEPROP13 | 6 | ≈2,400 | 🟡 90 % | MOLEPROP13 done in scratch: DH23 Props 10.1, 10.3 (263 modules, against corrected B2) |
| G7 | MOLEPROP4 | 12 | ≈4,500 | 🟡 90 % | MOLEPROP4 done in scratch (moleprop4-t): DH23 Prop 10.4(2)' + THEOREM-A via named inputs (wt-torus) |
| L4 | PL4 | 4 | ≈2,500 | 🟡 90 % | PL4 done: kernel conjugation and Prop 6.3(iii) realness; app halves of (i)/(ii) a separate unconsumed node (ruling R1) |
| M1 | MOLE | 15 | ≈4,900 | 🟡 90 % | MOLE done in scratch: garden molecules, root-compatible decorations, reconstruction (C₀=20736), cuts; moves to Foundations at the freeze |
| M2 | BLOCKS | 6 | ≈1,600 | 🟡 90 % | blocks, hyper-blocks, realizations, overlap classification (connected convention, F57) in scratch |
| M3 | CLCN | 10 | ≈3,500 | 🟡 90 % | CLCN done in scratch: (CL)/(CN) dichotomy, splicing, blockchainprop, cnblock component bounds |
| M4 | VINES | 10 | ≈3,300 | 🟡 90 % | VINES done in scratch: templates incl. m = 1 vine (II) (F72), groups/coherence, subsetvc, VC/HVC/DV/HV (F71 reading), 358 declarations |
| M5 | MOLECPL | 4 | ≈1,500 | 🟡 90 % | MOLECPL done in scratch (DH23 Prop 5.3 for gardens; 2eacfc5) |
| M6 | TWIST | 8 | ≈2,800 | 🟡 90 % | TWIST done in scratch: twist involution, invariances, sign cancellation, 2^r gardens (287 modules) |
| M9 | VINEPARAM | 4 | ≈1,500 | 🟡 90 % | VINEPARAM: parametrization contract proved (538 certificates + rung-insertion induction); grouped charts match TARGET cohmol groups (vineparam_grouped) |
| RA2 | REGREF | 13 | ≈4,100 | 🟡 90 % | REGREF done: B2.1 regularAsymptotics proved at exact type from RA1Couple/RA1Tree (trace argument F76; leafwise kernel layer) |
| S2a | REDSPLICE-DEF | 2 | ≈800 | 🟡 90 % | REDSPLICE-DEF READY: the full Stage 1 construction (units, cover, C1 objects, gap specification, hinge pairs, gsk/bsk from the original garden); stage1PieceOf with Sound proved except the subpro obligation (S4) |
| V3 | REGRED | 6 | ≈1,900 | 🟡 90 % | REGRED done in scratch: skeleton reduction, vineest Step 1 (ab8680f); nonzero-gap boundary case separate (F21) |
| X2 | FLOWEREST | 16 | ≈8,900 | 🟡 90 % | FLOWEREST on the canonical universe: layergardenFlower_of_spine and layergardenFlower_v2_of_spine type-check against snapshot-9 B1.12 and the D10 successor; regular L0 leg proved (FLOWER-REG); flower Stage 1 gates and Dirac-root couples pending (S2a/S2/S4) |
| G2 | EXCESS-DH23 | 8 | ≈3,500 | 🟡 80 % | EXCESS-DH23 + VINE-COUNT: DH23 Prop 9.4 single cuts, triangles, single vines, hyper objects and double bonds (prop94_vine_all) with the source ladder-gap form; assembly in G3's excessprop1 |
| M7 | LFTWIST | 13 | ≈4,200 | 🟡 80 % | LFTWIST: unit and family lftwistprop proved in scratch; fresh closure rebuild ordered; port to the canonical universe (R8) pending |
| F2 | PLG | 12 | ≈4,150 | 🟡 70 % | PLG = LG-SPINE on the canonical universe: layergarden_of_spine (fresh 419-module rebuild) type-checks against snapshot-9 B1.2, and layergarden_v2_of_spine against the D10 successor; Stage 1 inputs pending |
| S1 | STAGE1-COMB | 7 | ≈2,400 | 🟡 65 % | STAGE1-COMB: vinechainlem; twist reversal/composition both choices; congruence symmetric; V-family invariant under twists; transitivity reduced to commutation (in progress) |
| G8 | RIGID | 10 | ≈4,600 | 🟡 60 % | RIGID: DH23 Prop 9.6 (gamma > 1/2) stated exactly; Prop 10.1' (off-protected-set), cycles, rough bound, cases (1)-(3) proved; even cases (4)-(6) in progress |
| V5 | VINEEST | 13 | ≈5,100 | 🟡 55 % | VINEEST: Step 3 engine, SumintSigned, degenerate decorations (errata E4); Step 3 statement ported to the canonical universe (422 modules); clauses (a)-(e) in progress; Step 4 (twists) next |
| G3 | EXCESS-T | 10 | ≈3,500 | 🟡 50 % | FINALMOL: DH23 Prop 9.5 assembled (HRun.prop95: cycles, chains, N1, N2, noBetaCut); final-shape mapping to Prop 9.6 proved except vine_LG; excessprop1 and remtame (errata E9) in progress |
| F1 | FINAL-RED | 4 | ≈1,200 | 🟡 30 % | FINAL-RED: finalsbest1/finalsbest2 consumed in LG-SPINE's assembly (counting cover, finalproof numerics) proved generically |
| F3 | FINAL-COUNT | 4 | ≈900 | 🟡 20 % | FINAL-COUNT: FinalCountGate stated (lg-spine); gamma > 1/2 chain: Props 9.4 (G2), 9.5 (G3), 9.6 (G8) in progress |
| G1 | STAGE2-DEF | 10 | ≈2,600 | 🟡 20 % | STAGE2-DEF: stage-2 operation datatype (Stage2Op) and TARGET's counting problem (lg-spine CountingChoices) defined |
| S2 | REDSPLICE | 6 | ≈2,400 | 🟡 10 % | REPRESENTS: redvine -> redvine2/3 for the S2a pieces; started (consumes V5 vineest and S1 congruence) |
| S4 | SUBPRO | 8 | ≈3,000 | 🟡 10 % | SUBPRO: TARGET Prop subpro (a)-(f) for the S2a construction; started |

</details>

Done fractions last reviewed: **2026-11-05 02:20 UTC**. Source: [`docs/campaign/progress.json`](docs/campaign/progress.json); history: [`docs/campaign/history.csv`](docs/campaign/history.csv).
<!-- /AUTO:progress -->

## Workers

<!-- AUTO:workers -->
| tmux | model / account | packet | branch: last commit | brief |
|---|---|---|---|---|
| wt-orch | Claude Opus / claude-1 | Task 34: snapshot-8 delta audit + freeze branch rebuild; done: letter draft, many audits | `w/orch`: 14 min ago, 56 unlanded | [brief](docs/campaign/orch/TASK4.md) |
| wt-gauss-hc | Claude Opus / claude-10 | FLOWER-SPINE: B1.12 layergardenFlower from named spine inputs (X2, X3 closed: fixedpoint from B1.12+B1.2+B1.5) | `w/waveb-infra`: — | [brief](docs/campaign/briefs/FLOWER-SPINE.md) |
| wt-torus | Claude Opus / claude-14 | G7 MOLEPROP4 (revived, repaired): DH23 ylem1′, ylem2, Prop 10.4 (A23-HALF done) | `w/approxnt`: 15 h ago | [brief](docs/campaign/briefs/MOLEPROP4.md) |
| wt-wke | Claude Opus / claude-13 | L3+L4: TARGET Props 6.1-6.3 (proplayer2-4); J1-J3, B̃ bridge, tree Prop 5.1 done | `w/jr-ops`: 15 h ago | [brief](docs/campaign/briefs/PL234.md) |
| wt-cumul | GPT-6.1-Sol low / codex-2 | LG-SPINE (pre-freeze): layergarden from named spine inputs (INDUCT, WKETAYLOR-GATE done) | `w/norm-bridge`: 22 h ago | [brief](docs/campaign/briefs/LG-SPINE.md) |
| wt-nt | GPT-6.1-Sol low / codex-2 | G4 APPB-OPS then G5 APPB-ALG (pre-freeze): DH23 Appendix B (MOLE M1+M2, CLCN M3 done) | `w/nt-circle`: 11 h ago | [brief](docs/campaign/briefs/APPB-OPS.md) |
| wt-ansob | GPT-6.1-Sol low / codex-2 | RA1 couples (RA1Couple): DH23 Prop 6.1 for couples; trees moved to wt-l2s | `w/bproc`: 12 h ago, 11 unlanded | [brief](docs/campaign/briefs/REGASYMP.md) |
| wt-gausssum | GPT-6.1-Sol low / codex-2 | M9 VINEPARAM (pre-freeze): molecule-level vine parametrizations (M4 VINES done) | `w/count`: 10 h ago, 11 unlanded | [brief](docs/campaign/briefs/VINES.md) |
| wt-resonant | GPT-6.1-Sol low / codex-2 | V4 VINEEST-S2 (pre-freeze): vineest Step 2 into sumint form (V3 REGRED done) | `w/resonant`: 16 h ago | [brief](docs/campaign/briefs/VINEEST-S2.md) |
| wt-anfourier | GPT-6.1-Sol low / codex-2 | M7 LFTWIST (pre-freeze); M5 MOLECPL, M6 TWIST, SUMINT done | `w/an-phase`: 29 h ago | [brief](docs/campaign/briefs/LFTWIST.md) |
| wt-l2s | GPT-6.1-Sol low / codex-2 | RA1-TREES: DH23 Prop 6.1 for trees (RA1Tree); INCOH-INST done: B2.2 proved at exact type | `w/wke-l2s`: 9 h ago, 23 unlanded | [brief](docs/campaign/briefs/RA1-TREES.md) |
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
