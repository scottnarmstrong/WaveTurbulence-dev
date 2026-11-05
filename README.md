# WaveTurbulence-dev — campaign HQ

Lean 4 formalization of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024).

<!-- AUTO:updated -->
> **Last updated: 2026-11-05 23:53 UTC** · **estimated completion 90.5 %** (Lean proofs 92.4 %) · frozen theorems sealed: 16 / 26 (+ 296 frozen definitions) · **443,222 lines of Lean on main** (4828 files) + 61,549 unlanded on worker branches · blueprint estimate ≈ 273,000 lines
<!-- /AUTO:updated -->

**Scope (D1):** everything proved in Lean, no black boxes. That covers the target paper and the results it uses from
Deng–Hani's earlier papers (DH21, DH23, parts of DH21-2 and DH19), the trilinear estimates of Germain–Ionescu–Tran
(GIT20), smooth-solution theory for cubic NLS on the torus, and the Gaussian/cumulant facts.
**Main theorem (D2):** Theorem 1.1 for `0 < γ < 1` on the square torus `[0,L]^d`, `d ≥ 3`.

## Status

**Phase:** P4 proof assembly and integration; P2 anchors are frozen. The pinned source theorem covers
`0 < γ < 1`. Under D9–D11, the active chain uses the approved `1/2 < γ < 1` successors; the `γ ≤ 1/2`
extension follows after that chain is sealed. See [erratum E1](docs/ERRATA-AND-DEVIATIONS.md).

**Exact closure:** 16/26 theorem anchors sealed; 10 draft theorem anchors; 296 frozen definitions.
Batch 2b landed as `675cf6c`, including `regularAsymptotics_v1`. The weighted meter below is an estimate of work
completed; it is not the percentage of theorem statements proved. Scratch and conditional helpers remain partial
until integrated, checked against the frozen exports, and independently audited.

**Current work:** Codex directs Terra-medium work on the VINEEST separated-family producer, integration of six
analytic spine packets, and an independent review of that integration. New scratch checkpoints include a modulated
Step-3 base estimate and loop-label/counting lemmas. The combined provider port is still being repaired and checked.
Remaining assemblies include the low-degree counting chain, vine Stage-1 reduction, flower Stage-1, and the final
spine instances. See the [current handover](docs/campaign/orch/CODEX-HANDOFF.md); earlier fleet history is preserved
in [SONNET-FLEET.md](docs/campaign/orch/SONNET-FLEET.md).

**Blueprint v2:** 275 nodes, 84 packets, approximately 273k lines estimated. **F32 resolved:** the general-d
trilinear estimate and WKE local well-posedness were proved; `wkelwp` is sealed.

```text
DRAFT_ANCHORS: 10
  WaveTurbulence/Frozen/Theorems/Main.lean
  WaveTurbulence/Frozen/Theorems/Fixedpoint.lean
  WaveTurbulence/Frozen/Theorems/Layergarden.lean
  WaveTurbulence/Frozen/Theorems/LayergardenFlower.lean
  WaveTurbulence/Frozen/Theorems/Propansatz.lean
  WaveTurbulence/Frozen/Theorems/MainV2.lean
  WaveTurbulence/Frozen/Theorems/PropansatzV2.lean
  WaveTurbulence/Frozen/Theorems/LayergardenV2.lean
  WaveTurbulence/Frozen/Theorems/FixedpointV2.lean
  WaveTurbulence/Frozen/Theorems/LayergardenFlowerV2.lean
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED_THIS_TURN: 0
```

## Progress

<!-- AUTO:progress -->
### Estimated completion: **90.5 %**

`███████████████████████████░░░` 90.5 %

| Part of the project | Items | Weight | Done | Completion |
|---|---|---|---|---|
| Sources, paper maps, blueprint (P0–P1) | 1 | 30 | 27.0 | `█████████░` 90 % |
| Exact Lean statements, frozen (P2) | 1 | 20 | 18.4 | `█████████░` 92 % |
| Lean proofs (P4) | 85 | 681 | 637.3 | `█████████░` 94 % |
| Frozen theorems sealed | 26 | 26 | 16.0 | `██████░░░░` 62 % |
| Release (P5) | 1 | 15 | 0.0 | `░░░░░░░░░░` 0 % |
| **Total** | | 772 | 698.7 | **90.5 %** |

Lean lines: 443,222 on main + 61,549 on branches, of ≈ 273,000 estimated by the blueprint (`████████████████████` 184.9 % of the estimate).

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
| RA2 | REGREF | 13 | ≈4,100 | ✅ 100 % | landed 675cf6c: B2.1 regularAsymptotics_v1 SEALED after independent audit; 360-module chain on main |
| V1 | SUMINT-A | 7 | ≈4,200 | ✅ 100 % | sumint (B1.6) proved at the exact snapshot-8 type (wt-anfourier, 436 axiom checks); seals at the freeze |
| V2 | SUMINT-B | 5 | ≈2,200 | ✅ 100 % | sumint (B1.6) proved at the exact snapshot-8 type (wt-anfourier, 436 axiom checks); seals at the freeze |
| WA | Wave A definitions | 5 | ≈230 | ✅ 100 % | frozen D6 |
| X3 | FIXEDPT | 9 | ≈3,400 | ✅ 100 % | FIXEDPT closed: fixedpoint_of_closed_gates from B1.12, B1.2, B1.5 only (O-X2-EXP, O-X3-CPL proved) |
| I1 | INDUCT-A | 10 | ≈4,000 | 🟡 98 % | INDUCT: propansatz_of_gates; gamma > 1/2 version propansatz_v2_of_gates on main (PORT batch 2a, 3a1b17a) |
| L3 | PL23 | 4 | ≈1,700 | 🟡 98 % | PL23: Props 6.1 (now at the literal 30d norm, PL23-30D) and 6.2 proved; leafwise B2.1 and B2.2 proved (RA1-LEAFWISE, INCOH-LEAFWISE) |
| RA1 | REGASYMP | 10 | ≈5,800 | 🟡 98 % | RA1 done: couples and trees on snapshot 9, plus the leafwise version for per-leaf profiles (RA1-LEAFWISE) |
| S3 | LADDER | 8 | ≈4,200 | 🟡 98 % | LADDER: all three spine inputs proved, re-proved on the root-time-truncated domain (R33) |
| Z1 | MAIN | 3 | ≈860 | 🟡 98 % | main <= layergarden + layergardenFlower; gamma > 1/2 links main_v2_of_propansatz and fixedpoint_v2_of_closed_gates on main (3a1b17a); wkeTaylor_v1 sealed |
| G3 | EXCESS-T | 10 | ≈3,500 | 🟡 97 % | FINALMOL READY: DH23 Prop 9.5 / TARGET finalmol under R29, R37, R38, and the run model extended to atoms of degree 0-2 and self-loops (G3-LOWDEG, errata E23) |
| G5 | APPB-ALG | 8 | ≈4,000 | 🟡 97 % | APPB-ALG READY: DH23 Prop 10.2 in full (dh23_prop_10_2), fresh 809-module rebuild; GraphOk size deviation recorded |
| G8 | RIGID | 10 | ≈4,600 | 🟡 95 % | RIGID READY in scratch: DH23 Prop 9.6 (gamma > 1/2) with no named input, damaged-component bound, constants independent of the size parameter (R34) |
| I2 | INDUCT-B | 10 | ≈3,050 | 🟡 95 % | INDUCT done (see I1) |
| J5 | MEXP | 6 | ≈2,700 | 🟡 95 % | MEXP done: DH21 Props 7.7, 7.8 (corrected weight) |
| J6 | WKE-ID | 6 | ≈2,800 | 🟡 95 % | WKE-ID done: Σ app = 𝒰_n (wke_identity), B2.1 item (4) proved; route avoids DH21 7.9/7.10 |
| J7 | REGCANCEL | 4 | ≈2,000 | 🟡 95 % | REGCANCEL done: DH23 Prop 6.3 (statement form chosen over B2 objects, to audit) |
| M8 | LAYERCNT | 6 | ≈2,100 | 🟡 95 % | LAYERCNT READY: layerlad, layervine (incl. the improved coherent bound) under TARGET's hypotheses; rebase onto the canonical universe pending |
| S1 | STAGE1-COMB | 7 | ≈2,400 | 🟡 95 % | STAGE1-COMB READY: vinechainlem; LF twist reversal, composition, commutation (Diamond, all four choice cases); congruence is an equivalence relation on V-family states (fresh 111-module rebuild) |
| S2a | REDSPLICE-DEF | 2 | ≈800 | 🟡 95 % | REDSPLICE-DEF READY: the full Stage 1 construction; stage1Piece_sound now also supplies the triple designation and no-hinge-loop facts (AMEND7+8) |
| S4 | SUBPRO | 8 | ≈3,000 | 🟡 95 % | SUBPRO done in atom-set form plus the hinge triple-bond designation (R37) |
| V4 | VINEEST-S2 | 4 | ≈2,500 | 🟡 95 % | VINEEST-S2 done: vineChain_eq_sumintForm (V4 endpoint, ruling R2), 709-module snapshot-9 rebuild OK; obligations VINEPARAM, SumintSigned |
| V5 | VINEEST | 13 | ≈5,100 | 🟡 95 % | Scratch checkpoints: modulated Step-3/no-twist base bound proved with the R58 loss; W13 full-square time bound and actual C2^b geometric class-count bound proved. General separated-family producer, unrolled-term certificates, modulated flattening and kind-general full VINEEST remain open |
| X1 | FLOWER-DEF | 10 | ≈3,100 | 🟡 95 % | FLOWER-DEF done in scratch: classes, kernels, identities, O-FK; B1.12 final (audited, F1/F2 applied) proposed for the freeze |
| C1 | REG-STRUCT | 11 | ≈4,000 | 🟡 90 % | REG-STRUCT done in scratch: structure theorem with uniqueness, decoding, legal/dominant chains, counts (C₀=12^9); F55 |
| C2 | LINKS | 11 | ≈3,000 | 🟡 90 % | LINKS done in scratch: branchpair, defchoice, linkXY, deflink, defcoh, auxlem, explem, treelemma, incohproof1 (couples); F62-F65 |
| C3 | SKELETON | 15 | ≈5,200 | 🟡 90 % | SKELETON done in scratch: prime skeletons with uniqueness (incl. DH21's omitted E4 argument), 194 declarations |
| C4 | LAYERREG | 8 | ≈4,000 | 🟡 90 % | LAYERREG done in scratch: TARGET Props 4.9 (structure, replacement keeps canonicity) and 4.10 (layering count, stronger) |
| C5 | ENHANCED | 9 | ≈3,150 | 🟡 90 % | ENHANCED done in scratch: dominant couples, special sets, equivalence (DH21 Def 4.18), encoded trees (Props 4.20, 4.23), net signs; + tree incohproof1 |
| D1 | COMB-CORE | 8 | ≈2,020 | 🟡 90 % | COMB-CORE done in scratch; ports at the freeze |
| D2 | SYS-DEFS | 14 | ≈3,400 | 🟡 90 % | SYS-DEFS + Duhamel identity done in scratch; ports at the freeze |
| D4 | REG-DEFS | 8 | ≈2,400 | 🟡 90 % | REG-DEFS done (B2 draft + REG-STRUCT scratch) |
| G0 | MOLE-COUNT-BASICS | 4 | ≈1,400 | 🟡 90 % | DEGEN done in scratch (DH21 Lemmas 9.13–9.14, DH23 §10.5, GAP.degenerate.tame, corrected remtame); moves to Foundations after the Wave B freeze |
| G2 | EXCESS-DH23 | 8 | ≈3,500 | 🟡 90 % | EXCESS-DH23 + VINE-COUNT + G2-SIBLING + G2-GHOST: DH23 Prop 9.4 all step types incl. new components and the charged ghost-triangle bound (errata E20) |
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
| M9 | VINEPARAM | 4 | ≈1,500 | 🟡 90 % | VINEPARAM: parametrization contract proved (538 certificates); being rebuilt on the canonical universe as a separate lean_lib (D12, VINEPARAM-U, ~1/3 done) |
| V3 | REGRED | 6 | ≈1,900 | 🟡 90 % | REGRED done in scratch: skeleton reduction, vineest Step 1 (ab8680f); nonzero-gap boundary case separate (F21) |
| X2 | FLOWEREST | 16 | ≈8,900 | 🟡 90 % | FLOWEREST scratch: conditional spine assembly and regular L0 leg exist; flower Stage-1, fixed-time traces and marked-flower LF-twist construction remain unresolved |
| F2 | PLG | 12 | ≈4,150 | 🟡 86 % | LG-SPINE scratch: AMEND4/5/7+8 checkpoint and AMEND6-prime pair-type gate exist; AMEND9/10 consumer rework unfinished. Full Stage-1 and final-count producers remain required |
| M7 | LFTWIST | 13 | ≈4,200 | 🟡 85 % | LFTWIST on main with the canonical universe; leaf bijection of LF twists on ordinary leaves proved (LFTWIST-LEAFMAP, R45) |
| F3 | FINAL-COUNT | 4 | ≈900 | 🟡 81 % | Scratch LOW-FRONT A1-A3 compiled: actual loop-label determination, GL17/LoopCtx applications and loop-count bookkeeping; provisional farm only. REG half exists; A4, LOW-CHAIN/GARDEN/GLUE and canonical-world validation remain open |
| S2 | REDSPLICE | 6 | ≈2,400 | 🟡 58 % | REPRESENTS scratch: vine-free reduction and CLASSCOUNT checkpoints exist; vine case split VINE-A/B/C/D/E/F. INTERFACE v2 routes lower-child mode frequencies through the R58 modulated kernel. Producer and full vine reduction remain open |
| F1 | FINAL-RED | 4 | ≈1,200 | 🟡 30 % | FINAL-RED: finalsbest1/finalsbest2 consumed in LG-SPINE's assembly (counting cover, finalproof numerics) proved generically |
| G1 | STAGE2-DEF | 10 | ≈2,600 | 🟡 20 % | STAGE2-DEF: stage-2 operation datatype (Stage2Op) and TARGET's counting problem (lg-spine CountingChoices) defined |

</details>

Done fractions last reviewed: **2026-11-05 23:09 UTC**. Source: [`docs/campaign/progress.json`](docs/campaign/progress.json); history: [`docs/campaign/history.csv`](docs/campaign/history.csv).
<!-- /AUTO:progress -->

## Workers

<!-- AUTO:workers -->
| Worker / session | model / account | packet | branch: last commit | brief |
|---|---|---|---|---|
| Codex orchestrator | Codex / current session | Source rulings, safe landings, proof-state review and HQ upkeep | `w/orch`: 42 min ago | [brief](docs/campaign/orch/CODEX-HANDOFF.md) |
| subagent v5_w2 | GPT-6.1 Terra medium / current session | Six-packet analytic spine port: warning/proof hygiene after V5 modulated-Step3 checkpoint | `w/port-b3a`: 0 min ago, 1 unlanded | [brief](docs/campaign/orch/briefs/TERRA-LINT-PORT-B3.md) |
| subagent v5_w13 | GPT-6.1 Terra medium / current session | V5 W1/W3: separated-family producer and final-count constants | `w/orch`: 42 min ago | [brief](docs/campaign/orch/briefs/TERRA-V5-W13.md) |
| subagent finalcount_low | GPT-6.1 Terra medium / current session | Independent port review; LOW-FRONT A1-A3 provisionally complete in scratch | `w/port-b3a`: 0 min ago, 1 unlanded | [brief](docs/campaign/orch/briefs/TERRA-AUDIT-PORT-B3.md) |
| cx-world | GPT-6.1 Sol medium / codex-2 (existing session) | Existing serial canonical-world upstream rebuild; axiom closeout and assembly overlay pending | `w/orch`: 42 min ago | [brief](docs/campaign/orch/CODEX-HANDOFF.md) |
| cx-b4bprep | GPT-6.1 Sol medium / codex-2 (existing session) | Existing R52 Batch-4b serial catalogue rebuild; skeleton/layer-count/N4 checks pending | `w/orch`: 42 min ago | [brief](docs/campaign/orch/CODEX-HANDOFF.md) |
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
