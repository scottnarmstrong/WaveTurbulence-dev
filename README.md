# WaveTurbulence-dev — campaign HQ

Lean 4 formalization of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024).

<!-- AUTO:updated -->
> **Last updated: 2026-11-08 13:03 UTC** · **estimated completion 91.4 %** (Lean proofs 92.9 %) · frozen theorems sealed: 17 / 27 (+ 300 frozen definitions) · **1,487,753 lines of Lean on main** (11928 files) + 134,849 unlanded on worker branches · blueprint estimate ≈ 273,000 lines
<!-- /AUTO:updated -->

**Scope (D1):** everything proved in Lean, no black boxes. That covers the target paper and the results it uses from
Deng–Hani's earlier papers (DH21, DH23, parts of DH21-2 and DH19), the trilinear estimates of Germain–Ionescu–Tran
(GIT20), smooth-solution theory for cubic NLS on the torus, and the Gaussian/cumulant facts.
**Main theorem (D2):** Theorem 1.1 for `0 < γ < 1` on the square torus `[0,L]^d`, `d ≥ 3`.

## Status

**Phase (reviewed 2026-11-07):** P4 proofs. `layergarden_v2` is **PROVED** (sealed, two keys; R152). On main, Theorem 1.1
for 1/2 < γ < 1 (`main_v2`) follows from `layergarden_v2` and `layergardenFlower_v3` by proved assembly. So the
remaining proof work for that range is the flower estimate `flowerest1` (= `layergardenFlower_v3`), tracked by the
flower bar below. Its paper-level proof is complete and refereed (R155); its Lean formalization is in progress. Then
`layergardenFlower_v3 → fixedpoint_v2 → propansatz_v2 → main_v2` are sealed with two-key audits.
**γ ≤ 1/2:** DH23 Prop 9.6 is false there (erratum E1). The T-vine repair (D11) is deferred until the 1/2 < γ < 1
chain is sealed. Errata and deviations are consolidated in `docs/ERRATA-AND-DEVIATIONS.md` on branch `w/report`,
which lands with the next Lean landing.

```text
DRAFT_ANCHORS: 10 theorem anchors at DRAFT_SORRY (main, fixedpoint, propansatz v1/v2; layergarden v1; layergardenFlower v1/v2/v3; superseded versions stay frozen as history)
UNREGISTERED_SORRIES: 0 (frozen-anchor guard OK on HEAD)
DRAFT_IMPORT_VIOLATIONS: 0
SEALED: 17 theorems + 300 definitions
```

## Flower estimate

<!-- AUTO:flower -->
### Flower estimate (`flowerest1` = frozen `layergardenFlower_v3`): **91.9 %**

`████████████████████████████░░` 91.9 % · 70 of 76 packets done, 1 partial, 2 running, 3 queued · ledger updated 2026-11-08 13:03 UTC

- **Paper proof:** ✅ Paper-level proof complete and refereed (R155): SUPPLEMENT-v2 + 6.3', 7.3', 7.5', 8.2', 8.3, 10.2-10.4, U-clock; 7 referee reports, no FAIL.
- **Lean:** 181,616 lines in the flower world (sorry-free, pinned to main), plus main-side threading on worker branches. When the cores close, the world lands on main and the chain `layergardenFlower_v3 → fixedpoint_v2 → propansatz_v2 → main_v2` is sealed.
- **Next:** B4 (gate assembly; consumes B2e, B3, WTPrefix MarkedClassRepresentsMK); B3s α→β→δ→γ; B3-2 + V5W-2L (two-layer top filters); D3-3 (ProtBoundGate); D6b (ProtAnnBoundGate, regular component); D7-2 (chiDN); C5b (MarkedComponentBoundAtI at B = 18000); SEAL-PREP dry run; then CORES, PORT, seals.
- **Open risks:** flowerest1 waits on D3 ProtBoundGate (termChild (P7) traced-couple cases) and B3s MarkedClassRepresentsMK (α integration, then β/δ/γ; helper splits requested); Then: PORT-2 final sync, landing, seal_chain.sh

| Workstream | Packets | Done | Running | Completion |
|---|---|---|---|---|
| Flower top reduction (landed on main) | 6 | 6 | 0 | `██████████` 100 % |
| Weighted Stage 1, unmarked gardens | 5 | 5 | 0 | `██████████` 100 % |
| Weighted vine estimate (V5W) | 5 | 5 | 0 | `██████████` 100 % |
| Supplement lemma stock | 8 | 8 | 0 | `██████████` 100 % |
| Marked layer A: interface, capping, top assembly | 7 | 7 | 0 | `██████████` 100 % |
| Marked layer B: marked Stage 1 | 13 | 12 | 1 | `█████████░` 92 % |
| Marked layer C: final count (Stage 2') | 11 | 11 | 0 | `██████████` 100 % |
| Marked layer D: protected objects | 17 | 16 | 1 | `█████████░` 93 % |
| Cores, landing and seals | 4 | 0 | 0 | `█░░░░░░░░░` 10 % |
| **Total** | 76 | 70 | 2 | **91.9 %** |

<details><summary>All flower packets</summary>

| Workstream | Packet | Weight | Status | Note |
|---|---|---|---|---|
| Flower top reduction (landed on main) | FT1 | 4 | ✅ done | flower top reduction, main 89e2e136 |
| Flower top reduction (landed on main) | FC23W | 4 | ✅ done | M1, main 796c0f5f |
| Flower top reduction (landed on main) | FL-CASES | 2 | ✅ done | M1 |
| Flower top reduction (landed on main) | FL-TYPED | 2 | ✅ done | M1 |
| Flower top reduction (landed on main) | FL-POLAR | 2 | ✅ done | M1 |
| Flower top reduction (landed on main) | FL-FAM | 4 | ✅ done | M1: layergardenFlower_v3 from the two cores |
| Weighted Stage 1, unmarked gardens | STAGE1W-GLUE | 4 | ✅ done | gate glue, exponent c_psi^{16N} |
| Weighted Stage 1, unmarked gardens | STAGE1W-O4 | 4 | ✅ done | noVineRepresentsFW |
| Weighted Stage 1, unmarked gardens | INC-TOP | 4 | ✅ done | topIncoherentDecayGateR |
| Weighted Stage 1, unmarked gardens | COH-TRUNK | 4 | ✅ done | coherent trunk |
| Weighted Stage 1, unmarked gardens | STAGE1W-VINE | 4 | ✅ done | weighted Stage-1 gate (now unconditional via V5WB) |
| Weighted vine estimate (V5W) | V5W-0 | 4 | ✅ done | class factorization and continuity |
| Weighted vine estimate (V5W) | V5W-A | 4 | ✅ done | S = none from main's certificate |
| Weighted vine estimate (V5W) | V5W-B-MAIN | 8 | ✅ done | LANDED on main 416902c8 (land_check, 327 ABI OK) |
| Weighted vine estimate (V5W) | V5W-B-WORLD | 4 | ✅ done | S = none half; weighted Stage-1 gate UNCONDITIONAL |
| Weighted vine estimate (V5W) | V5W-T | 4 | ✅ done | top filter; V5FrontierClassBound unconditional |
| Supplement lemma stock | FL-SHELL | 2 | ✅ done |  |
| Supplement lemma stock | FL-SEP | 2 | ✅ done |  |
| Supplement lemma stock | FL-AFFINE | 2 | ✅ done |  |
| Supplement lemma stock | FL-PIN | 2 | ✅ done |  |
| Supplement lemma stock | FL-EXCISE | 2 | ✅ done |  |
| Supplement lemma stock | FL-COEF | 2 | ✅ done |  |
| Supplement lemma stock | FL-FIBER | 2 | ✅ done |  |
| Supplement lemma stock | FL-FACE | 4 | ✅ done | Lemma 9.1 faces |
| Marked layer A: interface, capping, top assembly | A1 MK-DEFS | 2 | ✅ done |  |
| Marked layer A: interface, capping, top assembly | A5 MK-ASM | 2 | ✅ done | flower_v3_of_marked_of_caps |
| Marked layer A: interface, capping, top assembly | A2 CAPS-ID | 4 | ✅ done | capped encoding; A2-R final interface |
| Marked layer A: interface, capping, top assembly | CAPS-FUBINI | 2 | ✅ done | shell integral exchange |
| Marked layer A: interface, capping, top assembly | A3a CAPS-GLUE | 2 | ✅ done | n-ary glue identity |
| Marked layer A: interface, capping, top assembly | A3b CAPS-COMP | 4 | ✅ done | CapsDecompF/G |
| Marked layer A: interface, capping, top assembly | CAPS-STABLE | 4 | ✅ done | CapsTwistStable; flower_v3_of_marked: flowerest1 <= MarkedComponentBoundAtI alone |
| Marked layer B: marked Stage 1 | B0 design | 2 | ✅ done | S-STAGE1MK |
| Marked layer B: marked Stage 1 | B1a THREAD-ROOTS | 8 | ✅ done | LANDED on main (b9ffa69f) |
| Marked layer B: marked Stage 1 | B1b THREAD-GEN | 4 | ✅ done | part 1 landed; rest READY a08a78bd (lands jointly) |
| Marked layer B: marked Stage 1 | B2a MK-RUNS | 4 | ✅ done | LANDED on main (b9ffa69f) |
| Marked layer B: marked Stage 1 | B2b MK-MARK | 4 | ✅ done | Lemmas 1+ and 2+ and the sigma-bridge (zero weight for stem-unclean pieces) |
| Marked layer B: marked Stage 1 | B2c MK-SUBPRO | 8 | ✅ done | complete (main + world: SoundMKFull geometric fields) |
| Marked layer B: marked Stage 1 | B2d CLASSCOUNT-MK | 4 | ✅ done | ClassCountStmtMk at any marking; landed on main (004ebeb7) |
| Marked layer B: marked Stage 1 | B2e MK-X | 2 | ✅ done | markIX transport (no clean hyp), per-tree FL-SEP, FineMarking both cases |
| Marked layer B: marked Stage 1 | B3 MK-UNITS | 2 | ✅ done | marked run producer, pieces at mkF ∩ vinesV0 (R177); audit clean |
| Marked layer B: marked Stage 1 | B3-2 MK-UNITS-L | 2 | ✅ done | markedUnitsRepresentsFWL' unconditional (per-unit top filters) |
| Marked layer B: marked Stage 1 | V5W-2L | 2 | ✅ done | v5FrontierClassBoundL: V5 bound for a product of top filters (mass topFilterMass^|S|) |
| Marked layer B: marked Stage 1 | B3s MK-SLOTS | 4 | 🟡 running | claude-2 wt-b3s (moved): R179 ruled; ProtSlotSupM repaired form, then milestones α→β→δ→γ |
| Marked layer B: marked Stage 1 | B4 STAGE1MK-GATE | 2 | ✅ done | stage1ReductionAtMKFull_of_B3s (single hypothesis: B3s); ZeroVanish, B2eIX, survivor count proved |
| Marked layer C: final count (Stage 2') | C0 design | 2 | ✅ done | S-FINALMK |
| Marked layer C: final count (Stage 2') | C3 LAD-FILT | 4 | ✅ done | filtered ladders |
| Marked layer C: final count (Stage 2') | C2 FINALMK-CRUDE | 2 | ✅ done | crude bound gate |
| Marked layer C: final count (Stage 2') | C1a SURV-STEP | 4 | ✅ done | re-cut potential step (riskiest C step) |
| Marked layer C: final count (Stage 2') | C5a PIECE-MK | 2 | ✅ done | MarkedPieceTarget (R161: 1 <= d) and the class sum |
| Marked layer C: final count (Stage 2') | C1b1 MK-PHASE1 | 4 | ✅ done | phase-1 cover; survivor budget proved sound (recut_hone, recut_not_both_ab) |
| Marked layer C: final count (Stage 2') | C4a PIN-FOURIER | 4 | ✅ done | pinned ladder Fourier bound + face export for D7 |
| Marked layer C: final count (Stage 2') | C1b2 MK-CHAIN | 4 | ✅ done | LowLoopClassBoundMKAll; FinalCountGateHalfMK unconditional |
| Marked layer C: final count (Stage 2') | C1c MK-GARDEN | 2 | ✅ done | FinalCountGateHalfMK (now unconditional with C1b2) |
| Marked layer C: final count (Stage 2') | C4b FINE-PIN | 4 | ✅ done | FineSplicedGateHalfMK unconditional |
| Marked layer C: final count (Stage 2') | C5b COMP-MK | 2 | ✅ done | flowerest1_of_B3s_D6b_452: LayergardenFlowerV3Gate from B3s + D6b (D7, B4 discharged) |
| Marked layer D: protected objects | D0 design | 2 | ✅ done | S-PROT |
| Marked layer D: protected objects | D1 PROT-TA | 2 | ✅ done |  |
| Marked layer D: protected objects | D2a PROT-KER | 2 | ✅ done | ProtDefs + kernel bridge |
| Marked layer D: protected objects | D5c FILT-NT | 2 | ✅ done |  |
| Marked layer D: protected objects | D1b PROT-OPS | 4 | ✅ done | all 7 time-operator bounds incl. FoldInterpolation |
| Marked layer D: protected objects | D2b PROT-GEO | 4 | ✅ done | protected geometry (i)-(iv); R163 carrier fix |
| Marked layer D: protected objects | D2c PROT-CUT | 4 | ✅ done | all cut identities incl. o104 Prop 7.4 |
| Marked layer D: protected objects | D5a FILT-LINK | 4 | ✅ done | o82 Lemma 14.1 + the D5b map (copy-thread recommended) |
| Marked layer D: protected objects | D5d FILT-COH | 8 | ✅ done | FiltCoherentBoundGate unconditional |
| Marked layer D: protected objects | D3 PROT-PIN | 4 | 🟡 running | claude-2: ProtBoundSelGate done; ProtBoundGate reduced to the (P7)-tree and cap slices (workers) |
| Marked layer D: protected objects | D5b-1 FILT-SRC | 4 | ✅ done | filtered source phase, twins, kernel identity |
| Marked layer D: protected objects | D5b-2 FILT-PROD | 2 | ✅ done | filters threaded to the link product |
| Marked layer D: protected objects | D5b-3 FILT-GATE | 2 | ✅ done | FiltIncoherentDecayGate at eta and 1/4 |
| Marked layer D: protected objects | D6a PROT-PTW | 4 | ✅ done | protPtwGate unconditional (o82 Prop 14.2, form 18.4); 22 modules, audit clean; F-D6a-1 → R178 Sel.card ≤ 1 |
| Marked layer D: protected objects | D6b PROT-WHOLE | 4 | ✅ done | RegularComponentTargetI + ProtAnnBoundGate from ProtBoundGate (D3) alone |
| Marked layer D: protected objects | D7 SEL-RES | 4 | ✅ done | markedSumBoundSel_of_gates (R175 κ = 400d); 13 modules, audit clean |
| Marked layer D: protected objects | D7-2 SEL-NORM | 1 | ✅ done | chiDN in PieceSel/SelRes (same RHS); selSumTargetT per-tree (F-C5b-1) |
| Cores, landing and seals | CORES | 4 | ⬜ queued | Core-F and Core-G from the component bound |
| Cores, landing and seals | LAND | 4 | 🟠 checkpoint 35 % | PORT-1 ready (271 modules, 43.7k lines on w/flower-port); lands at the next lull |
| Cores, landing and seals | SEAL layergardenFlower_v3 | 2 | ⬜ queued | seal_chain.sh dry run OK (all four, no drift); live run needs the closed composite theorem |
| Cores, landing and seals | SEAL fixedpoint_v2 / propansatz_v2 / main_v2 | 4 | ⬜ queued | two keys each; Theorem 1.1 for 1/2 < gamma < 1 |

</details>

Packet weights follow the blueprint convention (hard = 4, standard = 2, multi-packet items more). Credit: done = 1; a CHECKPOINT carries an explicit partial fraction; running and queued packets carry 0. Source: [`docs/campaign/flower.json`](docs/campaign/flower.json); history: [`docs/campaign/flower-history.csv`](docs/campaign/flower-history.csv).
<!-- /AUTO:flower -->

## Progress

<!-- AUTO:progress -->
### Estimated completion: **91.4 %**

`███████████████████████████░░░` 91.4 %

| Part of the project | Items | Weight | Done | Completion |
|---|---|---|---|---|
| Sources, paper maps, blueprint (P0–P1) | 1 | 30 | 27.0 | `█████████░` 90 % |
| Exact Lean statements, frozen (P2) | 1 | 20 | 18.6 | `█████████░` 93 % |
| Lean proofs (P4) | 85 | 918 | 860.5 | `█████████░` 94 % |
| Frozen theorems sealed | 27 | 27 | 17.0 | `██████░░░░` 63 % |
| Release (P5) | 1 | 15 | 0.0 | `░░░░░░░░░░` 0 % |
| **Total** | | 1010 | 923.1 | **91.4 %** |

Lean lines: 1,487,753 on main + 134,849 on branches, of ≈ 273,000 estimated by the blueprint (`████████████████████` 594.4 % of the estimate).

<details><summary>All Lean work packets (blueprint §E) with weight and status</summary>

| Packet | Name | Weight | Lines (est.) | Done | Note |
|---|---|---|---|---|---|
| B1 | NLS-A | 6 | ≈1,600 | ✅ 100 % | landed: Fourier equation, mass, reduction |
| B2 | NLS-B | 9 | ≈3,200 | ✅ 100 % | done: LWP/persistence, inverse reduction, uniqueness; NLS bridge helpers landed (4639fe2) |
| B3 | NLS-C | 10 | ≈3,000 | ✅ 100 % | done: nlsAkBridge (all 4 conjuncts) proved at the exact snapshot-5 type (scratch, wt-l2s); moves to Foundations at the Wave B freeze |
| D3 | CANON | 9 | ≈3,950 | ✅ 100 % | CANON: canonicalCharacterization sealed and second-key audited PROVED (audits/SEAL-B1-second-key.md) |
| F3 | FINAL-COUNT | 4 | ≈900 | ✅ 100 % | FINAL-COUNT: unconditional finalCount_half : FinalCountGateHalf (REG half R59 + LOW half via treatment A, R79) landed on main as PORT batch 5 (1,801 modules, e58db09) |
| J1 | BCOEF | 7 | ≈3,800 | ✅ 100 % | done: time coefficients, class J/R operators, DH21 Lemmas 5.3-5.5 |
| J2 | CLASSJR2 | 8 | ≈4,000 | ✅ 100 % | done: DH21 Lemmas 5.6-5.10 (legal-partition induction, ≤ 2^m expansion); sign F61 open (traced in J3) |
| J3 | MAINCOEF | 4 | ≈3,000 | ✅ 100 % | MAINCOEF done: DH21 Prop 5.1 for couples and trees (DH23 weights), garden↔code B̃ bridge |
| J4 | CANCEL7 | 6 | ≈3,400 | ✅ 100 % | CANCEL7 done with the F61 correction; BtRec discharged by the B̃ bridge |
| L1 | PL1A | 7 | ≈2,800 | ✅ 100 % | done: B2.2 incoherentDecay proved at the exact type (INCOH-INST, e77e692); seals at the B2 freeze |
| L2 | PL1B | 9 | ≈4,650 | ✅ 100 % | PL1 done: abstract TARGET Prop 5.1 incl. one-clock case (541d4c8); garden instantiation = INCOH-INST |
| M9 | VINEPARAM | 4 | ≈1,500 | ✅ 100 % | VINEPARAM: catalogue on main as the separate lean_lib WaveTurbulenceVineParam (D12, PORT batch 4a, 97036a3) |
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
| RA2 | REGREF | 13 | ≈4,100 | ✅ 100 % | REGREF: B2.1 regularAsymptotics proved and SEALED on main (PORT batch 2b, 675cf6c; second-key audit PASS) |
| V1 | SUMINT-A | 7 | ≈4,200 | ✅ 100 % | sumint (B1.6) proved at the exact snapshot-8 type (wt-anfourier, 436 axiom checks); seals at the freeze |
| V2 | SUMINT-B | 5 | ≈2,200 | ✅ 100 % | sumint (B1.6) proved at the exact snapshot-8 type (wt-anfourier, 436 axiom checks); seals at the freeze |
| WA | Wave A definitions | 5 | ≈230 | ✅ 100 % | frozen D6 |
| X3 | FIXEDPT | 9 | ≈3,400 | ✅ 100 % | FIXEDPT closed: fixedpoint_of_closed_gates from B1.12, B1.2, B1.5 only (O-X2-EXP, O-X3-CPL proved) |
| F2 | PLG | 12 | ≈4,150 | 🟡 99 % | PLG = LG-SPINE: layergarden_v2_of_V5 on main (batch 4b-2): layergarden_v2 conditional only on V5's VINEEST HalfMK |
| S3 | LADDER | 8 | ≈4,200 | 🟡 99 % | LADDER: all spine inputs proved; providers re-pinned to the current spine with exact gate checks (cx-repin) |
| V5 | VINEEST | 13 | ≈5,100 | 🟡 98 % | VINEEST: statement layer and weighted SpatialMeasure statements on main (batches 4b-1/4b-1b); V5-SPACE READY; W2 certificate: all record kinds built (kind 2 cross-window lemmas READY), final constants and integration in progress |
| I1 | INDUCT-A | 10 | ≈4,000 | 🟡 98 % | INDUCT: propansatz_of_gates; gamma > 1/2 version propansatz_v2_of_gates on main (PORT batch 2a, 3a1b17a) |
| L3 | PL23 | 4 | ≈1,700 | 🟡 98 % | PL23: Props 6.1 (now at the literal 30d norm, PL23-30D) and 6.2 proved; leafwise B2.1 and B2.2 proved (RA1-LEAFWISE, INCOH-LEAFWISE) |
| RA1 | REGASYMP | 10 | ≈5,800 | 🟡 98 % | RA1 done: couples and trees on snapshot 9, plus the leafwise version for per-leaf profiles (RA1-LEAFWISE) |
| Z1 | MAIN | 3 | ≈860 | 🟡 98 % | main <= layergarden + layergardenFlower; gamma > 1/2 links main_v2_of_propansatz and fixedpoint_v2_of_closed_gates on main (3a1b17a); wkeTaylor_v1 sealed |
| G3 | EXCESS-T | 10 | ≈3,500 | 🟡 97 % | FINALMOL READY: DH23 Prop 9.5 / TARGET finalmol under R29, R37, R38, and the run model extended to atoms of degree 0-2 and self-loops (G3-LOWDEG, errata E23) |
| G5 | APPB-ALG | 8 | ≈4,000 | 🟡 97 % | APPB-ALG READY: DH23 Prop 10.2 in full (dh23_prop_10_2), fresh 809-module rebuild; GraphOk size deviation recorded |
| S2 | REDSPLICE | 6 | ≈2,400 | 🟡 97 % | REPRESENTS: on main as PORT batch 4b-2 (96c8e1d): stage1ReductionGate_of_V5' : WTPrefix VineEstCanonLayerHalfMK -> Stage1ReductionGate (vineparam and leafwise gates discharged on main); second key PASS (R123) |
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
| X1 | FLOWER-DEF | 10 | ≈3,100 | 🟡 92 % | FLOWER-DEF: product-form cutoff successor layergardenFlower_v3 audited (FIDELITY/CONSUMERS PASS) and frozen (D13); fixedpoint consumers rewired to it (FC1 READY) |
| X2 | FLOWEREST | 253 | ≈8,900 | 🟡 92 % | FLOWEREST: weight and completion from the flower ledger (70 packets done, 2 running, 3 queued; see the flower bar) |
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
| V3 | REGRED | 6 | ≈1,900 | 🟡 90 % | REGRED done in scratch: skeleton reduction, vineest Step 1 (ab8680f); nonzero-gap boundary case separate (F21) |
| M7 | LFTWIST | 13 | ≈4,200 | 🟡 85 % | LFTWIST on main with the canonical universe; leaf bijection of LF twists on ordinary leaves proved (LFTWIST-LEAFMAP, R45) |
| F1 | FINAL-RED | 4 | ≈1,200 | 🟡 30 % | FINAL-RED: finalsbest1/finalsbest2 consumed in LG-SPINE's assembly (counting cover, finalproof numerics) proved generically |
| G1 | STAGE2-DEF | 10 | ≈2,600 | 🟡 20 % | STAGE2-DEF: stage-2 operation datatype (Stage2Op) and TARGET's counting problem (lg-spine CountingChoices) defined |

</details>

Done fractions last reviewed: **2026-11-07 05:24 UTC**. Source: [`docs/campaign/progress.json`](docs/campaign/progress.json); history: [`docs/campaign/history.csv`](docs/campaign/history.csv).
<!-- /AUTO:progress -->

## Workers

<!-- AUTO:workers -->
| tmux | model / account | packet | branch: last commit | brief |
|---|---|---|---|---|
| wt-orch | Claude Opus / claude-1 | Task 34: snapshot-8 delta audit + freeze branch rebuild; done: letter draft, many audits | `w/orch`: 0 min ago, 154 unlanded | [brief](docs/campaign/orch/TASK4.md) |
| wt-gauss-hc | Claude Opus / claude-10 | FLOWER-SPINE: B1.12 layergardenFlower from named spine inputs (X2, X3 closed: fixedpoint from B1.12+B1.2+B1.5) | `w/waveb-infra`: — | [brief](docs/campaign/briefs/FLOWER-SPINE.md) |
| wt-torus | Claude Opus / claude-14 | G7 MOLEPROP4 (revived, repaired): DH23 ylem1′, ylem2, Prop 10.4 (A23-HALF done) | `w/approxnt`: 97 h ago | [brief](docs/campaign/briefs/MOLEPROP4.md) |
| wt-wke | Claude Opus / claude-13 | L3+L4: TARGET Props 6.1-6.3 (proplayer2-4); J1-J3, B̃ bridge, tree Prop 5.1 done | `w/jr-ops`: 97 h ago | [brief](docs/campaign/briefs/PL234.md) |
| wt-cumul | GPT-6.1-Sol low / codex-2 | LG-SPINE (pre-freeze): layergarden from named spine inputs (INDUCT, WKETAYLOR-GATE done) | `w/norm-bridge`: 104 h ago | [brief](docs/campaign/briefs/LG-SPINE.md) |
| wt-nt | GPT-6.1-Sol low / codex-2 | G4 APPB-OPS then G5 APPB-ALG (pre-freeze): DH23 Appendix B (MOLE M1+M2, CLCN M3 done) | `w/nt-circle`: 92 h ago | [brief](docs/campaign/briefs/APPB-OPS.md) |
| wt-ansob | GPT-6.1-Sol low / codex-2 | RA1 couples (RA1Couple): DH23 Prop 6.1 for couples; trees moved to wt-l2s | `w/bproc`: 94 h ago, 11 unlanded | [brief](docs/campaign/briefs/REGASYMP.md) |
| wt-gausssum | GPT-6.1-Sol low / codex-2 | M9 VINEPARAM (pre-freeze): molecule-level vine parametrizations (M4 VINES done) | `w/count`: 92 h ago, 11 unlanded | [brief](docs/campaign/briefs/VINES.md) |
| wt-resonant | GPT-6.1-Sol low / codex-2 | V4 VINEEST-S2 (pre-freeze): vineest Step 2 into sumint form (V3 REGRED done) | `w/resonant`: 97 h ago | [brief](docs/campaign/briefs/VINEEST-S2.md) |
| wt-anfourier | GPT-6.1-Sol low / codex-2 | M7 LFTWIST (pre-freeze); M5 MOLECPL, M6 TWIST, SUMINT done | `w/an-phase`: 110 h ago | [brief](docs/campaign/briefs/LFTWIST.md) |
| wt-l2s | GPT-6.1-Sol low / codex-2 | RA1-TREES: DH23 Prop 6.1 for trees (RA1Tree); INCOH-INST done: B2.2 proved at exact type | `w/wke-l2s`: 91 h ago, 23 unlanded | [brief](docs/campaign/briefs/RA1-TREES.md) |
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
