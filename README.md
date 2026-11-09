# Wave turbulence in Lean 4

This repository is a formalization, in the [Lean 4](https://lean-lang.org) proof assistant, of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024),

together with the results it relies on from the authors' earlier papers and from the literature (listed under
[Papers](#papers) below). Every step is checked by Lean; nothing is assumed beyond Lean's standard axioms.

<!-- AUTO:updated -->
> **Last updated: 2026-11-09 09:53 UTC** · frozen theorems sealed: 21 / 27 (+ 300 frozen definitions) · **1,678,769 lines of Lean on main** (12733 files) · overall completion of the whole project (full range 0 < γ < 1): 93.8 %
<!-- /AUTO:updated -->

## At a glance

- ✅ **Theorem 1.1 is formally proved for 1/2 < γ < 1.** The exact Lean statement (`main_v2`) was frozen before its
  proof was written. It was sealed on 2026-11-08 and passed two independent audits on 2026-11-09. Each audit includes a
  full replay of the proof in Lean's kernel. The theorem depends only on Lean's standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`).
- 🚧 **The range 0 < γ ≤ 1/2 is not finished.** There, the printed proof relies on a counting proposition (DH23
  Prop 9.6) that is false in that range. This is a gap in the proof, not a counterexample to the theorem. A repair is
  now complete on paper and independently refereed; its Lean formalization started on 2026-11-09. **→ [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md)** explains
  the problem and the plan.
- 📄 **Errata and deviations.** Formalizing a long proof surfaces mistakes and gaps. Every defect we found in the
  published arguments, and every way our formal statements differ from the printed ones, is recorded with evidence
  and a repair. **→ [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md)**

## What the theorem says, in brief

Wave turbulence theory predicts that, for a large system of weakly interacting waves, the distribution of energy
across frequencies evolves according to an effective *wave kinetic equation*. Deng and Hani's Theorem 1.1 proves this
rigorously for the cubic nonlinear Schrödinger equation on a large square torus in dimension d ≥ 3, with random
initial data, on long time scales.

### The exponent γ, and the values that matter physically

The theorem involves two limits at once: the side length L of the torus tends to infinity, and the strength α of the
nonlinearity tends to zero. The exponent γ fixes how the two are linked: α = L^(−γ). The time scale on which the
kinetic equation describes the waves, the *kinetic time*, is then T_kin = 1/(2α²) = L^(2γ)/2. For a given box size L,
a smaller γ means a stronger nonlinearity and a shorter kinetic time.

- **Why 0 < γ < 1.** The kinetic description needs the resonance frequencies of the waves to be spread out evenly
  ("equidistributed") at the scale 1/T_kin. On the square torus these frequencies are multiples of 1/L², so they cannot
  be equidistributed at finer scales; this rules out γ ≥ 1. At the other end, γ = 0 (letting L → ∞ before α → 0) is
  not compatible with the continuum setting. Deng and Hani show that every γ in between is admissible, and that
  different values of γ correspond to genuinely different physical and mathematical regimes (DH23, §1.2).
- **γ = 1/2, the "ballistic" scaling law.** Here T_kin is of order L: the kinetic time equals the time a wave packet
  needs to cross the box. Deng and Hani point out that this is the wave analogue of the Boltzmann–Grad scaling used in
  Lanford's theorem for the Boltzmann equation (where the mean free path is equated with the transport length scale),
  and that it is the natural scaling law for spatially inhomogeneous problems. **This value lies in the range that our
  formal proof does not yet cover:** the proved result is for 1/2 < γ < 1, and γ = 1/2 itself belongs to the
  [γ ≤ 1/2 work](docs/GAMMA-LE-HALF.md).
- **γ = 1, the endpoint.** Here T_kin is of order L², which matches the natural (parabolic) scaling of the Schrödinger
  equation, so results at this scaling translate into statements on a torus of fixed size. In three dimensions this
  connects to the open problem of whether the Gibbs measure (Φ⁴₃) is invariant under the cubic Schrödinger flow, and
  to energy cascades. On the square torus γ = 1 is not admissible. Theorem 1.1 covers it only on rectangular tori with
  generic side lengths, a case this project does not formalize (decision D2 in [docs/DECISIONS.md](docs/DECISIONS.md)).
  **So at γ = 1 our formal result is narrower than the printed Theorem 1.1.** This is listed among the deviations in
  [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md).
- **γ ≤ 1/2 more broadly.** In this range the equidistribution the theory needs holds for essentially any dispersion
  relation, without number theory (DH23, §1.2). The difficulty we found there is of a different, combinatorial kind
  (see [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md)).

## How a result counts as "proved" here

1. **The statement is fixed first.** The exact Lean statement of each key theorem is written down and approved before
   its proof exists. It is then frozen (recorded with hashes in [`manifest/frozen.json`](manifest/frozen.json)), so
   the proof cannot quietly change what is being proved.
2. **No gaps.** Proofs contain no `sorry` and no added axioms. Automated checks enforce this on every change.
3. **Sealing.** When the proof is complete, the frozen statement's placeholder is replaced by a one-line reference to
   the proof. Tooling checks that the statement itself is byte-for-byte unchanged.
4. **Two independent audits.** Two auditors, who did not write the proof, each work separately:
   - re-derive the statement from the paper's source and check that no extra hypotheses were added;
   - check the axioms used;
   - replay the entire proof in Lean's kernel.

   The audit records for Theorem 1.1 (1/2 < γ < 1) and its chain are in
   [`docs/audits/v2-chain/`](docs/audits/v2-chain/).

## Current status

- **Done:** Theorem 1.1 for 1/2 < γ < 1, i.e. `main_v2` and the theorems it is assembled from (`propansatz_v2`,
  `fixedpoint_v2`, `layergarden_v2`, and the "flower estimate" `layergardenFlower_v3`). All are sealed and audited.
- **In progress:**
  - the range 0 < γ ≤ 1/2: the Lean formalization of the repair, started on 2026-11-09
    ([plan and status](docs/GAMMA-LE-HALF.md); [progress meter](#progress-on-0--γ--12));
  - removing code that the final proof does not use (the code base grew large while alternative routes were
    explored). A first pass removed about 48,000 lines; the rest waits until the γ ≤ 1/2 work is done, since that
    work reuses part of the code;
  - preparing a public release.
- The six frozen theorem statements that are not yet sealed are the original full-range versions (0 < γ < 1). They
  will be proved when the γ ≤ 1/2 work is complete.

<details><summary>Technical status fields</summary>

```text
DRAFT_ANCHORS: 6 theorem anchors at DRAFT_SORRY (the full-range originals main, propansatz, fixedpoint, layergarden,
               layergardenFlower v1, and the superseded layergardenFlower_v2)
UNREGISTERED_SORRIES: 0 (frozen-anchor guard OK)
DRAFT_IMPORT_VIOLATIONS: 0
SEALED: 21 theorems (incl. main_v2, PROVED with two-key audits) + 300 definitions
```
</details>

## Progress on 0 < γ ≤ 1/2

<!-- AUTO:gammalow -->
### The γ ≤ 1/2 campaign: **16.5 %**

`█████░░░░░░░░░░░░░░░░░░░░░░░░░` 16.5 % · 2 of 18 work packages done, 13 running, 3 not started · **6,996 lines of new Lean compiling** (16,813 written) in the γ ≤ 1/2 work area, not yet on main · ledger updated 2026-11-09 11:05 UTC

This meter tracks the extension of the formal proof of Theorem 1.1 from 1/2 < γ < 1 to the full range 0 < γ < 1 (see [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md)). Weights are the estimated size of each work package (thousands of new Lean lines; non-Lean steps get an equivalent weight). A finished package counts fully. A running package counts in proportion to the Lean it has written that compiles in the work area (part of it adapted from the existing proof), capped at 75 % until the package passes its checks and is accepted.

- **Next:** Freeze the full-range flower statement layergardenFlower_v4 (branch in preparation); T-vine core API (L1); first counting results (L6).
- **Risks:** kernel cost of the T-vine checker at 13 atoms (benchmark under way); account quota (the work is spread over 5 accounts); new mathematics may need local repairs once formalized

| Stage | What it does | Packages | Done | Completion |
|---|---|---|---|---|
| Mathematics on paper | the repair for γ ≤ 1/2, proved and checked by independent referees | 1 | 1 | `██████████` 100 % |
| Statements | the new full-range flower statement: audited, then frozen | 2 | 1 | `██████░░░░` 65 % |
| T-vine combinatorics | the enlarged vine family: structure, a verified checker, parametrizations | 4 | 0 | `░░░░░░░░░░` 5 % |
| Counting estimates for γ ≤ 1/2 | DH23 Props 9.4–9.6 and 10.4 in the low range, and the ghost step | 4 | 0 | `█░░░░░░░░░` 12 % |
| Moving the proof to the enlarged vine family | stage 1, the vine estimate and the source objects with T-vines | 3 | 0 | `░░░░░░░░░░` 4 % |
| Flower estimate for γ ≤ 1/2 | the marked stage 1 and the marked final count in the low range | 1 | 0 | `░░░░░░░░░░` 0 % |
| Assembly | joining the two halves γ ≤ 1/2 and γ > 1/2 | 2 | 0 | `░░░░░░░░░░` 0 % |
| Landing, sealing and audits | land on main; seal main, propansatz, fixedpoint, layergarden and the flower statement; two independent audits each | 1 | 0 | `░░░░░░░░░░` 0 % |
| **Total** | | 18 | 2 | **16.5 %** |

<details><summary>All work packages</summary>

| Stage | Package | Content | Weight | Lean lines (compiling / written) | Status | Credit | Note |
|---|---|---|---|---|---|---|---|
| Mathematics on paper | RESEARCH | T-vines, the ghost step, the counting and flower re-checks (notes N1–N3, M1–M4) | 20 | — | ✅ done | 100 % | all refereed (R191) |
| Statements | AUDIT-V4 | independent audit of layergardenFlower_v4 | 1 | — | ✅ done | 100 % | fidelity PASS, 0 extra hypotheses |
| Statements | FREEZE-V4 | freeze layergardenFlower_v4, pin the T-vine text | 1 | — | 🔄 running | 30 % | branch in preparation |
| T-vine combinatorics | L1 | core API, rung surgery, gap criterion | 15 | 675 / 1,112 | 🔄 running | 4 % |  |
| T-vine combinatorics | L2 | verified checker for the small cases | 8 | 1,471 / 1,509 | 🔄 running | 18 % |  |
| T-vine combinatorics | L3 | structure theorems (pieces, sub-objects) | 16 | 322 / 322 | 🔄 running | 2 % |  |
| T-vine combinatorics | L4 | charts (parametrizations) of all T-vines | 11.5 | 0 / 1,368 | 🔄 running | 0 % |  |
| Counting estimates for γ ≤ 1/2 | L6 | final count: gate, Prop 9.6, assembly | 18 | 1,922 / 2,849 | 🔄 running | 11 % |  |
| Counting estimates for γ ≤ 1/2 | L6E | the ghost step (erratum E20) | 4 | 0 / 1,085 | 🔄 running | 0 % |  |
| Counting estimates for γ ≤ 1/2 | L6-COUNT | volume counts and operations (App. A, Prop 10.4) | 5 | 1,534 / 1,534 | 🔄 running | 31 % |  |
| Counting estimates for γ ≤ 1/2 | L6-STEP1 | Step-1 deviation for T-vines | 3 | 0 / 5,583 | 🔄 running | 0 % |  |
| Moving the proof to the enlarged vine family | L5a | stage 1 and the class count | 8 | 632 / 632 | 🔄 running | 8 % |  |
| Moving the proof to the enlarged vine family | L5b | the vine estimate for T-vines | 12 | 0 / 0 | 🔄 running | 0 % |  |
| Moving the proof to the enlarged vine family | L5c | source objects, spliced count, subpro | 10 | 440 / 440 | 🔄 running | 4 % |  |
| Flower estimate for γ ≤ 1/2 | L8 | flower estimate, low half | 30 | 0 / 379 | 🔄 running | 0 % |  |
| Assembly | L0 | glue lemmas | 1 | 0 / 0 | ⬜ queued | 0 % |  |
| Assembly | L7 | layergarden, low half | 2 | 0 / 0 | ⬜ queued | 0 % |  |
| Landing, sealing and audits | L9 | landing, seals, two-key audits | 6 | — | ⬜ queued | 0 % |  |

</details>

Source: [`docs/campaign/gammalow.json`](docs/campaign/gammalow.json); history: [`docs/campaign/gammalow-history.csv`](docs/campaign/gammalow-history.csv).
<!-- /AUTO:gammalow -->

## Progress

The percentage below measures the **whole project**, i.e. the full range 0 < γ < 1. The 1/2 < γ < 1 result is
complete; the remaining percentage is mostly the γ ≤ 1/2 work.

<!-- AUTO:progress -->
### Overall completion (whole project: full range 0 < γ < 1): **93.8 %**

`████████████████████████████░░` 93.8 %

| Part of the project | Items | Weight | Done | Completion |
|---|---|---|---|---|
| Sources, paper maps, blueprint (P0–P1) | 1 | 30 | 27.0 | `█████████░` 90 % |
| Exact Lean statements, frozen (P2) | 1 | 20 | 18.6 | `█████████░` 93 % |
| Lean proofs (P4) | 85 | 918 | 881.1 | `██████████` 96 % |
| Frozen theorems sealed | 27 | 27 | 21.0 | `████████░░` 78 % |
| Release (P5) | 1 | 15 | 0.0 | `░░░░░░░░░░` 0 % |
| **Total** | | 1010 | 947.7 | **93.8 %** |

Lean lines: 1,678,769 on main + 2,643 on worker branches. (The original blueprint estimate, ≈ 273,000 lines, was set before the project's scope and the errata were known; it is no longer a useful yardstick.)

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
| X2 | FLOWEREST | 253 | ≈8,900 | ✅ 100 % | FLOWEREST: weight and completion from the flower ledger (76 packets done, 0 running, 0 queued) |
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

- [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md): the range 0 < γ ≤ 1/2, what goes wrong and the plan (work in
  progress).
- [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md): errata in the published arguments and deviations of
  the formal statements.
- [docs/audits/v2-chain/](docs/audits/v2-chain/): the two-key seal audits of Theorem 1.1 for 1/2 < γ < 1 and its
  chain.
- [docs/DECISIONS.md](docs/DECISIONS.md): the author's decisions (scope, statement versions, rulings).
- [docs/FINDINGS.md](docs/FINDINGS.md): the running ledger of source findings.
- [docs/THIRD-PARTY.md](docs/THIRD-PARTY.md): third-party code (Apache 2.0, attributed).
- [docs/campaign/](docs/campaign/): internal campaign records (plan, blueprint, rulings, audits).

## Internal: worker sessions

Campaign bookkeeping, refreshed automatically; may lag behind the actual sessions.

<!-- AUTO:workers -->
| tmux | model / account | packet | branch: last commit | brief |
|---|---|---|---|---|
| wt-orch | Claude Opus / claude-1 | Task 34: snapshot-8 delta audit + freeze branch rebuild; done: letter draft, many audits | `w/orch`: 14 min ago, 200 unlanded | [brief](docs/campaign/orch/TASK4.md) |
| wt-gauss-hc | Claude Opus / claude-10 | FLOWER-SPINE: B1.12 layergardenFlower from named spine inputs (X2, X3 closed: fixedpoint from B1.12+B1.2+B1.5) | `w/waveb-infra`: — | [brief](docs/campaign/briefs/FLOWER-SPINE.md) |
| wt-torus | Claude Opus / claude-14 | G7 MOLEPROP4 (revived, repaired): DH23 ylem1′, ylem2, Prop 10.4 (A23-HALF done) | `w/approxnt`: 117 h ago | [brief](docs/campaign/briefs/MOLEPROP4.md) |
| wt-wke | Claude Opus / claude-13 | L3+L4: TARGET Props 6.1-6.3 (proplayer2-4); J1-J3, B̃ bridge, tree Prop 5.1 done | `w/jr-ops`: 117 h ago | [brief](docs/campaign/briefs/PL234.md) |
| wt-cumul | GPT-6.1-Sol low / codex-2 | LG-SPINE (pre-freeze): layergarden from named spine inputs (INDUCT, WKETAYLOR-GATE done) | `w/norm-bridge`: 124 h ago | [brief](docs/campaign/briefs/LG-SPINE.md) |
| wt-nt | GPT-6.1-Sol low / codex-2 | G4 APPB-OPS then G5 APPB-ALG (pre-freeze): DH23 Appendix B (MOLE M1+M2, CLCN M3 done) | `w/nt-circle`: 113 h ago | [brief](docs/campaign/briefs/APPB-OPS.md) |
| wt-ansob | GPT-6.1-Sol low / codex-2 | RA1 couples (RA1Couple): DH23 Prop 6.1 for couples; trees moved to wt-l2s | `w/bproc`: 114 h ago, 11 unlanded | [brief](docs/campaign/briefs/REGASYMP.md) |
| wt-gausssum | GPT-6.1-Sol low / codex-2 | M9 VINEPARAM (pre-freeze): molecule-level vine parametrizations (M4 VINES done) | `w/count`: 113 h ago, 11 unlanded | [brief](docs/campaign/briefs/VINES.md) |
| wt-resonant | GPT-6.1-Sol low / codex-2 | V4 VINEEST-S2 (pre-freeze): vineest Step 2 into sumint form (V3 REGRED done) | `w/resonant`: 118 h ago | [brief](docs/campaign/briefs/VINEEST-S2.md) |
| wt-anfourier | GPT-6.1-Sol low / codex-2 | M7 LFTWIST (pre-freeze); M5 MOLECPL, M6 TWIST, SUMINT done | `w/an-phase`: 131 h ago | [brief](docs/campaign/briefs/LFTWIST.md) |
| wt-l2s | GPT-6.1-Sol low / codex-2 | RA1-TREES: DH23 Prop 6.1 for trees (RA1Tree); INCOH-INST done: B2.2 proved at exact type | `w/wke-l2s`: 111 h ago, 23 unlanded | [brief](docs/campaign/briefs/RA1-TREES.md) |
<!-- /AUTO:workers -->
