# Wave turbulence in Lean 4

This repository is a formalization, in the [Lean 4](https://lean-lang.org) proof assistant, of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024),

together with the results it relies on from the authors' earlier papers and from the literature (listed under
[Papers](#papers) below). The main result, Theorem 1.1, is formalized for the full range of its scaling exponent,
0 < γ < 1. Every step is checked by Lean; nothing is assumed beyond Lean's standard axioms.

**Authors:** Scott Armstrong and Ahmed Bou-Rabee.

<!-- AUTO:updated -->
> **Last changed: 2026-11-10 09:40 UTC** (checked every 10 minutes) · frozen theorems sealed: 26 / 28, the other 2 being superseded drafts (+ 300 frozen definitions) · **1,994,316 lines of Lean on main** (14409 files) · overall completion of the whole project (full range 0 < γ < 1): 98.8 %
<!-- /AUTO:updated -->

## At a glance

- ✅ **Theorem 1.1 is formally proved for the full range 0 < γ < 1.** The Lean statement (`WaveTurbulence.main`) is
  the printed one for 0 < γ < 1 on the square torus. It was frozen on 2026-11-03, before its proof was written, and
  never changed. The proof was sealed on 2026-11-09 and passed two independent audits, each including a full replay of
  the proof in Lean's kernel ([records](docs/audits/full-range/README.md)). It depends only on Lean's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`).
- ✅ **The earlier version for 1/2 < γ < 1** (`main_v2`; sealed on 2026-11-08, audited on 2026-11-09) is also proved.
  The full-range proof uses it for γ > 1/2.
- 🔧 **What it took for γ ≤ 1/2.** There the printed proof has a gap: it relies on a counting proposition (DH23
  Prop 9.6) that is false in that range. The repair enlarges the family of "vines" that the proof splices out,
  re-proves the counting proposition for the enlarged family, and corrects one step of the counting procedure (the
  "ghost" step). **→
  [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md)** explains the problem, the repair and where it is in Lean.
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
  and that it is the natural scaling law for spatially inhomogeneous problems. **The formal proof covers this value.**
  It lies in the range 0 < γ ≤ 1/2, where the printed proof needed the repair described in
  [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md).
- **γ = 1, the endpoint.** Here T_kin is of order L², which matches the natural (parabolic) scaling of the Schrödinger
  equation, so results at this scaling translate into statements on a torus of fixed size. In three dimensions this
  connects to the open problem of whether the Gibbs measure (Φ⁴₃) is invariant under the cubic Schrödinger flow, and
  to energy cascades. On the square torus γ = 1 is not admissible. Theorem 1.1 covers it only on rectangular tori with
  generic side lengths, a case this project does not formalize (decision D2 in [docs/DECISIONS.md](docs/DECISIONS.md)).
  **So at γ = 1 our formal result is narrower than the printed Theorem 1.1.** This is listed among the deviations in
  [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md).
- **γ ≤ 1/2 more broadly.** In this range the equidistribution the theory needs holds for essentially any dispersion
  relation, without number theory (DH23, §1.2). The difficulty we found there is of a different, combinatorial kind,
  and it is repaired (see [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md)).

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

   The audit records for Theorem 1.1 for the full range are collected in
   [`docs/audits/full-range/`](docs/audits/full-range/README.md); those for the earlier 1/2 < γ < 1 version are in
   [`docs/audits/v2-chain/`](docs/audits/v2-chain/README.md).

## How to verify

You need git and [elan](https://github.com/leanprover/elan), which installs the Lean version pinned in
[`lean-toolchain`](lean-toolchain) (v4.35.0). In a clone of this repository:

```bash
lake exe cache get   # download Mathlib's prebuilt files (Mathlib v4.35.0)
lake build           # build the project: Lean checks every proof
```

`lake build` builds the library `WaveTurbulence`, including the five sealed full-range theorems (`WaveTurbulence.main`
and the four statements it is assembled from). It succeeds only if Lean accepts every proof.

**What a full build costs.** Even with Mathlib taken from its cache, building the project from scratch is heavy.
Measured on this repository in November 2026:
- about 27 CPU-hours on an AMD Ryzen 7 7700 (8 cores, 16 threads);
- one file needs about 11 GB of RAM at its peak;
- the build writes about 73 GB to disk. Most of it is Lake's per-module `*.setup.json` files under `.lake/build/ir/`,
  which are not needed once their module is built and can be deleted as the build proceeds.

So a full build needs a workstation-class machine; it does not fit on a standard CI runner.

**Fast checks (minutes, no build needed).** These check the bookkeeping that guards the statements:

```bash
python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json
python3 -I scripts/check_lean_modules.py
python3 -I scripts/check_pinned_texts.py
scripts/check_index.sh
```

- `check_frozen_anchors.py`: every frozen statement and definition is byte-for-byte the approved text (hashes in
  [`manifest/frozen.json`](manifest/frozen.json)), its state is recorded, there is no `sorry` outside the registered
  unproved statements, and those are imported by nothing else. About 2.5 minutes here.
- `check_lean_modules.py`: every Lean file is a Lean module and within the size limit. Under a second.
- `check_pinned_texts.py`: the approved T-vine definitions
  ([`WaveTurbulence/Foundations/TVine/Defs.lean`](WaveTurbulence/Foundations/TVine/Defs.lean)) are byte-for-byte
  the pinned text. Under a second.
- `check_index.sh`: the first two checks, run on exactly the committed tree.

**Independent kernel replays.** Each of the two independent audits of the sealed theorems replayed the entire proof in
Lean's kernel. Their records are in [`docs/audits/full-range/`](docs/audits/full-range/README.md) (full range) and
[`docs/audits/v2-chain/`](docs/audits/v2-chain/README.md) (the earlier 1/2 < γ < 1 version).

## Current status

- **Proved (sealed and audited):** Theorem 1.1 for the full range 0 < γ < 1, `main`, and the four statements it is
  assembled from: `propansatz`, `fixedpoint`, `layergarden` (all three as printed, for 0 < γ < 1) and the flower
  estimate `layergardenFlower_v4`. Sealed on 2026-11-09 (decision D17); both independent audits passed for all five
  ([records](docs/audits/full-range/README.md)). How the proof is put together:
  [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md).
- **Sealed and audited:** Theorem 1.1 for 1/2 < γ < 1, `main_v2`, and the theorems it is assembled from
  (`propansatz_v2`, `fixedpoint_v2`, `layergarden_v2` and the flower estimate `layergardenFlower_v3`). The
  full-range proof uses these for γ > 1/2.
- **Sealed:** the other 16 frozen theorems (so 26 of the 28 frozen theorem statements are sealed), and all 300
  frozen definitions.
- **Not proved, by design:** the two original flower statements `layergardenFlower` (v1) and `layergardenFlower_v2`.
  Their cutoffs mis-transcribe the paper's (erratum E34); `layergardenFlower_v3` and `layergardenFlower_v4` replace
  them, and nothing depends on them.
- **In progress:** removing code that the final proof does not use (the code base grew large while alternative routes
  were explored; a first pass removed about 48,000 lines), and preparing the public release.

<details><summary>Technical status fields</summary>

```text
DRAFT_ANCHORS: 2 theorem anchors at DRAFT_SORRY (the superseded flower statements layergardenFlower v1 and
               layergardenFlower_v2; erratum E34)
UNREGISTERED_SORRIES: 0 (frozen-anchor guard OK)
DRAFT_IMPORT_VIOLATIONS: 0
SEALED: 26 theorems + 300 definitions. Full range: main, propansatz, fixedpoint, layergarden, layergardenFlower_v4
        sealed 2026-11-09 (main 5c19b015), PROVED with two-key audits. 1/2 < γ < 1: main_v2 PROVED (two-key audits).
```
</details>

## Progress

The percentage below is the project's internal bookkeeping for the **whole project**: sources, statements, proofs,
seals and the public release. It was reassessed on 2026-11-10, after the full-range proof was sealed and audited;
the only open part is the public release. The authoritative state is [Current status](#current-status) above.

<!-- AUTO:progress -->
### Overall completion (whole project: full range 0 < γ < 1): **98.8 %**

`██████████████████████████████` 98.8 %

| Part of the project | Items | Weight | Done | Completion |
|---|---|---|---|---|
| Sources, paper maps, blueprint (P0–P1) | 1 | 30 | 30.0 | `██████████` 100 % |
| Exact Lean statements, frozen (P2) | 1 | 20 | 20.0 | `██████████` 100 % |
| Lean proofs (P4) | 85 | 918 | 918.0 | `██████████` 100 % |
| Frozen theorems sealed | 26 | 26 | 26.0 | `██████████` 100 % |
| Release (P5) | 1 | 15 | 3.0 | `██░░░░░░░░` 20 % |
| **Total** | | 1009 | 997.0 | **98.8 %** |

Lean lines: 1,994,316 on main + 3,102 on worker branches. (The original blueprint estimate, ≈ 273,000 lines, was set before the project's scope and the errata were known; it is no longer a useful yardstick.)

<details><summary>All Lean work packets (blueprint §E) with weight and status</summary>

| Packet | Name | Weight | Lines (est.) | Done | Note |
|---|---|---|---|---|---|
| B1 | NLS-A | 6 | ≈1,600 | ✅ 100 % | landed: Fourier equation, mass, reduction |
| B2 | NLS-B | 9 | ≈3,200 | ✅ 100 % | done: LWP/persistence, inverse reduction, uniqueness; NLS bridge helpers landed (4639fe2) |
| B3 | NLS-C | 10 | ≈3,000 | ✅ 100 % | done: nlsAkBridge (all 4 conjuncts) proved at the exact snapshot-5 type (scratch, wt-l2s); moves to Foundations at the Wave B freeze |
| C1 | REG-STRUCT | 11 | ≈4,000 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| C2 | LINKS | 11 | ≈3,000 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| C3 | SKELETON | 15 | ≈5,200 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| C4 | LAYERREG | 8 | ≈4,000 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| C5 | ENHANCED | 9 | ≈3,150 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| D1 | COMB-CORE | 8 | ≈2,020 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| D2 | SYS-DEFS | 14 | ≈3,400 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| D3 | CANON | 9 | ≈3,950 | ✅ 100 % | CANON: canonicalCharacterization sealed and second-key audited PROVED (audits/SEAL-B1-second-key.md) |
| D4 | REG-DEFS | 8 | ≈2,400 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| F1 | FINAL-RED | 4 | ≈1,200 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| F2 | PLG | 12 | ≈4,150 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| F3 | FINAL-COUNT | 4 | ≈900 | ✅ 100 % | FINAL-COUNT: unconditional finalCount_half : FinalCountGateHalf (REG half R59 + LOW half via treatment A, R79) landed on main as PORT batch 5 (1,801 modules, e58db09) |
| G0 | MOLE-COUNT-BASICS | 4 | ≈1,400 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| G1 | STAGE2-DEF | 10 | ≈2,600 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| G2 | EXCESS-DH23 | 8 | ≈3,500 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| G3 | EXCESS-T | 10 | ≈3,500 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| G4 | APPB-OPS | 8 | ≈4,000 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| G5 | APPB-ALG | 8 | ≈4,000 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| G6 | MOLEPROP13 | 6 | ≈2,400 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| G7 | MOLEPROP4 | 12 | ≈4,500 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| G8 | RIGID | 10 | ≈4,600 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| I1 | INDUCT-A | 10 | ≈4,000 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| I2 | INDUCT-B | 10 | ≈3,050 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| J1 | BCOEF | 7 | ≈3,800 | ✅ 100 % | done: time coefficients, class J/R operators, DH21 Lemmas 5.3-5.5 |
| J2 | CLASSJR2 | 8 | ≈4,000 | ✅ 100 % | done: DH21 Lemmas 5.6-5.10 (legal-partition induction, ≤ 2^m expansion); sign F61 open (traced in J3) |
| J3 | MAINCOEF | 4 | ≈3,000 | ✅ 100 % | MAINCOEF done: DH21 Prop 5.1 for couples and trees (DH23 weights), garden↔code B̃ bridge |
| J4 | CANCEL7 | 6 | ≈3,400 | ✅ 100 % | CANCEL7 done with the F61 correction; BtRec discharged by the B̃ bridge |
| J5 | MEXP | 6 | ≈2,700 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| J6 | WKE-ID | 6 | ≈2,800 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| J7 | REGCANCEL | 4 | ≈2,000 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| L1 | PL1A | 7 | ≈2,800 | ✅ 100 % | done: B2.2 incoherentDecay proved at the exact type (INCOH-INST, e77e692); seals at the B2 freeze |
| L2 | PL1B | 9 | ≈4,650 | ✅ 100 % | PL1 done: abstract TARGET Prop 5.1 incl. one-clock case (541d4c8); garden instantiation = INCOH-INST |
| L3 | PL23 | 4 | ≈1,700 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| L4 | PL4 | 4 | ≈2,500 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| M1 | MOLE | 15 | ≈4,900 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| M2 | BLOCKS | 6 | ≈1,600 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| M3 | CLCN | 10 | ≈3,500 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| M4 | VINES | 10 | ≈3,300 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| M5 | MOLECPL | 4 | ≈1,500 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| M6 | TWIST | 8 | ≈2,800 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| M7 | LFTWIST | 13 | ≈4,200 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| M8 | LAYERCNT | 6 | ≈2,100 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
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
| RA1 | REGASYMP | 10 | ≈5,800 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| RA2 | REGREF | 13 | ≈4,100 | ✅ 100 % | REGREF: B2.1 regularAsymptotics proved and SEALED on main (PORT batch 2b, 675cf6c; second-key audit PASS) |
| S1 | STAGE1-COMB | 7 | ≈2,400 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| S2 | REDSPLICE | 6 | ≈2,400 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| S2a | REDSPLICE-DEF | 2 | ≈800 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| S3 | LADDER | 8 | ≈4,200 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| S4 | SUBPRO | 8 | ≈3,000 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| V1 | SUMINT-A | 7 | ≈4,200 | ✅ 100 % | sumint (B1.6) proved at the exact snapshot-8 type (wt-anfourier, 436 axiom checks); seals at the freeze |
| V2 | SUMINT-B | 5 | ≈2,200 | ✅ 100 % | sumint (B1.6) proved at the exact snapshot-8 type (wt-anfourier, 436 axiom checks); seals at the freeze |
| V3 | REGRED | 6 | ≈1,900 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| V4 | VINEEST-S2 | 4 | ≈2,500 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| V5 | VINEEST | 13 | ≈5,100 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| WA | Wave A definitions | 5 | ≈230 | ✅ 100 % | frozen D6 |
| X1 | FLOWER-DEF | 10 | ≈3,100 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |
| X2 | FLOWEREST | 253 | ≈8,900 | ✅ 100 % | FLOWEREST: weight and completion from the flower ledger (76 packets done, 0 running, 0 queued) |
| X3 | FIXEDPT | 9 | ≈3,400 | ✅ 100 % | FIXEDPT closed: fixedpoint_of_closed_gates from B1.12, B1.2, B1.5 only (O-X2-EXP, O-X3-CPL proved) |
| Z1 | MAIN | 3 | ≈860 | ✅ 100 % | closed: Theorem 1.1 is sealed and proved for 0 < γ < 1 (R198); this package's result is part of the proved chain or was superseded by the route used |

</details>

Done fractions last reviewed: **2026-11-10 05:36 UTC**. Source: [`docs/campaign/progress.json`](docs/campaign/progress.json); history: [`docs/campaign/history.csv`](docs/campaign/history.csv).
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

- [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md): the range 0 < γ ≤ 1/2, what goes wrong in the printed proof, the
  repair, and where it is in Lean.
- [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md): errata in the published arguments and deviations of
  the formal statements.
- [docs/audits/full-range/](docs/audits/full-range/README.md): the two-key seal audits of Theorem 1.1 for the full
  range 0 < γ < 1 and its chain.
- [docs/audits/v2-chain/](docs/audits/v2-chain/README.md): the two-key seal audits of Theorem 1.1 for 1/2 < γ < 1 and
  its chain.
- [docs/research/](docs/research/INDEX.md): research notes, referee reports and scripts behind the errata.
- [docs/DECISIONS.md](docs/DECISIONS.md): the author's decisions (scope, statement versions, rulings).
- [docs/FINDINGS.md](docs/FINDINGS.md): the running ledger of source findings.
- [docs/THIRD-PARTY.md](docs/THIRD-PARTY.md): third-party code (Apache 2.0, attributed).
- [docs/campaign/](docs/campaign/): internal campaign records (plan, blueprint, rulings, audits).

