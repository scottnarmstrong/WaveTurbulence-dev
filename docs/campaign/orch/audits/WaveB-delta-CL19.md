# Audit: Wave B tier B1 delta CL-19 (`waveb-snap-5` against `waveb-snap-4`)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03.

## Inputs

**Snapshot.** `/home/scott/wt-scratch/waveb-snap-5/`. All `SHA256SUMS` entries verify.

**Changed files**, compared with `waveb-snap-4` (checked PASS in `WaveB-packaging-check.md`):

| File | sha256 | Δ lines |
|---|---|---|
| `WaveB1-System.lean` | `59365906…` | 12: the `SNorm` guard and its docstring |
| `WaveB1-Statements.lean` | `e72e32df…` | 6: two docstrings |
| `WaveB1-Lemmas.lean` | `c7312be4…` | 16: `WTParams.Lambda_ne_zero`; premise `hΛ` on `contDiff_of_SNormR_lt_top` |
| `WaveB1-System-probes.lean` | `b78d1835…` | 21: regression probe `SNorm_zero_left` |
| `WaveB1-Statements-probes.lean` | `d087ace3…` | 9: `contDiff_of_remainderBound` takes `hd`; `or_true` in `remainderBound_zero` |
| `DESIGN.md` | `3b1486ca…` | 26: the CL-19 entry |

**Unchanged, byte-identical:** Core, Sumint, Deferred, Deferred-probes, Bridges, Core-probes, `FreezeList.lean` and
`FREEZE-LIST.md` (`0fadaa62…`).

**Sources.**
- TARGET (normX2), L585: ‖F‖_{𝔖^{Λ₁,Λ₂}} = max_{|ρ|≤Λ₁} ‖⟨k⟩^{Λ₂} ∂_k^ρ F(k)‖_{L^∞_k}.
- The landed `Fourier.spatialNorm` (`WaveTurbulence/Foundations/Fourier/MixedNorm.lean`, owner ruling of
  2026-11-03; it is identical in my worktree and in `WaveTurbulence-dev`).

**The counterexample.** It is not at the path in the brief. It is archived as
`/home/scott/wt-scratch/norm-bridge/historical/SpatialObstruction.lean.before-guard-fix`: the indicator of {0} on
`Mom 1` gives the snapshot-4 value `SNormR 0 0 = ⊤`, against `spatialNorm 0 0 ≤ 1`. The current file
`norm-bridge/SpatialZeroRegression.lean` shows the two now agree.

## Verdict: PASS. CL-19 is exactly the stated change, faithful to (normX2); no other change.

- **It is exactly the stated change.**
  - In the source, the only edits are the `SNorm` guard (`ContDiff ℝ Λ₁ F` → `Λ₁ = 0 ∨ ContDiff ℝ Λ₁ F`), the
    premise `hΛ : Λ₁ ≠ 0` on `contDiff_of_SNormR_lt_top` with its one-line proof change, the new lemma
    `WTParams.Lambda_ne_zero`, the probes, and docstrings.
  - My environment comparison (§2) confirms that nothing else changed in elaborated content.
- **It is faithful to (normX2).**
  - At Λ₁ = 0 the source is max over |ρ| ≤ 0, i.e. ‖⟨k⟩^{Λ₂}F‖_∞, which carries no regularity condition. The new
    `SNorm 0 Λ₂ F` is that supremum for **every** `F`.
  - I prove `SNorm 0 Λ₂ F = Fourier.spatialNorm 0 Λ₂ F` for all `F` against the landed definition.
  - For Λ₁ ≠ 0 I prove `SNorm` equals the snapshot-4 body token for token, so nothing changes there.
- **Frozen anchors keep their meaning.** Every frozen use of `SNorm`/`SNormR` has order `Λ_q`, `4Λ_{p+1}` or `30d`.
  The anchors reach them only under `WTPrefix`/`WTPrefixA`, which build `P` with `d ≥ 3`, where all three orders
  are nonzero (proved).
  - The frozen **definitions** `AnsatzAt`, `RemainderBound` and `SumintDatum.Admissible` change meaning only at
    order 0. That needs `P.d = 0` (or `d = 0`), and there they now say what the source says.
- **The new premise is necessary.** I prove the unpremised helper false: there is a discontinuous `F` with
  `SNormR 0 0 F ≤ 1`. The premise is discharged wherever the helper is used.
- **All files elaborate.** FREEZE-LIST is still correct: regenerated from the snapshot-5 build, it has the same 202
  rows, kinds, files and *uses* (834 edges).

## 1. Elaboration (snapshot 5, fresh build root, one `lake env lean` at a time, `nice -n 5`)

| Module | Errors | `sorry` | Other warnings |
|---|---|---|---|
| Core, System | 0 | 0 | 0 |
| Statements | 0 | 10 (B1.1–B1.5, B1.7–B1.11) | 0 |
| Sumint | 0 | 1 (B1.6) | 0 |
| Lemmas | 0 | 0 | 0 |
| CoreProbes, SystemProbes, StatementsProbes | 0 | 0 | 0 |
| Deferred | 0 | 1 (deferred B1.12) | 0 |
| DeferredProbes, Bridges | 0 | 0 | 0 |
| `FreezeList.lean` (run) | 0 | — | 202 rows |

Frozen modules were compiled before Lemmas, as in Task 9a.

## 2. "No other change": machine check against snapshot 4

I ran the Task 9a environment dump (`scratch/WaveB-pack-dump.lean`) on the snapshot-5 build: normalized
types/values with proofs erased, reducibility, instance status and priority, and axioms of every constant in the four
frozen modules and Lemmas. Compared with the snapshot-4 dump:

| Difference | Constant | Expected? |
|---|---|---|
| value | `SNorm` | ✓ the guard |
| type | `contDiff_of_SNormR_lt_top` (Lemmas, not frozen) | ✓ the premise `hΛ` |
| new | `WTParams.Lambda_ne_zero` with its `_proof_1_1` (Lemmas, not frozen) | ✓ |
| anything else | — | **none**: no other value, type, reducibility, instance or axiom difference; `sorryAx` still in exactly the 11 anchors |

`SNormR` and every other user of `SNorm` refer to it by name, so their values are unchanged.

**FREEZE-LIST.** `FreezeList.lean` run on the snapshot-5 build matches the snapshot-4 run on names, kinds, modules
and *uses*. Only the docstring column differs, for `SNorm`, `RemainderBound` and `propansatz`. `FREEZE-LIST.md`
matches the snapshot-5 generator output row for row, so the claim "regenerated, byte-identical" holds: the guard adds
no frozen dependency.

## 3. Verdict table

| Item | Verdict | Evidence |
|---|---|---|
| `SNorm` guard `Λ₁ = 0 ∨ ContDiff ℝ Λ₁ F` | **FAITHFUL** to (normX2) | **Order 0:** `SystemProbes.SNorm_zero_left` gives `SNorm 0 Λ₂ F = ⨆ k, ofReal (⟨k⟩^{Λ₂}‖F k‖)`, the source's ρ = 0 term with no regularity. My `SNorm_zero_eq_spatialNorm` proves equality with the landed `Fourier.spatialNorm 0 Λ₂ F` for all `F`. **Order ≥ 1:** `SNorm_eq_snap4` proves it is the snapshot-4 body verbatim, so the stage-2 reading (classical derivatives, ⊤ off `C^{Λ₁}`) is unchanged. The guard matches the landed `spatialNorm` and CL-13's `XNorm`. The `SNorm` body (with `iterPartial`, `jbr`, `partialMom`) is byte-identical to the patched System on which wt-cumul proved the universal `SNormR_eq_spatialNorm` at all orders. |
| `SNorm` docstring | ACCURATE | It states the order-0 reading and the `Λ₁ ≠ 0` qualification on the helper. |
| Frozen uses keep their meaning | ✓ | The users of `SNorm`/`SNormR` (FREEZE-LIST *uses*) are `SNormR`, `AnsatzAt` (`Λ_p`), `RemainderBound` (`Λ_q`), `layergarden` (`4Λ_{p+1}`), `wkeTaylor` (`4Λ_{p+1}`) and `SumintDatum.Admissible` (`30d`). `frozen_orders_ne_zero` shows these orders are ≠ 0 when `3 ≤ P.d`. All five anchors that reach them are `WTPrefix fun P => …` / `WTPrefixA fun A P => …`, which instantiate `P` with `d ≥ 3` (Core L75–L83, Sumint L240–L248). |
| `contDiff_of_SNormR_lt_top` gains `hΛ : Λ₁ ≠ 0` (Lemmas) | NECESSARY and CORRECT | `helper_premise_needed`: the unpremised statement is refutable by the indicator of {0} on `Mom 1`, which has `SNormR 0 0 ≤ 1` and is not continuous. The proof change is `hc.resolve_left hΛ`, the same as wt-cumul's approved patch. The only term-level caller is the probe `contDiff_of_remainderBound`, now fed by `P.Lambda_ne_zero hd q` (grep over `wt-scratch` and `WaveTurbulence-dev`). |
| `WTParams.Lambda_ne_zero` | CORRECT | `(40d)^{𝔇+1-p} ≠ 0` from `d ≠ 0` (`pow_ne_zero`). Standard axioms. |
| Statements docstring edits (`propansatz` D1; `RemainderBound`) | DOCSTRING-ONLY, accurate | The diff is inside `/-- … -/`; the dump shows no type change. |
| Probe edits | ✓ | `remainderBound_zero` needs `or_true` (the guard is now a disjunction). `SNorm_zero_left` is a useful regression guard. |
| DESIGN CL-19 | ACCURATE | Its claims are all confirmed above: the frozen orders are ≥ 1, the helper premise, FREEZE-LIST byte-identical, the rebuild list. I did not re-check the B2 rebuild claim. |

## REQUIRED

None.

## OPTIONAL

- **N1. Pointwise vs essential supremum at order 0 (information; no action for B1).**
  - (normX2) writes `L^∞_k`, an essential supremum. `SNorm` and the landed `spatialNorm` use the pointwise
    supremum: the ruled reading of WAVE-B §2.6, shared by the two definitions, so the bridges hold.
  - At order ≥ 1 the inputs are `C^{Λ₁}`, so the two agree. At order 0 CL-19 now admits discontinuous `F`, where the
    pointwise value can exceed the source's: e.g. the indicator of {0} has `SNorm 0 0 = 1` while its `L^∞` norm is 0.
  - No frozen statement uses order 0, so this is moot for the freeze. A future consumer that applies `SNorm`/
    `spatialNorm` at order 0 to a.e.-defined data should know the norm is the (larger) pointwise one.
- **N2. Source column for `SNorm`.**
  - The new docstring names "(normX2)", but the generator still gives the `(file)` fallback citing `defcm`. It
    apparently looks for a `T (…)` pattern.
  - Writing "T (normX2), L585" in the docstring would give `SNorm` a precise row, as Task 9a O2 suggested for all 46
    fallback rows.
- **N3. Brief path.** The counterexample is at `norm-bridge/historical/SpatialObstruction.lean.before-guard-fix`, not
  `norm-bridge/SpatialObstruction.lean`.

## Probe (untracked)

`scratch/WaveB-delta-CL19.lean` (sha256 `b9a2a25a…eaa507`). It was built against my snapshot-5 modules and the landed
`Foundations/Fourier/{TimeFourier, MixedNorm}`, which I compiled from source into my scratchpad (byte-identical to
`WaveTurbulence-dev`). Each theorem uses only `propext, Classical.choice, Quot.sound`:
- `SNorm_eq_snap4`;
- `frozen_orders_ne_zero`;
- `SNorm_zero_eq_spatialNorm`;
- `singletonR_not_continuous`, `SNormR_zero_singletonR_le_one`, `helper_premise_needed`.
