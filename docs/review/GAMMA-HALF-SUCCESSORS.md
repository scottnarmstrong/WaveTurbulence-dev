# Review page: the γ ∈ (1/2, 1) versioned successors (ruling D9)

> **Outcome (recorded 2026-11-09).** The five successors were approved and frozen (D10). `main_v2`, `propansatz_v2`,
> `layergarden_v2` and `fixedpoint_v2` were proved and audited, and `layergardenFlower_v2` was superseded by
> `layergardenFlower_v3` (D13). The original full-range statements were later sealed as printed (D17). This page is
> kept as the record of the approval. Current account: [`../GAMMA-LE-HALF.md`](../GAMMA-LE-HALF.md).

For approval by Scott. Prepared by wt-orch, 2026-11-04.

## Why

DH23 Prop 9.6 is false for 0 < γ ≤ 1/2 (necklace counterexample, `docs/ERRATA-AND-DEVIATIONS.md` E1). The proof chain of
TARGET (finalcount1, `lgmolect`) therefore fails in that range, and `layergarden` (B1.2), `layergardenFlower` (B1.12) and
everything built on them (`fixedpoint`, `propansatz`, `main`) can only be proved for γ ∈ (1/2, 1) by this route.
Ruling D9: restrict the formal endpoint by versioned successors (this page), keep researching γ ≤ 1/2.

## What changes

The originals stay frozen, unchanged and open (DRAFT_SORRY). The main theorems are **not** claimed false for γ ≤ 1/2.
Five new anchors are added, each the original file with exactly these changes:

1. the theorem is renamed `<name>_v2`;
2. the restriction:
   - for the four `WTPrefix`/`WTPrefixP` statements, the hypothesis `1 / 2 < P.γ →` is inserted at the head of the
     body. `WTPrefix` already quantifies `γ ∈ Ioo 0 1` first, and every later choice (η₀, C₁, …) is made for that γ,
     so this is exactly "for every γ ∈ (1/2, 1)";
   - for `main`, the hypothesis becomes `hγ : γ ∈ Ioo (1 / 2 : ℝ) 1`;
3. one docstring paragraph stating the restriction and its reason.

Nothing else changes: same imports, binders, definitions and conclusions. `wkeTaylor` (B1.5) does not depend on the
counting chain and needs no successor.

Each draft below elaborates against main `dfe30e3` (`lake env lean`, exit 0; the only warning is the `sorry` of the
DRAFT body).

After approval, each successor is frozen like the originals:
- a manifest entry with state DRAFT_SORRY and a provider stub;
- `approval_ref` `docs/DECISIONS.md#D10`;
- the anchor proof assembled from the existing work (`layergarden_of_spine`, `layergardenFlower_of_spine`, INDUCT,
  X3, MAIN-GLUE), with `finalCountGate_of_half` discharging the counting input for 1/2 < γ.

## Diffs against the frozen originals

```diff

--- Main.lean
+++ MainV2.lean
@@ -39,2 +39,6 @@
-/-- **Deng–Hani, Theorem 1.1** (case `0 < γ < 1`, square torus). -/
-theorem main (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
+/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
+For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
+anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.
+
+**Deng–Hani, Theorem 1.1** (case `0 < γ < 1`, square torus). -/
+theorem main_v2 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) :

--- Propansatz.lean
+++ PropansatzV2.lean
@@ -32 +32,5 @@
-/-- **B1.1 `propansatz`** (T Prop `propansatz`, L689–L707; + time parameter F7/F27; + L951).
+/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
+For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
+anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.
+
+**B1.1 `propansatz`** (T Prop `propansatz`, L689–L707; + time parameter F7/F27; + L951).
@@ -45 +49 @@
-theorem propansatz : WTPrefix fun P =>
+theorem propansatz_v2 : WTPrefix fun P => 1 / 2 < P.γ →

--- Layergarden.lean
+++ LayergardenV2.lean
@@ -41 +41,5 @@
-/-- **B1.2 `layergarden`** (T Prop `layergarden`, L761–L779; deterministic, F36; time parameter
+/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
+For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
+anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.
+
+**B1.2 `layergarden`** (T Prop `layergarden`, L761–L779; deterministic, F36; time parameter
@@ -51 +55 @@
-theorem layergarden : WTPrefix fun P =>
+theorem layergarden_v2 : WTPrefix fun P => 1 / 2 < P.γ →

--- Fixedpoint.lean
+++ FixedpointV2.lean
@@ -41 +41,5 @@
-/-- **B1.3 `fixedpoint`** (T Prop `fixedpoint`, L780–L794). For probability data, `0 ≤ p < 𝔇` and
+/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
+For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
+anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.
+
+**B1.3 `fixedpoint`** (T Prop `fixedpoint`, L780–L794). For probability data, `0 ≤ p < 𝔇` and
@@ -51 +55 @@
-theorem fixedpoint : WTPrefix fun P =>
+theorem fixedpoint_v2 : WTPrefix fun P => 1 / 2 < P.γ →

--- LayergardenFlower.lean
+++ LayergardenFlowerV2.lean
@@ -42 +42,5 @@
-/-- **B1.12 `layergardenFlower`** (T Prop `flowerest1`, L2279–L2305, deterministic core; T L2306–L2338 for
+/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
+For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
+anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.
+
+**B1.12 `layergardenFlower`** (T Prop `flowerest1`, L2279–L2305, deterministic core; T L2306–L2338 for
@@ -84 +88 @@
-theorem layergardenFlower : WTPrefixP fun Pm P =>
+theorem layergardenFlower_v2 : WTPrefixP fun Pm P => 1 / 2 < P.γ →
```

## Full text of the five drafts

### `WaveTurbulence/Frozen/Theorems/MainV2.lean` (sha256 `802baaa3fd5c681d…`)

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.IsWKESolution
public import WaveTurbulence.Frozen.Defs.PartialDeriv
public import WaveTurbulence.Frozen.Defs.NormLaplacian
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.StdComplexGaussian
public import WaveTurbulence.Frozen.Defs.InitialCoeff
public import WaveTurbulence.Frozen.Defs.SolvableEvent
public import WaveTurbulence.Frozen.Defs.KineticTime
public import WaveTurbulence.Provider.Main

/-!
# Main

Deng–Hani, L314-L320 (Theorem 1.1, label main). Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

universe u

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.

**Deng–Hani, Theorem 1.1** (case `0 < γ < 1`, square torus). -/
theorem main_v2 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ θ > (0 : ℝ), ∀ φin : 𝓢(Mom d, ℝ), (∀ k, 0 ≤ φin k) →
      ∀ τstar > (0 : ℝ), ∀ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ →
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α T : ℝ, α = L ^ (-γ) → T = τstar * kineticTime α →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (g : (Fin d → ℤ) → Ω → ℂ),
        (∀ n, Measurable (g n)) → iIndepFun g P → (∀ n, P.map (g n) = stdComplexGaussian) →
        MeasurableSet (solvableEvent L α T φin g) ∧
        1 - Real.exp (-(Real.log L ^ (40 * d))) ≤ P.real (solvableEvent L α T φin g) ∧
        ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
          (∀ ω ∈ solvableEvent L α T φin g,
            IsSmoothNLSSolution L α T (initialCoeff L φin g ω) (U ω)) →
          ∀ t ∈ Icc 0 T, ∀ n : Fin d → ℤ,
            |(∫ ω, (solvableEvent L α T φin g).indicator
                  (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω ∂P)
              - φ (t / kineticTime α) (latticePoint L n)| ≤ L ^ (-θ) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
```

### `WaveTurbulence/Frozen/Theorems/PropansatzV2.lean` (sha256 `67677d439daa2429…`)

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.AnsatzAt
public import WaveTurbulence.Frozen.Defs.IsGaussianData
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Provider.Propansatz

/-!
# propansatz

Wave B tier B1 (WaveB1-Statements.lean), source: T Prop `propansatz`, L689–L707; WAVE-B v2 §4.1; T L819. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.

**B1.1 `propansatz`** (T Prop `propansatz`, L689–L707; + time parameter F7/F27; + L951).
Under (Π), for all probability data of Wave A there are a solution `a`, events `Fev`, two-point
corrections `R, E` and cumulant remainders `Ẽ` such that `AnsatzAt p` holds for every `0 ≤ p ≤ 𝔇`.
Deviations (WAVE-B v2 §4.1): (D1) `R p` is a real `C^{Λ_p}` function on `ℝ^d` with the `ℝ^d` 𝔖-norm
(regularity from the norm bound for `Λ_p ≠ 0`, `contDiff_of_SNormR_lt_top`; stage-3 R1, option B);
(D2) the cumulant of (ansatz1) is written as the moment; (D3) item (2') (intermediate times) is
new, constant `2`; (D4) uniqueness in the classed solution notion (Q16, C1); (D5) measurability
(`Measurable`, C1) and integrability conjuncts added; (D6) the sums of (3)–(4) are the shared
`truncSum` (equal to the source's untruncated sums: `truncSum_untruncated`); (D7, DESIGN Q5)
symmetric events are preimages of invariant sets of initial data.
Beyond the frozen anchors, `main` needs three unfrozen glue lemmas (stage-3 O8): mass conservation for
smooth NLS solutions (T L819), the almost-sure rapid decay of `initialCoeff` (PROB.smoothData), and the
Gaussian moments of the mass `∑ φin(n/L)|g_n|²`. -/
theorem propansatz_v2 : WTPrefix fun P => 1 / 2 < P.γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∃ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      ∀ p ≤ P.D, AnsatzAt P μ g a Fev R E Et p :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
```

### `WaveTurbulence/Frozen/Theorems/LayergardenV2.lean` (sha256 `f2272693676bca80…`)

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleRemainder
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.IsBalancedSig
public import WaveTurbulence.Frozen.Defs.JbrProd
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.SNorm
public import WaveTurbulence.Frozen.Defs.TruncSum
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTParamsR
public import WaveTurbulence.Frozen.Defs.WTParamsTheta
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Provider.Layergarden

/-!
# layergarden

Wave B tier B1 (WaveB1-Statements.lean), source: T Prop `layergarden`, L761–L779; T L776; WAVE-B v2 §4.2; T L762. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.

**B1.2 `layergarden`** (T Prop `layergarden`, L761–L779; deterministic, F36; time parameter
F27). For `0 ≤ p < 𝔇`, remainders with (ansatz2) bounds, inputs `F_q = φ(δq) + R_q`, every
`t ∈ (p, p+1]` and `N ≤ N_{p+1}^4`: (1) for `2 ≤ m ≤ 10 R_{p+1}` the truncated garden sum is
`≤ (∏⟨n_j⟩)^{-4Λ_{p+1}} L^{-(m-1)/4} δ^{2νN}`; (2)(a) the lattice couple sum vanishes off the diagonal;
(2)(b) `k ↦ 𝒦^tr_{p+1,N}(t;k) - [N even] 𝒰^{(p)}_{N/2}(t,k)` has
`𝔖^{4Λ_{p+1},4Λ_{p+1}}` norm `≤ L^{-(4θ_{p+1}+θ_p)/5} δ^{2νN}` (so it is `C^{4Λ_{p+1}}`; TARGET L776
claims no more: a smoothness conjunct was false, stage-3 R2).
Deviations (WAVE-B v2 §4.2): (D1) the induction hypothesis is replaced by `RemainderBound`;
(D2) `t ∈ (p, p+1]`; (D3) (estcouple)+(estcouple2) merged; (D4) shared sums; (D5) general carriers.
Note T L762: for `N ≤ N_{p+1}^4` the attached-garden truncation is void. -/
theorem layergarden_v2 : WTPrefix fun P => 1 / 2 < P.γ →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioc (p : ℝ) (p + 1), ∀ N ≤ P.N (p + 1) ^ 4,
      (∀ m : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → ∀ ζ : Fin (2 * m) → ℤˣ, IsBalancedSig ζ →
        ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
          ‖truncSum P (inputsF P R) (p + 1) N t ζ n‖ ≤
            jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
              P.δ ^ (2 * P.ν * N)) ∧
      (∀ n : Fin 2 → (Fin P.d → ℤ), n 0 ≠ n 1 →
        truncSum P (inputsF P R) (p + 1) N t ![1, -1] n = 0) ∧
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
        ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
```

### `WaveTurbulence/Frozen/Theorems/FixedpointV2.lean` (sha256 `d10ca91da69b2610…`)

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ATr
public import WaveTurbulence.Frozen.Defs.AnsatzAt
public import WaveTurbulence.Frozen.Defs.IsGaussianData
public import WaveTurbulence.Frozen.Defs.IsSymmetricEvent
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Lop
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.ZNorm
public import WaveTurbulence.Frozen.Defs.ZSpace
public import WaveTurbulence.Provider.Fixedpoint

/-!
# fixedpoint

Wave B tier B1 (WaveB1-Statements.lean), source: T Prop `fixedpoint`, L780–L794; WAVE-B v2 §4.3. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.

**B1.3 `fixedpoint`** (T Prop `fixedpoint`, L780–L794). For probability data, `0 ≤ p < 𝔇` and
ansatz data with `AnsatzAt q` for all `q ≤ p`, with `𝒥_N, a^tr, ℒ_j` built from `a(p)` and
`Z = Z^{(5/4)Λ_{p+1}}([p,p+1])`, there is a measurable symmetric `F' ⊆ F_p` with
`P(F_p ∖ F') ≤ e^{-4N_{p+1}}` on which: (1) `|a^tr_n(t)| ≤ ⟨n⟩^{-(3/2)Λ_{p+1}} e^{3N_{p+1}}`;
(2) `|(ℒ₀)_n(t)| ≤ ⟨n⟩^{-(3/2)Λ_{p+1}} e^{-20N_{p+1}}`; (3) `1 - ℒ₁` maps `Z` into `Z`, is a bijection
of `Z`, and `‖b‖_Z ≤ e^{3N_{p+1}} ‖(1-ℒ₁)b‖_Z`; (4) for `b, b'` in the ball `B` of radius
`e^{-10N_{p+1}}`, the solution `Φ(b) ∈ Z` of `(1-ℒ₁)Φ(b) = ℒ₀ + ℒ₂(b,b) + ℒ₃(b,b,b)` lies in `B`, and
`‖Φ(b) - Φ(b')‖_Z ≤ ½‖b - b'‖_Z`. Deviations (WAVE-B v2 §4.3): (D1) contraction constant `½`;
(D2) continuity in `Z`; (D3) F9 conjugations; (D4) `(1-ℒ₁)^{-1}` expressed through unique
solvability. -/
theorem fixedpoint_v2 : WTPrefix fun P => 1 / 2 < P.γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∀ p : ℕ, p < P.D →
    ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
    ∃ F' : Set Ω, F' ⊆ Fev p ∧ MeasurableSet F' ∧ IsSymmetricEvent P.L P.φin g F' ∧
      μ.real (Fev p \ F') ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) ∧
      ∀ ω ∈ F',
        let Ntr := P.N (p + 1)
        let Λ : ℝ := 5 / 4 * P.Lambda (p + 1)
        let ℒ : ℕ → (Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) →
            Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ :=
          fun j b t n => Lop P.L P.γ P.δ p Ntr (a ω p) j b t n
        let Zs := ZSpace (d := P.d) P.L Λ p
        (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
          ‖aTr P.L P.γ P.δ p Ntr (a ω p) t n‖ ≤
            jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
              Real.exp (3 * Ntr)) ∧
        (∀ (b : Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) (t : Icc (p : ℝ) (p + 1)) (n),
          ‖ℒ 0 b t n‖ ≤ jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
            Real.exp (-(20 * Ntr : ℝ))) ∧
        (∀ b ∈ Zs, b - ℒ 1 b ∈ Zs) ∧
        (∀ c ∈ Zs, ∃! b, b ∈ Zs ∧ b - ℒ 1 b = c) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (3 * Ntr)) * ZNorm P.L Λ (b - ℒ 1 b)) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ∃ c ∈ Zs, c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b ∧
            ZNorm P.L Λ c ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ)))) ∧
        (∀ b ∈ Zs, ∀ b' ∈ Zs, ∀ c ∈ Zs, ∀ c' ∈ Zs,
          ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ZNorm P.L Λ b' ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b → c' - ℒ 1 c' = ℒ 0 b' + ℒ 2 b' + ℒ 3 b' →
          ZNorm P.L Λ (c - c') ≤ 2⁻¹ * ZNorm P.L Λ (b - b')) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
```

### `WaveTurbulence/Frozen/Theorems/LayergardenFlowerV2.lean` (sha256 `5fb5f6fc43015fef…`)

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleSum
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.FlowerKind
public import WaveTurbulence.Frozen.Defs.FlowerSum
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.InstDecidableEqFixPat
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.TreeKind
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefixP
public import WaveTurbulence.Provider.LayergardenFlower

/-!
# layergardenFlower

Wave B tier B1 (WaveB1-Flower.lean), source: T Prop `flowerest1`, L2279–L2305; T L2306–L2338; WAVE-B v2 §4.15; T L2280; T (flowerest2); T (newnormn); T L2331; T L2312; T L2290. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
open Classical in
/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.

**B1.12 `layergardenFlower`** (T Prop `flowerest1`, L2279–L2305, deterministic core; T L2306–L2338 for
its uses; review G-1, stage-3 R8, WAVE-B v2 §4.15).

Setting: `(Π_P)`, `0 ≤ p < 𝔇`, remainders as in B1.2, inputs `F_q = φ(δq) + R_q`.

**(1) Flower gardens of width `2P`.** For `p < s < t < p+1` (T's range for the flower kernels, L2263),
`n, n' ∈ ℤ^d`, `ζ`, `N ≤ N_{p+1}^4`, every kind (`𝒳`, `𝒴`, `𝒲`), every pattern vector, with or without `†`
and the cutoffs:

  `|flowerSum| ≤ ⟨k − ζk'⟩^{−4Λ_{p+1}P} L^{c(100d)³P} δ^{2νN} · M₁^{−80dP} · M₂^{−P/9}`

- `c = 1` if all patterns are plain, `c = 2` otherwise.
- The `M₁` factor is present iff the `M₁` cutoff is, also for derivative patterns.
- The `M₂` factor is present iff the `M₂` cutoff is and all patterns are plain. The `M₂` cutoff requires the
  `M₁` cutoff and `|k| ≥ M₁^{10}`.

**(2) Couples.** For `p < t < p+1`, `k ∈ ℝ^d`, `N ≤ N_{p+1}^4`, kind `ℒ₀`, or kind `a^tr` with `∂_t`:

  `|coupleSum| ≤ ⟨k⟩^{−4Λ_{p+1}} L^{100d} δ^{νN}`

**Uses.**
- The `𝒴`/`𝒲` gain `e^{−100N_{p+1}}` (T L2280) comes from summing over `N ≥ 2P(N_{p+1}+1)`, the kinds'
  lower bound.
- The bounds of (1) give T (flowerest2) with its cutoff variants, and T (newnormn) with the `∂_{t,s}` terms
  of (sobolev2), T L2331.
- Those of (2) give (trterm1) for `ℒ₀`, and for `∂_t a^tr`, `∂_t ℒ₀` with an extra `L^{100d}` (T L2312).

**Deviations** (FLOWER-DESIGN.md):
- (D1) The moment expansions `𝔼_p|𝒦|^{2P} = ∑ + errors` are left to T.flowerest1 and T.fp.part1. This gate
  is their deterministic core.
- (D2) Per-order bounds with `δ^{2νN}` (flowers) and `δ^{νN}` (couples).
- (D3) Range `N ≤ N_{p+1}^4` (T L2290).
- (D4) Prefactor `L^{d−γ}` (F25).
- (D5) Kind `𝒳` excludes the trivial flower tree (F39).
- (D6) `𝒴`/`𝒲` replace the top bound (F46).
- (D7) Explicit dyadic cutoffs.
- (D8) The derivative patterns and `†` as designated nodes, removed phases and weights (R8).
- (D9) `L^{2(100d)³P}` for derivative patterns.
- (D10) The couple clause covers `ℒ₀`, which B1.2 does not.
- (D11) Per-tree choices: the `†` labels `c j` and the patterns `pat j` may differ between the trees `j` of
  the garden. The consumer uses one uniform choice, so this is more general than `fixedpoint` needs (the
  proof is per tree). -/
theorem layergardenFlower_v2 : WTPrefixP fun Pm P => 1 / 2 < P.γ →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSum P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
```

