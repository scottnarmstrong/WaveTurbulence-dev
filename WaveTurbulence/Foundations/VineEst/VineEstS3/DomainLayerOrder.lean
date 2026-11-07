/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.SumintDatum

public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible

public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec

public import WaveTurbulence.Frozen.Defs.SumintDatumExpr

public import WaveTurbulence.Frozen.Defs.SumintDatumKVec

public import WaveTurbulence.Frozen.Defs.SumintDatumM0

public import WaveTurbulence.Frozen.Defs.SumintDatumM1

public import WaveTurbulence.Frozen.Defs.SumintDatumPhase

public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom

public import WaveTurbulence.Frozen.Defs.SumintShape

public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt

public import WaveTurbulence.Frozen.Defs.SumintShapeM

public import WaveTurbulence.Frozen.Defs.SumintShapeN

public import WaveTurbulence.Frozen.Defs.SumintShapeTVar

public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot

public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot

public import WaveTurbulence.Frozen.Defs.WTPrefixA

public import WaveTurbulence.Frozen.Defs.EpsCoef

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # The layer-order domain lemma (R20 (2), TARGET L1846-L1847)

Adding to the constraint set of a `sumint` datum pairs `(v, w)` with `q v + 1 ≤ q w` (unit-interval order) changes the
time domain only by a Lebesgue null set: on the window `[q v, q v + 1] × [q w, q w + 1]` one has `τ v ≤ τ w`
automatically, and equality is a hyperplane.  So the integral over the domain is unchanged.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence MeasureTheory Set

variable {d : ℕ}

theorem volume_diag_null {ι : Type*} [Fintype ι] {i j : ι} (h : i ≠ j) :
    volume {τ : ι → ℝ | τ i = τ j} = 0 := by
  classical
  let K : Submodule ℝ (ι → ℝ) := LinearMap.ker ((LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj j : (ι → ℝ) →ₗ[ℝ] ℝ))
  have hK : K ≠ ⊤ := by
    intro htop
    have : (Pi.single i (1 : ℝ) : ι → ℝ) ∈ K := by rw [htop]; trivial
    simp [K, h] at this
  have := Measure.addHaar_submodule (volume : Measure (ι → ℝ)) K hK
  convert this using 2
  ext τ
  simp [K, sub_eq_zero]

/-- **Domain lemma.**  Extra constraints between unit intervals in strict order change the time domain by a null set. -/
theorem timeDom_ae_eq_of_layer_order (D : SumintDatum d) (C : Finset (D.S.TVar × D.S.TVar))
    (hsub : C ⊆ D.constraints) (hex : ∀ c ∈ D.constraints, c ∉ C → D.q c.1 + 1 ≤ D.q c.2)
    (hI : 0 < D.S.I) (t t' t'' : ℝ) :
    D.timeDom hI t t' t'' =ᵐ[volume] ({D with constraints := C} : SumintDatum d).timeDom hI t t' t'' := by
  rw [Filter.eventuallyEq_set]
  have hN : ∀ᵐ τ : D.S.TVar → ℝ, ∀ c ∈ D.constraints, c ∉ C → τ c.1 ≠ τ c.2 := by
    rw [Filter.eventually_all_finset]
    intro c hc
    by_cases hcC : c ∈ C
    · exact Filter.Eventually.of_forall fun τ h => absurd hcC h
    · have hlt := hex c hc hcC
      have hne : c.1 ≠ c.2 := by
        intro h
        rw [h] at hlt
        omega
      have h0 := volume_diag_null (ι := D.S.TVar) hne
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with τ hτ _ using hτ
  filter_upwards [hN] with τ hτ
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun c hc => h3 c (hsub hc)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun c hc => ?_⟩
    by_cases hcC : c ∈ C
    · exact h3 c hcC
    · have h5 := hex c hc hcC
      have a1 := (h1 c.1).2.1
      have a2 := (h1 c.2).1
      have a3 : (D.q c.1 : ℝ) + 1 ≤ D.q c.2 := by exact_mod_cast h5
      have : τ c.1 ≤ τ c.2 := by linarith
      exact lt_of_le_of_ne this (hτ c hc hcC)

end WaveTurbulence.VineEstS3
