/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsSpart3

/-! # Algebra of `SAbs` (V5 Step 4d part C, `hAbs`, leaf `sb`): congruence on clocks, finite sums, constant multiples -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem sAbs_congr_clock (RS : CLRegionData G S a b) (L : ℝ) (base : Mom d)
    (Ψ Ψ' : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) (C : ℝ)
    (h : ∀ (t : Fin 3 → ℝ) (e f : Mom d) (x : ExtS RS L base e f) (σ : CLInternalTime RS),
      Ψ x.1 (clLocalClock RS t σ) = Ψ' x.1 (clLocalClock RS t σ)) :
    SAbs RS L base Ψ C ↔ SAbs RS L base Ψ' C := by
  unfold SAbs
  refine forall_congr' fun t => forall_congr' fun e => forall_congr' fun f => ?_
  simp_rw [h t e f]

theorem sAbs_mono (RS : CLRegionData G S a b) (L : ℝ) (base : Mom d)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) {C C' : ℝ} (hC : C ≤ C') (h : SAbs RS L base Ψ C) :
    SAbs RS L base Ψ C' := fun t e f => by
  obtain ⟨h1, h2, h3⟩ := h t e f
  exact ⟨h1, h2, h3.trans hC⟩

theorem sAbs_const_mul (RS : CLRegionData G S a b) (L : ℝ) (base : Mom d)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) (c : ℂ) {C : ℝ} (h : SAbs RS L base Ψ C) :
    SAbs RS L base (fun x u => c * Ψ x u) (‖c‖ * C) := fun t e f => by
  obtain ⟨h1, h2, h3⟩ := h t e f
  refine ⟨fun x => (h1 x).const_mul c, ?_, ?_⟩
  · have : (fun x : ExtS RS L base e f => ∫ σ : CLInternalTime RS, ‖c * Ψ x.1 (clLocalClock RS t σ)‖) =
        fun x => ‖c‖ * ∫ σ : CLInternalTime RS, ‖Ψ x.1 (clLocalClock RS t σ)‖ := by
      funext x; simp_rw [norm_mul]; rw [integral_const_mul]
    rw [this]; exact h2.mul_left _
  · have : (fun x : ExtS RS L base e f => ∫ σ : CLInternalTime RS, ‖c * Ψ x.1 (clLocalClock RS t σ)‖) =
        fun x => ‖c‖ * ∫ σ : CLInternalTime RS, ‖Ψ x.1 (clLocalClock RS t σ)‖ := by
      funext x; simp_rw [norm_mul]; rw [integral_const_mul]
    rw [this, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h3 (norm_nonneg c)

theorem sAbs_finsetSum {β : Type*} (RS : CLRegionData G S a b) (L : ℝ) (base : Mom d) (s : Finset β)
    (Ψ : β → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) (C : β → ℝ)
    (h : ∀ i ∈ s, SAbs RS L base (Ψ i) (C i)) :
    SAbs RS L base (fun x u => ∑ i ∈ s, Ψ i x u) (∑ i ∈ s, C i) := fun t e f => by
  classical
  have hh := fun i (hi : i ∈ s) => h i hi t e f
  refine ⟨fun x => ?_, ?_, ?_⟩
  · exact integrable_finsetSum _ fun i hi => (hh i hi).1 x
  · have hle : ∀ x : ExtS RS L base e f, ∫ σ : CLInternalTime RS, ‖∑ i ∈ s, Ψ i x.1 (clLocalClock RS t σ)‖ ≤
        ∑ i ∈ s, ∫ σ : CLInternalTime RS, ‖Ψ i x.1 (clLocalClock RS t σ)‖ := by
      intro x
      rw [← integral_finsetSum _ fun i hi => ((hh i hi).1 x).norm]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun σ => norm_nonneg _)
        (integrable_finsetSum _ fun i hi => ((hh i hi).1 x).norm) (Filter.Eventually.of_forall fun σ => ?_)
      exact norm_sum_le _ _
    exact Summable.of_nonneg_of_le (fun x => integral_nonneg fun _ => norm_nonneg _) hle
      (summable_sum fun i hi => (hh i hi).2.1)
  · have hle : ∀ x : ExtS RS L base e f, ∫ σ : CLInternalTime RS, ‖∑ i ∈ s, Ψ i x.1 (clLocalClock RS t σ)‖ ≤
        ∑ i ∈ s, ∫ σ : CLInternalTime RS, ‖Ψ i x.1 (clLocalClock RS t σ)‖ := by
      intro x
      rw [← integral_finsetSum _ fun i hi => ((hh i hi).1 x).norm]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun σ => norm_nonneg _)
        (integrable_finsetSum _ fun i hi => ((hh i hi).1 x).norm) (Filter.Eventually.of_forall fun σ => ?_)
      exact norm_sum_le _ _
    have hs : Summable fun x : ExtS RS L base e f => ∑ i ∈ s, ∫ σ : CLInternalTime RS, ‖Ψ i x.1 (clLocalClock RS t σ)‖ :=
      summable_sum fun i hi => (hh i hi).2.1
    have hs0 : Summable fun x : ExtS RS L base e f => ∫ σ : CLInternalTime RS, ‖∑ i ∈ s, Ψ i x.1 (clLocalClock RS t σ)‖ :=
      Summable.of_nonneg_of_le (fun x => integral_nonneg fun _ => norm_nonneg _) hle hs
    calc ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS, ‖∑ i ∈ s, Ψ i x.1 (clLocalClock RS t σ)‖
        ≤ ∑' x : ExtS RS L base e f, ∑ i ∈ s, ∫ σ : CLInternalTime RS, ‖Ψ i x.1 (clLocalClock RS t σ)‖ :=
          hs0.tsum_le_tsum hle hs
      _ = ∑ i ∈ s, ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS, ‖Ψ i x.1 (clLocalClock RS t σ)‖ :=
          (Summable.tsum_finsetSum fun i hi => (hh i hi).2.1)
      _ ≤ ∑ i ∈ s, C i := Finset.sum_le_sum fun i hi => (hh i hi).2.2

end WaveTurbulence.VineEstS5C
