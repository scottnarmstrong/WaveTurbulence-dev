/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumSpectralShift

/-! # Polynomial moments of the actual source root frequency

Every leaf profile has root coefficient one, and every link profile has
root coefficient zero. A product of individual leaf moments controls the
root frequency without additional derivative allocations.
-/

public section
noncomputable section
open WithLp

namespace WaveTurbulence.Incoh

/-- Elementary positive product bound, including the empty input family. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : 1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self _ _)
      have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum := Finset.sum_nonneg hfs
      have hp : 1 ≤ ∏ i ∈ s, (1 + f i) :=
        Finset.one_le_prod₀ (fun i hi => by linarith [hfs i hi])
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hh := ih hfs
      nlinarith only [hh, hp, hfa, mul_nonneg hfa (sub_nonneg.mpr hp)]

/-- The root Fourier shift is literally the sum of the leaf-profile frequencies. -/
theorem MomentumTreeData.spectralShift_none {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    P.spectralShift ξ none = ∑ a : Fin m, toLp 2 (ξ (.inl a)) := by
  simp [spectralShift, profileRow, P.input_root_column, momentumUnitRow]

/-- Every root-frequency moment is bounded by a product of the individual leaf moments. -/
theorem MomentumTreeData.norm_spectralShift_none_pow_le {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (J : ℕ) :
    ‖P.spectralShift ξ none‖ ^ J ≤ ∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) ^ J := by
  have hsum := one_add_sum_le_prod_one_add Finset.univ
    (fun a : Fin m => ‖toLp 2 (ξ (.inl a))‖) (fun a _ => norm_nonneg _)
  have hn : ‖P.spectralShift ξ none‖ ≤ ∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) := by
    rw [P.spectralShift_none]
    exact (norm_sum_le _ _).trans (by linarith only [hsum])
  simpa only [Finset.prod_pow] using pow_le_pow_left₀ (norm_nonneg _) hn J

end WaveTurbulence.Incoh
