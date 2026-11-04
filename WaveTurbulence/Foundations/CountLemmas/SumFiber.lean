/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PositiveAtomReduction

/-! # Bilinear energy bands at fixed vector sum -/

public section
open Finset Set
namespace WaveTurbulence.CountLemmas

/-- At fixed sum, a bilinear band is precisely a same-sign atomic energy
band. The finite-family form is used inside projection fibers. -/
theorem card_fixed_sum_band_le {d : ℕ} {L τ : ℝ} (hL : 0 < L)
    (hτ : 0 ≤ τ) (hW : 1 ≤ τ*L^2) (a b : Mom (d+2))
    (nk : Fin (d+2) → ℤ) (α : ℝ)
    (s : Finset ((Fin (d+2) → ℤ) × (Fin (d+2) → ℤ)))
    (hs : ∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧ q.1+q.2 = nk ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ) :
    (s.card : ℝ) ≤ (2*L+1)^d*(6*Real.pi+1284002)*(2*τ*L^2+L) := by
  have hsub : (s : Set _) ⊆ atomPairSet L a b nk (‖latticePoint L nk‖^2-2*α) (2*τ) 1 := by
    intro q hq
    obtain ⟨ha,hb,hcon,he⟩ := hs q hq
    refine ⟨ha,hb,by simpa using hcon,?_⟩
    have hk : latticePoint L q.1+latticePoint L q.2 = latticePoint L nk := by
      rw [← WeylSums.latticePoint_add_eq,hcon]
    have hid : ‖latticePoint L q.1‖^2+‖latticePoint L q.2‖^2-
        (‖latticePoint L nk‖^2-2*α) =
        -2*(inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α) := by
      rw [← hk,norm_add_sq_real]
      ring
    simp only [Units.val_one,Int.cast_one,one_mul]
    rw [hid,abs_mul]
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left he (by norm_num)
  have hc := Set.ncard_le_ncard hsub (finite_atomPairSet hL a b nk _ _ 1)
  have hcR : (s.card : ℝ) ≤ (atomPairSet L a b nk (‖latticePoint L nk‖^2-2*α) (2*τ) 1).ncard := by
    exact_mod_cast (by simpa only [Set.ncard_coe_finset] using hc)
  exact hcR.trans (positive_atom_shell_bound hL (by positivity)
    (by linarith only [hW]) a b nk _)

end WaveTurbulence.CountLemmas
