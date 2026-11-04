/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Statement
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # The NT frequency length is bounded by the sum of link lengths -/

public section
namespace WaveTurbulence.RegAsymp

/-- Euclidean block length loses no dimension-dependent derivative factor. -/
theorem freqNorm_le_sum {d n : ℕ} (ξ η : Fin n → Mom d) :
    ApproxNT.freqNorm ξ η ≤ ∑ j, (‖ξ j‖+‖η j‖) := by
  let f : Fin n × Fin 2 → ℝ := fun p => if p.2=0 then ‖ξ p.1‖ else ‖η p.1‖
  have hf (p : Fin n × Fin 2) : 0 ≤ f p := by
    dsimp only [f]
    split <;> exact norm_nonneg _
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun p _ => hf p)
  have he : (∑ p : Fin n × Fin 2, f p^2) = ∑ j, (‖ξ j‖^2+‖η j‖^2) := by
    simp [f,Fintype.sum_prod_type,Fin.sum_univ_two]
  have hs : (∑ p : Fin n × Fin 2, f p) = ∑ j, (‖ξ j‖+‖η j‖) := by
    simp [f,Fintype.sum_prod_type,Fin.sum_univ_two]
  rw [he,hs] at hh
  unfold ApproxNT.freqNorm
  apply (Real.sqrt_le_iff).mpr
  exact ⟨Finset.sum_nonneg (fun j _ => by positivity),hh⟩

end WaveTurbulence.RegAsymp
