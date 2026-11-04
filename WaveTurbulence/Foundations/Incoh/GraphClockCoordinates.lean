/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.GraphClockBounds
public import WaveTurbulence.Foundations.Incoh.RootCoordinatesOfEmbedding

/-! # Reading the selected and remaining actual branching clocks -/

public section
noncomputable section
namespace WaveTurbulence.Incoh

/-- Reading a remaining coordinate after splitting reads its original source vertex. -/
theorem RootCoordinates.equiv_restVertex {n r : ℕ} (R : RootCoordinates n r)
    (t : Fin n → Fin 2 → ℝ) (k : Fin R.restCount) :
    (R.equiv t).2 k = t (R.restVertex k).1 (R.restVertex k).2 := by
  have h : R.equiv.symm ((R.equiv t).1, (R.equiv t).2)
      (R.restVertex k).1 (R.restVertex k).2 = (R.equiv t).2 k := by
    rw [R.equiv_symm_apply]
    simp only [RootCoordinates.restVertex, Prod.mk.eta, Equiv.apply_symm_apply, Sum.elim_inr]
  simpa only [Prod.eta, MeasurableEquiv.symm_apply_apply] using h.symm

/-- Every actual vertex is either one selected clock or one remaining clock. -/
theorem RootCoordinates.vertex_cases {n r : ℕ} (R : RootCoordinates n r)
    (v : Fin n × Fin 2) :
    (∃ j, v = R.rootVertex j) ∨ (∃ k, v = R.restVertex k) := by
  rcases he : R.permutation (finProdFinEquiv v) with j | k
  · left
    refine ⟨j, ?_⟩
    change v = finProdFinEquiv.symm (R.permutation.symm (Sum.inl j))
    rw [← he, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · right
    refine ⟨k, ?_⟩
    change v = finProdFinEquiv.symm (R.permutation.symm (Sum.inr k))
    rw [← he, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end WaveTurbulence.Incoh
