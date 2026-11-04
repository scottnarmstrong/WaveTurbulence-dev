/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SelectedClockDomain

/-!
# Literal causal order of the tree root and lone-parent clocks

Their order follows from the selected descendant chain, independently of
any analytic estimates or time-domain integral representation.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The first and last selected vertices have strictly ordered source clocks. -/
theorem TreeClockFibers.root_order {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    (w : Fin n → Fin 2 → ℝ) (hw : w ∈ T.timeDomain) :
    (R.equiv w).1 1 < (R.equiv w).1 0 := by
  have h0 : (R.equiv w).1 0 = (T.selection.coordinates.equiv w).1 0 := by
    rw [R.equiv_fst_apply, T.selection.coordinates.equiv_fst_apply, hfirst]
  have h1 : (R.equiv w).1 1 = (T.selection.coordinates.equiv w).1 (Fin.last (m + 1)) := by
    rw [R.equiv_fst_apply, T.selection.coordinates.equiv_fst_apply, hlast]
  rw [h0, h1]
  exact (Fin.strictAnti_iff_succ_lt.mpr hw.2.2) (by simp [Fin.lt_def])

end WaveTurbulence.Incoh
