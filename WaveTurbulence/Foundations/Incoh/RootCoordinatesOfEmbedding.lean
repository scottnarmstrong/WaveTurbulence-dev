/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootGeometry

/-! # Constructing the analytic clock split from actual selected vertices -/

public section
noncomputable section
open scoped Classical

namespace WaveTurbulence.Incoh

/-- Reading a selected coordinate after splitting reads the original selected vertex. -/
theorem RootCoordinates.equiv_rootVertex {n r : ℕ} (R : RootCoordinates n r)
    (t : Fin n → Fin 2 → ℝ) (j : Fin r) :
    (R.equiv t).1 j = t (R.rootVertex j).1 (R.rootVertex j).2 := by
  have h := R.equiv_symm_rootVertex (R.equiv t).1 (R.equiv t).2 j
  simpa only [Prod.eta, MeasurableEquiv.symm_apply_apply] using h.symm

/-- Select actual distinct branching clocks and enumerate exactly their complement. -/
@[expose] def rootCoordinatesOfEmbedding {n r : ℕ} (v : Fin r ↪ (Fin n × Fin 2)) : RootCoordinates n r := by
  let f : Fin r ↪ Fin (n * 2) := v.trans finProdFinEquiv.toEmbedding
  let C := {i : Fin (n * 2) // i ∉ Set.range f}
  exact
    { restCount := Fintype.card C
      permutation := ((Equiv.sumCongr (Equiv.ofInjective f f.injective)
        (Fintype.equivFin C).symm).trans (Equiv.Set.sumCompl (Set.range f))).symm }

/-- The computed selected vertex is exactly the source vertex used to construct the split. -/
theorem rootCoordinatesOfEmbedding_rootVertex {n r : ℕ} (v : Fin r ↪ (Fin n × Fin 2)) (j : Fin r) :
    (rootCoordinatesOfEmbedding v).rootVertex j = v j := by
  change finProdFinEquiv.symm (finProdFinEquiv (v j)) = v j
  exact finProdFinEquiv.symm_apply_apply (v j)

end WaveTurbulence.Incoh
