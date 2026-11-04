/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootGeometry

/-!
# Completing one genuine root clock by an auxiliary branching clock

A nontrivial incoherent object has at least one link and hence two
branching clocks. A finite permutation puts any chosen genuine root in
either selected position; the other position is automatically auxiliary.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Explicit selection of an arbitrary genuine root and one auxiliary branching clock. -/
@[expose] def oneClockSelection (n : ℕ) (hn : 1 ≤ n) (v : Fin n × Fin 2) (a : Fin 2) :
    RootCoordinates n where
  restCount := n * 2 - 2
  permutation :=
    (Equiv.swap (finProdFinEquiv v) (Fin.castLE (by omega : 2 ≤ n * 2) a)).trans
      ((finCongr (by omega : n * 2 = 2 + (n * 2 - 2))).trans finSumFinEquiv.symm)

/-- The genuine root occupies the requested selected external-clock position. -/
theorem oneClockSelection_rootVertex (n : ℕ) (hn : 1 ≤ n) (v : Fin n × Fin 2) (a : Fin 2) :
    (oneClockSelection n hn v a).rootVertex a = v := by
  let R := oneClockSelection n hn v a
  have hp : R.permutation (finProdFinEquiv v) = Sum.inl a := by
    change finSumFinEquiv.symm
      ((finCongr (by omega : n * 2 = 2 + (n * 2 - 2)))
        (Equiv.swap (finProdFinEquiv v) (Fin.castLE (by omega : 2 ≤ n * 2) a) (finProdFinEquiv v))) = _
    rw [Equiv.swap_apply_left]
    have he : (finCongr (by omega : n * 2 = 2 + (n * 2 - 2)))
        (Fin.castLE (by omega : 2 ≤ n * 2) a) = Fin.castAdd (n * 2 - 2) a := by
      ext
      rfl
    rw [he, finSumFinEquiv_symm_apply_castAdd]
    rfl
  change finProdFinEquiv.symm (R.permutation.symm (Sum.inl a)) = v
  rw [← hp, R.permutation.symm_apply_apply, finProdFinEquiv.symm_apply_apply]

end WaveTurbulence.Incoh
