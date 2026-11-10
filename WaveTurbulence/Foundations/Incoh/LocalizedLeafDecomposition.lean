/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FiniteLinkCellLocalization
public import WaveTurbulence.Foundations.Incoh.SmoothLeafCells

/-!
# Exact finite smooth decomposition of localized source inputs

TARGET (incohproof4–8): the half-width link partition is finite on each
actual leaf localization, with a dimensional exponential cardinal bound.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The literal localized product of the source input functions. -/
@[expose] def MomentumTreeData.localizedLeafWeight {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) : ℂ :=
  ∏ a, leafCell (f a) (c a) (P.inputMomentum k x a)

/-- The actual leaf localization factors out of the source input product. -/
theorem MomentumTreeData.localizedLeafWeight_eq {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    P.localizedLeafWeight f c k x =
      (∏ a, f a (P.inputMomentum k x a)) * P.inputCellWeight c k x := by
  simp only [localizedLeafWeight, leafCell, inputCellWeight, leafCellProfile,
    Finset.prod_mul_distrib]

end WaveTurbulence.Incoh
