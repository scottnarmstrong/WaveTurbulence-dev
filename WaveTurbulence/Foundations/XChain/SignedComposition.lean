/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SignedSeries
/-! The root sign and the intrinsic tree sign compose to the actual global node sign. -/
public section
namespace WaveTurbulence.Induct

theorem zpowSign_comp (a b : ℤˣ) (z : ℂ) : zpowSign a (zpowSign b z) = zpowSign (a * b) z := by
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;> simp [zpowSign]

theorem nodeSign_single_mul {w : ℕ} (sig : Fin w → ℤˣ) (T : Fin w → TTree) (j : Fin w)
    (a : GNode (single (T j))) :
    sig j * treeSign (T j) a = nodeSign sig (j, a.1.2) := by
  simp only [treeSign, nodeSign, TTree.pathSign, one_mul]

end WaveTurbulence.Induct
