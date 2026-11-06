/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ProperGardenZero
/-! Exact vanishing of the proper-garden truncated sum at order zero. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem truncSum_zero_of_proper (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (p : ℕ) {w : ℕ} (hw : 4 ≤ w) (t : ℝ) (ζ : Fin w → ℤˣ)
    (n : Fin w → (Fin P.d → ℤ)) : truncSum P F (p + 1) 0 t ζ n = 0 := by
  unfold truncSum
  apply finsum_eq_zero_of_forall_eq_zero
  intro LG
  have hnot : ¬ (IsCanonGC (p + 1) LG ∧
      LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LG.garden.sig = ζ ∧ LG.garden.order = 0) := by
    intro hm
    have hc := hm.1
    have hp : LG.garden.IsPlain := hc.1
    have hi : LG.garden.Irreducible := by
      rcases hc.2.1 with ⟨_, hi⟩ | ⟨h2, _⟩
      · exact hi
      · omega
    exact not_irreducible_of_plain_order_zero hw LG.garden hp hm.2.2.2 hi
  letI : IsEmpty (IsCanonGC (p + 1) LG ∧
      LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LG.garden.sig = ζ ∧ LG.garden.order = 0) := ⟨hnot⟩
  exact finsum_of_isEmpty _

end WaveTurbulence.LGSpine
