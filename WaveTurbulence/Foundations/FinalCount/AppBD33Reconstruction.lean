/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33CutData
import Mathlib.Tactic

/-! # Reconstruction of the fourth label in a degree-three double pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The fourth double-pair label is reconstructed from the first three
using actual momentum at the second degree-three atom. -/
theorem appb_d33_projection_injective {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn ((appbD33Frame r).project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  intro q hq q' hq' he
  obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q).mp hq
  obtain ⟨κ',hκ',rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q').mp hq'
  have h0 := congrFun he (0 : Fin 3)
  have h1 := congrFun he (1 : Fin 3)
  have h2 := congrFun he (2 : Fin 3)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · apply r.local_label_eq_of_others hL.ne'
      (mem_image_of_mem _ (show 2 ∈ AppbPatternKind.d33.pattern.removed by decide)) ⟨3,by decide⟩
      (by rw [r.edge_incidence _ 2 (by decide)]; decide) w p.momentum κ κ' hκ.1 hκ'.1
    intro j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact False.elim (hj rfl)

end WaveTurbulence.Mole
