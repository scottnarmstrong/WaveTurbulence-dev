/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.TypeFamilyST
public import WaveTurbulence.Foundations.FlowerTop.Port.AnchoredGardenWeights
/-! Exact comparison of the adopted partner-anchor convention and X5's two-member convention. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.S2ST
open LGSpine FlowerX7X5
open scoped Classical

/-- Both conventions agree on an ordinary leaf whose own tree is not an anchor. -/
theorem anchor_profiles_eq_away {w d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (a : GLeaf LG.garden.tree) (ha : a.1.1 ∉ J) :
    typeProfilesAnch J LG h a.1 = anchoredProfiles LG J (fun t => h t.1 t.2.1 t.2.2) a.1 := by
  funext x
  rw [typeProfilesAnch_leaf, anchoredProfiles_leaf]
  simp only [isAnchorType, pairType, ha, false_or, ite_apply]

/-- X5 makes an own-tree anchor profile one, irrespective of its partner. -/
theorem own_anchor_profile {w d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (a : GLeaf LG.garden.tree) (ha : a.1.1 ∈ J) :
    anchoredProfiles LG J (fun t => h t.1 t.2.1 t.2.2) a.1 = fun _ => 1 := by
  funext x
  rw [anchoredProfiles_leaf]
  exact ite_eq_left (Or.inl ha)

/-- A precise obstruction to an unconditional bridge: with zero input profile,
LG reads zero at an own-tree anchor paired outside J, while X5 reads one. -/
theorem own_anchor_profile_mismatch {w d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (a : GLeaf LG.garden.tree) (ha : a.1.1 ∈ J) (hp : (LG.garden.pair a).1.1 ∉ J) :
    typeProfilesAnch (d := d) J LG (fun _ _ _ _ => (0 : ℝ)) a.1 ≠
      anchoredProfiles LG J (fun _ _ => (0 : ℝ)) a.1 := by
  rw [typeProfilesAnch_leaf, ite_eq_right hp]
  have hx := own_anchor_profile (d := d) LG J (fun _ _ _ _ => (0 : ℝ)) a ha
  rw [hx]
  intro he
  have := congrFun he (0 : Mom d)
  exact zero_ne_one this
end WaveTurbulence.S2ST
