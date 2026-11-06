/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootModifiedProfiles
/-! Each input receives at most 4m coordinate factors from even root weights of order 2m.
The bound is independent of the number of roots, by the actual leaf pairing. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem root_of_rootInputSlot_eq {w : ℕ} (G : Garden w) (hp : G.IsPlain) {j : Fin w}
    (a : RootLeafSlots G j) (l : ActualInputLeaves G) (h : rootInputSlot G hp j a = l) :
    j = l.1.1.1 ∨ j = (G.pair l.1).1.1 := by
  have ha : a.1.1.1 = j := by
    have hm : a.1 ∈ (GNode.root G.tree j).leavesBelow := a.2
    have hx : (GNode.root G.tree j).IsDesc a.1.toNode := (mem_filter.mp hm).2
    exact hx.1.symm
  have he : positiveRepresentative G a.1 = l.1 := congrArg Subtype.val h
  rcases eq_or_pair_of_positiveRepresentative_eq G a.1 l.1 he with he | he
  · exact Or.inl (ha.symm.trans (congrArg (fun x : GLeaf G.tree => x.1.1) he))
  · exact Or.inr (ha.symm.trans (congrArg (fun x : GLeaf G.tree => x.1.1) he))

theorem rootCoordinateSlots_root {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (c : RootWeightChoices G d m) (t : (Fin w × Fin m) × Bool)
    (l : ActualInputLeaves G) (q : Fin d) (h : rootCoordinateSlots G hp c t = some (l, q)) :
    t.1.1 = l.1.1.1 ∨ t.1.1 = (G.pair l.1).1.1 := by
  rcases t with ⟨⟨j, a⟩, b⟩
  cases hc : c j a with
  | none => simp only [rootCoordinateSlots, hc, mapQuadraticChoice, quadraticCoordinate] at h; cases h
  | some z =>
    rcases z with ⟨r, l₁, l₂⟩
    cases b
    · simp only [rootCoordinateSlots, hc, mapQuadraticChoice, quadraticCoordinate,
        Bool.false_eq_true, ite_false] at h
      exact root_of_rootInputSlot_eq G hp l₁ l (Prod.mk.inj (Option.some.inj h)).1
    · simp only [rootCoordinateSlots, hc, mapQuadraticChoice, quadraticCoordinate, ite_true] at h
      exact root_of_rootInputSlot_eq G hp l₂ l (Prod.mk.inj (Option.some.inj h)).1

theorem card_root_coordinates_per_input {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (c : RootWeightChoices G d m) (l : ActualInputLeaves G) :
    ((univ : Finset ((Fin w × Fin m) × Bool)).filter
      (fun t => ∃ q, rootCoordinateSlots G hp c t = some (l, q))).card ≤ 4 * m := by
  classical
  let roots : Finset (Fin w) := {l.1.1.1, (G.pair l.1).1.1}
  have hsub : ((univ : Finset ((Fin w × Fin m) × Bool)).filter
      (fun t => ∃ q, rootCoordinateSlots G hp c t = some (l, q))) ⊆
      (roots ×ˢ (univ : Finset (Fin m))) ×ˢ (univ : Finset Bool) := by
    intro t ht
    obtain ⟨q, hq⟩ := (mem_filter.mp ht).2
    have hr := rootCoordinateSlots_root G hp c t l q hq
    apply mem_product.mpr
    refine ⟨mem_product.mpr ⟨?_, mem_univ _⟩, mem_univ _⟩
    exact mem_insert.mpr (hr.imp_right fun he => mem_singleton.mpr he)
  calc
    _ ≤ ((roots ×ˢ (univ : Finset (Fin m))) ×ˢ (univ : Finset Bool)).card := card_le_card hsub
    _ = roots.card * m * 2 := by simp only [card_product, card_univ, Fintype.card_fin, Fintype.card_bool]
    _ ≤ 2 * m * 2 := Nat.mul_le_mul_right 2 (Nat.mul_le_mul_right m card_le_two)
    _ = _ := by omega

end WaveTurbulence.LGSpine
