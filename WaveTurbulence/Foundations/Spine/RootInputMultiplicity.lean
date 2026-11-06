/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.InputLeafCount
/-! A paired input belongs to at most two distinct original root trees. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

def positiveRepresentative {w : ℕ} (G : Garden w) (l : GLeaf G.tree) : GLeaf G.tree :=
  if G.sign l.toNode = 1 then l else G.pair l

theorem positiveRepresentative_mem {w : ℕ} (G : Garden w) (hp : G.IsPlain)
    (l : GLeaf G.tree) : positiveRepresentative G l ∈ inputLeaves G := by
  have hflip : G.sign (G.pair l).toNode = -G.sign l.toNode :=
    G.pair_sign l (fun he => ((G.pair_eq_iff l).mp he) (hp l))
  unfold positiveRepresentative
  split_ifs with hs
  · exact mem_filter.mpr ⟨mem_univ _, hs, hp l⟩
  · have hn : G.sign l.toNode = -1 := (Int.units_eq_one_or _).resolve_left hs
    exact mem_filter.mpr ⟨mem_univ _, by rw [hflip, hn, neg_neg], hp _⟩

theorem eq_or_pair_of_positiveRepresentative_eq {w : ℕ} (G : Garden w)
    (l r : GLeaf G.tree) (h : positiveRepresentative G l = r) : l = r ∨ l = G.pair r := by
  unfold positiveRepresentative at h
  split_ifs at h
  · exact Or.inl h
  · have hh := congrArg G.pair h
    exact Or.inr ((G.pair_pair l).symm.trans hh)

/-- A choice of one leaf from each original root tree is injective. -/
theorem root_leaf_choice_injective {w : ℕ} (G : Garden w) (chooseLeaf : Fin w → GLeaf G.tree)
    (hroot : ∀ j, (chooseLeaf j).1.1 = j) : Function.Injective chooseLeaf := by
  intro i j he
  have hh := congrArg (fun l : GLeaf G.tree => l.1.1) he
  simpa only [hroot] using hh

/-- The maximum per-input weight budget is 2*M, irrespective of garden width. -/
theorem card_roots_selecting_input_le_two {w : ℕ} (G : Garden w)
    (chooseLeaf : Fin w → GLeaf G.tree) (hroot : ∀ j, (chooseLeaf j).1.1 = j)
    (r : GLeaf G.tree) :
    ((univ : Finset (Fin w)).filter fun j => positiveRepresentative G (chooseLeaf j) = r).card ≤ 2 := by
  classical
  let S := (univ : Finset (Fin w)).filter fun j => positiveRepresentative G (chooseLeaf j) = r
  have hh : S.card ≤ ({r, G.pair r} : Finset (GLeaf G.tree)).card := by
    apply card_le_card_of_injOn chooseLeaf
    · intro j hj
      have h := eq_or_pair_of_positiveRepresentative_eq G (chooseLeaf j) r (mem_filter.mp hj).2
      exact mem_insert.mpr (h.imp_right fun he => mem_singleton.mpr he)
    · exact (root_leaf_choice_injective G chooseLeaf hroot).injOn
  exact hh.trans card_le_two

end WaveTurbulence.LGSpine
