/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntPlan
public import WaveTurbulence.Foundations.Spine.InputLeafCount

/-! # B3s MK-SLOTS (integration): the anchored leaf count (the mass `b ^ N`)

In a plain garden of order `N` with `2R` trees there are `N + R` input leaves (one per leaf pair, main's
`twice_card_inputLeaves`). The anchored profile `1` sits on the input leaves of the pairs meeting a cap tree. When the
cap trees are single leaves and no two cap roots are paired, there is exactly one such input leaf per cap tree
(`card_anchoredInputs`), so with `J.card = R` the free input leaves number `N` (`card_freeInputs`): the class value is
of degree `N` in the profiles, matching the mass `b ^ N` (F-B3s-8). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset

namespace WaveTurbulence.Flower.MkSlots

variable {w : ℕ}

/-- The input leaves of the pairs meeting a cap tree. -/
def anchoredInputs (G : Garden w) (J : Finset (Fin w)) : Finset (GLeaf G.tree) :=
  (inputLeaves G).filter fun ℓ => ℓ.1.1 ∈ J ∨ (G.pair ℓ).1.1 ∈ J

/-- The leaf of a single-leaf tree. -/
def rootLeaf (G : Garden w) (j : Fin w) (hj : G.tree j = TTree.leaf) : GLeaf G.tree :=
  ⟨(j, []), by rw [hj]; simp [TTree.leaves]⟩

theorem eq_rootLeaf {G : Garden w} {j : Fin w} (hj : G.tree j = TTree.leaf) (ℓ : GLeaf G.tree) (hℓ : ℓ.1.1 = j) :
    ℓ = rootLeaf G j hj := by
  have hl := ℓ.2
  rw [hℓ, hj] at hl
  have hp : ℓ.1.2 = [] := by simpa [TTree.leaves] using hl
  exact Subtype.ext (Prod.ext hℓ hp)

/-- **One anchored input leaf per cap tree.** -/
theorem card_anchoredInputs (G : Garden w) (hp : G.IsPlain) (J : Finset (Fin w))
    (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) (hcc : ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J) :
    (anchoredInputs G J).card = J.card := by
  have hflip (l : GLeaf G.tree) : G.sign (G.pair l).toNode = -G.sign l.toNode :=
    G.pair_sign l (fun he => ((G.pair_eq_iff l).mp he) (hp l))
  -- the input leaf of the pair of the cap root `j`
  let f : ∀ j ∈ J, GLeaf G.tree := fun j hj =>
    if G.sign (rootLeaf G j (hcap j hj)).toNode = 1 then rootLeaf G j (hcap j hj)
    else G.pair (rootLeaf G j (hcap j hj))
  have hfmem : ∀ j (hj : j ∈ J), f j hj ∈ anchoredInputs G J := by
    intro j hj
    simp only [f]
    split_ifs with hs
    · refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hs, hp _⟩, Or.inl hj⟩
    · have hs' : G.sign (rootLeaf G j (hcap j hj)).toNode = -1 := (Int.units_eq_one_or _).resolve_left hs
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_, hp _⟩, Or.inr ?_⟩
      · rw [hflip, hs', neg_neg]
      · rw [G.pair_pair]; exact hj
  refine (card_bij' (fun j hj => f j hj) (fun ℓ hℓ => if ℓ.1.1 ∈ J then ℓ.1.1 else (G.pair ℓ).1.1)
    (fun j hj => hfmem j hj) ?_ ?_ ?_).symm
  · intro ℓ hℓ
    split_ifs with h
    · exact h
    · exact ((mem_filter.mp hℓ).2.resolve_left h)
  · intro j hj
    simp only [f]
    split_ifs with hs h2 h2
    · rfl
    · exact absurd hj h2
    · exact absurd h2 (hcc _ hj)
    · rw [G.pair_pair]; rfl
  · intro ℓ hℓ
    have hin := (mem_filter.mp (mem_filter.mp hℓ).1).2.1
    by_cases h : ℓ.1.1 ∈ J
    · simp only [h, ite_true, f]
      have he := (eq_rootLeaf (hcap _ h) ℓ rfl).symm
      rw [he, if_pos (he ▸ hin)]
    · simp only [h, ite_false, f]
      have h2 : (G.pair ℓ).1.1 ∈ J := (mem_filter.mp hℓ).2.resolve_left h
      have he : rootLeaf G _ (hcap _ h2) = G.pair ℓ := (eq_rootLeaf (hcap _ h2) (G.pair ℓ) rfl).symm
      rw [he]
      have hneg : ¬ G.sign (G.pair ℓ).toNode = 1 := by
        rw [hflip, hin]; decide
      rw [if_neg hneg, G.pair_pair]

/-- **The free input leaves**: with `J.card = R`, `N + R - R = N` input leaves carry a non-anchored profile. -/
theorem card_freeInputs {R : ℕ} (G : Garden (2 * R)) (hp : G.IsPlain) (J : Finset (Fin (2 * R))) (hJ : J.card = R)
    (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) (hcc : ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J) :
    ((inputLeaves G).filter fun ℓ => ¬ (ℓ.1.1 ∈ J ∨ (G.pair ℓ).1.1 ∈ J)).card = G.order := by
  have h1 := twice_card_inputLeaves G hp
  have h2 := card_anchoredInputs G hp J hcap hcc
  have h3 := card_filter_add_card_filter_not (s := inputLeaves G) (fun ℓ => ℓ.1.1 ∈ J ∨ (G.pair ℓ).1.1 ∈ J)
  unfold anchoredInputs at h2
  omega

end WaveTurbulence.Flower.MkSlots
