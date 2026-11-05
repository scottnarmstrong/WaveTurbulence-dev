/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts
/-! Exact number of multilinear input slots of a plain garden. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

theorem twice_card_inputLeaves {w : ℕ} (G : Garden w) (hp : G.IsPlain) :
    2 * (inputLeaves G).card = 2 * G.order + w := by
  classical
  let S := (univ : Finset (GLeaf G.tree)).filter fun l => G.sign l.toNode = 1
  let T := (univ : Finset (GLeaf G.tree)).filter fun l => G.sign l.toNode ≠ 1
  have hflip (l : GLeaf G.tree) : G.sign (G.pair l).toNode = -G.sign l.toNode :=
    G.pair_sign l (fun he => ((G.pair_eq_iff l).mp he) (hp l))
  have hst : S.card = T.card := by
    apply card_bij (fun l _ => G.pair l)
    · intro l hl
      have hl' : G.sign l.toNode = 1 := (mem_filter.mp hl).2
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [hflip, hl']
      decide
    · intro a _ b _ he
      have hh := congrArg G.pair he
      simpa only [G.pair_pair] using hh
    · intro l hl
      have hl' : G.sign l.toNode = -1 :=
        (Int.units_eq_one_or _).resolve_left (mem_filter.mp hl).2
      refine ⟨G.pair l, ?_, G.pair_pair l⟩
      apply mem_filter.mpr
      exact ⟨mem_univ _, by rw [hflip, hl', neg_neg]⟩
  have hinput : inputLeaves G = S := by
    ext l
    simp only [inputLeaves, S, mem_filter, mem_univ, true_and, hp l, and_true]
  have hc := card_filter_add_card_filter_not (s := (univ : Finset (GLeaf G.tree)))
    (fun l => G.sign l.toNode = 1)
  rw [card_univ, Comb.card_gleaf] at hc
  change S.card + T.card = 2 * G.order + w at hc
  rw [hinput]
  omega

theorem card_inputLeaves_couple {n : ℕ} (G : Garden 2) (hp : G.IsPlain) (ho : G.order = 2 * n) :
    (inputLeaves G).card = 2 * n + 1 := by
  have hh := twice_card_inputLeaves G hp
  rw [ho] at hh
  omega

end WaveTurbulence.LGSpine
