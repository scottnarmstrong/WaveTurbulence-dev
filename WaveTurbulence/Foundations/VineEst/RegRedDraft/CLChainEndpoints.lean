/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLIngredientGaps

/-! # Whole-chain boundary labels agree with its endpoint ingredients -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree
variable {w : ℕ} {G : Garden w}

theorem cl_internalPositions_mono {A B : Finset (GBranch G.tree)} (hAB : A ⊆ B)
    (v : GBranch G.tree) : Mole.internalPositions G A v ⊆ Mole.internalPositions G B v := by
  intro i hi
  obtain ⟨x,hx,hg,hp⟩ := (Mole.mem_internalPositions G).mp hi
  exact (Mole.mem_internalPositions G).mpr ⟨x,hx,⟨hAB hg.1,hAB hg.2⟩,hp⟩

/-- A source chain endpoint has degree two in both the ingredient and the
whole chain. Containment therefore fixes all its actual incidence positions. -/
theorem cl_endpoint_positions_eq {A B : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hAB : A ⊆ B) (hA : G.molecule.degIn A v = 2) (hB : G.molecule.degIn B v = 2) :
    Mole.internalPositions G A v = Mole.internalPositions G B v := by
  apply Finset.eq_of_subset_of_card_le (cl_internalPositions_mono hAB v)
  rw [Mole.card_internalPositions,Mole.card_internalPositions,hA,hB]

/-- TARGET vineest Step 1: the bottom ingredient has the whole chain's two
sign-ordered lower children. The ordering follows from their actual signs. -/
theorem cl_lower_endpoint_children {A B : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hA : G.molecule.IsBlock A a b) (hB : G.molecule.IsBlock B c b) (hAB : A ⊆ B)
    (RA : CLRegionData G A a b) (RB : CLRegionData G B c b) :
    b.child RA.positive = b.child RB.positive ∧ b.child RA.negative = b.child RB.negative := by
  have ha := (Mole.block_joint_degrees G.molecule hA).2
  have hb := (Mole.block_joint_degrees G.molecule hB).2
  have he := cl_endpoint_positions_eq hAB ha hb
  have hk : RA.kept = RB.kept := by
    have hm := (RA.lower RA.kept).mpr rfl
    rw [he] at hm
    exact (RB.lower RA.kept).mp hm
  have hp : RA.positive = RB.positive := by
    have hn := (RA.lower_excluded RA.positive).mpr (Or.inl rfl)
    rw [hk] at hn
    rcases (RB.lower_excluded RA.positive).mp hn with h | h
    · exact h
    · have hs := RA.positive_sign
      rw [h,RB.negative_sign] at hs
      have hc := congrArg (fun z : ℤˣ => (z : ℤ)) hs
      norm_num at hc
  have hn : RA.negative = RB.negative := by
    have hn := (RA.lower_excluded RA.negative).mpr (Or.inr rfl)
    rw [hk] at hn
    rcases (RB.lower_excluded RA.negative).mp hn with h | h
    · have hs := RA.negative_sign
      rw [h,RB.positive_sign] at hs
      have hc := congrArg (fun z : ℤˣ => (z : ℤ)) hs
      norm_num at hc
    · exact h
  exact ⟨congrArg b.child hp,congrArg b.child hn⟩

end WaveTurbulence.RegRed
