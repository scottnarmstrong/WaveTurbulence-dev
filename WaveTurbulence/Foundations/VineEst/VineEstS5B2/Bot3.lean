/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot2

/-! # V5 Step 4d-B2: the bottom vine, part 3 (the boundary children of the lower joint under the twist)

At the lower joint `b = P.lower` of a twist the two free child slots are exchanged (`freeSwap P.keep`) and the sign of `b` flips, but the
signs of the free children do not: so the positive (negative) boundary slot of the twisted region data is the image of the positive
(negative) slot of the original (`STw.positive_eq`, `STw.negative_eq`).  The labels at the boundary children are unchanged
(`label_pos`, `label_neg`), and a boundary child is a branch iff its image is (`bTimeOK_tw`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

theorem sign_naive_lowerChild (j : Fin 3) (hj : j ≠ P.keep) :
    (unitTwistGarden G P).sign (naiveNodeEquiv G P (P.lower.child j)) = G.sign (P.lower.child j) := by
  obtain ⟨q, hq⟩ := (nodePieceEquiv G.tree).surjective (P.lower.child j)
  cases q with
  | inl b0 =>
    have hb : b0.toNode = P.lower.child j := hq
    rw [← hb, naiveNodeEquiv_branch, coreBranchEquiv_sign]
    have hne : b0 ≠ P.lower := by
      intro he
      rw [he] at hb
      exact child_ne_parent G P.lower j hb.symm
    rw [if_neg hne]
  | inr l =>
    have hl : l.toNode = P.lower.child j := hq
    rw [← hl, naiveNodeEquiv_leaf, leaf_sign_transport]
    have h1 : l ≠ P.retained := by
      intro he
      rw [he, P.child] at hl
      exact hj (Molecpl.child_injective G P.lower hl).symm
    have h2 : l ≠ G.pair P.retained := by
      intro he
      apply P.paired_outside
      rw [← he, hl]
      exact ⟨rfl, [j], rfl⟩
    simp only [coreLeafMultiplier, h1, h2, or_self, ite_false, one_mul]

variable {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')

include h

theorem stw_positive_ne_keep : RS.positive ≠ P.keep := by
  intro he
  have := (RS.lower_excluded RS.positive).mpr (Or.inl rfl)
  exact this (he.trans h.keep.symm)

theorem stw_negative_ne_keep : RS.negative ≠ P.keep := by
  intro he
  have := (RS.lower_excluded RS.negative).mpr (Or.inr rfl)
  exact this (he.trans h.keep.symm)

theorem stw_child_eb (j : Fin 3) :
    (eB P b).child (freeSwap P.keep j) = naiveNodeEquiv G P (P.lower.child j) := by
  rw [lower_naive_child, h.lower]
  rfl

theorem stw_positive_eq : RS'.positive = freeSwap P.keep RS.positive := by
  have hne : freeSwap P.keep RS.positive ≠ RS'.kept := by
    rw [h.keep']
    intro he
    exact stw_positive_ne_keep P h ((freeSwap_eq_keep_iff G P RS.positive).mp he)
  rcases (RS'.lower_excluded _).mp hne with he | he
  · exact he.symm
  · exfalso
    have s1 := RS'.negative_sign
    have s2 : (unitTwistGarden G P).sign ((eB P b).child (freeSwap P.keep RS.positive)) = 1 := by
      rw [stw_child_eb P h, sign_naive_lowerChild P _ (stw_positive_ne_keep P h), ← h.lower]
      exact RS.positive_sign
    rw [he] at s2
    rw [s2] at s1
    exact absurd s1 (by decide)

theorem stw_negative_eq : RS'.negative = freeSwap P.keep RS.negative := by
  have hne : freeSwap P.keep RS.negative ≠ RS'.kept := by
    rw [h.keep']
    intro he
    exact stw_negative_ne_keep P h ((freeSwap_eq_keep_iff G P RS.negative).mp he)
  rcases (RS'.lower_excluded _).mp hne with he | he
  · exfalso
    have s1 := RS'.positive_sign
    have s2 : (unitTwistGarden G P).sign ((eB P b).child (freeSwap P.keep RS.negative)) = -1 := by
      rw [stw_child_eb P h, sign_naive_lowerChild P _ (stw_negative_ne_keep P h), ← h.lower]
      exact RS.negative_sign
    rw [he] at s2
    rw [s2] at s1
    exact absurd s1 (by decide)
  · exact he.symm

end WaveTurbulence.VineEstS5B2
