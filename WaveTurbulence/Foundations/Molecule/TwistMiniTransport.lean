/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MiniTripleBonds
public import WaveTurbulence.Foundations.Molecule.TwistTripleTransport

/-! # Transport of every embedded mini piece away from the lower joint

TARGET twist: the exceptional PC/LP exchange cannot create a mini piece
at the lower joint, and all other source mini pieces transport literally.
-/

public section
namespace WaveTurbulence.Twist
open TTree Reg.Skeleton
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Actual leaf bonds between ordinary atoms keep their ordered slots and pairing. -/
theorem leafBond_unitTwist {b c : GBranch G.tree} {i j : Fin 3}
    (h : LeafBond G b c i j) (hb : b ≠ P.lower) (hc : c ≠ P.lower) :
    LeafBond (unitTwistGarden G P) (coreBranchEquiv G P b) (coreBranchEquiv G P c) i j := by
  obtain ⟨l,q,hl,hq,hpair⟩ := h
  have hlp : l ≠ G.pair P.retained := by
    intro he
    have hqr : q = P.retained := by rw [← hpair,he,G.pair_pair]
    have hh : P.retained.toNode = c.child j := by rw [← hqr]; exact hq
    have hp := parent_eq_of_child (retained_nonroot G P) hh
    rw [retained_parent] at hp
    exact hc hp.symm
  have hqp : q ≠ G.pair P.retained := by
    intro he
    have hlr : l = P.retained := by
      have hh := congrArg G.pair (hpair.trans he)
      simpa only [G.pair_pair] using hh
    have hh : P.retained.toNode = b.child i := by rw [← hlr]; exact hl
    have hp := parent_eq_of_child (retained_nonroot G P) hh
    rw [retained_parent] at hp
    exact hb hp.symm
  have hbv : b.1 ≠ P.lower.1 := fun he => hb (Subtype.ext he)
  have hcv : c.1 ≠ P.lower.1 := fun he => hc (Subtype.ext he)
  have hlt := leaf_child_transport G P hl hlp
  have hqt := leaf_child_transport G P hq hqp
  simp only [exchangeChildSlot,hbv,hcv,ite_false] at hlt hqt
  exact ⟨coreLeafEquiv G P l,coreLeafEquiv G P q,hlt,hqt,
    (unitTwistGarden_pair G P l).trans (congrArg (coreLeafEquiv G P) hpair)⟩

/-- A source mini couple on ordinary branching nodes remains the same code. -/
theorem miniA_unitTwist {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) (hb : b ≠ P.lower) (hc : c ≠ P.lower) :
    MiniAOccurrence (unitTwistGarden G P) (coreBranchEquiv G P b) (coreBranchEquiv G P c) k := by
  have hbs := (coreBranchEquiv_sign G P b).trans (ite_eq_right hb)
  have hcs := (coreBranchEquiv_sign G P c).trans (ite_eq_right hc)
  exact ⟨hcs.trans (h.1.trans (congrArg Neg.neg hbs.symm)),
    fun i => leafBond_unitTwist G P (h.2 i) hb hc⟩

/-- A source mini tree on ordinary branching nodes remains the same code. -/
theorem miniB_unitTwist {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hb : b ≠ P.lower) (hc : c ≠ P.lower) :
    MiniBOccurrence (unitTwistGarden G P) (coreBranchEquiv G P b) (coreBranchEquiv G P c) m := by
  have hbv : b.1 ≠ P.lower.1 := fun he => hb (Subtype.ext he)
  have ht := branch_child_transport G P h.1.symm hc
  simp only [exchangeChildSlot,hbv,ite_false] at ht
  exact ⟨ht.symm,leafBond_unitTwist G P h.2.1 hb hc,leafBond_unitTwist G P h.2.2 hb hc⟩

/-- All embedded source mini pieces transport when the lower atom cannot have a triple bond. -/
theorem miniOccurrence_unitTwist (hplain : G.IsPlain) (hno : NoTripleAt G P.lower)
    (h : MiniOccurrence G) : Nonempty (MiniOccurrence (unitTwistGarden G P)) := by
  cases h with
  | opA b c k h =>
    obtain ⟨hne,ht⟩ := miniA_triple G hplain h
    have hb : b ≠ P.lower := by intro he; subst b; exact hno c hne ht
    have hc : c ≠ P.lower := by intro he; subst c; exact hno b hne.symm ht.symm
    exact ⟨.opA _ _ k (miniA_unitTwist G P h hb hc)⟩
  | opB b c m h =>
    obtain ⟨hne,ht⟩ := miniB_triple G hplain h
    have hb : b ≠ P.lower := by intro he; subst b; exact hno c hne ht
    have hc : c ≠ P.lower := by intro he; subst c; exact hno b hne.symm ht.symm
    exact ⟨.opB _ _ m (miniB_unitTwist G P h hb hc)⟩

end WaveTurbulence.Twist
