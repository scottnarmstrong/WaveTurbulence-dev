/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LeafBasics
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Structure

/-! # Actual scalar decorations extending arbitrary paired leaf labels

The signed sum rule is inverted using the node sign, which is an integer
unit. This supplies separating decorations for complete-pairing tests.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (G : Garden w)

/-- Extend actual leaf values by the signed descendant-leaf sum. -/
@[expose] noncomputable def leafExtension (f : GLeaf G.tree → ℤ) (n : GNode G.tree) : ℤ :=
  (((G.sign n)⁻¹ : ℤˣ) : ℤ) * ∑ l ∈ n.leavesBelow, (G.sign l.toNode : ℤ) * f l

/-- The node sign cancels the exact unit used in the extension. -/
theorem leafExtension_signed (f : GLeaf G.tree → ℤ) (n : GNode G.tree) :
    (G.sign n : ℤ) * leafExtension G f n = ∑ l ∈ n.leavesBelow, (G.sign l.toNode : ℤ) * f l := by
  unfold leafExtension
  rw [← mul_assoc,← Units.val_mul]
  simp only [mul_inv_cancel,Units.val_one,one_mul]

/-- At an actual leaf the extension is exactly its assigned value. -/
theorem leafExtension_leaf (f : GLeaf G.tree → ℤ) (l : GLeaf G.tree) : leafExtension G f l.toNode = f l := by
  unfold leafExtension
  rw [leavesBelow_leaf,Finset.sum_singleton,← mul_assoc,← Units.val_mul]
  simp only [inv_mul_cancel,Units.val_one,one_mul]

/-- The extension satisfies every actual ternary conservation equation. -/
theorem leafExtension_conservation (f : GLeaf G.tree → ℤ) (b : GBranch G.tree) :
    leafExtension G f b.toNode = leafExtension G f (b.child 0) - leafExtension G f (b.child 1) +
      leafExtension G f (b.child 2) := by
  obtain ⟨h₀,h₁,h₂⟩ := Comb.nodeSign_child G.sig b
  have hs : (G.sign b.toNode : ℤ) * (leafExtension G f b.toNode - leafExtension G f (b.child 0) +
      leafExtension G f (b.child 1) - leafExtension G f (b.child 2)) = 0 := by
    have hb := leafExtension_signed G f b.toNode
    have hc₀ := leafExtension_signed G f (b.child 0)
    have hc₁ := leafExtension_signed G f (b.child 1)
    have hc₂ := leafExtension_signed G f (b.child 2)
    have hd := Comb.GBranch.sum_leavesBelow b (fun l => (G.sign l.toNode : ℤ) * f l)
    rw [Fin.sum_univ_three] at hd
    change (G.sign (b.child 0) : ℤˣ) = G.sign b.toNode at h₀
    change (G.sign (b.child 1) : ℤˣ) = -G.sign b.toNode at h₁
    change (G.sign (b.child 2) : ℤˣ) = G.sign b.toNode at h₂
    rw [h₀] at hc₀
    rw [h₁,Units.val_neg] at hc₁
    rw [h₂] at hc₂
    linarith only [hb,hc₀,hc₁,hc₂,hd]
  rcases mul_eq_zero.mp hs with hn | hz
  · exact ((G.sign b.toNode).ne_zero hn).elim
  · omega

/-- Every pair-invariant leaf assignment extends to an actual source decoration. -/
theorem leafExtension_isDecoration (f : GLeaf G.tree → ℤ) (hf : ∀ l, f l = f (G.pair l)) :
    IsDecoration G (leafExtension G f) := by
  refine ⟨leafExtension_conservation G f,?_⟩
  intro l
  exact (leafExtension_leaf G f l).trans ((hf l).trans (leafExtension_leaf G f (G.pair l)).symm)

/-- The unit label on one actual paired orbit, zero on every other leaf. -/
@[expose] noncomputable def pairIndicator (l : GLeaf G.tree) (m : GLeaf G.tree) : ℤ :=
  if m = l ∨ m = G.pair l then 1 else 0

/-- The orbit indicator is invariant under the literal source pairing. -/
theorem pairIndicator_pair (l m : GLeaf G.tree) : pairIndicator G l m = pairIndicator G l (G.pair m) := by
  classical
  have h₀ : G.pair m = l ↔ m = G.pair l := by
    constructor
    · intro h
      exact (G.pair_pair m).symm.trans (congrArg G.pair h)
    · intro h
      exact (congrArg G.pair h).trans (G.pair_pair l)
  have h₁ : G.pair m = G.pair l ↔ m = l := by
    constructor
    · intro h
      exact (G.pair_pair m).symm.trans ((congrArg G.pair h).trans (G.pair_pair l))
    · exact congrArg G.pair
  simp only [pairIndicator,h₀,h₁,or_comm]

/-- The separating indicator gives a genuine scalar decoration. -/
theorem pairIndicator_isDecoration (l : GLeaf G.tree) :
    IsDecoration G (leafExtension G (pairIndicator G l)) :=
  leafExtension_isDecoration G _ (pairIndicator_pair G l)

end WaveTurbulence.LFTwist
