/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LeafExtension

/-! # Complete pairing is detected by actual integer decorations

The source canonicity test concerns two incomparable node subtrees.
Their union is completely paired exactly when every scalar decoration
has zero signed sum of the two node values.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (G : Garden w)

/-- A completely paired leaf set has zero signed sum in every scalar decoration. -/
theorem completelyPaired_signed_sum {U : Finset (GLeaf G.tree)} (hU : G.CompletelyPaired U)
    (κ : GNode G.tree → ℤ) (hκ : IsDecoration G κ) :
    ∑ l ∈ U, (G.sign l.toNode : ℤ) * κ l.toNode = 0 := by
  classical
  apply Finset.sum_involution (fun l _ => G.pair l)
  · intro l hl
    have hs := G.pair_sign l (hU l hl).1
    change G.sign (G.pair l).toNode = -G.sign l.toNode at hs
    rw [hs,Units.val_neg,← hκ.2 l]
    ring
  · intro l hl _
    exact (hU l hl).1
  · intro l hl
    exact (hU l hl).2
  · intro l _
    exact G.pair_pair l

/-- The orbit indicator isolates a single unbalanced leaf in a finite set. -/
theorem pairIndicator_sum_single {U : Finset (GLeaf G.tree)} {l : GLeaf G.tree} (hl : l ∈ U)
    (hother : ∀ m ∈ U, m ≠ l → m ≠ G.pair l) :
    ∑ m ∈ U, (G.sign m.toNode : ℤ) * pairIndicator G l m = (G.sign l.toNode : ℤ) := by
  classical
  rw [Finset.sum_eq_single_of_mem l hl]
  · simp only [pairIndicator,eq_self,true_or,ite_true,mul_one]
  · intro m hm hml
    simp only [pairIndicator,hml,hother m hm hml,or_self,ite_false,mul_zero]

/-- No nonclosed leaf set can annihilate every actual scalar decoration. -/
theorem completelyPaired_of_signed_sums {U : Finset (GLeaf G.tree)}
    (h : ∀ κ : GNode G.tree → ℤ, IsDecoration G κ → ∑ l ∈ U, (G.sign l.toNode : ℤ) * κ l.toNode = 0) :
    G.CompletelyPaired U := by
  classical
  intro l hl
  have hs := h (leafExtension G (pairIndicator G l)) (pairIndicator_isDecoration G l)
  simp only [leafExtension_leaf] at hs
  constructor
  · intro hfix
    have he := pairIndicator_sum_single G hl (fun m _ hml => by simpa only [hfix] using hml)
    exact (G.sign l.toNode).ne_zero (he.symm.trans hs)
  · by_contra hn
    have he := pairIndicator_sum_single G hl (fun m hm _ he => hn (he ▸ hm))
    exact (G.sign l.toNode).ne_zero (he.symm.trans hs)

/-- The exact source complete-pairing condition is equivalent to a test over
all actual scalar decorations, without prescribed-root restrictions. -/
theorem completelyPaired_iff_signed_sums (U : Finset (GLeaf G.tree)) :
    G.CompletelyPaired U ↔ ∀ κ : GNode G.tree → ℤ, IsDecoration G κ →
      ∑ l ∈ U, (G.sign l.toNode : ℤ) * κ l.toNode = 0 :=
  ⟨fun h κ hκ => completelyPaired_signed_sum G h κ hκ,completelyPaired_of_signed_sums G⟩

/-- The node-level version used in TARGET canonequiv and lftwistprop. -/
theorem completelyPaired_iff_node_sums (a b : GNode G.tree) (hi : a.Incomparable b) :
    G.CompletelyPaired (a.leavesBelow ∪ b.leavesBelow) ↔
      ∀ κ : GNode G.tree → ℤ, IsDecoration G κ →
        (G.sign a : ℤ) * κ a + (G.sign b : ℤ) * κ b = 0 := by
  have hd := leavesBelow_disjoint hi
  rw [completelyPaired_iff_signed_sums]
  constructor <;> intro h κ hκ
  · have hs := h κ hκ
    rw [Finset.sum_union hd] at hs
    have ha := Comb.sum_rule G.sig κ hκ.1 a
    have hb := Comb.sum_rule G.sig κ hκ.1 b
    simp only [smul_eq_mul] at ha hb
    exact (congrArg₂ (· + ·) ha hb).trans hs
  · have hs := h κ hκ
    rw [Finset.sum_union hd]
    have ha := Comb.sum_rule G.sig κ hκ.1 a
    have hb := Comb.sum_rule G.sig κ hκ.1 b
    simp only [smul_eq_mul] at ha hb
    exact (congrArg₂ (· + ·) ha hb).symm.trans hs

end WaveTurbulence.LFTwist
