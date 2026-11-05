/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistChildLabels

/-! # Exact switched child values at the lower branch -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The retained child is exactly the original outer slot. -/
theorem lower_child_retained_iff (i : Fin 3) : P.lower.child i = P.retained.toNode ↔ i = P.keep := by
  constructor
  · intro he
    exact Molecpl.child_injective G P.lower (he.trans P.child)
  · intro he
    rw [he]
    exact P.child.symm

/-- The free-child permutation fixes precisely the retained slot among its preimages. -/
theorem freeSwap_eq_keep_iff (i : Fin 3) : freeSwap P.keep i = P.keep ↔ i = P.keep := by
  constructor
  · intro he
    exact (freeSwap P.keep).injective (he.trans (freeSwap_keep P.keep P.outer).symm)
  · intro he
    rw [he,freeSwap_keep P.keep P.outer]

/-- At the lower branch, exchange the root/retained values and permute the free children. -/
theorem twistNodeLabels_lower_child {E : Type*} (κ : GNode G.tree → E) (i : Fin 3) :
    twistNodeLabels G P κ ((coreBranchEquiv G P P.lower).child i) =
      if i = P.keep then κ P.lower.toNode else κ (P.lower.child (freeSwap P.keep i)) := by
  have hn := lower_naive_child G P (freeSwap P.keep i)
  rw [freeSwap_involutive P.keep i] at hn
  rw [← hn,twistNodeLabels_naive]
  have hlow := child_ne_parent G P.lower (freeSwap P.keep i)
  have hpair : P.lower.child (freeSwap P.keep i) ≠ (G.pair P.retained).toNode := by
    intro he
    apply P.paired_outside
    rw [← he]
    exact ⟨rfl,[freeSwap P.keep i],rfl⟩
  simp only [switchedOldLabels,hlow,ite_false,hpair,or_false,
    lower_child_retained_iff,freeSwap_eq_keep_iff]

/-- The transported labels retain every actual leaf-pair equality. -/
theorem twistNodeLabels_leaf_pairs {E : Type*} (κ : GNode G.tree → E)
    (hκ : ∀ l : GLeaf G.tree, κ l.toNode = κ (G.pair l).toNode)
    (l : GLeaf (unitTwistGarden G P).tree) :
    twistNodeLabels G P κ l.toNode = twistNodeLabels G P κ ((unitTwistGarden G P).pair l).toNode := by
  classical
  obtain ⟨l,rfl⟩ := (coreLeafEquiv G P).surjective l
  rw [unitTwistGarden_pair G P l]
  refine (twistNodeLabels_leaf G P κ l).trans (Eq.trans ?_ (twistNodeLabels_leaf G P κ (G.pair l)).symm)
  have h1 : G.pair l = P.retained ↔ l = G.pair P.retained := by
    constructor
    · intro he
      have hh := congrArg G.pair he
      simpa only [G.pair_pair] using hh
    · intro he
      rw [he,G.pair_pair]
  have h2 : G.pair l = G.pair P.retained ↔ l = P.retained :=
    ⟨fun he => by have hh := congrArg G.pair he; simpa only [G.pair_pair] using hh,
      fun he => congrArg G.pair he⟩
  simp only [h1,h2,or_comm]
  split
  · rfl
  · exact hκ l

end WaveTurbulence.Twist
