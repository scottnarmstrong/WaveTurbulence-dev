/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPairLeaves

/-! # Canonical pair sides identify distinct actual cropped leaves -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clPairOriginal (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) (c : Fin 2) : GLeaf G.tree :=
  if c = 0 then p.1.firstLeaf hG else p.1.secondLeaf hG

noncomputable def clPairSideLeaf (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) (c : Fin 2) : GLeaf (CLTreeForest R) :=
  if c = 0 then clPairFirstLeaf hU R hG p else clPairSecondLeaf hU R hG p

theorem clPairSideLeaf_node (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) (c : Fin 2) :
    clTreeNode R (clPairSideLeaf hU R hG p c).toNode = (clPairOriginal hG p c).toNode := by
  by_cases hc : c = 0
  · simpa only [clPairSideLeaf,clPairOriginal,hc,ite_true] using clPairFirstLeaf_node hU R hG p
  · simpa only [clPairSideLeaf,clPairOriginal,hc,ite_false] using clPairSecondLeaf_node hU R hG p

theorem clPairOriginal_pair (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) (c : Fin 2) :
    pairOfLeaf G hG (clPairOriginal hG p c) = p.1 := by
  by_cases hc : c = 0
  · simp only [clPairOriginal,hc,ite_true,pairOfLeaf_firstLeaf]
  · simp only [clPairOriginal,hc,ite_false,pairOfLeaf_secondLeaf]

theorem clPairSideLeaf_injective_pair (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) {p q : ↥(clRegionalPairs hG U)} {i j : Fin 2}
    (he : clPairSideLeaf hU R hG p i = clPairSideLeaf hU R hG q j) : p = q := by
  have hm := congrArg (fun l : GLeaf (CLTreeForest R) => clTreeNode R l.toNode) he
  have hn := (clPairSideLeaf_node hU R hG p i).symm.trans (hm.trans (clPairSideLeaf_node hU R hG q j))
  have hl := Mole.leaf_toNode_injective hn
  have hp := congrArg (pairOfLeaf G hG) hl
  rw [clPairOriginal_pair,clPairOriginal_pair] at hp
  exact Subtype.ext hp

theorem clPairFirst_ne_second (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) :
    clPairFirstLeaf hU R hG p ≠ clPairSecondLeaf hU R hG p := by
  intro he
  have hn : (1:ℤ) = -1 := by
    calc
      _ = (nodeSign (fun _ : Fin 1 => G.sign a.toNode) (clPairFirstLeaf hU R hG p).1 : ℤ) :=
        congrArg (fun z : ℤˣ => (z : ℤ)) (clPairFirstLeaf_sign hU R hG p).symm
      _ = (nodeSign (fun _ : Fin 1 => G.sign a.toNode) (clPairSecondLeaf hU R hG p).1 : ℤ) :=
        congrArg (fun l : GLeaf (CLTreeForest R) => (nodeSign (fun _ : Fin 1 => G.sign a.toNode) l.1 : ℤ)) he
      _ = -1 := congrArg (fun z : ℤˣ => (z : ℤ)) (clPairSecondLeaf_sign hU R hG p)
  norm_num at hn

theorem clPairSideLeaf_injective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) : Function.Injective (fun p : ↥(clRegionalPairs hG U) × Fin 2 => clPairSideLeaf hU R hG p.1 p.2) := by
  rintro ⟨p,i⟩ ⟨q,j⟩ he
  have hp := clPairSideLeaf_injective_pair hU R hG he
  change p = q at hp
  subst q
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · rfl
  · exact (clPairFirst_ne_second hU R hG p he).elim
  · exact (clPairFirst_ne_second hU R hG p he.symm).elim
  · rfl

end WaveTurbulence.VineEstS2
