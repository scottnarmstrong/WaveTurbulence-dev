/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPairCoefficients
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalDecorations

/-! # Pair coefficient consumption on genuine local decorations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clPairLeaves_value_eq {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
    (p : ↥(clRegionalPairs hG U)) (κ : GNode G.tree → E)
    (hκ : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    κ (clTreeNode R (clPairSecondLeaf hU R hG p).toNode) =
      κ (clTreeNode R (clPairFirstLeaf hU R hG p).toNode) := by
  have hp : G.pair (p.1.firstLeaf hG) = p.1.secondLeaf hG :=
    sourcePair_partner G _ _ (Or.inl p.1.2)
  have hi := (leaf_mem_clRealizationNodes _).mp (clRegionalPair_realization hG p.1 p.2).1
  have hk := (hκ (p.1.firstLeaf hG) hi).trans (congrArg (fun l : GLeaf G.tree => κ l.toNode) hp)
  exact (congrArg κ (clPairSecondLeaf_node hU R hG p)).trans
    (hk.symm.trans (congrArg κ (clPairFirstLeaf_node hU R hG p)).symm)

/-- Actual local decoration matching supplies the pair-equality premise of
coefficient cancellation, including the physical common lattice coset. -/
theorem clPairLeaves_local_momenta_eq {d : ℕ} (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U))
    (L : ℝ) (base : Mom d) (boundary : Fin 4 → Mom d) (κ : CLLocalDecoration R L base boundary) :
    cosetDecoration G L base (clExtendIndices R κ.1) (clTreeNode R (clPairSecondLeaf hU R hG p).toNode) =
      cosetDecoration G L base (clExtendIndices R κ.1) (clTreeNode R (clPairFirstLeaf hU R hG p).toNode) := by
  apply clPairLeaves_value_eq hU R hG p
  intro ℓ hℓ
  exact congrArg (fun z => base+latticePoint L z) (κ.2.2.1 ℓ hℓ)

end WaveTurbulence.VineEstS2
