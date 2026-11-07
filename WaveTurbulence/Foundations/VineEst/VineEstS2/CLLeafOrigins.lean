/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLeafEnumeration
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPairValues

/-! # Actual paired-leaf and boundary origins for predecessor coefficients -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clLeafOrigin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (l : GLeaf (CLTreeForest R)) : ↥(clRegionalPairs hG U) ⊕ Fin 4 :=
  match (clLeafEquiv hU R hG).symm l with
  | .inl p => .inl p.1
  | .inr j => .inr j.succ

theorem clLeafOrigin_apply (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (x : (↥(clRegionalPairs hG U) × Fin 2) ⊕ Fin 3) :
    clLeafOrigin hU R hG ((clLeafEquiv hU R hG) x) =
      match x with | .inl p => .inl p.1 | .inr j => .inr j.succ := by
  unfold clLeafOrigin
  rw [Equiv.symm_apply_apply]

theorem clLeafOrigin_first (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) :
    clLeafOrigin hU R hG (clPairFirstLeaf hU R hG p) = .inl p :=
  clLeafOrigin_apply hU R hG (.inl (p,0))

theorem clLeafOrigin_second (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) :
    clLeafOrigin hU R hG (clPairSecondLeaf hU R hG p) = .inl p :=
  clLeafOrigin_apply hU R hG (.inl (p,1))

theorem clLeafOrigin_boundary (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (j : Fin 3) :
    clLeafOrigin hU R hG (clBoundaryLeaf hU R j) = .inr j.succ :=
  clLeafOrigin_apply hU R hG (.inr j)

noncomputable def clOriginValue {E : Type*} (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (κ : GNode G.tree → E) : ↥(clRegionalPairs hG U) ⊕ Fin 4 → E
  | .inl p => κ (clTreeNode R (clPairFirstLeaf hU R hG p).toNode)
  | .inr j => κ (clBoundaryNodes R j)

/-- Origin values are literal source momenta. The only identification is the
actual equality at the two leaves of a pair, proved for local decorations. -/
theorem clLeafOrigin_value {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
    (κ : GNode G.tree → E)
    (hκ : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (l : GLeaf (CLTreeForest R)) :
    κ (clTreeNode R l.toNode) = clOriginValue hU R hG κ (clLeafOrigin hU R hG l) := by
  obtain ⟨x,rfl⟩ := (clLeafEquiv hU R hG).surjective l
  rw [clLeafOrigin_apply]
  rcases x with ⟨p,c⟩ | j
  · have hc : c = 0 ∨ c = 1 := by omega
    rcases hc with rfl | rfl
    · rfl
    · exact clPairLeaves_value_eq hU R hG p κ hκ
  · exact congrArg κ (clBoundaryLeaf_node hU R j)

end WaveTurbulence.VineEstS2
