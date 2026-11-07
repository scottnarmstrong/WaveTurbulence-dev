/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalConsumption
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairFunction

/-! # Native regional kernels are the literal factors of the global reduction -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clRegionalPair_realization (hG : G.IsPlain) (p : SourcePair G)
    (hp : p ∈ clRegionalPairs hG U) :
    (p.firstLeaf hG).toNode ∈ clRealizationNodes G U ∧
      (p.secondLeaf hG).toNode ∈ clRealizationNodes G U := by
  classical
  have hfirst : Mole.IsInternalLeaf G U (p.firstLeaf hG) := (Finset.mem_filter.mp hp).2
  have he : G.pair (p.firstLeaf hG) = p.secondLeaf hG :=
    sourcePair_partner G _ _ (Or.inl p.2)
  exact ⟨(leaf_mem_clRealizationNodes _).mpr hfirst,
    (leaf_mem_clRealizationNodes _).mpr (he ▸ (Mole.internal_leaf_pair_iff G U _).mpr hfirst)⟩

theorem clLocalStarProduct_restrictS (hU : G.molecule.IsBlock U a b)
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ top : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (τ : GBranch G.tree → ℝ) :
    clLocalStarProduct D hG R L γ δ F layer hLayer base
      (clExtendIndices R (fun x => κ x.1)) (clExternalTimes R τ) (clRestrictTime R τ) =
    (∏ p ∈ clRegionalPairs hG U, VineEst.selCoupleRow L γ δ F D hG layer hLayer p
      (parentClock top τ (p.firstLeaf hG).toNode) (parentClock top τ (p.secondLeaf hG).toNode)
      (cosetDecoration G L base κ (p.firstLeaf hG).toNode)) *
    (∏ v ∈ clInteriorBranches R, VineEst.selTreeRow L γ δ F D hG layer hLayer v
      (parentClock top τ v.toNode) (τ v) (cosetDecoration G L base κ v.toNode)) := by
  classical
  unfold clLocalStarProduct
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨hx,hy⟩ := clRegionalPair_realization hG p hp
    rw [clLocalParentClock_restrict hU R τ top _ hx (Mole.branch_toNode_ne_leaf a _).symm,
      clLocalParentClock_restrict hU R τ top _ hy (Mole.branch_toNode_ne_leaf a _).symm]
    unfold cosetDecoration
    rw [clExtendIndices_restrict R κ _ (cl_realization_mem_support R hx)]
  · apply Finset.prod_congr rfl
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    have hn : v.toNode ≠ a.toNode := fun he => hv'.1 (Subtype.ext (congrArg (fun x : GNode G.tree => x.1) he))
    have hx := (branch_mem_clRealizationNodes v).mpr hv'.2
    rw [clLocalParentClock_restrict hU R τ top _ hx hn,
      clLocalClock_restrict_region R τ v hv'.2]
    unfold cosetDecoration
    rw [clExtendIndices_restrict R κ _ (cl_realization_mem_support R hx)]

/-- `clLocalStarProduct_restrictS` at the plain selector, in main's original form (used by `Vine/B/PointB`). -/
theorem clLocalStarProduct_restrict (hU : G.molecule.IsBlock U a b)
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ top : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (τ : GBranch G.tree → ℝ) :
    clLocalStarProduct (rowSel := VineEst.RowSel.plain) D hG R L γ δ F layer hLayer base
      (clExtendIndices R (fun x => κ x.1)) (clExternalTimes R τ) (clRestrictTime R τ) =
    (∏ p ∈ clRegionalPairs hG U, KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer p)
      (parentClock top τ (p.firstLeaf hG).toNode) (parentClock top τ (p.secondLeaf hG).toNode)
      (cosetDecoration G L base κ (p.firstLeaf hG).toNode)) *
    (∏ v ∈ clInteriorBranches R, KTstar L γ δ F (nativeChainLayered D hG layer hLayer v)
      (parentClock top τ v.toNode) (τ v) (cosetDecoration G L base κ v.toNode)) :=
  clLocalStarProduct_restrictS (rowSel := VineEst.RowSel.plain) hU D hG R L γ δ top F layer hLayer base κ τ

end WaveTurbulence.RegRed
