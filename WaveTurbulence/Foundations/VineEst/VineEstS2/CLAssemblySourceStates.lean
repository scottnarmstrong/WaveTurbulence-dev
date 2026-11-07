/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceStates
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLChainEndpoints

/-! # Every inherited ingredient current and anchor is a literal source label -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

 theorem internalLeaf_mono {S T : Finset (GBranch G.tree)} (hST : S ⊆ T) (ℓ : GLeaf G.tree)
    (h : Mole.IsInternalLeaf G S ℓ) : Mole.IsInternalLeaf G T ℓ := by
  obtain ⟨hm,hn,hp,hg⟩ := h
  exact ⟨hm,hn,hp,hST hg.1,hST hg.2⟩

theorem assemblyPiece_subset
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (i : Fin n) : (assemblyPieceAt B i).atoms ⊆ U := by
  induction B with
  | single hV R => exact Finset.Subset.refl _
  | append B hT hi hU R ih =>
    refine Fin.cases Finset.subset_union_right (fun j => ?_) i
    exact (ih j).trans Finset.subset_union_left

 theorem restrictFlow_left_source_labels {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    {E : Type} [AddCommGroup E] {r : E} (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : G.molecule.IsBlock (S ∪ T) a c)
    (k : FlowFiber G.molecule (S ∪ T) a c E r) (κ : GNode G.tree → E)
    (hk : ∀ e, k.1 e = Mole.restrictLabels G κ e.1) (e : Bond G.molecule S) :
    (restrictFlowFiber_left (Mole.garden_isMolecule G) hS hT hi hU k).1 e = Mole.restrictLabels G κ e.1 := by
  have he := congrArg (fun f : Bond G.molecule S → E => f e)
    (restrictFlowFiber_left_val (Mole.garden_isMolecule G) hS hT hi hU k)
  exact he.trans (hk (includeBond Finset.subset_union_left e))

 theorem restrictFlow_right_source_labels {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    {E : Type} [AddCommGroup E] {r : E} (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : G.molecule.IsBlock (S ∪ T) a c)
    (k : FlowFiber G.molecule (S ∪ T) a c E r) (κ : GNode G.tree → E)
    (hk : ∀ e, k.1 e = Mole.restrictLabels G κ e.1) (e : Bond G.molecule T) :
    (restrictFlowFiber_right (Mole.garden_isMolecule G) hS hT hi hU k).1 e = Mole.restrictLabels G κ e.1 := by
  have he := congrArg (fun f : Bond G.molecule T → E => f e)
    (restrictFlowFiber_right_val (Mole.garden_isMolecule G) hS hT hi hU k)
  exact he.trans (hk (includeBond Finset.subset_union_right e))

theorem assemblyFlowAt_source_labels
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (κ : GNode G.tree → E)
    (hk : ∀ e, k.1 e = Mole.restrictLabels G κ e.1) :
    ∀ (i : Fin n) (e : Bond G.molecule (assemblyPieceAt B i).atoms),
      (assemblyFlowAt B k i).1 e = Mole.restrictLabels G κ e.1 := by
  induction B with
  | single hV R => exact fun _ e => hk e
  | append B hT hi hU R ih =>
    intro i
    refine Fin.cases ?_ (fun i => ?_) i <;> intro e
    · exact restrictFlow_right_source_labels B.isBlock hT.1 hi hU k κ hk e
    · exact ih (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k)
        (restrictFlow_left_source_labels B.isBlock hT.1 hi hU k κ hk) i e

end WaveTurbulence.VineEstS2
