/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceStates
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLChainEndpoints
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySourceStates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieceStates
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySourceStates` (sha256 16896fdaadbfe39a…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Every inherited ingredient current and anchor is a literal source label -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

theorem assemblyPiece_subsetΓ
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) (i : Fin n) : (assemblyPieceAtΓ B i).atoms ⊆ U := by
  induction B with
  | single hV R => exact Finset.Subset.refl _
  | append B hT hi hU R ih =>
    refine Fin.cases Finset.subset_union_right (fun j => ?_) i
    exact (ih j).trans Finset.subset_union_left

theorem assemblyFlowAt_source_labelsΓ
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (κ : GNode G.tree → E)
    (hk : ∀ e, k.1 e = Mole.restrictLabels G κ e.1) :
    ∀ (i : Fin n) (e : Bond G.molecule (assemblyPieceAtΓ B i).atoms),
      (assemblyFlowAtΓ B k i).1 e = Mole.restrictLabels G κ e.1 := by
  induction B with
  | single hV R => exact fun _ e => hk e
  | append B hT hi hU R ih =>
    intro i
    refine Fin.cases ?_ (fun i => ?_) i <;> intro e
    · exact restrictFlow_right_source_labels B.isBlock (memBlock hT) hi hU k κ hk e
    · exact ih (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k)
        (restrictFlow_left_source_labels B.isBlock (memBlock hT) hi hU k κ hk) i e

end WaveTurbulence.GammaLow.Famb.VineEstS2
