/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySourceStates
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySourceAnchors
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySourceStates
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySourceAnchors` (sha256 d796abec4927ef3e…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Every inherited vine anchor is its literal sign-ordered source boundary -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

theorem assemblyAnchorAt_sourceΓ
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (κ : GNode G.tree → E)
    (hk : ∀ e, k.1 e = Mole.restrictLabels G κ e.1)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (g : E) (hg : g = κ (b.child R.positive)) :
    ∀ i : Fin n, assemblyAnchorAtΓ B k g i =
      κ ((assemblyPieceAtΓ B i).lower.child (assemblyRegionAtΓ B i).positive) := by
  induction B generalizing g with
  | single hV R => exact fun _ => hg
  | @append S T a b c n RP B hT hi hU R ih =>
    let kS := restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k
    let kT := restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k
    have hkS := restrictFlow_left_source_labels B.isBlock (memBlock hT) hi hU k κ hk
    have hkT := restrictFlow_right_source_labels B.isBlock (memBlock hT) hi hU k κ hk
    have hpS : ∀ ℓ, Mole.IsInternalLeaf G S ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode :=
      fun ℓ hℓ => hp ℓ (internalLeaf_mono Finset.subset_union_left ℓ hℓ)
    have hpT : ∀ ℓ, Mole.IsInternalLeaf G T ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode :=
      fun ℓ hℓ => hp ℓ (internalLeaf_mono Finset.subset_union_right ℓ hℓ)
    have hanchor : kT.1 (B.terminalAnchor hT hi hU R) = κ (b.child RP.positive) :=
      (hkT (B.terminalAnchor hT hi hU R)).trans
        (clPrefixChildBond_value B.isBlock (memBlock hT) RP (B.terminalRegion hT hi hU R) hi
          RP.positive (clRegionPositive_ne_kept RP) κ hpT).symm
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hg.trans (congrArg κ
        (cl_lower_endpoint_children (memBlock hT) hU Finset.subset_union_right (B.terminalRegion hT hi hU R) R).1).symm
    · exact ih kS hkS hpS (kT.1 (B.terminalAnchor hT hi hU R)) hanchor i

end WaveTurbulence.GammaLow.Famb.VineEstS2
