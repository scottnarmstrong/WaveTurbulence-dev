/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySourceAnchors
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLResonanceCorrespondence
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFlowFiber
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyResonances
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySourceAnchors
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyResonances` (sha256 2bf885aa4a39dc19…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Source resonances at every ingredient of the actual chain

For a global physical decoration and its flow fiber, every ingredient chart's
node resonance, evaluated at the inherited current, anchor and common gap, is
the literal signed source resonance at the corresponding interior atom. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assembly_piece_resonanceΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) {r : Mom d}
    (k : FlowFiber G.molecule U a b (Mom d) r) (κ : GNode G.tree → Mom d)
    (hc : ∀ v ∈ U, κ v.toNode = κ (v.child 0) - κ (v.child 1) + κ (v.child 2))
    (hk : ∀ e, k.1 e = Mole.restrictLabels G κ e.1)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (i : Fin n) (j : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) :
    (((G.sign ((assemblyChartAtΓ hM9 B i).indexing.atom j).1.toNode : ℤ) : ℝ) *
        omegaNode G κ ((assemblyChartAtΓ hM9 B i).indexing.atom j).1) =
      nodeResonance (assemblyChartAtΓ hM9 B i).indexing (assemblyFlowAtΓ B k i).1
        (assemblyAnchorAtΓ B k (κ (b.child R.positive)) i) r j := by
  have hV := (assemblyPieceAtΓ B i).vine
  have hsub := assemblyPiece_subsetΓ B i
  have hpi : ∀ ℓ, Mole.IsInternalLeaf G (assemblyPieceAtΓ B i).atoms ℓ →
      κ ℓ.toNode = κ (G.pair ℓ).toNode :=
    fun ℓ hℓ => hp ℓ (internalLeaf_mono hsub ℓ hℓ)
  have hci : ∀ v ∈ (assemblyPieceAtΓ B i).atoms,
      κ v.toNode = κ (v.child 0) - κ (v.child 1) + κ (v.child 2) := fun v hv => hc v (hsub hv)
  have hlab := assemblyFlowAt_source_labelsΓ B k κ hk i
  have hfun : (assemblyFlowAtΓ B k i).1 = fun e => Mole.restrictLabels G κ e.1 := funext hlab
  have hanchor := assemblyAnchorAt_sourceΓ B k κ hk hp (κ (b.child R.positive)) rfl i
  have hgap := clInternalFlow_lower (memBlock hV) (assemblyRegionAtΓ B i) κ hci hpi
  have hr : κ ((assemblyPieceAtΓ B i).lower.child (assemblyRegionAtΓ B i).positive) -
      κ ((assemblyPieceAtΓ B i).lower.child (assemblyRegionAtΓ B i).negative) = r := by
    rw [← hgap, ← hfun]
    exact (assemblyFlowAtΓ B k i).2.2.1
  have hres := clNodeResonance_eq_signedOmega (memBlock hV) (assemblyRegionAtΓ B i)
    (assemblyChartAtΓ hM9 B i).indexing κ hpi j
  rw [hr] at hres
  rw [hanchor, hfun]
  exact hres.symm

end WaveTurbulence.GammaLow.Famb.VineEstS2
