/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySourceAnchors
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLResonanceCorrespondence
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFlowFiber

/-! # Source resonances at every ingredient of the actual chain

For a global physical decoration and its flow fiber, every ingredient chart's
node resonance, evaluated at the inherited current, anchor and common gap, is
the literal signed source resonance at the corresponding interior atom. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assembly_piece_resonance (hM9 : VINEPARAM) (B : CLChainAssembly G R n) {r : Mom d}
    (k : FlowFiber G.molecule U a b (Mom d) r) (κ : GNode G.tree → Mom d)
    (hc : ∀ v ∈ U, κ v.toNode = κ (v.child 0) - κ (v.child 1) + κ (v.child 2))
    (hk : ∀ e, k.1 e = Mole.restrictLabels G κ e.1)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (i : Fin n) (j : Fin (assemblyChartAt hM9 B i).indexing.shape.n) :
    (((G.sign ((assemblyChartAt hM9 B i).indexing.atom j).1.toNode : ℤ) : ℝ) *
        omegaNode G κ ((assemblyChartAt hM9 B i).indexing.atom j).1) =
      nodeResonance (assemblyChartAt hM9 B i).indexing (assemblyFlowAt B k i).1
        (assemblyAnchorAt B k (κ (b.child R.positive)) i) r j := by
  have hV := (assemblyPieceAt B i).vine
  have hsub := assemblyPiece_subset B i
  have hpi : ∀ ℓ, Mole.IsInternalLeaf G (assemblyPieceAt B i).atoms ℓ →
      κ ℓ.toNode = κ (G.pair ℓ).toNode :=
    fun ℓ hℓ => hp ℓ (internalLeaf_mono hsub ℓ hℓ)
  have hci : ∀ v ∈ (assemblyPieceAt B i).atoms,
      κ v.toNode = κ (v.child 0) - κ (v.child 1) + κ (v.child 2) := fun v hv => hc v (hsub hv)
  have hlab := assemblyFlowAt_source_labels B k κ hk i
  have hfun : (assemblyFlowAt B k i).1 = fun e => Mole.restrictLabels G κ e.1 := funext hlab
  have hanchor := assemblyAnchorAt_source B k κ hk hp (κ (b.child R.positive)) rfl i
  have hgap := clInternalFlow_lower hV.1 (assemblyRegionAt B i) κ hci hpi
  have hr : κ ((assemblyPieceAt B i).lower.child (assemblyRegionAt B i).positive) -
      κ ((assemblyPieceAt B i).lower.child (assemblyRegionAt B i).negative) = r := by
    rw [← hgap, ← hfun]
    exact (assemblyFlowAt B k i).2.2.1
  have hres := clNodeResonance_eq_signedOmega hV.1 (assemblyRegionAt B i)
    (assemblyChartAt hM9 B i).indexing κ hpi j
  rw [hr] at hres
  rw [hanchor, hfun]
  exact hres.symm

end WaveTurbulence.VineEstS2
