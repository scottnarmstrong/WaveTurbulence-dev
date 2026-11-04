/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleLinkCoordinates
public import WaveTurbulence.Foundations.IncohInst.TreeLinkCoordinates
public import WaveTurbulence.Foundations.Fourier.PoissonBlocks

/-! # Exact Lebesgue transport from source branching clocks to link clocks -/

public section
noncomputable section
open MeasureTheory
namespace WaveTurbulence.IncohInst

/-- The actual source couple clocks, with no assumed Jacobian. -/
@[expose] def coupleClockEquiv {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    (Fin Q.links.length → Fin 2 → ℝ) ≃ᵐ (GBranch G.tree → ℝ) :=
  (Fourier.flattenBlocks Q.links.length 2).trans
    (MeasurableEquiv.piCongrLeft (fun _ : GBranch G.tree => ℝ)
      (finProdFinEquiv.symm.trans (coupleLinkEquiv hQ)))

/-- The actual source tree clocks. -/
@[expose] def treeClockEquiv {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    (Fin (X.treeLinks (G.sig 0)).length → Fin 2 → ℝ) ≃ᵐ (GBranch G.tree → ℝ) :=
  (Fourier.flattenBlocks (X.treeLinks (G.sig 0)).length 2).trans
    (MeasurableEquiv.piCongrLeft (fun _ : GBranch G.tree => ℝ)
      (finProdFinEquiv.symm.trans (treeLinkEquiv hX)))

/-- Source couple time integrals have exactly unit Jacobian under the actual link coordinates. -/
theorem measurePreserving_coupleClockEquiv {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    MeasurePreserving (coupleClockEquiv hQ) :=
  (Fourier.flattenBlocks_measurePreserving Q.links.length 2).trans
    (volume_measurePreserving_piCongrLeft (fun _ : GBranch G.tree => ℝ)
      (finProdFinEquiv.symm.trans (coupleLinkEquiv hQ)))

/-- The tree clock reindexing also has exactly unit Jacobian. -/
theorem measurePreserving_treeClockEquiv {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    MeasurePreserving (treeClockEquiv hX) :=
  (Fourier.flattenBlocks_measurePreserving (X.treeLinks (G.sig 0)).length 2).trans
    (volume_measurePreserving_piCongrLeft (fun _ : GBranch G.tree => ℝ)
      (finProdFinEquiv.symm.trans (treeLinkEquiv hX)))

/-- Reading a source couple endpoint reads its original link clock. -/
theorem coupleClockEquiv_apply {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (t : Fin Q.links.length → Fin 2 → ℝ) (j : Fin Q.links.length) (b : Fin 2) :
    coupleClockEquiv hQ t (coupleLinkBranch hQ j b) = t j b := by
  let e := finProdFinEquiv.symm.trans (coupleLinkEquiv hQ)
  change (Equiv.piCongrLeft (fun _ : GBranch G.tree => ℝ) e)
    (Fourier.flattenBlocks Q.links.length 2 t) (coupleLinkEquiv hQ (j, b)) = _
  have he : e (finProdFinEquiv (j, b)) = coupleLinkEquiv hQ (j, b) := by simp [e]
  rw [← he, Equiv.piCongrLeft_apply_apply, Fourier.flattenBlocks_apply]
  simp

/-- Reading a source tree endpoint reads its original link clock. -/
theorem treeClockEquiv_apply {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (t : Fin (X.treeLinks (G.sig 0)).length → Fin 2 → ℝ)
    (j : Fin (X.treeLinks (G.sig 0)).length) (b : Fin 2) :
    treeClockEquiv hX t (treeLinkBranch hX j b) = t j b := by
  let e := finProdFinEquiv.symm.trans (treeLinkEquiv hX)
  change (Equiv.piCongrLeft (fun _ : GBranch G.tree => ℝ) e)
    (Fourier.flattenBlocks (X.treeLinks (G.sig 0)).length 2 t) (treeLinkEquiv hX (j, b)) = _
  have he : e (finProdFinEquiv (j, b)) = treeLinkEquiv hX (j, b) := by simp [e]
  rw [← he, Equiv.piCongrLeft_apply_apply, Fourier.flattenBlocks_apply]
  simp

end WaveTurbulence.IncohInst
