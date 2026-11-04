/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreePhaseIdentity
public import WaveTurbulence.Foundations.IncohInst.WickFactors
public import WaveTurbulence.Foundations.IncohInst.CosetDecorationIdentity
public import WaveTurbulence.Foundations.IncohInst.LinkParameterValues
public import WaveTurbulence.Foundations.IncohInst.CoupleLayers
public import WaveTurbulence.Foundations.IncohInst.TreeLayers
public import WaveTurbulence.Foundations.Incoh.SourceTemporalPhase

/-! # The exact original lattice Wick-phase integrand after source reindexing -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- Exact couple source temporal integrand, with the original integer Wick factor and
original real coset phase. -/
theorem couple_temporalSource_eq {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    {d : ℕ} (L γ δ : ℝ) (k : Mom d) (p : Fin Q.links.length × Fin 2 → Fin d → ℤ)
    (t : Fin Q.links.length → Fin 2 → ℝ) :
    (epsDec LG.garden (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
      phaseProd L γ δ LG.garden
        (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1)
        (coupleClockEquiv hQ t) = sourceTemporalPhase L γ δ (coupleLayerLinks LG hQ) p t := by
  rw [← couple_decOfParams_eq_coset hQ L k]
  rw [couple_phaseProd_eq_links hQ L γ δ (decOfParams hQ k _).2.1]
  rw [couple_epsDec_eq_linkWickFactor hQ (decOfParams hQ (0 : Fin d → ℤ) _).2.1]
  simp only [couple_xNode_decOfParams, couple_yNode_decOfParams]
  rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rfl

/-- Exact paired-tree source temporal integrand, with the squared Wick factor required by F62. -/
theorem tree_temporalSource_eq {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    {d : ℕ} (L γ δ : ℝ) (k : Mom d)
    (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ)
    (t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ) :
    (epsDec LG.garden (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
      phaseProd L γ δ LG.garden
        (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1)
        (treeClockEquiv hX t) = sourceTemporalPhase L γ δ (treeLayerLinks LG hX) p t := by
  rw [← tree_decOfParams_eq_coset hX L k]
  rw [tree_phaseProd_eq_links hX L γ δ (treeDecOfParams hX k _).2.1]
  rw [tree_epsDec_eq_linkWickFactor hX (treeDecOfParams hX (0 : Fin d → ℤ) _).2.1]
  simp only [tree_xNode_decOfParams, tree_yNode_decOfParams]
  rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rfl

end WaveTurbulence.IncohInst
