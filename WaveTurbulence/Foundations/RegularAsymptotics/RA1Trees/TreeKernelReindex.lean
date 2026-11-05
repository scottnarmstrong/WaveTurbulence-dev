/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.DecorationEquivalences
public import WaveTurbulence.Foundations.IncohInst.WickFactors
public import WaveTurbulence.Foundations.IncohInst.LinkParameterValues

/-! # The original tree kernel in its actual independent integer link coordinates -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links IncohInst Incoh

/-- Exact reindexing, retaining the source Wick factor and both original time endpoints. -/
theorem KTstar_treeLatticeEquiv {d : ℕ} (L γ δ : ℝ) (F : Mom d → ℝ)
    (LG : LayeredGarden 1) {X : RegChain} (hX : X.DecodesTree LG.garden)
    (t s : ℝ) (k : Mom d) :
    KTstar L γ δ (fun _ => F) LG t s k =
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
          let κ := (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j,0),p (j,1)))).val
          ((∏ j, linkWickFactor (p (j,0)) (p (j,1))):ℂ) *
            phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s
              (cosetDecoration LG.garden L k κ) *
            ∏ ℓ ∈ inputLeaves LG.garden, (F (cosetDecoration LG.garden L k κ ℓ.toNode):ℂ) := by
  unfold KTstar kernelK
  congr 1
  rw [← (treeLatticeEquiv hX d).symm.tsum_eq]
  apply tsum_congr
  intro p
  have hdec : ((treeLatticeEquiv hX d).symm p).val =
      (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j,0),p (j,1)))).val := rfl
  rw [hdec]
  change (epsDec LG.garden (treeDecOfParams hX (0 : Fin d → ℤ)
    (fun j => (p (j,0),p (j,1)))).val:ℂ) * _ * _ = _
  rw [tree_epsDec_eq_linkWickFactor hX (treeDecOfParams hX (0 : Fin d → ℤ) _).property.1]
  simp only [tree_xNode_decOfParams, tree_yNode_decOfParams, Complex.ofReal_prod]

end WaveTurbulence.RegAsymp
