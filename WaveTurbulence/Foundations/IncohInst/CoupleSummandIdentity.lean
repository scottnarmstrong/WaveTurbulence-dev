/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CouplePhaseIntegral
public import WaveTurbulence.Foundations.IncohInst.TemporalSourceIdentity
public import WaveTurbulence.Foundations.IncohInst.InputProductIdentity

/-! # Exact original couple lattice summand in link/time coordinates -/

public section
noncomputable section
open MeasureTheory
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- For each original integer decoration, the source summand equals its literal analytic
link-time integral. No localization, approximation or convergence premise enters this identity. -/
theorem couple_summand_eq_linkIntegral {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (k : Mom d) (ts : Fin 2 → ℝ)
    (p : Fin Q.links.length × Fin 2 → Fin d → ℤ) :
    let κ := (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1
    (epsDec LG.garden κ : ℂ) *
      phaseIntegral L γ δ LG.garden (kDomain LG (fun b => ts b.1.1) 0) 0
        (cosetDecoration LG.garden L k κ) *
      ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k κ ℓ.toNode) : ℂ) =
    ∫ t in (coupleInternalLinkDomain LG hQ ∩ (coupleRootCoordinates hQ hb).rootCut ts),
      sourceTemporalPhase L γ δ (coupleLayerLinks LG hQ) p t *
        (coupleCarrier hQ).sourceLeafWeight (coupleInputFunctions LG F) k
          (fun i j => latticePoint L (p (i, j))) := by
  dsimp only
  rw [couple_phaseIntegral_eq_linkIntegral hQ hb]
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  rw [couple_temporalSource_eq hQ L γ δ k p t]
  congr 1
  rw [couple_sourceLeafWeight_eq hQ F k]
  have he := couple_decOfParams_eq_coset hQ L k (fun j => (p (j, 0), p (j, 1)))
  apply Finset.prod_congr rfl
  intro ℓ _
  exact congrArg (fun v : Mom d => (F (LG.layer ℓ.toNode) v : ℂ)) (congrFun he ℓ.toNode).symm

end WaveTurbulence.IncohInst
