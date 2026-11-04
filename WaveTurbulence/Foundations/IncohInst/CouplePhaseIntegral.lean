/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleTimeBoundary
public import WaveTurbulence.Foundations.IncohInst.CoupleTimeDomain
public import WaveTurbulence.Foundations.IncohInst.NoFlowerTimeIntegral
public import WaveTurbulence.Foundations.IncohInst.NoFlowers

/-! # Exact original couple time integral in the analytic root-cut coordinates -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh

/-- The actual source root constraint pulls back to the computed analytic root cut. -/
theorem coupleClockEquiv_preimage_rootDomain {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    (ts : Fin 2 → ℝ) :
    coupleClockEquiv hQ ⁻¹' (internalTimeDomain LG ∩
      {τ | ∀ i : Fin 2, τ ⟨(i, []), hb i⟩ ≤ ts i}) =
      coupleInternalLinkDomain LG hQ ∩ (coupleRootCoordinates hQ hb).rootCut ts := by
  ext t
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, coupleInternalLinkDomain,
    RootCoordinates.rootCut, mem_prod, mem_Iic, mem_univ, and_true]
  simp_rw [coupleClockEquiv_root hQ hb]
  rfl

/-- The original phase integral, including its source strict boundary convention, is exactly
an integral over the analytic internal domain with its two selected root cuts. -/
theorem couple_phaseIntegral_eq_linkIntegral {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    {d : ℕ} (L γ δ : ℝ) (ts : Fin 2 → ℝ) (κ : GNode LG.garden.tree → Mom d) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun b => ts b.1.1) 0) 0 κ =
      ∫ t in (coupleInternalLinkDomain LG hQ ∩ (coupleRootCoordinates hQ hb).rootCut ts),
        phaseProd L γ δ LG.garden κ (coupleClockEquiv hQ t) := by
  rw [phaseIntegral_eq_of_noFlowers LG.garden (couple_noFlowers hQ) L γ δ _
    (measurableSet_kDomain LG _ 0)]
  rw [setIntegral_congr_set (couple_kDomain_ae_rootCut LG hb ts)]
  rw [← (measurePreserving_coupleClockEquiv hQ).setIntegral_preimage_emb
    (coupleClockEquiv hQ).measurableEmbedding]
  rw [coupleClockEquiv_preimage_rootDomain hQ hb ts]

end WaveTurbulence.IncohInst
