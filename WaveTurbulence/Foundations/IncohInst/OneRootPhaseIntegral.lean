/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.OneRootTimeBoundary
public import WaveTurbulence.Foundations.Incoh.OneClockSelection
public import WaveTurbulence.Foundations.Incoh.OneClockCouple
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
theorem coupleClockEquiv_preimage_oneRootDomain {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hn : 1 ≤ Q.links.length) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
    (ts : Fin 2 → ℝ) :
    coupleClockEquiv hQ ⁻¹' (internalTimeDomain LG ∩
      {τ | τ ⟨(a, []), hb⟩ ≤ ts a}) =
      coupleInternalLinkDomain LG hQ ∩ (oneClockSelection Q.links.length hn ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩) a).oneClockCut a (ts a) := by
  ext t
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, coupleInternalLinkDomain,
    RootCoordinates.oneClockCut]
  rw [RootCoordinates.equiv_rootVertex, oneClockSelection_rootVertex]
  have he := coupleClockEquiv_apply hQ t
    ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩).1 ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩).2
  have he' : coupleLinkBranch hQ ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩).1
      ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩).2 = (⟨(a, []), hb⟩ : GBranch LG.garden.tree) :=
    (coupleLinkEquiv hQ).apply_symm_apply _
  rw [he'] at he
  rw [he]

/-- The original phase integral, including its source strict boundary convention, is exactly
an integral over the analytic internal domain with its two selected root cuts. -/
theorem couple_phaseIntegral_eq_oneRootIntegral {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hn : 1 ≤ Q.links.length) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
    (hwidth : ∀ b : GBranch LG.garden.tree, b.1.1 = a)
    {d : ℕ} (L γ δ : ℝ) (ts : Fin 2 → ℝ) (κ : GNode LG.garden.tree → Mom d) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun b => ts b.1.1) 0) 0 κ =
      ∫ t in (coupleInternalLinkDomain LG hQ ∩ (oneClockSelection Q.links.length hn ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩) a).oneClockCut a (ts a)),
        phaseProd L γ δ LG.garden κ (coupleClockEquiv hQ t) := by
  rw [phaseIntegral_eq_of_noFlowers LG.garden (couple_noFlowers hQ) L γ δ _
    (measurableSet_kDomain LG _ 0)]
  rw [setIntegral_congr_set (couple_kDomain_ae_oneRootCut LG a hb hwidth ts)]
  rw [← (measurePreserving_coupleClockEquiv hQ).setIntegral_preimage_emb
    (coupleClockEquiv hQ).measurableEmbedding]
  rw [coupleClockEquiv_preimage_oneRootDomain hQ hn a hb ts]

end WaveTurbulence.IncohInst
