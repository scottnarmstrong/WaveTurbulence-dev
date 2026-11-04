/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleRootClocks
public import WaveTurbulence.Foundations.IncohInst.ClockTransport
public import WaveTurbulence.Foundations.IncohInst.CoupleLayers
public import WaveTurbulence.Foundations.IncohInst.InternalTimeDomain
public import WaveTurbulence.Foundations.Incoh.RootCumulative

/-! # The actual source couple domain in link coordinates -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh

variable {LG : LayeredGarden 2} {Q : RegCpl}

/-- The external-time-independent part of the literal source domain, in actual link clocks. -/
@[expose] def coupleInternalLinkDomain (LG : LayeredGarden 2) {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) : Set (Fin Q.links.length → Fin 2 → ℝ) :=
  coupleClockEquiv hQ ⁻¹' internalTimeDomain LG

theorem measurableSet_coupleInternalLinkDomain (hQ : Q.Decodes LG.garden) :
    MeasurableSet (coupleInternalLinkDomain LG hQ) :=
  (measurableSet_internalTimeDomain LG).preimage (coupleClockEquiv hQ).measurable

/-- The actual source domain lies in the exact product of its source layer boxes. -/
theorem coupleInternalLinkDomain_subset_boxes (d : ℕ) (hQ : Q.Decodes LG.garden) :
    coupleInternalLinkDomain LG hQ ⊆ Set.univ.pi (fun j => linkBox (coupleLayerLinks (d := d) LG hQ j)) := by
  intro t ht j _
  constructor <;> intro b <;> fin_cases b
  · simpa [coupleLayerLinks, coupleClockEquiv_apply] using (ht (coupleLinkBranch hQ j 0)).1.le
  · simpa [coupleLayerLinks, coupleClockEquiv_apply] using (ht (coupleLinkBranch hQ j 1)).1.le
  · simpa [coupleLayerLinks, coupleClockEquiv_apply] using (ht (coupleLinkBranch hQ j 0)).2.1.le
  · simpa [coupleLayerLinks, coupleClockEquiv_apply] using (ht (coupleLinkBranch hQ j 1)).2.1.le

/-- Selecting the actual roots recovers exactly the source root times under clock transport. -/
theorem coupleClockEquiv_root (hQ : Q.Decodes LG.garden)
    (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    (t : Fin Q.links.length → Fin 2 → ℝ) (i : Fin 2) :
    coupleClockEquiv hQ t ⟨(i, []), hb i⟩ = ((coupleRootCoordinates hQ hb).equiv t).1 i := by
  have he := coupleRootCoordinates_vertex hQ hb i
  rw [RootCoordinates.equiv_rootVertex, ← he]
  exact coupleClockEquiv_apply hQ t _ _

end WaveTurbulence.IncohInst
