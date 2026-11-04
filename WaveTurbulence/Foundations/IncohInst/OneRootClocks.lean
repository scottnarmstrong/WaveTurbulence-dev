/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.OneRootPhaseIntegral
public import WaveTurbulence.Foundations.IncohInst.CoupleRootLayers

/-! # The actual one-root source clock and its analytic auxiliary completion -/

public section
noncomputable section
namespace WaveTurbulence.IncohInst
open Incoh

variable {LG : LayeredGarden 2} {Q : RegCpl}

/-- Complete the actual single root by an auxiliary branching clock, never by a fictitious root. -/
@[expose] def oneRootCoordinates (hQ : Q.Decodes LG.garden) (hn : 1 ≤ Q.links.length) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching) : RootCoordinates Q.links.length :=
  oneClockSelection Q.links.length hn ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩) a

/-- Only the active selected clock is asserted to be a source root. -/
theorem oneRootCoordinates_base (d : ℕ) (hQ : Q.Decodes LG.garden) (hn : 1 ≤ Q.links.length) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching) :
    (oneRootCoordinates hQ hn a hb).baseRootTimes (coupleLayerLinks (d := d) LG hQ) a =
      (LG.layer (GNode.root LG.garden.tree a) : ℝ) := by
  change (vertexLayer (coupleLayerLinks (d := d) LG hQ) ((oneRootCoordinates hQ hn a hb).rootVertex a) : ℝ) = _
  rw [oneRootCoordinates, oneClockSelection_rootVertex, couple_vertexLayer]
  have he : coupleLinkBranch hQ ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩).1
      ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩).2 = (⟨(a, []), hb⟩ : GBranch LG.garden.tree) :=
    (coupleLinkEquiv hQ).apply_symm_apply _
  rw [he]
  simp only [Int.cast_natCast]
  rfl

end WaveTurbulence.IncohInst
