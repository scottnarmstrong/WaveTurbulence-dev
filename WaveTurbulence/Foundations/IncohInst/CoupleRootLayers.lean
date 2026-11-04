/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleTimeDomain

/-! # The computed analytic root bases equal the original source root layers -/

public section
noncomputable section
namespace WaveTurbulence.IncohInst
open Incoh

/-- Reading an analytic vertex layer reads precisely its original source endpoint layer. -/
theorem couple_vertexLayer {LG : LayeredGarden 2} {Q : RegCpl} (d : ℕ) (hQ : Q.Decodes LG.garden)
    (v : Fin Q.links.length × Fin 2) :
    vertexLayer (coupleLayerLinks (d := d) LG hQ) v = (LG.layer (coupleLinkBranch hQ v.1 v.2).toNode : ℤ) := by
  rcases v with ⟨j, b⟩
  fin_cases b <;> rfl

/-- The actual source root layers are the bases of the computed analytic clock split. -/
theorem couple_baseRootTimes {LG : LayeredGarden 2} {Q : RegCpl} (d : ℕ) (hQ : Q.Decodes LG.garden)
    (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) (i : Fin 2) :
    (coupleRootCoordinates hQ hb).baseRootTimes (coupleLayerLinks (d := d) LG hQ) i =
      (LG.layer (GNode.root LG.garden.tree i) : ℝ) := by
  change (vertexLayer (coupleLayerLinks (d := d) LG hQ) ((coupleRootCoordinates hQ hb).rootVertex i) : ℝ) = _
  rw [couple_vertexLayer]
  have he := coupleRootCoordinates_vertex hQ hb i
  have he' : coupleLinkBranch hQ ((coupleRootCoordinates hQ hb).rootVertex i).1
      ((coupleRootCoordinates hQ hb).rootVertex i).2 = (⟨(i, []), hb i⟩ : GBranch LG.garden.tree) := he
  rw [he']
  simp only [Int.cast_natCast]
  rfl

end WaveTurbulence.IncohInst
