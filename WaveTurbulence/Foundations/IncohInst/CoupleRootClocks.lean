/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleLinkCoordinates
public import WaveTurbulence.Foundations.Incoh.RootCoordinatesOfEmbedding

/-! # The actual two-root source clock split -/

public section
noncomputable section
namespace WaveTurbulence.IncohInst
open Incoh

variable {G : Garden 2} {Q : RegCpl}

/-- The actual root clocks, when both source trees branch, form an embedding of the two
external clock indices into the link endpoints. -/
@[expose] def coupleRootEmbedding (hQ : Q.Decodes G)
    (hb : ∀ i, ([] : TTree.Path) ∈ (G.tree i).branching) : Fin 2 ↪ (Fin Q.links.length × Fin 2) where
  toFun i := (coupleLinkEquiv hQ).symm ⟨(i, []), hb i⟩
  inj' := by
    intro i j he
    have hh := (coupleLinkEquiv hQ).symm.injective he
    exact congrArg (fun b : GBranch G.tree => b.1.1) hh

/-- The analytic two-root clock split is constructed from the actual source roots. -/
@[expose] def coupleRootCoordinates (hQ : Q.Decodes G)
    (hb : ∀ i, ([] : TTree.Path) ∈ (G.tree i).branching) : RootCoordinates Q.links.length :=
  rootCoordinatesOfEmbedding (coupleRootEmbedding hQ hb)

/-- Each selected analytic clock is exactly its source root clock. -/
theorem coupleRootCoordinates_vertex (hQ : Q.Decodes G)
    (hb : ∀ i, ([] : TTree.Path) ∈ (G.tree i).branching) (i : Fin 2) :
    coupleLinkEquiv hQ ((coupleRootCoordinates hQ hb).rootVertex i) = ⟨(i, []), hb i⟩ := by
  rw [coupleRootCoordinates, rootCoordinatesOfEmbedding_rootVertex]
  exact (coupleLinkEquiv hQ).apply_symm_apply _

end WaveTurbulence.IncohInst
