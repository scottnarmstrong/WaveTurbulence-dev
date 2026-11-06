/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedFullChart
public import WaveTurbulenceVineParam.VineParamInsertedPhysicalPairs
import Mathlib.Tactic

/-! # The complete strengthened physical chart after one geometric insertion -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Retain all fixed physical origins as well as the full contract after a
source splice. Choices of representatives are geometric, uniform in labels
and in the additive momentum group. -/
@[expose] noncomputable def insertedPhysicalChart {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (hcap : P.CapSupported G.cap)
    (hpairs : ∀ j : Fin P.full.indexing.shape.m,
      (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ G.cap ↔
        (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ G.cap)
    (hbad : X.IsBad=true → G.gapSign a b ≠ 0) :
    PhysicalGraphChart G.newEnds X (.inl a) (.inl b) where
  distinct := fun h => P.distinct (Sum.inl.inj h)
  full := G.insertedFullChart P hX ha hb hcap hpairs hbad
  reference := G.representative P.reference (decide (b ∈ G.cap))
  reference_at := by
    simpa only [hb] using G.representative_incident P.reference b P.reference_at
  reference_eq := G.inserted_reference_eq P hX ha hb
  reference_column := G.contractInsertedFree_reference P.full hX (decide (b ∈ G.cap)) P.reference_column
  differencePair := G.insertedPhysicalPair P hcap hX
  difference_eq := G.insertedPhysicalPair_eq P hcap hX ha hb

end WaveTurbulence.Vine.Param.RungSpliceGeometry
