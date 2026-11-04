/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PredecessorOrder
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Counting alternative localization labels by predecessor differences

Instead of recursively enumerating labels with a changing center, use
their edge differences. Acyclicity makes this map injective, and the edge
labels range over an ordinary finite product of fixed choice sets.
-/

public section

open Finset Set

namespace WaveTurbulence.Sumint

/-- Label assignments whose predecessor differences lie in fixed finite choice sets. -/
@[expose] def predecessorLabelSet {ι G : Type*} [AddGroup G]
    (prev : ι → Option ι) (choices : ι → Finset G) : Set (ι → G) :=
  {a | ∀ v, edgeDifference prev a v ∈ choices v}

/-- Fixed finite edge-choice sets give a finite family of complete labels. -/
theorem predecessorLabelSet_finite {ι G : Type*} [Fintype ι] [AddGroup G]
    (prev : ι → Option ι) (rank : ι → ℕ)
    (hp : ∀ v w, prev v = some w → rank w < rank v) (choices : ι → Finset G) :
    (predecessorLabelSet prev choices).Finite := by
  classical
  have hm : Set.MapsTo (edgeDifference prev) (predecessorLabelSet prev choices)
      (↑(Fintype.piFinset choices) : Set (ι → G)) := by
    intro a ha
    exact Fintype.mem_piFinset.mpr ha
  exact Set.Finite.of_injOn hm (edgeDifference_injective prev rank hp).injOn
    (Fintype.piFinset choices).finite_toSet

/-- The number of complete labels is at most the product of the numbers of edge choices. -/
theorem predecessorLabelSet_ncard_le {ι G : Type*} [Fintype ι] [AddGroup G]
    (prev : ι → Option ι) (rank : ι → ℕ)
    (hp : ∀ v w, prev v = some w → rank w < rank v) (choices : ι → Finset G) :
    (predecessorLabelSet prev choices).ncard ≤ ∏ v, (choices v).card := by
  classical
  have hm : Set.MapsTo (edgeDifference prev) (predecessorLabelSet prev choices)
      (↑(Fintype.piFinset choices) : Set (ι → G)) := by
    intro a ha
    exact Fintype.mem_piFinset.mpr ha
  have hh := Set.ncard_le_ncard_of_injOn (edgeDifference prev) hm
    (edgeDifference_injective prev rank hp).injOn (Fintype.piFinset choices).finite_toSet
  simpa only [Set.ncard_coe_finset, Fintype.card_piFinset] using hh

/-- The exact source admissibility premise supplies the required predecessor acyclicity. -/
theorem source_predecessor_labels_count {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {Dsteps : ℕ}
    (hD : D.Admissible A L γ η Dsteps) (choices : D.S.VIdx → Finset (Fin d → ℤ)) :
    (predecessorLabelSet D.prev choices).Finite ∧
      (predecessorLabelSet D.prev choices).ncard ≤ ∏ v, (choices v).card := by
  have hp : ∀ v w, D.prev v = some w → lexRank D.S w < lexRank D.S v :=
    fun _ _ hw => predecessor_rank_lt D hD hw
  exact ⟨predecessorLabelSet_finite D.prev (lexRank D.S) hp choices,
    predecessorLabelSet_ncard_le D.prev (lexRank D.S) hp choices⟩

end WaveTurbulence.Sumint
