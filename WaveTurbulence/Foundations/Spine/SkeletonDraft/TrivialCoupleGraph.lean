/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RegularCoupleReduction

/-! # Exact root-port matching of the actual trivial couple -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

noncomputable def trivialCoupleLeaf (j : Fin 2) : GLeaf (decodedCouple .triv).tree :=
  ⟨(j,[]),by
    have ht : (decodedCouple .triv).tree j = .leaf := by fin_cases j <;> rfl
    rw [ht]
    exact Finset.mem_singleton_self _⟩

theorem trivialCouple_pair_left : (decodedCouple .triv).pair (trivialCoupleLeaf 0) = trivialCoupleLeaf 1 := by
  apply Subtype.ext
  have h := (decodedCouple_decodes .triv).2.2.2 (trivialCoupleLeaf 0)
  simpa [RegCpl.raw,RegCpl.pairsAt,symmPairs,trivialCoupleLeaf] using h

theorem trivialCouple_pair_right : (decodedCouple .triv).pair (trivialCoupleLeaf 1) = trivialCoupleLeaf 0 := by
  rw [← trivialCouple_pair_left,(decodedCouple .triv).pair_pair]

theorem LabelledGarden.trivialCouple_root_mate {B : Type*}
    (label : GBranch (decodedCouple .triv).tree ↪ B) (j : Fin 2) :
    (LabelledGarden.mk (decodedCouple .triv) label).graph.mate (.inl j,0) = (.inl (1-j),0) := by
  let G := LabelledGarden.mk (decodedCouple .triv) label
  have hn (i : Fin 2) : (trivialCoupleLeaf i).toNode = GNode.root G.garden.tree i := Subtype.ext rfl
  have hi (i : Fin 2) : G.incoming (trivialCoupleLeaf i).toNode = (.inl i,0) :=
    (congrArg G.incoming (hn i)).trans (G.incoming_root i)
  fin_cases j
  · exact (congrArg G.graph.mate (hi 0).symm).trans
      ((G.graph_mate_incoming_leaf (trivialCoupleLeaf 0)).trans
        ((congrArg (fun ℓ : GLeaf G.garden.tree => G.incoming ℓ.toNode) trivialCouple_pair_left).trans (hi 1)))
  · exact (congrArg G.graph.mate (hi 1).symm).trans
      ((G.graph_mate_incoming_leaf (trivialCoupleLeaf 1)).trans
        ((congrArg (fun ℓ : GLeaf G.garden.tree => G.incoming ℓ.toNode) trivialCouple_pair_right).trans (hi 0)))

end WaveTurbulence.Reg.Skeleton
