/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineData
/-! Literal TARGET vinechainlem L1930–L1933 (DH23 Lemma 8.1), provider S1 STAGE1-COMB. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset

/-- The source collection consists of disjoint actual atomic groups. Its coverage
is over actual designated vine-like objects, including hyper-adjoint objects. -/
def IsSourceVinePartition {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (collection : Set (Finset V)) : Prop :=
  (∀ S ∈ collection, ∃ a b,
    SourceVine.IsHV M S a b ∨ SourceVine.IsVC M S a b ∨
      SourceVine.IsHVC M S a b ∨ SourceVine.IsDV M S a b) ∧
  collection.Pairwise (fun S T => Disjoint S T) ∧
  ∀ P : SourceVine.Object M, ∃ S ∈ collection, P.atoms ⊆ S

end WaveTurbulence.LGSpine
