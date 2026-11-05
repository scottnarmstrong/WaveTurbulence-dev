/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LeafInsertion

/-! # Exact leaf bijection for insertion at a forest leaf

TARGET twist: the unchanged leaves and leaves of the inserted subtree
form disjoint pieces. This bijection transports the actual garden pairing.
-/

public section
namespace WaveTurbulence.Twist
open TTree Finset
variable {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) (t : TTree)

/-- Leaves outside the insertion point, together with inserted-subtree leaves. -/
abbrev InsertionLeafPiece := {l : GLeaf F // l ≠ h} ⊕ ↥t.leaves

/-- Insert the pieces into the actual new leaf carrier. -/
@[expose] def insertionLeafMap : InsertionLeafPiece F h t → GLeaf (insertLeaf F h t)
  | .inl l => ⟨l.1.1,by
      by_cases hi : l.1.1.1 = h.1.1
      · rw [hi,insertLeaf_leaves]
        apply mem_union_left
        apply mem_filter.mpr
        refine ⟨hi ▸ l.1.2,?_⟩
        intro hp
        exact l.2 (Subtype.ext (Prod.ext hi hp))
      · rw [insertLeaf_other F h t _ hi]
        exact l.1.2⟩
  | .inr q => ⟨(h.1.1,h.1.2 ++ q.1),by
      rw [insertLeaf_leaves]
      exact mem_union_right _ (mem_image.mpr ⟨q.1,q.2,rfl⟩)⟩

/-- Distinct pieces give distinct actual new leaves. -/
theorem insertionLeafMap_injective : Function.Injective (insertionLeafMap F h t) := by
  rintro (l | q) (m | r) he
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (congrArg (fun n : GLeaf (insertLeaf F h t) => n.1) he)))
  · have hi := congrArg (fun l : GLeaf (insertLeaf F h t) => l.1.1) he
    have hp := congrArg (fun l : GLeaf (insertLeaf F h t) => l.1.2) he
    have hpre : h.1.2 <+: l.1.1.2 := ⟨r.1,hp.symm⟩
    have hleaf : l.1.1.2 ∈ (F h.1.1).leaves := hi ▸ l.1.2
    have hh := leaf_prefix_eq h.2 hleaf hpre
    exact (l.2 (Subtype.ext (Prod.ext hi hh.symm))).elim
  · have hi := congrArg (fun l : GLeaf (insertLeaf F h t) => l.1.1) he
    have hp := congrArg (fun l : GLeaf (insertLeaf F h t) => l.1.2) he
    have hpre : h.1.2 <+: m.1.1.2 := ⟨q.1,hp⟩
    have hleaf : m.1.1.2 ∈ (F h.1.1).leaves := hi.symm ▸ m.1.2
    have hh := leaf_prefix_eq h.2 hleaf hpre
    exact (m.2 (Subtype.ext (Prod.ext hi.symm hh.symm))).elim
  · have hp := congrArg (fun l : GLeaf (insertLeaf F h t) => l.1.2) he
    exact congrArg Sum.inr (Subtype.ext (List.append_cancel_left hp))

/-- Every new actual leaf belongs to one of the two pieces. -/
theorem insertionLeafMap_surjective : Function.Surjective (insertionLeafMap F h t) := by
  intro l
  by_cases hi : l.1.1 = h.1.1
  · have hm : l.1.2 ∈ (insertLeaf F h t h.1.1).leaves := hi ▸ l.2
    rw [insertLeaf_leaves] at hm
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨hl,hne⟩ := mem_filter.mp hm
      let old : GLeaf F := ⟨l.1,hi.symm ▸ hl⟩
      have hold : old ≠ h := by
        intro he
        exact hne (congrArg (fun l : GLeaf F => l.1.2) he)
      exact ⟨.inl ⟨old,hold⟩,Subtype.ext rfl⟩
    · obtain ⟨q,hq,hpath⟩ := mem_image.mp hm
      exact ⟨.inr ⟨q,hq⟩,Subtype.ext (Prod.ext hi.symm hpath)⟩
  · let old : GLeaf F := ⟨l.1,by
      have hl := l.2
      rw [insertLeaf_other F h t _ hi] at hl
      exact hl⟩
    have hold : old ≠ h := fun he => hi (congrArg (fun l : GLeaf F => l.1.1) he)
    exact ⟨.inl ⟨old,hold⟩,Subtype.ext rfl⟩

/-- The concrete insertion leaf bijection; no abstract Garden is substituted. -/
@[expose] noncomputable def insertionLeafEquiv : InsertionLeafPiece F h t ≃ GLeaf (insertLeaf F h t) :=
  Equiv.ofBijective (insertionLeafMap F h t)
    ⟨insertionLeafMap_injective F h t,insertionLeafMap_surjective F h t⟩

end WaveTurbulence.Twist
