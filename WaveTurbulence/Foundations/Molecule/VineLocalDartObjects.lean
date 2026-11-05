/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLocalDartEmbedding
public import WaveTurbulence.Foundations.Molecule.VineObjects
import Mathlib.Tactic

/-! # Local dart identifications preserve blocks and exact vine realizations -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}
namespace LocalDartEmbedding
variable (F : LocalDartEmbedding M N A)

include F in
/-- Every induced outgoing bond occurrence is preserved, with its exact
unordered endpoints and multiplicity. -/
theorem groupBonds_eq (S : Finset V) (hSA : S ⊆ A) : N.groupBonds S=M.groupBonds S := by
  classical
  let f : E ↪ D := ⟨F.toFun,F.injective⟩
  let U := (univ : Finset E).filter (fun d => N.out d=true ∧ N.InGroup S d)
  let T := (univ : Finset D).filter (fun d => M.out d=true ∧ M.InGroup S d)
  have hmap : U.map f=T := by
    ext d
    constructor
    · intro hd
      obtain ⟨e,he,rfl⟩ := mem_map.mp hd
      obtain ⟨_he,ho,hg⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨mem_univ _,(F.out_eq e).trans ho,(F.inGroup_iff S e).mpr hg⟩
    · intro hd
      obtain ⟨_hd,ho,hg⟩ := mem_filter.mp hd
      obtain ⟨e,he⟩ := F.surjective_internal d ⟨hSA hg.1,hSA hg.2⟩
      refine mem_map.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,?_,?_⟩,he⟩
      · rw [← F.out_eq,he]
        exact ho
      · apply (F.inGroup_iff S e).mp
        rwa [he]
  have hv := congrArg Finset.val hmap
  rw [map_val] at hv
  have hh := congrArg (Multiset.map M.ends) hv
  rw [Multiset.map_map] at hh
  have he : M.ends ∘ f=N.ends := by funext d; exact F.ends_eq d
  rw [he] at hh
  exact hh

include F in
omit [Fintype D] [Fintype E] in
/-- The source induced connectivity predicate retains exactly the same paths. -/
private theorem groupConnected_iff (S : Finset V) (hSA : S ⊆ A) :
    N.GroupConnected S ↔ M.GroupConnected S := by
  have hrel : (fun a b => ∃ e, N.InGroup S e ∧ N.atom e = a ∧ N.atom (N.mate e) = b) =
      (fun a b => ∃ d, M.InGroup S d ∧ M.atom d = a ∧ M.atom (M.mate d) = b) := by
    funext a b
    apply propext
    constructor
    · rintro ⟨e, hg, ha, hb⟩
      exact ⟨F.toFun e, (F.inGroup_iff S e).mpr hg,
        (F.atom_eq e).trans ha, (F.neighbor_eq e).trans hb⟩
    · rintro ⟨d, hg, ha, hb⟩
      obtain ⟨e, he⟩ := F.surjective_internal d ⟨hSA hg.1, hSA hg.2⟩
      refine ⟨e, ?_, ?_, ?_⟩
      · apply (F.inGroup_iff S e).mp
        rwa [he]
      · rw [← F.atom_eq, he]
        exact ha
      · rw [← F.neighbor_eq, he]
        exact hb
  simp only [Molecule.GroupConnected, hrel]

include F in
/-- The exact oriented block predicate is invariant under the local
identification; full atom-set inclusion and all joint degrees are retained. -/
theorem isBlock_iff (S : Finset V) (hSA : S ⊆ A) (a b : V) :
    N.IsBlock S a b ↔ M.IsBlock S a b := by
  have ho (v : V) := (F.degrees S hSA v).1
  have hi (v : V) := (F.degrees S hSA v).2.1
  have hd (v : V) := (F.degrees S hSA v).2.2
  simp only [Molecule.IsBlock,← F.atoms_eq,ho,hi,hd,F.groupConnected_iff S hSA]

include F in
/-- The pinned undirected template realization and its actual block
premise are preserved exactly under internal dart identification. -/
theorem isVine_iff (X : VineType) (S : Finset V) (hSA : S ⊆ A) (a b : V) :
    N.IsVine X S a b ↔ M.IsVine X S a b := by
  simp only [Molecule.IsVine,F.isBlock_iff S hSA a b,F.groupBonds_eq S hSA]

end LocalDartEmbedding
end WaveTurbulence.Vine
