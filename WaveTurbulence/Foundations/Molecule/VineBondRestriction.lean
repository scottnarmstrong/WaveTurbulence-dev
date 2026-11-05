/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMappedDegrees
public import Mathlib.Data.Finset.Sym
import Mathlib.Tactic

/-! # Restricting the exact undirected realization to nested atomic groups -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The induced bond multiset on a subgroup is the outer bond multiset
filtered to bonds with both endpoints in the subgroup. -/
theorem groupBonds_filter (M : Molecule V D) {A S : Finset V} (hAS : A ⊆ S) :
    M.groupBonds A=(M.groupBonds S).filter (fun e => e ∈ A.sym2) := by
  have hf : univ.filter (fun x : D => M.out x=true ∧ M.InGroup A x) =
      (univ.filter (fun x : D => M.out x=true ∧ M.InGroup S x)).filter
        (fun x => M.ends x ∈ A.sym2) := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hd := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨mem_univ _,hd.1,hAS hd.2.1,hAS hd.2.2⟩,?_⟩
      exact mk_mem_sym2_iff.mpr ⟨hd.2.1,hd.2.2⟩
    · intro hx
      have hd := Finset.mem_filter.mp hx
      have ho := (Finset.mem_filter.mp hd.1).2.1
      have hp := mk_mem_sym2_iff.mp hd.2
      exact Finset.mem_filter.mpr ⟨mem_univ _,ho,hp.1,hp.2⟩
  have he := congrArg (fun T : Finset D => T.val.map M.ends) hf
  simpa only [Molecule.groupBonds,filter_val,Multiset.filter_map,Function.comp_apply] using he

omit [DecidableEq V] in
/-- On an injective outer atom carrier, membership in the image of a subgroup
is exactly original membership, including at each bond endpoint. -/
theorem mem_image_iff_of_injOn {A S : Finset V} (hAS : A ⊆ S) (f : V → ℕ)
    (hf : Set.InjOn f S) {v : V} (hv : v ∈ S) : f v ∈ A.image f ↔ v ∈ A := by
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := mem_image.mp h
    have hwv := hf (hAS hw) hv he
    exact hwv ▸ hw
  · exact mem_image_of_mem f

/-- Restriction commutes with the undirected bond realization, without
assuming that the nested group itself is a vine. -/
theorem mapped_groupBonds_filter (M : Molecule V D) {A S : Finset V} (hAS : A ⊆ S)
    (f : V → ℕ) (hf : Set.InjOn f S) :
    (M.groupBonds A).map (Sym2.map f)=
      ((M.groupBonds S).map (Sym2.map f)).filter (fun e => e ∈ (A.image f).sym2) := by
  rw [groupBonds_filter M hAS,Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro e he
  simp only [Molecule.groupBonds,Multiset.mem_map,Finset.mem_val,mem_filter,mem_univ,true_and] at he
  obtain ⟨x,⟨_hout,hg⟩,rfl⟩ := he
  simp only [Function.comp_apply,Molecule.ends,Sym2.map_mk,mk_mem_sym2_iff,
    mem_image_iff_of_injOn hAS f hf hg.1,mem_image_iff_of_injOn hAS f hf hg.2]

end WaveTurbulence.Vine
