/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreIntrinsicLift
import Mathlib.Tactic

/-! # Every prescribed expanded group is intrinsically connected -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Any actual label at least two is a nonjoint atom. -/
theorem VineRealization.interior_of_label {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b u : V} (R : VineRealization M X S a b) (hB : M.IsBlock S a b)
    (hu : u ∈ S) (h2 : 2 ≤ R.f u) : VineInterior S a b u := by
  have hh := realization_index_lt_two_iff R hB hu
  have hn : ¬(u=a ∨ u=b) := fun he => by have := hh.mpr he; omega
  exact ⟨hu,not_or.mp hn⟩

omit [DecidableEq D] in
/-- The two atoms of an actual allocated rung are intrinsically adjacent. -/
theorem RealizedSlot.coherence_double (M : Molecule V D)
    {X : VineType} {S : Finset V} {a b : V} {R : VineRealization M X S a b}
    (A : RealizedSlot R) (hB : M.IsBlock S a b) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ A.k) :
    CoherenceDouble M S a b (A.Q.u i) (A.Q.v i) := by
  have hn : 2 ≤ (A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
    rw [fold_insertRungs_atoms]
    have : 2 ≤ X.template.n := by cases X <;> decide
    omega
  exact ⟨R.interior_of_label hB (A.mem i).1 (by rw [(A.labels i hi hin).1]; omega),
    R.interior_of_label hB (A.mem i).2 (by rw [(A.labels i hi hin).2]; omega),
    A.frame.upper_cross i i hi hin (by omega),⟨A.double i hi hin⟩⟩

/-- Every pair of atoms in one literal expanded group has an intrinsic path. -/
theorem VineRealization.group_intrinsic_connected (M : Molecule V D)
    (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b u v : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b)
    {g : List ℕ} (hg : g ∈ (X.expand R.k).groups)
    (hu : u ∈ S) (hv : v ∈ S) (hug : R.f u ∈ g) (hvg : R.f v ∈ g) :
    Relation.EqvGen (CoherenceEdge M S a b) u v := by
  rcases fold_group_origin X.template (X.template.slots.zip R.k) hg with hg | ⟨pre,post,s,k,i,hloc,hi,hg⟩
  · have bound (z : V) (hz : R.f z ∈ g) : R.f z<X.template.n := by
      have hh := (template_groups_partition X).mem_iff.mp (List.mem_flatten.mpr ⟨g,hg,hz⟩)
      exact List.mem_range.mp (List.mem_of_mem_drop hh)
    have huo := bound u hug
    have hvo := bound v hvg
    have heU := R.eq_coreAtom_of_label hu ⟨R.f u,huo⟩ rfl
    have heV := R.eq_coreAtom_of_label hv ⟨R.f v,hvo⟩ rfl
    rw [heU,heV]
    exact R.core_group_intrinsic_connected M hM hB hg ⟨R.f u,huo⟩ ⟨R.f v,hvo⟩ hug hvg
  · obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
    let A : RealizedSlot R := ⟨pre,post,s,k,hloc,Q,hmem,hports,hlabels⟩
    have hi1 : 1 ≤ i+1 := by omega
    have hin : i+1 ≤ A.k := by change i+1 ≤ k; omega
    have hpair : g=[R.f (Q.u (i+1)),R.f (Q.v (i+1))] := by
      rw [(hlabels (i+1) hi1 hin).1,(hlabels (i+1) hi1 hin).2]
      simpa only [Nat.add_sub_cancel] using hg
    have hd : Relation.EqvGen (CoherenceEdge M S a b) (Q.u (i+1)) (Q.v (i+1)) :=
      Relation.EqvGen.rel _ _ (Or.inl (A.coherence_double M hB (i+1) hi1 hin))
    have toU (z : V) (hz : z ∈ S) (hzg : R.f z ∈ g) :
        Relation.EqvGen (CoherenceEdge M S a b) z (Q.u (i+1)) := by
      rw [hpair] at hzg
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hzg
      rcases hzg with hzU | hzV
      · have he := R.injOn hz (hmem (i+1)).1 hzU
        rw [he]; exact Relation.EqvGen.refl _
      · have he := R.injOn hz (hmem (i+1)).2 hzV
        rw [he]; exact Relation.EqvGen.symm _ _ hd
    exact Relation.EqvGen.trans _ _ _ (toU u hu hug) (Relation.EqvGen.symm _ _ (toU v hv hvg))

end WaveTurbulence.Vine
