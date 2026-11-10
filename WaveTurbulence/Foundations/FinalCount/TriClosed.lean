/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriCover3
/-! Triangles, part 8 (FINALCOUNT-G2): closed atom sets of the final cut molecule `m3` coming from the `β`-cuts
(the component of `f j` after the `j`-th cut): they contain no `t i`, contain `f j`, and no `f i` with `i > j`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- An atom set is closed under adjacency. -/
def IsClosedSet (N : Molecule V D) (S : Finset V) : Prop := ∀ x, N.atom x ∈ S → N.atom (N.mate x) ∈ S

theorem isClosedSet_cut {N : Molecule V D} {S : Finset V} (hS : IsClosedSet N S) (hsub : ∀ a ∈ S, a ∈ N.atoms)
    {v v₂ : V} {x₁ x₂ : D} (hv : v ∉ S) (hv₂ : v₂ ∉ N.atoms) : IsClosedSet (N.cut v v₂ x₁ x₂) S := by
  intro x hx
  rw [cut_atom] at hx ⊢
  split_ifs at hx with h1
  · exact absurd (hsub _ hx) hv₂
  · have h2 := hS x hx
    rw [if_neg]
    · exact h2
    · intro h3; exact hv (h3.1 ▸ h2)


theorem isClosedSet_comp (N : Molecule V D) (u : V) :
    IsClosedSet N (N.atoms.filter fun a => N.SameComponent a u) := by
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨N.atom_mem _, Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩)) hx.2⟩

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem sc_t (N : Molecule V D) (hmate : ∀ x, N.mate x = M.mate x)
    (hat : ∀ x j, (x = T.a j ∨ x = T.b j) → N.atom x = T.t j) (i j : Fin 3) :
    N.SameComponent (T.t i) (T.t j) := by
  have adj : ∀ k : Fin 3, N.SameComponent (T.t k) (T.t (k + 1)) := fun k =>
    Relation.EqvGen.rel _ _ ⟨T.b k, hat _ k (Or.inr rfl), by
      rw [hmate, T.mate_b]; exact hat _ _ (Or.inl rfl)⟩
  have h0 : ∀ k : Fin 3, N.SameComponent (T.t k) (T.t 0) := by
    intro k
    fin_cases k
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.symm _ _ (adj 0)
    · exact adj 2
  exact Relation.EqvGen.trans _ _ _ (h0 i) (Relation.EqvGen.symm _ _ (h0 j))

theorem sc_t_m1 (i j : Fin 3) : T.m1.SameComponent (T.t i) (T.t j) :=
  T.sc_t T.m1 (fun _ => rfl) (fun x j h => T.m1_atom_tri x j h) i j

theorem sc_t_m2 (i j : Fin 3) : T.m2.SameComponent (T.t i) (T.t j) :=
  T.sc_t T.m2 (fun _ => rfl) (fun x j h => T.m2_atom_tri x j h) i j

theorem m1_atoms_sub_m2 : T.m1.atoms ⊆ T.m2.atoms := by
  intro a ha; rw [m2_atoms]; exact Finset.mem_insert_of_mem ha
theorem m2_atoms_sub_m3 : T.m2.atoms ⊆ T.m3.atoms := by
  intro a ha; rw [m3_atoms]; exact Finset.mem_insert_of_mem ha


/-- The set from the first `β`-cut. -/
noncomputable def S0 : Finset V := T.m1.atoms.filter fun a => T.m1.SameComponent a (T.f 0)


/-- The set from the second `β`-cut. -/
noncomputable def S1 : Finset V := T.m2.atoms.filter fun a => T.m2.SameComponent a (T.f 1)

theorem S0_sub : ∀ a ∈ T.S0, a ∈ T.m1.atoms := fun a ha => (Finset.mem_filter.mp ha).1
theorem S1_sub : ∀ a ∈ T.S1, a ∈ T.m2.atoms := fun a ha => (Finset.mem_filter.mp ha).1

theorem t_nmem_S0 (hβ : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) (j : Fin 3) : T.t j ∉ T.S0 := by
  intro h
  have h1 := (Finset.mem_filter.mp h).2
  exact hβ (Relation.EqvGen.trans _ _ _ (T.sc_t_m1 0 j) h1)

theorem t_nmem_S1 (hβ : ¬ T.m2.SameComponent (T.t 1) (T.f 1)) (j : Fin 3) : T.t j ∉ T.S1 := by
  intro h
  have h1 := (Finset.mem_filter.mp h).2
  exact hβ (Relation.EqvGen.trans _ _ _ (T.sc_t_m2 1 j) h1)

theorem S0_closed (hβ : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) : IsClosedSet T.m3 T.S0 := by
  have h1 : IsClosedSet T.m1 T.S0 := isClosedSet_comp T.m1 (T.f 0)
  have h2 : IsClosedSet T.m2 T.S0 :=
    isClosedSet_cut h1 T.S0_sub (T.t_nmem_S0 hβ 1) T.f_fresh_m1
  exact isClosedSet_cut h2 (fun a ha => T.m1_atoms_sub_m2 (T.S0_sub a ha)) (T.t_nmem_S0 hβ 2) T.f_fresh_m2

theorem S1_closed (hβ : ¬ T.m2.SameComponent (T.t 1) (T.f 1)) : IsClosedSet T.m3 T.S1 :=
  isClosedSet_cut (isClosedSet_comp T.m2 (T.f 1)) T.S1_sub (T.t_nmem_S1 hβ 2) T.f_fresh_m2

theorem S0_sub3 : ∀ a ∈ T.S0, a ∈ T.m3.atoms := fun a ha =>
  T.m2_atoms_sub_m3 (T.m1_atoms_sub_m2 (T.S0_sub a ha))
theorem S1_sub3 : ∀ a ∈ T.S1, a ∈ T.m3.atoms := fun a ha => T.m2_atoms_sub_m3 (T.S1_sub a ha)

theorem f_mem_S0_iff (j : Fin 3) : T.f j ∈ T.S0 ↔ j = 0 := by
  constructor
  · intro h
    have := T.S0_sub _ h
    by_contra hj
    rw [m1_atoms, Finset.mem_insert] at this
    rcases this with h1 | h1
    · exact hj (T.f_inj h1)
    · exact T.f_fresh j h1
  · rintro rfl
    exact Finset.mem_filter.mpr ⟨by rw [m1_atoms]; exact Finset.mem_insert_self _ _, Relation.EqvGen.refl _⟩

theorem f1_mem_S1 : T.f 1 ∈ T.S1 :=
  Finset.mem_filter.mpr ⟨by rw [m2_atoms]; exact Finset.mem_insert_self _ _, Relation.EqvGen.refl _⟩

theorem f2_nmem_S1 : T.f 2 ∉ T.S1 := fun h => T.f_fresh_m2 (T.S1_sub _ h)

end TriData
end WaveTurbulence.FinalCount
