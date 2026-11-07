/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriKept
/-! Triangles, part 3 (FINALCOUNT-G2): the darts at the atoms of the final cut molecule. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem m3_dartsAt_other {a : V} (ha : a ∈ M.atoms) (hP : T.TP a) : T.m3.dartsAt a = M.dartsAt a := by
  ext x
  rw [mem_dartsAt, mem_dartsAt]
  by_cases hx : ∃ j, M.atom x = T.t j
  · obtain ⟨j, hj⟩ := hx
    constructor
    · intro h
      by_cases hxj : x = T.a j ∨ x = T.b j
      · rw [T.m3_atom_tri x j hxj] at h; exact absurd h.symm (hP j)
      · push Not at hxj
        rw [T.m3_atom_moved x j hj hxj.1 hxj.2] at h
        exact absurd (h ▸ ha) (T.f_fresh j)
    · intro h; exact absurd (hj.symm.trans h).symm (hP j)
  · push Not at hx
    rw [T.m3_atom_other x hx]

theorem m3_dartsAt_f (j : Fin 3) :
    T.m3.dartsAt (T.f j) = (M.dartsAt (T.t j)).filter (fun x => x ≠ T.a j ∧ x ≠ T.b j) := by
  ext x
  rw [mem_dartsAt, Finset.mem_filter, mem_dartsAt]
  constructor
  · intro h
    by_cases hx : ∃ i, M.atom x = T.t i
    · obtain ⟨i, hi⟩ := hx
      by_cases hxi : x = T.a i ∨ x = T.b i
      · rw [T.m3_atom_tri x i hxi] at h; exact absurd h.symm (T.f_ne_t j i)
      · push Not at hxi
        rw [T.m3_atom_moved x i hi hxi.1 hxi.2] at h
        have : i = j := T.f_inj h
        subst this
        exact ⟨hi, hxi⟩
    · push Not at hx
      rw [T.m3_atom_other x hx] at h
      exact absurd (h ▸ M.atom_mem x) (T.f_fresh j)
  · rintro ⟨h, h1, h2⟩
    exact T.m3_atom_moved x j h h1 h2

theorem sum_t {E : Type*} [AddCommMonoid E] (j : Fin 3) (g : D → E) :
    ∑ x ∈ M.dartsAt (T.t j), g x = ∑ x ∈ T.m3.dartsAt (T.f j), g x + (g (T.a j) + g (T.b j)) := by
  have hab : T.a j ≠ T.b j := by
    intro e; have h1 := T.out_a j; have h2 := T.out_b j; rw [e] at h1; rw [h1] at h2; exact Bool.false_ne_true h2
  have hs : M.dartsAt (T.t j) = T.m3.dartsAt (T.f j) ∪ {T.a j, T.b j} := by
    ext x
    rw [T.m3_dartsAt_f, Finset.mem_union, Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      by_cases hx : x = T.a j ∨ x = T.b j
      · exact Or.inr hx
      · push Not at hx; exact Or.inl ⟨h, hx⟩
    · rintro (h | h)
      · exact h.1
      · rw [mem_dartsAt]; rcases h with rfl | rfl; exacts [T.atom_a j, T.atom_b j]
  rw [hs, Finset.sum_union, Finset.sum_pair hab]
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [T.m3_dartsAt_f, Finset.mem_filter] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with rfl | rfl
  exacts [hx.2.1 rfl, hx.2.2 rfl]

theorem kept_sum {E : Type*} [AddCommMonoid E] {a : V} (ha : T.TP a) (g : D → E) :
    ∑ x ∈ T.kept.dartsAt a, g x.1 = ∑ x ∈ T.m3.dartsAt a, g x := by
  unfold kept
  rw [restrictP_dartsAt T.m3 T.TP T.pclosed ha]
  rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem]
  intro x hx
  rw [mem_dartsAt] at hx
  rw [hx]; exact ha

end TriData
end WaveTurbulence.FinalCount
