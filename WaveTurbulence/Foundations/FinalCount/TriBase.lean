/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RemovalDev
/-! Triangles (DH23 §9.3 Step 2, L1777--L1779), part 1 (FINALCOUNT-G2): the data of a triangle `v_1 v_2 v_3`
(indices `Fin 3`, `v_j = t j`), the three successive cuts `m1, m2, m3` (cut `v_1`, then `v_2`, then `v_3`, along
the darts `(a j, b j)` of the triangle bonds) and the atom function of the final cut molecule. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **A triangle in `M`** (DH23 L1777): atoms `t j` (`= v_{j+1}`), the bond `ℓ_j` of `b j` (outgoing at `t j`) and
`a (j+1)` (incoming at `t (j+1)`) joins them cyclically; `a j` is incoming and `b j` outgoing at `t j`; `f j` are the
fresh atoms created by the cuts. -/
structure TriData (M : Molecule V D) where
  t : Fin 3 → V
  f : Fin 3 → V
  a : Fin 3 → D
  b : Fin 3 → D
  t_mem : ∀ j, t j ∈ M.atoms
  t_inj : Function.Injective t
  f_fresh : ∀ j, f j ∉ M.atoms
  f_inj : Function.Injective f
  atom_a : ∀ j, M.atom (a j) = t j
  atom_b : ∀ j, M.atom (b j) = t j
  out_a : ∀ j, M.out (a j) = false
  out_b : ∀ j, M.out (b j) = true
  mate_b : ∀ j, M.mate (b j) = a (j + 1)

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem mate_a (j : Fin 3) : M.mate (T.a (j + 1)) = T.b j := by
  rw [← T.mate_b j, M.mate_mate]

theorem t_ne {i j : Fin 3} (h : i ≠ j) : T.t i ≠ T.t j := fun e => h (T.t_inj e)
theorem f_ne {i j : Fin 3} (h : i ≠ j) : T.f i ≠ T.f j := fun e => h (T.f_inj e)

theorem f_ne_t (i j : Fin 3) : T.f i ≠ T.t j := fun e => T.f_fresh i (e ▸ T.t_mem j)

theorem b_ne_mate_a (j : Fin 3) : T.b j ≠ M.mate (T.a j) := by
  intro e
  have h1 : M.atom (T.b j) = T.t j := T.atom_b j
  have h2 : M.mate (T.a j) = T.b (j - 1) := by
    have := T.mate_a (j - 1); simpa using this
  rw [h2] at e
  have h3 : T.t j = T.t (j - 1) := by rw [← T.atom_b j, e, T.atom_b]
  have h4 : j = j - 1 := T.t_inj h3
  have hh : ∀ j : Fin 3, j ≠ j - 1 := by decide
  exact hh j h4

/-- The first cut: `v_1 = t 0` along `(a 0, b 0)`. -/
def m1 : Molecule V D := M.cut (T.t 0) (T.f 0) (T.a 0) (T.b 0)
/-- The second cut: `v_2 = t 1` along `(a 1, b 1)`. -/
def m2 : Molecule V D := T.m1.cut (T.t 1) (T.f 1) (T.a 1) (T.b 1)
/-- The third cut: `v_3 = t 2` along `(a 2, b 2)`. -/
def m3 : Molecule V D := T.m2.cut (T.t 2) (T.f 2) (T.a 2) (T.b 2)

theorem cd1 : M.IsCutData (T.t 0) (T.f 0) (T.a 0) (T.b 0) :=
  ⟨T.t_mem 0, T.f_fresh 0, T.atom_a 0, T.atom_b 0, T.b_ne_mate_a 0, T.out_a 0, T.out_b 0⟩

theorem m1_atom (x : D) : T.m1.atom x = if M.atom x = T.t 0 ∧ x ≠ T.a 0 ∧ x ≠ T.b 0 then T.f 0 else M.atom x := rfl
theorem m2_atom (x : D) : T.m2.atom x =
    if T.m1.atom x = T.t 1 ∧ x ≠ T.a 1 ∧ x ≠ T.b 1 then T.f 1 else T.m1.atom x := rfl
theorem m3_atom (x : D) : T.m3.atom x =
    if T.m2.atom x = T.t 2 ∧ x ≠ T.a 2 ∧ x ≠ T.b 2 then T.f 2 else T.m2.atom x := rfl

theorem m1_atoms : T.m1.atoms = insert (T.f 0) M.atoms := rfl
theorem m2_atoms : T.m2.atoms = insert (T.f 1) (insert (T.f 0) M.atoms) := rfl
theorem m3_atoms : T.m3.atoms = insert (T.f 2) (insert (T.f 1) (insert (T.f 0) M.atoms)) := rfl

theorem t_mem_m1 (j : Fin 3) : T.t j ∈ T.m1.atoms := by
  rw [m1_atoms]; exact Finset.mem_insert_of_mem (T.t_mem j)
theorem f_fresh_m1 : T.f 1 ∉ T.m1.atoms := by
  rw [m1_atoms, Finset.mem_insert]; rintro (h | h)
  · exact T.f_ne (by decide) h
  · exact T.f_fresh 1 h
theorem f_fresh_m2 : T.f 2 ∉ T.m2.atoms := by
  rw [m2_atoms, Finset.mem_insert, Finset.mem_insert]; rintro (h | h | h)
  · exact T.f_ne (by decide) h
  · exact T.f_ne (by decide) h
  · exact T.f_fresh 2 h
theorem t_mem_m2 (j : Fin 3) : T.t j ∈ T.m2.atoms := by
  rw [m2_atoms]; exact Finset.mem_insert_of_mem (T.t_mem_m1 j)

/-- The atom of a dart at the triangle atoms is unchanged for the triangle darts. -/
theorem m1_atom_tri (x : D) (j : Fin 3) (h : x = T.a j ∨ x = T.b j) : T.m1.atom x = T.t j := by
  rw [m1_atom]
  have hx : M.atom x = T.t j := by rcases h with rfl | rfl; exacts [T.atom_a j, T.atom_b j]
  split_ifs with hc
  · exfalso
    have : j = 0 := T.t_inj (hx.symm.trans hc.1)
    subst this
    rcases h with rfl | rfl
    exacts [hc.2.1 rfl, hc.2.2 rfl]
  · exact hx

theorem m2_atom_tri (x : D) (j : Fin 3) (h : x = T.a j ∨ x = T.b j) : T.m2.atom x = T.t j := by
  rw [m2_atom, T.m1_atom_tri x j h]
  split_ifs with hc
  · exfalso
    have : j = 1 := T.t_inj hc.1
    subst this
    rcases h with rfl | rfl
    exacts [hc.2.1 rfl, hc.2.2 rfl]
  · rfl

theorem m3_atom_tri (x : D) (j : Fin 3) (h : x = T.a j ∨ x = T.b j) : T.m3.atom x = T.t j := by
  rw [m3_atom, T.m2_atom_tri x j h]
  split_ifs with hc
  · exfalso
    have : j = 2 := T.t_inj hc.1
    subst this
    rcases h with rfl | rfl
    exacts [hc.2.1 rfl, hc.2.2 rfl]
  · rfl


theorem m3_atom_moved (x : D) (j : Fin 3) (h : M.atom x = T.t j) (h1 : x ≠ T.a j) (h2 : x ≠ T.b j) :
    T.m3.atom x = T.f j := by
  have n0 : ∀ i : Fin 3, i ≠ j → ¬ (M.atom x = T.t i) := fun i hi e => T.t_ne hi (e.symm.trans h)
  have ha : ∀ i : Fin 3, i ≠ j → x ≠ T.a i := fun i hi e => n0 i hi (e ▸ T.atom_a i)
  have hb : ∀ i : Fin 3, i ≠ j → x ≠ T.b i := fun i hi e => n0 i hi (e ▸ T.atom_b i)
  fin_cases j
  · simp only [Fin.zero_eta] at h h1 h2 ⊢
    have e1 : T.m1.atom x = T.f 0 := by rw [m1_atom]; exact if_pos ⟨h, h1, h2⟩
    have e2 : T.m2.atom x = T.f 0 := by
      rw [m2_atom, e1]; exact if_neg (fun hc => T.f_ne_t 0 1 hc.1)
    rw [m3_atom, e2]; exact if_neg (fun hc => T.f_ne_t 0 2 hc.1)
  · have h' : M.atom x = T.t 1 := h
    have h1' : x ≠ T.a 1 := h1
    have h2' : x ≠ T.b 1 := h2
    have e1 : T.m1.atom x = T.t 1 := by
      rw [m1_atom, if_neg (fun hc => n0 0 (by decide) hc.1)]; exact h'
    have e2 : T.m2.atom x = T.f 1 := by rw [m2_atom, e1]; exact if_pos ⟨rfl, h1', h2'⟩
    rw [m3_atom, e2]; exact if_neg (fun hc => T.f_ne_t 1 2 hc.1)
  · have h' : M.atom x = T.t 2 := h
    have h1' : x ≠ T.a 2 := h1
    have h2' : x ≠ T.b 2 := h2
    have e1 : T.m1.atom x = T.t 2 := by
      rw [m1_atom, if_neg (fun hc => n0 0 (by decide) hc.1)]; exact h'
    have e2 : T.m2.atom x = T.t 2 := by
      rw [m2_atom, e1, if_neg (fun hc => T.t_ne (i := 1) (j := 2) (by decide) hc.1.symm)]
    rw [m3_atom, e2]; exact if_pos ⟨rfl, h1', h2'⟩

theorem m3_atom_other (x : D) (h : ∀ j, M.atom x ≠ T.t j) : T.m3.atom x = M.atom x := by
  have e1 : T.m1.atom x = M.atom x := by rw [m1_atom]; exact if_neg (fun hc => h 0 hc.1)
  have e2 : T.m2.atom x = M.atom x := by rw [m2_atom, e1]; exact if_neg (fun hc => h 1 hc.1)
  rw [m3_atom, e2]; exact if_neg (fun hc => h 2 hc.1)

theorem t_ne_of_eq {x : D} {i j : Fin 3} (h : T.t i = T.t j) (hc : x ≠ T.a j ∧ x ≠ T.b j)
    (hxi : x = T.a i ∨ x = T.b i) : False := by
  have : i = j := T.t_inj h
  subst this
  rcases hxi with rfl | rfl
  exacts [hc.1 rfl, hc.2 rfl]

/-- The darts at `t j` in the final cut molecule are exactly `a j` and `b j`. -/
theorem m3_atom_eq_t (x : D) (j : Fin 3) : T.m3.atom x = T.t j ↔ (x = T.a j ∨ x = T.b j) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    by_cases hx : ∃ i, M.atom x = T.t i
    · obtain ⟨i, hi⟩ := hx
      by_cases hxi : x = T.a i ∨ x = T.b i
      · have := T.m3_atom_tri x i hxi
        exact T.t_ne_of_eq (this.symm.trans h) hc hxi
      · push Not at hxi
        rw [T.m3_atom_moved x i hi hxi.1 hxi.2] at h
        exact T.f_ne_t i j h
    · push Not at hx
      rw [T.m3_atom_other x hx] at h
      exact hx j h
  · intro h; exact T.m3_atom_tri x j h

end TriData
end WaveTurbulence.FinalCount
