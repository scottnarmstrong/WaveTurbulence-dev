/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5VineF
public import WaveTurbulence.Foundations.FinalCount.C5Fold
import Mathlib.Tactic

/-! # Prop 9.6, case (5): `M₀` is a vine (II) when its reduction is a half-closed vine (II) -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bb_zero_of_not_mem (M : Molecule V D) {p : V} (hp : p ∉ M.atoms) (q : V) : M.bondsBetween p q = 0 := by
  by_contra h
  exact hp (mem_atoms_of_bondsBetween_pos (a := q) (by rw [Degen.bondsBetween_comm]; omega))

theorem multiset_identity (M : Molecule V D) {D' : Type*} [Fintype D'] [DecidableEq D'] (P : Molecule V D') (a b c d u₁ u₂ : V)
    (hid : ∀ p q : V, M.bondsBetween p q + (if s(d, c) = s(p, q) then 1 else 0) =
      P.bondsBetween p q + (if s(c, b) = s(p, q) then 1 else 0) + (if s(b, d) = s(p, q) then 1 else 0) +
      (if s(u₁, a) = s(p, q) then 1 else 0) + (if s(a, u₂) = s(p, q) then 1 else 0)) :
    M.groupBonds M.atoms + {s(d, c)} =
      P.groupBonds P.atoms + ({s(c, b)} + {s(b, d)} + {s(u₁, a)} + {s(a, u₂)}) := by
  classical
  refine Multiset.ext.mpr fun e => ?_
  induction e using Sym2.ind with
  | _ p q =>
    simp only [Multiset.count_add, Multiset.count_singleton, count_groupBonds_atoms]
    have := hid p q
    simp only [eq_comm (a := s(p, q))]
    omega


theorem Q_eq_J (k fc fd fu1 fu2 : ℕ) (h1 : s(fd, fc) = s(2, 3))
    (h2 : (fu1 = labA k k ∧ fu2 = labB k k) ∨ (fu1 = labB k k ∧ fu2 = labA k k)) :
    ({s(fc, 0)} + {s(0, fd)} + {s(fu1, 1)} + {s(1, fu2)} : Multiset (Sym2 ℕ)) = jointBonds k := by
  have h1' : (fd = 2 ∧ fc = 3) ∨ (fd = 3 ∧ fc = 2) := by
    rcases Sym2.eq_iff.mp h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr ⟨a, b⟩
  unfold jointBonds
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
  rcases h1' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [Sym2.eq_swap (a := (3 : ℕ)) (b := 0), Sym2.eq_swap (a := (2 : ℕ)) (b := 0), Sym2.eq_swap (a := (1 : ℕ))] <;> abel_nf

end
end WaveTurbulence.FinalCountG8
