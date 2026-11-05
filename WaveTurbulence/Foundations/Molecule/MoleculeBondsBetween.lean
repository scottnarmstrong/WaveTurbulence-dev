/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeConnectedBlocks
import Mathlib.Tactic

/-! # Joint-to-joint bond counts from actual half-edge incidences -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

theorem bondsBetween_symm (a b : V) : M.bondsBetween a b = M.bondsBetween b a := by
  unfold Molecule.bondsBetween
  rw [Sym2.eq_swap (a := a) (b := b)]

/-- For distinct endpoints, each actual bond has exactly one dart at the
first endpoint, irrespective of its direction. -/
theorem bondsBetween_eq_card_darts {a b : V} (hne : a ≠ b) :
    M.bondsBetween a b = ((M.dartsAt a).filter (fun x => M.atom (M.mate x) = b)).card := by
  let F : D → D := fun x => if M.atom x = a then x else M.mate x
  apply Finset.card_bij (fun x _hx => F x)
  · intro x hx
    obtain ⟨hxout,hends⟩ := Finset.mem_filter.mp hx
    have he : (M.atom x = a ∧ M.atom (M.mate x) = b) ∨
        (M.atom x = b ∧ M.atom (M.mate x) = a) := Sym2.eq_iff.mp hends
    rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Finset.mem_filter.mpr ⟨(mem_dartsAt _ _ _).mpr (by simp only [F,ha,ite_true]),
        by simp only [F,ha,ite_true,hb]⟩
    · have hxa : M.atom x ≠ a := by rw [ha]; exact Ne.symm hne
      exact Finset.mem_filter.mpr ⟨(mem_dartsAt _ _ _).mpr (by simp only [F,hxa,ite_false,hb]),
        by simp [F,ha,Ne.symm hne,M.mate_mate]⟩
  · intro x hx y hy he
    have hxo : M.out x = true := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hyo : M.out y = true := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    dsimp only [F] at he
    split at he <;> split at he
    · exact he
    · have hh := congrArg M.out he
      rw [hxo,M.out_mate,hyo] at hh
      cases hh
    · have hh := congrArg M.out he
      rw [M.out_mate,hxo,hyo] at hh
      cases hh
    · exact mate_injective M he
  · intro y hy
    obtain ⟨hyv,hyb⟩ := Finset.mem_filter.mp hy
    have hya := (mem_dartsAt M a y).mp hyv
    cases hyo : M.out y
    · refine ⟨M.mate y,Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [M.out_mate,hyo]; rfl⟩
      · change s(M.atom (M.mate y),M.atom (M.mate (M.mate y))) = s(a,b)
        rw [M.mate_mate,hya,hyb]
        exact Sym2.eq_swap
      · dsimp only [F]
        have hna : M.atom (M.mate y) ≠ a := by rw [hyb]; exact Ne.symm hne
        rw [ite_eq_right hna,M.mate_mate]
    · refine ⟨y,Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hyo⟩
      · change s(M.atom y,M.atom (M.mate y)) = s(a,b)
        rw [hya,hyb]
      · dsimp only [F]
        rw [ite_eq_left hya]

/-- When there is no loop at a joint, its internal degree in the two-joint
intersection is exactly the actual bond multiplicity sigma. -/
theorem degIn_pair_eq_bondsBetween {a b : V} (hne : a ≠ b)
    (hloop : ∀ x, M.atom x = a → M.atom (M.mate x) ≠ a) :
    M.degIn {a,b} a = M.bondsBetween a b := by
  rw [bondsBetween_eq_card_darts M hne]
  unfold Molecule.degIn
  congr 1
  ext x
  simp only [Finset.mem_filter,Molecule.InGroup,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hx,ha,hm⟩
    have hxa := (mem_dartsAt M a x).mp hx
    exact ⟨hx,hm.resolve_left (hloop x hxa)⟩
  · rintro ⟨hx,hm⟩
    exact ⟨hx,Or.inl ((mem_dartsAt M a x).mp hx),Or.inr hm⟩

/-- The source bound sigma <=2 for an actual block follows directly from
its joint degree, with no connectedness premise. -/
theorem block_sigma_le_two {S : Finset V} {a b : V} (hB : M.IsBlock S a b) : M.sigma a b ≤ 2 := by
  rw [Molecule.sigma,bondsBetween_eq_card_darts M hB.2.2.2.1]
  have hsub : (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) ⊆
      (M.dartsAt a).filter (M.InGroup S) := by
    intro x hx
    obtain ⟨hxv,hxm⟩ := Finset.mem_filter.mp hx
    have ha := (mem_dartsAt M a x).mp hxv
    exact Finset.mem_filter.mpr ⟨hxv,ha.symm ▸ hB.2.1,hxm.symm ▸ hB.2.2.1⟩
  have hc := Finset.card_le_card hsub
  have hd := (block_joint_degrees M hB).1
  exact hc.trans (le_of_eq hd)

end WaveTurbulence.Mole
