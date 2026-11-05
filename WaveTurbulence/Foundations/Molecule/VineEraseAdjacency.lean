/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDeletedBondMultiset
public import WaveTurbulence.Foundations.Molecule.VineDoublePairClosure
public import WaveTurbulence.Foundations.Molecule.VineGroupAdjacency
import Mathlib.Tactic

/-! # Surviving actual edges in a designated bond deletion -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- Any actual adjacency with a different unordered endpoint pair survives
the designated deletion. -/
theorem eraseBond_adj_of_pair_ne (M : Molecule V D) (e : D) {u v : V}
    (h : M.Adj u v) (hne : s(u,v) ≠ M.ends e) : (Mole.eraseBond M e).Adj u v := by
  obtain ⟨d,hd,hv⟩ := h
  have hdne : d ≠ e := by
    intro he
    subst d
    exact hne (by simp only [Molecule.ends,hd,hv])
  have hdm : d ≠ M.mate e := by
    intro he
    subst d
    have hh : M.ends e=s(v,u) := by
      simp only [Molecule.ends]
      rw [← hv,← hd,M.mate_mate]
    exact hne (Sym2.eq_swap.trans hh.symm)
  exact ⟨⟨d,hdne,hdm⟩,hd,hv⟩

omit [DecidableEq V] [Fintype D] in
/-- Deleting one actual occurrence of a double bond leaves its two atoms
adjacent. The representative e may have either direction. -/
theorem eraseBond_double_pair_adj (M : Molecule V D) (e : D) {x y : V}
    (R : TwoIncidences M x y) (hne : x ≠ y) (he : M.ends e=s(x,y)) :
    (Mole.eraseBond M e).Adj x y := by
  have hjoint : M.atom e ≠ M.atom (M.mate e) := by
    have hh := Sym2.eq_iff.mp he
    change (M.atom e=x ∧ M.atom (M.mate e)=y) ∨
      (M.atom e=y ∧ M.atom (M.mate e)=x) at hh
    rcases hh with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2]
    · exact hne
    · exact hne.symm
  have h01 : R.dart 0 ≠ R.dart 1 := fun hh => by
    have hx := R.injective hh
    have hv := congrArg Fin.val hx
    norm_num at hv
  by_cases h0e : R.dart 0=e
  · have h1e : R.dart 1 ≠ e := fun hh => h01 (h0e.trans hh.symm)
    have h1m : R.dart 1 ≠ M.mate e := by
      intro hh
      have ha := R.atom_eq 1
      rw [hh] at ha
      have hb := R.atom_eq 0
      rw [h0e] at hb
      exact hjoint (hb.trans ha.symm)
    exact ⟨⟨R.dart 1,h1e,h1m⟩,R.atom_eq 1,R.neighbor_eq 1⟩
  · by_cases h0m : R.dart 0=M.mate e
    · have h1m : R.dart 1 ≠ M.mate e := fun hh => h01 (h0m.trans hh.symm)
      have h1e : R.dart 1 ≠ e := by
        intro hh
        have ha := R.atom_eq 1
        rw [hh] at ha
        have hb := R.atom_eq 0
        rw [h0m] at hb
        exact hjoint (ha.trans hb.symm)
      exact ⟨⟨R.dart 1,h1e,h1m⟩,R.atom_eq 1,R.neighbor_eq 1⟩
    · exact ⟨⟨R.dart 0,h0e,h0m⟩,R.atom_eq 0,R.neighbor_eq 0⟩

end WaveTurbulence.Vine
