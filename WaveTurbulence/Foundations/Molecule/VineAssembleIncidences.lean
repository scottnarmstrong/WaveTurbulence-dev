/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineClosedDoubleBlock
import Mathlib.Tactic

/-! # Four incidence rows assembled from doubled pairs and actual rail edges -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*}

/-- Two double pairs with distinct neighbors give four distinct actual darts. -/
@[expose] def FourIncidences.ofTwoPairs {M : Molecule V D} {x y z : V}
    (Ry : TwoIncidences M x y) (Rz : TwoIncidences M x z) (hyz : y ≠ z) :
    FourIncidences M x ![y,y,z,z] where
  dart := ![Ry.dart 0,Ry.dart 1,Rz.dart 0,Rz.dart 1]
  injective := by
    have hy01 : Ry.dart 0 ≠ Ry.dart 1 := by
      intro he
      have hh := Ry.injective he
      have hc := congrArg Fin.val hh
      norm_num at hc
    have hz01 : Rz.dart 0 ≠ Rz.dart 1 := by
      intro he
      have hh := Rz.injective he
      have hc := congrArg Fin.val hh
      norm_num at hc
    have hcross (i j : Fin 2) : Ry.dart i ≠ Rz.dart j := by
      intro he
      have hh := congrArg (fun d => M.atom (M.mate d)) he
      rw [Ry.neighbor_eq,Rz.neighbor_eq] at hh
      exact hyz hh
    intro i j he
    fin_cases i <;> fin_cases j
    · exact rfl
    · exact False.elim (hy01 he)
    · exact False.elim (hcross 0 0 he)
    · exact False.elim (hcross 0 1 he)
    · exact False.elim (hy01 he.symm)
    · exact rfl
    · exact False.elim (hcross 1 0 he)
    · exact False.elim (hcross 1 1 he)
    · exact False.elim (hcross 0 0 he.symm)
    · exact False.elim (hcross 1 0 he.symm)
    · exact rfl
    · exact False.elim (hz01 he)
    · exact False.elim (hcross 0 1 he.symm)
    · exact False.elim (hcross 1 1 he.symm)
    · exact False.elim (hz01 he.symm)
    · exact rfl
  atom_eq := by
    intro i
    fin_cases i
    · exact Ry.atom_eq 0
    · exact Ry.atom_eq 1
    · exact Rz.atom_eq 0
    · exact Rz.atom_eq 1
  neighbor_eq := by
    intro i
    fin_cases i
    · exact Ry.neighbor_eq 0
    · exact Ry.neighbor_eq 1
    · exact Rz.neighbor_eq 0
    · exact Rz.neighbor_eq 1

/-- A double pair and two rail edges with distinct neighboring atoms
supply a full four-dart row. The existential rail darts are extracted from
actual adjacency, not assumed as additional incidence witnesses. -/
theorem fourIncidences_of_double_and_edges {M : Molecule V D} {x y p q : V}
    (R : TwoIncidences M x y) (hp : M.Adj x p) (hq : M.Adj x q)
    (hyp : y ≠ p) (hyq : y ≠ q) (hpq : p ≠ q) :
    Nonempty (FourIncidences M x ![y,y,p,q]) := by
  obtain ⟨dp,hdpx,hdpp⟩ := hp
  obtain ⟨dq,hdqx,hdqq⟩ := hq
  have h01 : R.dart 0 ≠ R.dart 1 := by
    intro he
    have hh := R.injective he
    have hc := congrArg Fin.val hh
    norm_num at hc
  have hpr (i : Fin 2) : R.dart i ≠ dp := by
    intro he
    have hh := congrArg (fun d => M.atom (M.mate d)) he
    rw [R.neighbor_eq,hdpp] at hh
    exact hyp hh
  have hqr (i : Fin 2) : R.dart i ≠ dq := by
    intro he
    have hh := congrArg (fun d => M.atom (M.mate d)) he
    rw [R.neighbor_eq,hdqq] at hh
    exact hyq hh
  have hpqd : dp ≠ dq := by
    intro he
    have hh := congrArg (fun d => M.atom (M.mate d)) he
    rw [hdpp,hdqq] at hh
    exact hpq hh
  refine ⟨⟨![R.dart 0,R.dart 1,dp,dq],?_,?_,?_⟩⟩
  · intro i j he
    fin_cases i <;> fin_cases j
    · exact rfl
    · exact False.elim (h01 he)
    · exact False.elim (hpr 0 he)
    · exact False.elim (hqr 0 he)
    · exact False.elim (h01 he.symm)
    · exact rfl
    · exact False.elim (hpr 1 he)
    · exact False.elim (hqr 1 he)
    · exact False.elim (hpr 0 he.symm)
    · exact False.elim (hpr 1 he.symm)
    · exact rfl
    · exact False.elim (hpqd he)
    · exact False.elim (hqr 0 he.symm)
    · exact False.elim (hqr 1 he.symm)
    · exact False.elim (hpqd he.symm)
    · exact rfl
  · intro i
    fin_cases i
    · exact R.atom_eq 0
    · exact R.atom_eq 1
    · exact hdpx
    · exact hdqx
  · intro i
    fin_cases i
    · exact R.neighbor_eq 0
    · exact R.neighbor_eq 1
    · exact hdpp
    · exact hdqq

end WaveTurbulence.Vine
