/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeSeparation
public import WaveTurbulence.Foundations.Molecule.Degen.Cut
public import WaveTurbulence.Foundations.FinalCount.Degen.EvenDegreeCuts
import Mathlib.Tactic

/-! # Actual cut handshaking for the preliminary degree-profile reduction -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Handshaking with the OLD boundary, including loops and repeated bonds. -/
theorem sum_degrees_eq_internal_add_boundary (M : Molecule V D) (S : Finset V) :
    ∑ a ∈ S, M.deg a = 2 * (M.groupBonds S).card + (boundaryDarts M S).card :=
  Degen.sum_degrees_cut M S

/-- A two-bond cut cannot separate the two exceptional degree-three atoms:
each side contains either both or neither. -/
theorem two_degree_three_same_side_of_boundary_two (M : Molecule V D)
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb3 : M.deg b = 3)
    (hrest : ∀ z ∈ M.atoms, z ≠ a → z ≠ b → M.deg z = 4)
    (S : Finset V) (hS : S ⊆ M.atoms) (hboundary : (boundaryDarts M S).card = 2) :
    a ∈ S ↔ b ∈ S := by
  have hsum := sum_degrees_eq_internal_add_boundary M S
  rw [hboundary] at hsum
  have hsingle (c d : V) (hc3 : M.deg c = 3) (hc : c ∈ S) (hd : d ∉ S)
      (hfull : ∀ z ∈ S, z ≠ c → M.deg z = 4) : False := by
    have he := add_sum_erase S (fun z => M.deg z) hc
    have hs : (∑ z ∈ S.erase c, M.deg z) = 4 * (S.erase c).card := by
      calc
        _ = ∑ _z ∈ S.erase c, (4 : ℕ) := by
          apply sum_congr rfl
          intro z hz
          exact hfull z (mem_erase.mp hz).2 (mem_erase.mp hz).1
        _ = _ := by simp [sum_const,nsmul_eq_mul,Nat.mul_comm]
    rw [hc3,hs] at he
    omega
  constructor
  · intro ha
    by_contra hb
    apply hsingle a b ha3 ha hb
    intro z hz hza
    exact hrest z (hS hz) hza (fun h => hb (h ▸ hz))
  · intro hb
    by_contra ha
    apply hsingle b a hb3 hb ha
    intro z hz hzb
    exact hrest z (hS hz) (fun h => ha (h ▸ hz)) hzb

/-- The actual internal star loses exactly its OLD crossing darts. -/
theorem degreeIn_add_boundaryAt (M : Molecule V D) (S : Finset V) {a : V} (ha : a ∈ S) :
    M.degIn S a + ((boundaryDarts M S).filter (fun x => M.atom x = a)).card = M.deg a := by
  classical
  have hh := card_filter_add_card_filter_not (s := M.dartsAt a)
    (fun x => M.atom (M.mate x) ∈ S)
  have hi : (M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ S) =
      (M.dartsAt a).filter (M.InGroup S) := by
    ext x
    simp only [mem_filter,Molecule.InGroup]
    constructor
    · intro hx
      exact ⟨hx.1,((Mole.mem_dartsAt M a x).mp hx.1).symm ▸ ha,hx.2⟩
    · intro hx
      exact ⟨hx.1,hx.2.2⟩
  have ho : (M.dartsAt a).filter (fun x => M.atom (M.mate x) ∉ S) =
      (boundaryDarts M S).filter (fun x => M.atom x = a) := by
    ext x
    simp only [mem_filter,boundaryDarts,mem_univ,true_and,Mole.mem_dartsAt]
    constructor
    · intro hx
      exact ⟨⟨hx.1.symm ▸ ha,hx.2⟩,hx.1⟩
    · intro hx
      exact ⟨hx.2,hx.1.2⟩
  rw [hi,ho] at hh
  exact hh

/-- One of the two actual old sides of a two-bond beta cut has no
exceptional degree-three atom and hence has old degree four throughout. -/
theorem exists_four_regular_side_of_two_boundary (M : Molecule V D)
    {a b v : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb3 : M.deg b = 3)
    (hrest : ∀ z ∈ M.atoms, z ≠ a → z ≠ b → M.deg z = 4)
    (U : Finset V) (hU : U ⊆ M.atoms) (hboundary : (boundaryDarts M U).card = 2) :
    (∀ z ∈ U, M.deg z = 4) ∨ (∀ z ∈ (M.atoms \ {v}) \ U, M.deg z = 4) := by
  have hiff := two_degree_three_same_side_of_boundary_two M hab ha3 hb3 hrest U hU hboundary
  by_cases haU : a ∈ U
  · right
    have hbU := hiff.mp haU
    intro z hz
    have hz' := mem_sdiff.mp hz
    have hza : z ≠ a := fun he => hz'.2 (he.symm ▸ haU)
    have hzb : z ≠ b := fun he => hz'.2 (he.symm ▸ hbU)
    exact hrest z (mem_sdiff.mp hz'.1).1 hza hzb
  · left
    have hbU : b ∉ U := fun hbU => haU (hiff.mpr hbU)
    intro z hz
    exact hrest z (hU hz) (fun he => haU (he ▸ hz)) (fun he => hbU (he ▸ hz))

/-- The two exceptional atoms contribute one unit each to the old degree
four deficit, on every actual atom subset. -/
theorem degree_sum_add_exceptional_card (M : Molecule V D)
    {a b : V} (ha3 : M.deg a = 3) (hb3 : M.deg b = 3)
    (hrest : ∀ z ∈ M.atoms, z ≠ a → z ≠ b → M.deg z = 4)
    (S : Finset V) (hS : S ⊆ M.atoms) :
    (∑ z ∈ S, M.deg z) + (S.filter (fun z => z = a ∨ z = b)).card = 4 * S.card := by
  classical
  calc
    _ = ∑ z ∈ S, (M.deg z + if z = a ∨ z = b then 1 else 0) := by
      rw [sum_add_distrib,sum_boole,Nat.cast_id]
    _ = ∑ _z ∈ S, (4 : ℕ) := by
      apply sum_congr rfl
      intro z hz
      by_cases hza : z = a
      · subst z
        simp [ha3]
      by_cases hzb : z = b
      · subst z
        simp [hb3]
      simp [hza,hzb,hrest z (hS hz) hza hzb]
    _ = _ := by simp [sum_const,Nat.mul_comm]

/-- Each side of a genuine initial bridge contains exactly one of the two
old degree-three atoms. -/
theorem exactly_one_degree_three_of_boundary_one (M : Molecule V D)
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb3 : M.deg b = 3)
    (hrest : ∀ z ∈ M.atoms, z ≠ a → z ≠ b → M.deg z = 4)
    (S : Finset V) (hS : S ⊆ M.atoms) (hboundary : (boundaryDarts M S).card = 1) :
    a ∈ S ↔ b ∉ S := by
  classical
  let A := S.filter (fun z => z = a ∨ z = b)
  have hdef := degree_sum_add_exceptional_card M ha3 hb3 hrest S hS
  have hsum := sum_degrees_eq_internal_add_boundary M S
  have hsub : A ⊆ {a,b} := by
    intro z hz
    exact mem_insert.mpr ((mem_filter.mp hz).2.imp id mem_singleton.mpr)
  have hle : A.card ≤ 2 := by
    have hh := card_le_card hsub
    rw [card_pair hab] at hh
    exact hh
  have hc : A.card = 1 := by
    change (∑ z ∈ S, M.deg z) + A.card = 4 * S.card at hdef
    rw [hboundary] at hsum
    omega
  have hnotboth (ha : a ∈ S) (hb : b ∈ S) : False := by
    have hs : {a,b} ⊆ A := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_filter.mpr ⟨ha,Or.inl rfl⟩
      · exact mem_filter.mpr ⟨hb,Or.inr rfl⟩
    have hh := card_le_card hs
    rw [card_pair hab,hc] at hh
    omega
  constructor
  · exact hnotboth
  · intro hb
    by_contra ha
    have he : A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hh := mem_filter.mp hz
      rcases hh.2 with rfl | rfl
      · exact ha hh.1
      · exact hb hh.1
    rw [he,card_empty] at hc
    omega

/-- Exact actual degree profile after selecting one bridge side. -/
theorem induced_degree_add_single_boundary (M : Molecule V D) (S : Finset V)
    {e : D} (hboundary : boundaryDarts M S = {e}) {a : V} (ha : a ∈ S) :
    (Mole.induced M S).deg a + (if M.atom e = a then 1 else 0) = M.deg a := by
  classical
  have hh := degreeIn_add_boundaryAt M S ha
  rw [hboundary] at hh
  by_cases h : M.atom e = a
  · simpa [Mole.induced_deg,filter_singleton,h] using hh
  · simpa [Mole.induced_deg,filter_singleton,h] using hh

/-- An actual even-degree molecule has no bridge: every bridge would
produce an odd singleton cut. -/
theorem bridgeless_of_even_degrees (M : Molecule V D)
    (heven : ∀ a ∈ M.atoms, Even (M.deg a)) : ∀ e, ¬ IsBridge M e := by
  intro e he
  have hn := boundary_card_ne_one_of_even_degrees M heven (bridgeSide M e) (bridgeSide_subset M e)
  apply hn
  rw [boundary_bridgeSide M e he,card_singleton]

end WaveTurbulence.MoleProp
