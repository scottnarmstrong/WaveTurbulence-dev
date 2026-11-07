/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairCircuit
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderGapPropagation
import Mathlib.Tactic

/-! # Actual two-rung incidence stars for source operation (b) -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem card_triple {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x,y,z} : Finset D).card = 3 := by
  have hx : x ∉ ({y,z} : Finset D) := by simp only [mem_insert,mem_singleton]; tauto
  have hy : y ∉ ({z} : Finset D) := by simpa only [mem_singleton] using hyz
  rw [card_insert_of_notMem hx,card_insert_of_notMem hy,card_singleton]

/-- Three distinct known incidences exhaust a degree-three atom. -/
theorem dartsAt_eq_triple_of_degree_three (M : Molecule V D) {a : V}
    (hdeg : M.deg a = 3) {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : M.atom x = a) (hy : M.atom y = a) (hz : M.atom z = a) :
    M.dartsAt a = {x,y,z} := by
  have hsub : ({x,y,z} : Finset D) ⊆ M.dartsAt a := by
    intro t ht
    simp only [mem_insert,mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact (Mole.mem_dartsAt M _ _).mpr hx
    · exact (Mole.mem_dartsAt M _ _).mpr hy
    · exact (Mole.mem_dartsAt M _ _).mpr hz
  apply (eq_of_subset_of_card_le hsub _).symm
  rw [card_triple hxy hxz hyz]
  exact hdeg.le

/-- At a degree-four atom, three distinct known incidences leave exactly
one actual extra dart, chosen independently of all decorations. -/
theorem exists_extra_dart_of_degree_four (M : Molecule V D) {a : V}
    (hdeg : M.deg a = 4) {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : M.atom x = a) (hy : M.atom y = a) (hz : M.atom z = a) :
    ∃ t : D, t ∉ ({x,y,z} : Finset D) ∧ M.atom t = a ∧ M.dartsAt a = {x,y,z,t} := by
  classical
  let T : Finset D := {x,y,z}
  have hsub : T ⊆ M.dartsAt a := by
    intro t ht
    simp only [T,mem_insert,mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact (Mole.mem_dartsAt M _ _).mpr hx
    · exact (Mole.mem_dartsAt M _ _).mpr hy
    · exact (Mole.mem_dartsAt M _ _).mpr hz
  have hcard : (M.dartsAt a \ T).card = 1 := by
    have hh := card_sdiff_add_card_eq_card hsub
    have ht : T.card = 3 := card_triple hxy hxz hyz
    change (M.dartsAt a \ T).card + T.card = M.deg a at hh
    omega
  obtain ⟨t,ht⟩ := card_eq_one.mp hcard
  have htmem : t ∈ M.dartsAt a \ T := by rw [ht]; exact mem_singleton_self _
  obtain ⟨hta,htT⟩ := mem_sdiff.mp htmem
  refine ⟨t,htT,(Mole.mem_dartsAt M _ _).mp hta,?_⟩
  ext w
  constructor
  · intro hw
    by_cases hwT : w ∈ T
    · simp only [T,mem_insert,mem_singleton] at hwT ⊢
      tauto
    · have hwt : w = t := by
        have hh : w ∈ M.dartsAt a \ T := mem_sdiff.mpr ⟨hw,hwT⟩
        rw [ht] at hh
        exact mem_singleton.mp hh
      simp only [hwt,mem_insert,mem_singleton] <;> tauto
  · intro hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hsub (by simp [T])
    · exact hsub (by simp [T])
    · exact hsub (by simp [T])
    · exact hta

/-- Select the actual two rung darts and the two opposite single rails.
The first degree-three star is exhausted; the second star is exhausted
at degree three or has exactly one structural extra dart at degree four. -/
theorem exists_source_cell_rung_stars (M : Molecule V D)
    {u v : Fin 2 → V} (hL : SourceLadder M u v) (hdeg : M.deg (u 0) = 3) :
    ∃ x y r s : D,
      x ≠ y ∧
      (M.atom x = u 0 ∧ M.atom (M.mate x) = v 0) ∧
      (M.atom y = u 0 ∧ M.atom (M.mate y) = v 0) ∧
      neighborDarts M (u 0) (v 0) = {x,y} ∧
      (M.atom r = u 0 ∧ M.atom (M.mate r) = u 1) ∧
      (M.atom s = v 0 ∧ M.atom (M.mate s) = v 1) ∧
      M.out s = !M.out r ∧
      x ≠ r ∧ y ≠ r ∧ M.mate x ≠ M.mate y ∧ M.mate x ≠ s ∧ M.mate y ≠ s ∧
      M.dartsAt (u 0) = {x,y,r} ∧
      (M.deg (v 0) = 3 → M.dartsAt (v 0) = {M.mate x,M.mate y,s}) ∧
      (M.deg (v 0) = 4 → ∃ t : D, t ∉ ({M.mate x,M.mate y,s} : Finset D) ∧
        M.atom t = v 0 ∧ M.dartsAt (v 0) = {M.mate x,M.mate y,s,t}) := by
  classical
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp hL.2.1
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hrung : (neighborDarts M (u 0) (v 0)).card = 2 := by
    rw [card_neighborDarts M (huv 0 0)]
    exact hL.2.2.2.1 0
  obtain ⟨x,y,hxy,hR⟩ := card_eq_two.mp hrung
  have hxmem : x ∈ neighborDarts M (u 0) (v 0) := by rw [hR]; exact mem_insert_self _ _
  have hymem : y ∈ neighborDarts M (u 0) (v 0) := by rw [hR]; exact mem_insert_of_mem (mem_singleton_self _)
  have hx := (mem_neighborDarts M _ _ x).mp hxmem
  have hy := (mem_neighborDarts M _ _ y).mp hymem
  have hr1 : M.bondsBetween (u 0) (u 1) = 1 := (hL.2.2.2.2 0).1
  have hs1 : M.bondsBetween (v 0) (v 1) = 1 := (hL.2.2.2.2 0).2.1
  obtain ⟨r,hr,hrm⟩ := adj_of_bondsBetween_pos M (hu.ne h01) (by omega)
  obtain ⟨s,hs,hsm⟩ := adj_of_bondsBetween_pos M (hv.ne h01) (by omega)
  have hxr : x ≠ r := by
    intro h
    have hh := congrArg (fun z => M.atom (M.mate z)) h
    exact (huv 1 0).symm (hx.2.symm.trans (hh.trans hrm))
  have hyr : y ≠ r := by
    intro h
    have hh := congrArg (fun z => M.atom (M.mate z)) h
    exact (huv 1 0).symm (hy.2.symm.trans (hh.trans hrm))
  have hmxy : M.mate x ≠ M.mate y := fun h => hxy (Mole.mate_injective M h)
  have hmxs : M.mate x ≠ s := by
    intro h
    have hh := congrArg (fun z => M.atom (M.mate z)) h
    rw [M.mate_mate,hx.1,hsm] at hh
    exact huv 0 1 hh
  have hmys : M.mate y ≠ s := by
    intro h
    have hh := congrArg (fun z => M.atom (M.mate z)) h
    rw [M.mate_mate,hy.1,hsm] at hh
    exact huv 0 1 hh
  have hout : M.out s = !M.out r := rail_out_opposite M (hu.ne h01) (hv.ne h01) hr1 hs1
    (hL.2.2.2.2 0).2.2 ⟨hr,hrm⟩ ⟨hs,hsm⟩
  refine ⟨x,y,r,s,hxy,hx,hy,hR,⟨hr,hrm⟩,⟨hs,hsm⟩,hout,hxr,hyr,hmxy,hmxs,hmys,
    dartsAt_eq_triple_of_degree_three M hdeg hxy hxr hyr hx.1 hy.1 hr,?_,?_⟩
  · intro h3
    exact dartsAt_eq_triple_of_degree_three M h3 hmxy hmxs hmys hx.2 hy.2 hs
  · intro h4
    exact exists_extra_dart_of_degree_four M h4 hmxy hmxs hmys hx.2 hy.2 hs

/-- The actual operation-(b) pair supplies all these stars internally from
its affected cell, with no assumed incidence enumeration or equations. -/
theorem exists_double_pair_stars (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (hdeg : M.deg a = 3) (hdouble : M.bondsBetween a b = 2)
    {S : Finset V} (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b}) :
    ∃ (u v : Fin 2 → V) (x y r s : D), SourceLadder M u v ∧
      Molecule.ladderAtoms u v = S ∧ u 0 = a ∧ v 0 = b ∧
      x ≠ y ∧ (M.atom x = a ∧ M.atom (M.mate x) = b) ∧
      (M.atom y = a ∧ M.atom (M.mate y) = b) ∧
      (M.atom r = a ∧ M.atom (M.mate r) = u 1) ∧
      (M.atom s = b ∧ M.atom (M.mate s) = v 1) ∧ M.out s = !M.out r ∧
      x ≠ r ∧ y ≠ r ∧ M.mate x ≠ M.mate y ∧ M.mate x ≠ s ∧ M.mate y ≠ s ∧
      M.dartsAt a = {x,y,r} ∧
      (M.deg b = 3 → M.dartsAt b = {M.mate x,M.mate y,s}) ∧
      (M.deg b = 4 → ∃ t : D, t ∉ ({M.mate x,M.mate y,s} : Finset D) ∧
        M.atom t = b ∧ M.dartsAt b = {M.mate x,M.mate y,s,t}) := by
  obtain ⟨u,v,hL,hUS,hu0,hv0⟩ := exists_double_cell_rung_representation M hM hab hdouble hS hmeet
  obtain ⟨x,y,r,s,hxy,hx,hy,_hR,hr,hs,hout,hxr,hyr,hmxy,hmxs,hmys,hA,hB3,hB4⟩ :=
    exists_source_cell_rung_stars M hL (by rw [hu0]; exact hdeg)
  refine ⟨u,v,x,y,r,s,hL,hUS,hu0,hv0,?_⟩
  simpa only [hu0,hv0] using
    (show x ≠ y ∧ (M.atom x = u 0 ∧ M.atom (M.mate x) = v 0) ∧
      (M.atom y = u 0 ∧ M.atom (M.mate y) = v 0) ∧
      (M.atom r = u 0 ∧ M.atom (M.mate r) = u 1) ∧
      (M.atom s = v 0 ∧ M.atom (M.mate s) = v 1) ∧ M.out s = !M.out r ∧
      x ≠ r ∧ y ≠ r ∧ M.mate x ≠ M.mate y ∧ M.mate x ≠ s ∧ M.mate y ≠ s ∧
      M.dartsAt (u 0) = {x,y,r} ∧
      (M.deg (v 0) = 3 → M.dartsAt (v 0) = {M.mate x,M.mate y,s}) ∧
      (M.deg (v 0) = 4 → ∃ t : D, t ∉ ({M.mate x,M.mate y,s} : Finset D) ∧
        M.atom t = v 0 ∧ M.dartsAt (v 0) = {M.mate x,M.mate y,s,t}) from
      ⟨hxy,hx,hy,hr,hs,hout,hxr,hyr,hmxy,hmxs,hmys,hA,hB3,hB4⟩)


/-- Exact reindexing of a selected three-dart star. -/
theorem sum_dartsAt_triple {A : Type*} [AddCommMonoid A] (M : Molecule V D) (a : V)
    {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hstar : M.dartsAt a = {x,y,z}) (f : D → A) :
    (∑ t ∈ M.dartsAt a, f t) = f x + f y + f z := by
  have hx : x ∉ ({y,z} : Finset D) := by simp only [mem_insert,mem_singleton]; tauto
  have hy : y ∉ ({z} : Finset D) := by simpa only [mem_singleton] using hyz
  rw [hstar,sum_insert hx,sum_insert hy,sum_singleton]
  simp only [add_assoc]

/-- Exact reindexing of a selected three-dart star and its structural extra dart. -/
theorem sum_dartsAt_quadruple {A : Type*} [AddCommMonoid A] (M : Molecule V D) (a : V)
    {x y z t : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ht : t ∉ ({x,y,z} : Finset D)) (hstar : M.dartsAt a = {x,y,z,t}) (f : D → A) :
    (∑ q ∈ M.dartsAt a, f q) = f x + f y + f z + f t := by
  have he : ({x,y,z,t} : Finset D) = insert t {x,y,z} := by
    ext q
    simp only [mem_insert,mem_singleton]
    tauto
  rw [hstar,he,sum_insert ht]
  have hs : (∑ q ∈ ({x,y,z} : Finset D), f q) = f x+f y+f z := by
    have hx : x ∉ ({y,z} : Finset D) := by simp only [mem_insert,mem_singleton]; tauto
    have hy : y ∉ ({z} : Finset D) := by simpa only [mem_singleton] using hyz
    rw [sum_insert hx,sum_insert hy,sum_singleton]
    simp only [add_assoc]
  rw [hs]
  ac_rfl

/-- The actual momentum equation at a three-incidence star, without any
source-equation premise or charge restriction. -/
theorem momentum_of_dartsAt_triple (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a : V} (ha : a ∈ M.atoms) {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hstar : M.dartsAt a = {x,y,z}) {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) :
    M.dartSign x • latticePoint L (κ x) + M.dartSign y • latticePoint L (κ y) +
      M.dartSign z • latticePoint L (κ z) = c a := by
  have hh := hd.2 a ha
  rw [sum_dartsAt_triple M a hxy hxz hyz hstar] at hh
  simpa only [Molecule.kvec,zero_add] using hh

theorem momentum_of_dartsAt_quadruple (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a : V} (ha : a ∈ M.atoms) {x y z t : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ht : t ∉ ({x,y,z} : Finset D)) (hstar : M.dartsAt a = {x,y,z,t})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ) :
    M.dartSign x • latticePoint L (κ x) + M.dartSign y • latticePoint L (κ y) +
      M.dartSign z • latticePoint L (κ z) + M.dartSign t • latticePoint L (κ t) = c a := by
  have hh := hd.2 a ha
  rw [sum_dartsAt_quadruple M a hxy hxz hyz ht hstar] at hh
  simpa only [Molecule.kvec,zero_add] using hh

theorem energy_of_dartsAt_triple (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {a : V} (ha : a ∈ M.atoms) {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hstar : M.dartsAt a = {x,y,z}) {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |M.dartSign x * ‖latticePoint L (κ x)‖^2 + M.dartSign y * ‖latticePoint L (κ y)‖^2 +
      M.dartSign z * ‖latticePoint L (κ z)‖^2 - β a| ≤ δ⁻¹ * L^(-2*γ) := by
  have hh := hr.1 a ha
  unfold Molecule.Gamma at hh
  rw [sum_dartsAt_triple M a hxy hxz hyz hstar] at hh
  simpa only [Molecule.kvec,zero_add] using hh

theorem energy_of_dartsAt_quadruple (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {a : V} (ha : a ∈ M.atoms) {x y z t : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ht : t ∉ ({x,y,z} : Finset D)) (hstar : M.dartsAt a = {x,y,z,t})
    {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |M.dartSign x * ‖latticePoint L (κ x)‖^2 + M.dartSign y * ‖latticePoint L (κ y)‖^2 +
      M.dartSign z * ‖latticePoint L (κ z)‖^2 + M.dartSign t * ‖latticePoint L (κ t)‖^2 - β a| ≤ δ⁻¹ * L^(-2*γ) := by
  have hh := hr.1 a ha
  unfold Molecule.Gamma at hh
  rw [sum_dartsAt_quadruple M a hxy hxz hyz ht hstar] at hh
  simpa only [Molecule.kvec,zero_add] using hh

end WaveTurbulence.MoleProp
