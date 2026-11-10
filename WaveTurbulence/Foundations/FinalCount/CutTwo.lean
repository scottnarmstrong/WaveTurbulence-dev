/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreGraph
import Mathlib.Tactic

/-! # Two exits at one atom, any directions (copy of MOLEPROP4-T `Pinch` without direction fields)

`Cut2 N`: `Y` is attached to the rest only through two darts `x ≠ y` ending at one atom `w ∉ Y`. The straddle lemma
(`PinchSplit` of MOLEPROP4-T, proofs unchanged: they never used the directions) says that no ladder cell meets both
`Y` and its complement.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `Y` is attached by `x` and `y`, both ending at the same outside atom. -/
structure Cut2 (N : Molecule V D) where
  Y : Finset V
  sub : Y ⊆ N.atoms
  x : D
  y : D
  cross : crossDarts N Y = {x, y}
  ne : x ≠ y
  same : N.atom (N.mate x) = N.atom (N.mate y)

namespace Cut2
variable {N : Molecule V D} (T : Cut2 N)

def w : V := N.atom (N.mate T.x)

theorem x_mem : T.x ∈ crossDarts N T.Y := by rw [T.cross]; simp
theorem atom_x : N.atom T.x ∈ T.Y := (mem_crossDarts.mp T.x_mem).1
theorem w_notMem : T.w ∉ T.Y := (mem_crossDarts.mp T.x_mem).2

theorem cross_dart {z : D} (h1 : N.atom z ∈ T.Y) (h2 : N.atom (N.mate z) ∉ T.Y) : z = T.x ∨ z = T.y := by
  have hz : z ∈ crossDarts N T.Y := mem_crossDarts.mpr ⟨h1, h2⟩
  rw [T.cross] at hz; simpa using hz

/-- A bond from `Y` to outside goes from an exit atom to `w`. -/
theorem cross_far {a b : V} (ha : a ∈ T.Y) (hb : b ∉ T.Y) (hpos : 1 ≤ N.bondsBetween a b) :
    b = T.w ∧ (a = N.atom T.x ∨ a = N.atom T.y) := by
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  rw [← Degen.card_neighborDarts N hab] at hpos
  obtain ⟨z, hz⟩ := card_pos.mp hpos
  obtain ⟨hza, hzb⟩ := (Degen.mem_neighborDarts N a b z).mp hz
  rcases T.cross_dart (hza ▸ ha) (hzb ▸ hb) with rfl | rfl
  · exact ⟨hzb.symm, Or.inl hza.symm⟩
  · exact ⟨hzb.symm.trans T.same.symm, Or.inr hza.symm⟩

/-- A double bond from `Y` to outside is the pair of exits, from one atom. -/
theorem cross_double {a b : V} (ha : a ∈ T.Y) (hb : b ∉ T.Y) (h2 : N.bondsBetween a b = 2) :
    N.atom T.x = a ∧ N.atom T.y = a := by
  classical
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have hc := Degen.card_neighborDarts N hab
  rw [h2] at hc
  have hsub : Degen.neighborDarts N a b ⊆ {T.x, T.y} := by
    intro z hz
    obtain ⟨hza, hzb⟩ := (Degen.mem_neighborDarts N a b z).mp hz
    rcases T.cross_dart (hza ▸ ha) (hzb ▸ hb) with rfl | rfl <;> simp
  have heq : Degen.neighborDarts N a b = {T.x, T.y} :=
    eq_of_subset_of_card_le hsub (by rw [hc, card_pair T.ne])
  have hx : T.x ∈ Degen.neighborDarts N a b := by rw [heq]; simp
  have hy : T.y ∈ Degen.neighborDarts N a b := by rw [heq]; simp
  exact ⟨((Degen.mem_neighborDarts N a b _).mp hx).1, ((Degen.mem_neighborDarts N a b _).mp hy).1⟩

/-- A crossing rung cannot occur in a cell. -/
theorem no_cross_rung {p q p' q' : V} (hp : p ∈ T.Y) (hq : q ∉ T.Y) (hpq : N.bondsBetween p q = 2)
    (hrp : N.bondsBetween p p' = 1) (hrq : N.bondsBetween q q' = 1) (hr' : N.bondsBetween p' q' = 2)
    (hpp' : p ≠ p') (hqp' : q ≠ p') (hpq' : p ≠ q') : False := by
  obtain ⟨hxp, hyp⟩ := T.cross_double hp hq hpq
  have hqw := (T.cross_far hp hq (by rw [hpq]; norm_num)).1
  have hp' : p' ∈ T.Y := by
    by_contra h
    have := (T.cross_far hp h (by rw [hrp])).1
    exact hqp' (hqw.trans this.symm)
  have hq' : q' ∉ T.Y := by
    intro h
    have := (T.cross_far h hq (by rw [Degen.bondsBetween_comm, hrq])).2
    rcases this with h' | h'
    · exact hpq' (hxp.symm.trans h'.symm)
    · exact hpq' (hyp.symm.trans h'.symm)
  have := (T.cross_double hp' hq' hr').1
  exact hpp' (hxp.symm.trans this)

/-- **No cell of `N` meets both `Y` and its complement.** -/
theorem cell_sub_or_disjoint {S : Finset V} (hS : MoleProp.IsLadderCell N S) : S ⊆ T.Y ∨ Disjoint S T.Y := by
  classical
  obtain ⟨u, v, hL, rfl⟩ := hS
  obtain ⟨_, hinj, _, hrung, hrail⟩ := hL
  obtain ⟨su, sv, _⟩ := hrail 0
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at su sv
  have ne : ∀ {a b : Fin 2 ⊕ Fin 2}, a ≠ b → Sum.elim u v a ≠ Sum.elim u v b := fun h e => h (hinj e)
  have hu01 : u 0 ≠ u 1 := ne (a := .inl 0) (b := .inl 1) (by decide)
  have hv01 : v 0 ≠ v 1 := ne (a := .inr 0) (b := .inr 1) (by decide)
  have h00 : u 0 ≠ v 0 := ne (a := .inl 0) (b := .inr 0) (by decide)
  have h11 : u 1 ≠ v 1 := ne (a := .inl 1) (b := .inr 1) (by decide)
  have h01 : u 0 ≠ v 1 := ne (a := .inl 0) (b := .inr 1) (by decide)
  have h10 : u 1 ≠ v 0 := ne (a := .inl 1) (b := .inr 0) (by decide)
  have bc := fun a b => Degen.bondsBetween_comm N a b
  have r0 := hrung 0
  have r1 := hrung 1
  have rung0 : (u 0 ∈ T.Y ↔ v 0 ∈ T.Y) := by
    constructor
    · intro hu; by_contra hv
      exact T.no_cross_rung hu hv r0 su sv r1 hu01 h10.symm h01
    · intro hv; by_contra hu
      exact T.no_cross_rung hv hu (by rw [bc]; exact r0) sv su (by rw [bc]; exact r1) hv01 h01 h10.symm
  have rung1 : (u 1 ∈ T.Y ↔ v 1 ∈ T.Y) := by
    constructor
    · intro hu; by_contra hv
      exact T.no_cross_rung hu hv r1 (by rw [bc]; exact su) (by rw [bc]; exact sv) r0 hu01.symm h01.symm h10
    · intro hv; by_contra hu
      exact T.no_cross_rung hv hu (by rw [bc]; exact r1) (by rw [bc]; exact sv) (by rw [bc]; exact su)
        (by rw [bc]; exact r0) hv01.symm h10 h01.symm
  have hS4 : ∀ z, z ∈ Molecule.ladderAtoms u v ↔ z = u 0 ∨ z = u 1 ∨ z = v 0 ∨ z = v 1 := by
    intro z
    simp only [Molecule.ladderAtoms, mem_union, mem_image, mem_univ, true_and]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr ⟨0, rfl⟩, Or.inr ⟨1, rfl⟩]
  by_cases h0 : u 0 ∈ T.Y <;> by_cases h1 : u 1 ∈ T.Y
  · left; intro z hz; rw [hS4] at hz; rcases hz with rfl | rfl | rfl | rfl <;> tauto
  · exfalso
    have e1 := (T.cross_far h0 h1 (by rw [su])).1
    have e2 := (T.cross_far (rung0.mp h0) (fun h => h1 (rung1.mpr h)) (by rw [sv])).1
    exact h11 (e1.trans e2.symm)
  · exfalso
    have e1 := (T.cross_far h1 h0 (by rw [bc, su])).1
    have e2 := (T.cross_far (rung1.mp h1) (fun h => h0 (rung0.mpr h)) (by rw [bc, sv])).1
    exact h00 (e1.trans e2.symm)
  · right
    refine disjoint_left.mpr fun z hz hzY => ?_
    rw [hS4] at hz; rcases hz with rfl | rfl | rfl | rfl <;> tauto

end Cut2
end WaveTurbulence.FinalCountG8
