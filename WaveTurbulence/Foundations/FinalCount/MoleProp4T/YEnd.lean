/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YChain
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.CellGap
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-! # Endings of a (Y) chain

* `Y2End`: the last pair has its two extra single bonds `x, y` to distinct atoms outside the chain (DH23 (Y2));
  then the crossing darts of the chain are exactly `x, y`, with opposite directions (in/out caps), and the chain is a
  `TwoExit` set whose post molecule is DH23's `𝕄′`.
* `Y1End2`: exactly one extra bond (DH23 (Y1), case 2); the chain is a `OneExit` set.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace YChain
variable {M : Molecule V D} (C : YChain M)

omit [DecidableEq D] in
/-- A dart at the last pair leaving the chain is the unique extra dart there. -/
theorem away_last_a_eq {z z' : D} (hdeg : M.deg (C.a C.n) = 4) (hz : M.atom z = C.a C.n)
    (hzo : M.atom (M.mate z) ∉ C.set) (hz' : M.atom z' = C.a C.n) (hzo' : M.atom (M.mate z') ∉ C.set) : z = z' := by
  have h := C.card_away_last_a
  rw [hdeg] at h
  have h1 : ((M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n).card ≤ 1 := by omega
  refine card_le_one.mp h1 z ?_ z' ?_
  · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, fun h => hzo (C.nbA_sub le_rfl h)⟩
  · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz'⟩, fun h => hzo' (C.nbA_sub le_rfl h)⟩

omit [DecidableEq D] in
theorem away_last_b_eq {z z' : D} (hdeg : M.deg (C.b C.n) = 4) (hz : M.atom z = C.b C.n)
    (hzo : M.atom (M.mate z) ∉ C.set) (hz' : M.atom z' = C.b C.n) (hzo' : M.atom (M.mate z') ∉ C.set) : z = z' := by
  have h := C.card_away_last_b
  rw [hdeg] at h
  have h1 : ((M.dartsAt (C.b C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbB C.n).card ≤ 1 := by omega
  refine card_le_one.mp h1 z ?_ z' ?_
  · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, fun h => hzo (C.nbB_sub le_rfl h)⟩
  · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz'⟩, fun h => hzo' (C.nbB_sub le_rfl h)⟩

omit [DecidableEq D] in
/-- A crossing dart of the chain sits at the last pair. -/
theorem cross_at_last {z : D} (hz : z ∈ crossDarts M C.set) : M.atom z = C.a C.n ∨ M.atom z = C.b C.n := by
  obtain ⟨h1, h2⟩ := mem_crossDarts.mp hz
  obtain ⟨i, hi, hzi⟩ := C.mem_set.mp h1
  rcases Nat.lt_or_ge i C.n with hlt | hge
  · exact absurd (C.not_cross_of_lt hlt hzi) h2
  · have : i = C.n := le_antisymm hi hge
    subst this; exact hzi

end YChain

/-- **The (Y2) ending** (DH23 L1929): the last pair has two extra single bonds to distinct atoms. -/
structure Y2End {M : Molecule V D} (C : YChain M) where
  x : D
  y : D
  hx : M.atom x = C.a C.n
  hy : M.atom y = C.b C.n
  hxo : M.atom (M.mate x) ∉ C.set
  hyo : M.atom (M.mate y) ∉ C.set
  far : M.atom (M.mate x) ≠ M.atom (M.mate y)
  deg_a : M.deg (C.a C.n) = 4
  deg_b : M.deg (C.b C.n) = 4

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

omit [DecidableEq D] in
theorem x_ne_y : E.x ≠ E.y := by
  intro h
  have := E.hx; rw [h, E.hy] at this
  exact C.ne_ab C.n le_rfl C.n le_rfl this.symm

theorem cross_eq : crossDarts M C.set = {E.x, E.y} := by
  ext z
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hz
    obtain ⟨_, h2⟩ := mem_crossDarts.mp hz
    rcases C.cross_at_last hz with h | h
    · exact Or.inl (C.away_last_a_eq E.deg_a h h2 E.hx E.hxo)
    · exact Or.inr (C.away_last_b_eq E.deg_b h h2 E.hy E.hyo)
  · rintro (rfl | rfl)
    · exact mem_crossDarts.mpr ⟨E.hx ▸ C.a_mem le_rfl, E.hxo⟩
    · exact mem_crossDarts.mpr ⟨E.hy ▸ C.b_mem le_rfl, E.hyo⟩

omit [DecidableEq D] in
/-- Every chain atom has degree four. -/
theorem deg_four (E : Y2End C) : ∀ v ∈ C.set, M.deg v = 4 := by
  intro v hv
  obtain ⟨i, hi, rfl | rfl⟩ := C.mem_set.mp hv
  · rcases Nat.lt_or_ge i C.n with h | h
    · exact (C.sat i h).1
    · rw [le_antisymm hi h]; exact E.deg_a
  · rcases Nat.lt_or_ge i C.n with h | h
    · exact (C.sat i h).2
    · rw [le_antisymm hi h]; exact E.deg_b

/-- **The two extra bonds have opposite directions** (in/out caps, DH23 "matching the directions"). -/
theorem out_ne (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) : M.out E.x ≠ M.out E.y := by
  classical
  let f : D → ℤ := fun z => if M.out z = true then 1 else -1
  have hf : ∀ z, f (M.mate z) = -f z := by intro z; simp only [f, M.out_mate]; cases M.out z <;> rfl
  have hsum := sum_stars_eq_cross M C.set f hf
  rw [E.cross_eq, sum_pair E.x_ne_y] at hsum
  have hzero : ∀ v ∈ C.set, ∑ z ∈ M.dartsAt v, f z = 0 := by
    intro v hv
    have h4 := E.deg_four v hv
    have hc := hcap v (C.set_sub hv)
    have hod := Mole.outdeg_add_indeg M v
    have hs : ∑ z ∈ M.dartsAt v, f z = (M.outdeg v : ℤ) - M.indeg v := by
      simp only [f]
      rw [Finset.sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_neg_one]
      unfold Molecule.outdeg Molecule.indeg
      simp only [Bool.not_eq_true]
      ring
    rw [hs]; omega
  rw [sum_eq_zero hzero] at hsum
  intro h
  simp only [f, h] at hsum
  cases hy : M.out E.y <;> simp [hy] at hsum

/-- **The chain of a (Y2) ending as a two-exit set**, oriented so that `x` is outgoing. -/
def toTwoExit (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) : TwoExit M :=
  if h : M.out E.x = true then
    ⟨C.set, C.set_sub, E.x, E.y, E.cross_eq, E.x_ne_y, E.far, h, by
      have := E.out_ne hcap; rw [h] at this; cases hy : M.out E.y <;> simp_all⟩
  else
    ⟨C.set, C.set_sub, E.y, E.x, by rw [E.cross_eq, pair_comm], E.x_ne_y.symm, E.far.symm, by
      have := E.out_ne hcap; cases hy : M.out E.y <;> cases hx : M.out E.x <;> simp_all, by simpa using h⟩

theorem toTwoExit_Y (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) : (E.toTwoExit hcap).Y = C.set := by
  unfold toTwoExit; split_ifs <;> rfl

end Y2End

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- In a connected molecule with more than four atoms, every four-atom set is left by some bond. -/
theorem openSet_of_connected {M : Molecule V D} (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    {S : Finset V} (hS : S ⊆ M.atoms) (hne : S.Nonempty) (hlt : S.card < M.atoms.card) : OpenSet M S := by
  by_contra hno
  unfold OpenSet at hno
  push Not at hno
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hv, hvS⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hclosed : ∀ a b, M.SameComponent a b → (a ∈ S ↔ b ∈ S) := by
    intro a b h
    induction h with
    | rel a b hab =>
      obtain ⟨z, rfl, rfl⟩ := hab
      constructor
      · exact fun h => hno z h
      · intro h
        have := hno (M.mate z) h
        rwa [M.mate_mate] at this
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact hvS ((hclosed u v (hconn u (hS hu) v hv)).mp hu)

omit [DecidableEq D] in
/-- Hence every cell of such a molecule is good. -/
theorem goodCell_of_connected {M : Molecule V D} (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (h5 : 5 ≤ M.atoms.card) {S : Finset V} (hS : S ∈ MoleProp.ladderCells M) : GoodCell M S := by
  classical
  left
  obtain ⟨hsub, u, v, hL, rfl⟩ := mem_filter.mp hS
  rw [mem_powerset] at hsub
  refine openSet_of_connected hconn hsub ⟨u 0, mem_union_left _ (mem_image_of_mem _ (mem_univ 0))⟩ ?_
  calc (Molecule.ladderAtoms u v).card ≤ (univ.image u).card + (univ.image v).card := card_union_le _ _
    _ ≤ 2 + 2 := add_le_add (card_image_le.trans (by simp)) (card_image_le.trans (by simp))
    _ < _ := by omega

end WaveTurbulence.MoleProp4
