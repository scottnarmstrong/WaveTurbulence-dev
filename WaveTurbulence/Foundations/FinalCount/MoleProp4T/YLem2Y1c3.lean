/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YEnd
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PinchFinal
import Mathlib.Tactic

/-! # DH23 `ylem2` for a (Y) sequence ending in (Y1), case 3 (L1952)

The last pair has its two extra single bonds to the same third atom `w = v_{2n+1}`. The chain is then attached by these
two bonds only, with opposite directions, and `𝔄(𝕄) ≤ 𝔄(𝕄 ∖ chain)` (no loss, same LG parameter; the LG condition at
`w` pays for the extra factor, DH23 L1952).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The (Y1), case 3 ending**: the two extra bonds of the last pair go to the same atom. -/
structure Y1End3 {M : Molecule V D} (C : YChain M) where
  x : D
  y : D
  hx : M.atom x = C.a C.n
  hy : M.atom y = C.b C.n
  hxo : M.atom (M.mate x) ∉ C.set
  hyo : M.atom (M.mate y) ∉ C.set
  same : M.atom (M.mate x) = M.atom (M.mate y)
  deg_a : M.deg (C.a C.n) = 4
  deg_b : M.deg (C.b C.n) = 4

namespace Y1End3
variable {M : Molecule V D} {C : YChain M} (E : Y1End3 C)

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
theorem deg_four (E : Y1End3 C) : ∀ v ∈ C.set, M.deg v = 4 := by
  intro v hv
  obtain ⟨i, hi, rfl | rfl⟩ := C.mem_set.mp hv
  · rcases Nat.lt_or_ge i C.n with h | h
    · exact (C.sat i h).1
    · rw [le_antisymm hi h]; exact E.deg_a
  · rcases Nat.lt_or_ge i C.n with h | h
    · exact (C.sat i h).2
    · rw [le_antisymm hi h]; exact E.deg_b

/-- The two extra bonds have opposite directions. -/
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

/-- **The chain of a (Y1), case 3 ending as a pinched set**, oriented so that `x` is outgoing. -/
def toPinch (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) : Pinch M :=
  if h : M.out E.x = true then
    ⟨C.set, C.set_sub, E.x, E.y, E.cross_eq, E.x_ne_y, E.same, h, by
      have := E.out_ne hcap; rw [h] at this; cases hy : M.out E.y <;> simp_all⟩
  else
    ⟨C.set, C.set_sub, E.y, E.x, by rw [E.cross_eq, pair_comm], E.x_ne_y.symm, E.same.symm, by
      have := E.out_ne hcap; cases hy : M.out E.y <;> cases hx : M.out E.x <;> simp_all, by simpa using h⟩

theorem toPinch_Y (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) : (E.toPinch hcap).Y = C.set := by
  unfold toPinch; split_ifs <;> rfl

end Y1End3

/-- **DH23 Lemma `ylem2`, first statement, (Y1) case 3**: `𝔄(𝕄) ≤ 𝔄(𝕄 ∖ chain)`. -/
theorem ylem2_Y1c3 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) → ∀ (C : YChain M) (_ : Y1End3 C),
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
        AFree M d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms M C.set) d L γ δ η C1 P := by
  obtain ⟨Cstar, hCstar, hO⟩ := pinch_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := hO C1 hC1 δ hδ
  refine ⟨R, fun L hL => ?_⟩
  intro V D _ _ _ M hcap C E P hP
  have hY := E.toPinch_Y hcap
  have h := hR L hL M hcap (E.toPinch hcap) (by rw [hY]; exact E.deg_four) (by rw [hY]; exact C.piece_connected) P hP
  rwa [hY] at h

end WaveTurbulence.MoleProp4
