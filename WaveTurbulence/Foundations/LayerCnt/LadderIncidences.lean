/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # Interior atoms of a ladder have four incidences (TARGET layerlad, L1505)

"By disregarding the atoms at both ends of `𝕃`, we may also assume that all atoms in the ladder have
degree `4`": in a molecule (degree `≤ 4`) the bond multiplicities `2, 1, 1` of an interior atom exhaust its
four darts. This gives the `FullRungSequence` of the interior rungs.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Four incidences from bond multiplicities `2, 1, 1` to three distinct neighbours. -/
theorem fourIncidences_of_bonds (M : Molecule V D) {x a b c : V}
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : M.bondsBetween x a = 2) (h2 : M.bondsBetween x b = 1) (h3 : M.bondsBetween x c = 1) :
    Nonempty (FourIncidences M x ![a, a, b, c]) := by
  have c1 := Mole.bondsBetween_eq_card_darts M hxa
  have c2 := Mole.bondsBetween_eq_card_darts M hxb
  have c3 := Mole.bondsBetween_eq_card_darts M hxc
  rw [h1] at c1
  rw [h2] at c2
  rw [h3] at c3
  obtain ⟨d0, d1, hd01, hd⟩ := Finset.card_eq_two.mp c1.symm
  obtain ⟨d2, hd2⟩ := Finset.card_eq_one.mp c2.symm
  obtain ⟨d3, hd3⟩ := Finset.card_eq_one.mp c3.symm
  have m0 : d0 ∈ (M.dartsAt x).filter (fun y => M.atom (M.mate y) = a) := by rw [hd]; simp
  have m1 : d1 ∈ (M.dartsAt x).filter (fun y => M.atom (M.mate y) = a) := by rw [hd]; simp
  have m2 : d2 ∈ (M.dartsAt x).filter (fun y => M.atom (M.mate y) = b) := by rw [hd2]; simp
  have m3 : d3 ∈ (M.dartsAt x).filter (fun y => M.atom (M.mate y) = c) := by rw [hd3]; simp
  simp only [Finset.mem_filter, Mole.mem_dartsAt] at m0 m1 m2 m3
  refine ⟨⟨![d0, d1, d2, d3], ?_, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    all_goals first
      | exact hd01 hij
      | exact hd01 hij.symm
      | (exfalso; have := congrArg (fun z => M.atom (M.mate z)) hij; simp only [m0.2, m1.2, m2.2, m3.2] at this
         first | exact hab this | exact hab this.symm | exact hac this | exact hac this.symm
               | exact hbc this | exact hbc this.symm)
  · intro i; fin_cases i <;> simp [m0.1, m1.1, m2.1, m3.1]
  · intro i; fin_cases i <;> simp [m0.2, m1.2, m2.2, m3.2]

section Ladder
variable (M : Molecule V D) {m : ℕ} {u v : Fin (m + 1) → V}

/-- Adapter to the shape of `IsLadder`: the rung and rail clauses. In the B2 final-candidate form of
`IsLadder` (no "`4m+2` bonds" clause) this is `hL.2.2.2.2`; in this scratch universe's copy of
`MoleculeDefs` it is `hL.2.2.2.2.1`. Every other use of `IsLadder` below goes through the adapters. -/
theorem ladder_rails (hL : M.IsLadder u v) : ∀ j : Fin m,
    M.bondsBetween (u j.castSucc) (u j.succ) = 1 ∧ M.bondsBetween (v j.castSucc) (v j.succ) = 1 ∧
      (M.Directed (u j.castSucc) (u j.succ) ↔ M.Directed (v j.succ) (v j.castSucc)) :=
  hL.2.2.2.2

theorem ladder_inj (hL : M.IsLadder u v) : Function.Injective (Sum.elim u v) := hL.2.1

theorem ladder_rung (hL : M.IsLadder u v) (j : Fin (m + 1)) : M.bondsBetween (u j) (v j) = 2 :=
  hL.2.2.2.1 j

theorem ladder_pos (hL : M.IsLadder u v) : 1 ≤ m := hL.1

theorem ladder_uu (hL : M.IsLadder u v) (x y : Fin (m + 1)) (h : x ≠ y) : u x ≠ u y := fun hh =>
  h (by simpa using ladder_inj M hL (a₁ := Sum.inl x) (a₂ := Sum.inl y) (by simpa using hh))

theorem ladder_vv (hL : M.IsLadder u v) (x y : Fin (m + 1)) (h : x ≠ y) : v x ≠ v y := fun hh =>
  h (by simpa using ladder_inj M hL (a₁ := Sum.inr x) (a₂ := Sum.inr y) (by simpa using hh))

theorem ladder_uv (hL : M.IsLadder u v) (x y : Fin (m + 1)) : u x ≠ v y := fun hh => by
  have := ladder_inj M hL (a₁ := Sum.inl x) (a₂ := Sum.inr y) (by simpa using hh)
  simp at this

/-- The four incidences of the interior upper atom `u j`. -/
theorem ladder_upper_incidences (hL : M.IsLadder u v) (j jm jp : Fin (m + 1))
    (hjm : j.1 < m) (hjm' : jm.1 + 1 = j.1) (hjp' : j.1 + 1 = jp.1) :
    Nonempty (FourIncidences M (u j) ![v j, v j, u jm, u jp]) := by
  have hjjm : j ≠ jm := by intro h; rw [h] at hjm'; omega
  have hjjp : j ≠ jp := by intro h; rw [h] at hjp'; omega
  have hjmjp : jm ≠ jp := by intro h; rw [h] at hjm'; omega
  have e1 : M.bondsBetween (u j) (v j) = 2 := ladder_rung M hL j
  have e2 : M.bondsBetween (u j) (u jm) = 1 := by
    have := (ladder_rails M hL ⟨jm.1, by omega⟩).1
    have e : (⟨jm.1, by omega⟩ : Fin m).succ = j := Fin.ext (by simp [hjm'])
    have e' : (⟨jm.1, by omega⟩ : Fin m).castSucc = jm := Fin.ext (by simp)
    rw [e, e'] at this
    rw [Mole.bondsBetween_symm]; exact this
  have e3 : M.bondsBetween (u j) (u jp) = 1 := by
    have := (ladder_rails M hL ⟨j.1, hjm⟩).1
    have e : (⟨j.1, hjm⟩ : Fin m).succ = jp := Fin.ext (by simp [← hjp'])
    have e' : (⟨j.1, hjm⟩ : Fin m).castSucc = j := Fin.ext (by simp)
    rw [e, e'] at this
    exact this
  exact fourIncidences_of_bonds M (ladder_uv M hL j j) (ladder_uu M hL j jm hjjm)
    (ladder_uu M hL j jp hjjp) (Ne.symm (ladder_uv M hL jm j)) (Ne.symm (ladder_uv M hL jp j))
    (ladder_uu M hL jm jp hjmjp) e1 e2 e3

/-- The four incidences of the interior lower atom `v j`. -/
theorem ladder_lower_incidences (hL : M.IsLadder u v) (j jm jp : Fin (m + 1))
    (hjm : j.1 < m) (hjm' : jm.1 + 1 = j.1) (hjp' : j.1 + 1 = jp.1) :
    Nonempty (FourIncidences M (v j) ![u j, u j, v jm, v jp]) := by
  have hjjm : j ≠ jm := by intro h; rw [h] at hjm'; omega
  have hjjp : j ≠ jp := by intro h; rw [h] at hjp'; omega
  have hjmjp : jm ≠ jp := by intro h; rw [h] at hjm'; omega
  have e1 : M.bondsBetween (v j) (u j) = 2 := by
    rw [Mole.bondsBetween_symm]; exact ladder_rung M hL j
  have e2 : M.bondsBetween (v j) (v jm) = 1 := by
    have := (ladder_rails M hL ⟨jm.1, by omega⟩).2.1
    have e : (⟨jm.1, by omega⟩ : Fin m).succ = j := Fin.ext (by simp [hjm'])
    have e' : (⟨jm.1, by omega⟩ : Fin m).castSucc = jm := Fin.ext (by simp)
    rw [e, e'] at this
    rw [Mole.bondsBetween_symm]; exact this
  have e3 : M.bondsBetween (v j) (v jp) = 1 := by
    have := (ladder_rails M hL ⟨j.1, hjm⟩).2.1
    have e : (⟨j.1, hjm⟩ : Fin m).succ = jp := Fin.ext (by simp [← hjp'])
    have e' : (⟨j.1, hjm⟩ : Fin m).castSucc = j := Fin.ext (by simp)
    rw [e, e'] at this
    exact this
  exact fourIncidences_of_bonds M (Ne.symm (ladder_uv M hL j j)) (ladder_vv M hL j jm hjjm)
    (ladder_vv M hL j jp hjjp) (ladder_uv M hL j jm) (ladder_uv M hL j jp)
    (ladder_vv M hL jm jp hjmjp) e1 e2 e3

end Ladder

end WaveTurbulence.LayerCnt
