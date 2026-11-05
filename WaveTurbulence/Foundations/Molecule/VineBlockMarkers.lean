/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFourIncidences
import Mathlib.Tactic

/-! # Degree equations with the actual two block joints marked -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
/-- A membership indicator is always zero or one. -/
theorem jointIndicator_le_one (J : Finset V) (v : V) : jointIndicator J v≤1 := by
  unfold jointIndicator
  split_ifs <;> omega

omit [Fintype D] [DecidableEq D] in
/-- Indicator one means membership. -/
theorem jointIndicator_eq_one_iff (J : Finset V) (v : V) :
    jointIndicator J v=1 ↔ v ∈ J := by simp [jointIndicator]

omit [Fintype D] [DecidableEq D] in
/-- Equality of 0/1 indicators means the same membership decision. -/
theorem jointIndicator_eq_iff (J : Finset V) (v w : V) :
    jointIndicator J v=jointIndicator J w ↔ (v ∈ J ↔ w ∈ J) := by
  by_cases hv : v ∈ J <;> by_cases hw : w ∈ J <;> simp [jointIndicator,hv,hw]

omit [DecidableEq D] in
/-- Degree four except at the two degree-two joints, as one linear identity. -/
theorem block_degree_marker (M : Molecule V D) {S : Finset V} {a b v : V}
    (hB : M.IsBlock S a b) (hv : v ∈ S) :
    M.degIn S v+2*jointIndicator ({a,b} : Finset V) v=4 := by
  obtain ⟨ha,hb⟩ := Mole.block_joint_degrees M hB
  have hdeg : M.degIn S v=if v ∈ ({a,b} : Finset V) then 2 else 4 := by
    split_ifs with h
    · rcases mem_insert.mp h with rfl | h
      · exact ha
      · have he := mem_singleton.mp h
        subst v
        exact hb
    · have hn : v ≠ a ∧ v ≠ b := by simpa only [mem_insert,mem_singleton,not_or] using h
      exact hB.2.2.2.2.2.2.2.2.1 v hv hn.1 hn.2
  rw [hdeg,jointIndicator]
  split_ifs <;> norm_num

/-- The local block equation at an actual rung atom with two parallel rung
incidences and its two rail incidences. -/
theorem rung_degree_marker (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b x partner prev next : V} (hB : M.IsBlock S a b)
    (R : FourIncidences M x ![partner,partner,prev,next]) (hx : x ∈ S) :
    2*jointIndicator S partner+jointIndicator S prev+jointIndicator S next+
      2*jointIndicator ({a,b} : Finset V) x=4 := by
  have hd := fourIncidences_degree M hM R S hx
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero] at hd
  have hm := block_degree_marker M hB hx
  omega

end WaveTurbulence.Vine
