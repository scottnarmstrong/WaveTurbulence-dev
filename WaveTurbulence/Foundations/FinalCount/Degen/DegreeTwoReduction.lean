/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.EvenDegreeCuts
public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadderProductDeletion
public import WaveTurbulence.Foundations.FinalCount.Degen.ConditionedCountEFixedLabel
public import WaveTurbulence.Foundations.FinalCount.Degen.CircuitNormalization
import Mathlib.Tactic

/-! # Fixed-label degree-two degenerate removal in the all-even case -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A selected rung plus a selected rail already uses three half-edges. -/
theorem degree_ge_three_of_double_and_single (M : Molecule V D) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hb : M.bondsBetween a b = 2) (hc : M.bondsBetween a c = 1) : 3 ≤ M.deg a := by
  have hn : a ∉ ({b,c} : Finset V) := by simp only [mem_insert,mem_singleton]; tauto
  have hh := sum_neighbor_bonds_le_degree M a {b,c} hn
  have hbc' : b ∉ ({c} : Finset V) := by simpa only [mem_singleton] using hbc
  rw [sum_insert hbc',sum_singleton,hb,hc] at hh
  exact hh

/-- Every atom in either rail of a genuine source ladder has degree at least three. -/
theorem sourceLadder_row_degree_ge_three (M : Molecule V D) {m : ℕ}
    {u v : Fin (m+1) → V} (hL : SourceLadder M u v) (j : Fin (m+1)) : 3 ≤ M.deg (u j) := by
  have hm := hL.1
  have hcross (i k : Fin (m+1)) : u i ≠ v k := by
    intro he
    have hh : (Sum.inl i : Fin (m+1) ⊕ Fin (m+1)) = Sum.inr k := hL.2.1 he
    cases hh
  have huinj : Function.Injective u := (Sum.elim_injective.mp hL.2.1).1
  by_cases hj : j.val < m
  · let t : Fin m := ⟨j.val,hj⟩
    have he : t.castSucc = j := Fin.ext rfl
    have hne : j ≠ t.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      dsimp only [t] at hv
      simp only [Fin.val_succ] at hv
      omega
    apply degree_ge_three_of_double_and_single M (hcross j j) (fun hh => hne (huinj hh))
      (hcross t.succ j).symm (hL.2.2.2.1 j)
    simpa only [he] using (hL.2.2.2.2 t).1
  · let t : Fin m := ⟨m-1,by omega⟩
    have he : t.succ = j := by apply Fin.ext; dsimp only [t]; simp only [Fin.val_succ]; omega
    have hne : j ≠ t.castSucc := by
      intro hh
      have hv := congrArg Fin.val hh
      dsimp only [t] at hv
      simp only [Fin.val_castSucc] at hv
      omega
    apply degree_ge_three_of_double_and_single M (hcross j j) (fun hh => hne (huinj hh))
      (hcross t.castSucc j).symm (hL.2.2.2.1 j)
    rw [bondsBetween_comm, ← he]
    exact (hL.2.2.2.2 t).1

theorem sourceLadderSet_degree_ge_three (M : Molecule V D) {S : Finset V}
    (hS : SourceLadderSet M S) {z : V} (hz : z ∈ S) : 3 ≤ M.deg z := by
  obtain ⟨m,u,v,hL,rfl⟩ := hS
  rcases mem_union.mp hz with hz | hz
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact sourceLadder_row_degree_ge_three M hL j
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact sourceLadder_row_degree_ge_three M (sourceLadder_swap M hL) j

/-- A degree-two atom belongs to no source ladder, so the literal inherited
product is unchanged, independently of circuit counts. -/
theorem sourceLadderProduct_erase_eq_of_degree_two (M : Molecule V D) {z : V}
    (htwo : M.deg z = 2) (L γ δ : ℝ) (P : Finset V → ℝ) :
    sourceLadderProduct (eraseAtoms M {z}) L γ δ (inheritedSourceScale M P) =
      sourceLadderProduct M L γ δ P := by
  classical
  have havoid (S : Finset V) (hS : SourceLadderSet M S) : Disjoint S {z} := by
    apply disjoint_singleton_right.mpr
    intro hz
    have hh := sourceLadderSet_degree_ge_three M hS hz
    omega
  unfold sourceLadderProduct
  rw [sourceMaximalLadders_erase_eq_of_all_disjoint M {z} havoid]
  apply prod_congr rfl
  intro S hS
  rw [inheritedSourceScale_eq_on_old_maximal M P hS]

/-- Exact normalization gain for the all-even degree-two fixed-root removal. -/
theorem degree_two_normalization_le (M : Molecule V D) {d : ℕ} {L γ δ C1 : ℝ}
    (hL : 1 ≤ L) (hγ : γ ≤ (d : ℝ)) (hδ : 0 < δ) (hC : 0 < C1)
    (hB : C1⁻¹ * δ ^ (1/2 : ℝ) ≤ 1) (hlog : 0 < Real.log L ^ 2)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (heven : ∀ a ∈ M.atoms, Even (M.deg a)) {z : V} (hz : z ∈ M.atoms)
    (htwo : M.deg z = 2) (P : Finset V → ℝ)
    (hP : ∀ S ∈ sourceMaximalLadders M, 0 ≤ P S) :
    sourceNormalizationFactor M (d := d) L γ δ C1 P ≤
      (L ^ (-(d : ℝ)+γ) * (C1⁻¹ * δ ^ (1/2 : ℝ))) *
      sourceNormalizationFactor (eraseAtoms M {z}) (d := d) L γ δ C1 (inheritedSourceScale M P) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hB0 : 0 < C1⁻¹ * δ ^ (1/2 : ℝ) := by positivity
  have hχ := circuitRank_erase_two_le_sub_one_of_even M hconn heven hz htwo
  have hn := circuit_normalization_antitone hL (sub_nonneg.mpr hγ) hB0 hB (by omega :
    (eraseAtoms M {z}).circuitRank + 1 ≤ M.circuitRank)
  have he : L ^ (-((d:ℝ)-γ) * (((eraseAtoms M {z}).circuitRank+1 : ℤ) : ℝ)) *
      (C1⁻¹ * δ ^ (1/2 : ℝ)) ^ ((eraseAtoms M {z}).circuitRank+1) =
      (L ^ (-(d:ℝ)+γ) * (C1⁻¹ * δ ^ (1/2 : ℝ))) *
      (L ^ (-((d:ℝ)-γ) * ((eraseAtoms M {z}).circuitRank : ℝ)) *
      (C1⁻¹ * δ ^ (1/2 : ℝ)) ^ (eraseAtoms M {z}).circuitRank) := by
    rw [Int.cast_add,Int.cast_one,mul_add,Real.rpow_add hL0,zpow_add₀ hB0.ne']
    simp only [mul_one,zpow_one]
    rw [show -((d:ℝ)-γ) = -(d:ℝ)+γ by ring]
    ring
  rw [he] at hn
  unfold sourceNormalizationFactor
  rw [sourceLadderProduct_erase_eq_of_degree_two M htwo]
  exact (mul_le_mul_of_nonneg_right hn (sourceLadderProduct_pos M hL0.le hδ.le hlog P hP).le).trans_eq (by ring)

/-- DH23 10.5(2): the common label is source-prescribed and remains fixed
in the conditioned post problem; the gain is stronger than the printed eta-loss. -/
theorem sourceCountA_conditioned_erase_degree_two_prescribed_le (M : Molecule V D)
    (hM : M.IsMolecule) {d : ℕ} {L γ δ C1 : ℝ}
    (hL : 1 ≤ L) (hγ : γ ≤ (d : ℝ)) (hδ : 0 < δ) (hC : 0 < C1)
    (hB : C1⁻¹ * δ ^ (1/2 : ℝ) ≤ 1) (hlog : 0 < Real.log L ^ 2)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (heven : ∀ a ∈ M.atoms, Even (M.deg a)) {z : V} (hz : z ∈ M.atoms)
    (htwo : M.deg z = 2) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    {e : D} (he : M.atom e = z) (q : Fin d → ℤ)
    (hconstant : ∀ κ, Adm κ → ConstantAt M κ z) (hfixed : ∀ κ, Adm κ → κ e = q)
    (P : Finset V → ℝ) (hP : ∀ S ∈ sourceMaximalLadders M, 0 ≤ P S) :
    sourceCountA M L γ δ C1 w Adm P ≤
      ENNReal.ofReal (L ^ (-(d:ℝ)+γ) * (C1⁻¹ * δ ^ (1/2 : ℝ))) *
      sourceCountA (eraseAtoms M {z}) L γ δ C1 w
        (conditionedPostAdmissibility M L w z e Adm q) (inheritedSourceScale M P) := by
  have hc := countE_conditioned_erase_prescribed_label_le M hM L γ δ w Adm he q hconstant hfixed
  have hn := degree_two_normalization_le M hL hγ hδ hC hB hlog hconn heven hz htwo P hP
  rw [sourceCountA_eq_normalization,sourceCountA_eq_normalization]
  have heN := ENNReal.ofReal_mul
    (q := sourceNormalizationFactor (eraseAtoms M {z}) (d:=d) L γ δ C1 (inheritedSourceScale M P))
    (by positivity : 0 ≤ L ^ (-(d:ℝ)+γ) * (C1⁻¹ * δ ^ (1/2 : ℝ)))
  calc
    _ ≤ ((eraseAtoms M {z}).countE L γ δ w (conditionedPostAdmissibility M L w z e Adm q) : ℝ≥0∞) *
        ENNReal.ofReal ((L ^ (-(d:ℝ)+γ) * (C1⁻¹ * δ ^ (1/2 : ℝ))) *
          sourceNormalizationFactor (eraseAtoms M {z}) (d:=d) L γ δ C1 (inheritedSourceScale M P)) :=
      mul_le_mul (ENat.toENNReal_mono hc) (ENNReal.ofReal_le_ofReal hn) bot_le bot_le
    _ = _ := by rw [heN]; ring

end WaveTurbulence.Degen
