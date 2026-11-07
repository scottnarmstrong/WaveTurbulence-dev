/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCaseI
public import WaveTurbulence.Foundations.FinalCount.BridgeSplit
import Mathlib.Tactic

/-! # From a label-count bound to an `𝔄` bound for the removal of a pair of atoms

`erase_pair_bonds`: the bonds lost when two atoms are erased.
`countAFree_le_erase_pair`: if `𝔈(M) ≤ N · 𝔈(M ∖ {a,b})` (the relaxed count of the erased molecule with the erased
admissibility) and the circuit ranks differ by `r`, then
`𝔄(M) ≤ N L^{-(d-γ) r} (C₁⁻¹ δ^{1/2})^r (log L)^8 · 𝔄*(M ∖ {a,b})`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The bonds lost when two atoms are erased: `deg a + deg b − bondsBetween a b`. -/
theorem erase_pair_bonds (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {a b : V} (hab : a ≠ b)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) :
    (M.bonds.card : ℤ) = (Degen.eraseAtoms M {a, b}).bonds.card + (M.deg a + M.deg b - M.bondsBetween a b) := by
  classical
  have hY : ({a, b} : Finset V) ⊆ M.atoms := by
    intro z hz; rcases mem_insert.mp hz with rfl | hz
    · exact ha
    · rw [mem_singleton.mp hz]; exact hb
  have h1 := two_mul_erase_bonds M hY
  have h2 := card_cross_pair M hloop hab
  have h3 := Mole.sum_degrees_eq_two_mul_bonds M
  have h4 := sum_sdiff (f := fun v => M.deg v) hY
  rw [sum_pair hab] at h4
  omega

/-- Circuit ranks of `M` and of `M ∖ {a,b}` when both are connected. -/
theorem circuitRank_erase_pair (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {a b : V}
    (hab : a ≠ b) (ha : a ∈ M.atoms) (hb : b ∈ M.atoms)
    (hconnM : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hconnP : ∀ u ∈ (Degen.eraseAtoms M {a, b}).atoms, ∀ v ∈ (Degen.eraseAtoms M {a, b}).atoms,
      (Degen.eraseAtoms M {a, b}).SameComponent u v)
    (hne : (Degen.eraseAtoms M {a, b}).atoms.Nonempty) :
    M.circuitRank = (Degen.eraseAtoms M {a, b}).circuitRank +
      ((M.deg a + M.deg b - M.bondsBetween a b : ℤ) - 2) := by
  have hF1 := Mole.numComponents_eq_one M ⟨a, ha⟩ hconnM
  have hF2 := Mole.numComponents_eq_one _ hne hconnP
  have hB := erase_pair_bonds M hloop hab ha hb
  have hA : ((Degen.eraseAtoms M {a, b}).atoms.card : ℤ) + 2 = M.atoms.card := by
    change ((M.atoms \ {a, b}).card : ℤ) + 2 = _
    have hY : ({a, b} : Finset V) ⊆ M.atoms := by
      intro z hz; rcases mem_insert.mp hz with rfl | hz
      · exact ha
      · rw [mem_singleton.mp hz]; exact hb
    rw [card_sdiff_of_subset hY, card_pair hab, Nat.cast_sub (by have := card_le_card hY; rwa [card_pair hab] at this)]
    push_cast; ring
  unfold Molecule.circuitRank
  rw [hF1, hF2]
  push_cast
  omega

/-- The cells of `M` meeting `Y` number at most `2 |Y|`; the others are the cells of the erasure. -/
theorem cellProduct_le_erase (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4) (Y : Finset V) {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hlog : 1 ≤ Real.log L) (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) :
    MoleProp.cellProduct M L γ δ P ≤
      MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P * (Real.log L ^ 2) ^ (2 * Y.card) := by
  classical
  set f := fun S => Molecule.ladderWeight L γ δ (P S) with hf
  have hf0 : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ f S := fun S hS => ladderWeight_nonneg hL hδ (hP S hS)
  have hlog2 : 1 ≤ Real.log L ^ 2 := by nlinarith
  have hsplit : MoleProp.cellProduct M L γ δ P =
      (∏ S ∈ (MoleProp.ladderCells M).filter (fun S => Disjoint S Y), f S) * ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S Y), f S := by
    unfold MoleProp.cellProduct
    rw [prod_filter_mul_prod_filter_not]
  have h1 : ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => Disjoint S Y), f S = MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P := by
    unfold MoleProp.cellProduct
    refine prod_congr ?_ fun _ _ => rfl
    ext S
    simp only [MoleProp.ladderCells, mem_filter, mem_powerset, MoleProp.isLadderCell_erase_iff]
    constructor
    · rintro ⟨⟨_, hc⟩, hd⟩
      refine ⟨?_, hc, hd⟩
      intro z hz
      exact mem_sdiff.mpr ⟨MoleProp.isLadderCell_subset_atoms M hc hz, disjoint_left.mp hd hz⟩
    · rintro ⟨_, hc, hd⟩
      exact ⟨⟨MoleProp.isLadderCell_subset_atoms M hc, hc⟩, hd⟩
  have hcard : ((MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S Y)).card ≤ 2 * Y.card := by
    have hsub : (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S Y) ⊆ Y.biUnion fun c => (MoleProp.ladderCells M).filter fun S => c ∈ S := by
      intro S hS
      obtain ⟨hSC, hnd⟩ := mem_filter.mp hS
      obtain ⟨c, hcS, hcY⟩ := Finset.not_disjoint_iff.mp hnd
      exact mem_biUnion.mpr ⟨c, hcY, mem_filter.mpr ⟨hSC, hcS⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ c ∈ Y, ((MoleProp.ladderCells M).filter fun S => c ∈ S).card ≤ ∑ _c ∈ Y, 2 :=
          sum_le_sum fun c _ => card_cells_containing_le_two hloop hdeg c
      _ = 2 * Y.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have h2 : ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S Y), f S ≤ (Real.log L ^ 2) ^ (2 * Y.card) := by
    calc ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S Y), f S
        ≤ ∏ _S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S Y), Real.log L ^ 2 :=
          prod_le_prod₀ (fun S hS => hf0 S (mem_filter.mp hS).1) fun S _ => ladderWeight_le_log_sq L γ δ (P S)
      _ = (Real.log L ^ 2) ^ ((MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S Y)).card := prod_const _
      _ ≤ _ := pow_le_pow_right₀ hlog2 hcard
  have hc : 0 ≤ MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P := by
    rw [← h1]; exact prod_nonneg fun S hS => hf0 S (mem_filter.mp hS).1
  rw [hsplit, h1]
  calc MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P * ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S Y), f S
      ≤ MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P * (Real.log L ^ 2) ^ (2 * Y.card) :=
        mul_le_mul_of_nonneg_left h2 hc

end WaveTurbulence.FinalCountG8
