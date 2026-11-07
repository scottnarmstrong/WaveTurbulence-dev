/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCells
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairNormalization
import Mathlib.Tactic

/-! # The per-position ladder factors across a two-exit removal

`cellProduct N P ≤ cellProduct N[Y] P · cellProduct post P' · ((log L)²)⁶` when `P'` agrees with `P` on the cells of
the post molecule avoiding `c`. The cells of `N` inside `Y` are those of the piece, those avoiding `Y` and `c` are
cells of the post molecule, and the remaining ones (at most six: through `c` or an exit atom) have factor
`≤ (log L)²`. This is DH23's "for all but `O(1)` operations ... `𝔇 ≲ 1`" for the ladder product (L1952).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ladderWeight_le_log_sq (L γ δ P : ℝ) : Molecule.ladderWeight L γ δ P ≤ Real.log L ^ 2 := min_le_left _ _

theorem ladderWeight_nonneg {L γ δ P : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hP : 0 ≤ P) :
    0 ≤ Molecule.ladderWeight L γ δ P := by
  unfold Molecule.ladderWeight
  refine le_min (sq_nonneg _) ?_
  have := mul_nonneg (mul_nonneg hδ (Real.rpow_nonneg hL (2 * γ))) hP
  linarith

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

theorem ladderCells_piece_eq :
    MoleProp.ladderCells (piece N T.Y) = (MoleProp.ladderCells N).filter (fun S => S ⊆ T.Y) := by
  classical
  ext S
  simp only [MoleProp.ladderCells, mem_filter, mem_powerset, isLadderCell_piece_iff, piece_atoms T.sub]
  constructor
  · rintro ⟨hSY, hc, _⟩; exact ⟨⟨hSY.trans T.sub, hc⟩, hSY⟩
  · rintro ⟨⟨_, hc⟩, hSY⟩; exact ⟨hSY, hc, hSY⟩

/-- **Cell products across the removal.** -/
theorem cellProduct_le (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hlog : 1 ≤ Real.log L) (P P' : Finset V → ℝ)
    (hP : ∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) (hP' : ∀ S ∈ MoleProp.ladderCells T.post, 0 ≤ P' S)
    (hagree : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∉ S → P' S = P S) :
    MoleProp.cellProduct N L γ δ P ≤
      MoleProp.cellProduct (piece N T.Y) L γ δ P * MoleProp.cellProduct T.post L γ δ P' *
        (Real.log L ^ 2) ^ 6 := by
  classical
  set f := fun S => Molecule.ladderWeight L γ δ (P S) with hf
  set CN := MoleProp.ladderCells N
  have hf0 : ∀ S ∈ CN, 0 ≤ f S := fun S hS => ladderWeight_nonneg hL hδ (hP S hS)
  have hlog2 : 1 ≤ Real.log L ^ 2 := by nlinarith
  -- the three parts
  have hsplit : MoleProp.cellProduct N L γ δ P =
      (∏ S ∈ CN.filter (fun S => S ⊆ T.Y), f S) *
        ((∏ S ∈ (CN.filter fun S => ¬ S ⊆ T.Y).filter (fun S => Disjoint S T.Y ∧ T.c ∉ S), f S) *
          ∏ S ∈ (CN.filter fun S => ¬ S ⊆ T.Y).filter (fun S => ¬ (Disjoint S T.Y ∧ T.c ∉ S)), f S) := by
    unfold MoleProp.cellProduct
    rw [prod_filter_mul_prod_filter_not, prod_filter_mul_prod_filter_not]
  have h1 : ∏ S ∈ CN.filter (fun S => S ⊆ T.Y), f S = MoleProp.cellProduct (piece N T.Y) L γ δ P := by
    unfold MoleProp.cellProduct; rw [T.ladderCells_piece_eq]
  set A2 := (CN.filter fun S => ¬ S ⊆ T.Y).filter (fun S => Disjoint S T.Y ∧ T.c ∉ S)
  set A3 := (CN.filter fun S => ¬ S ⊆ T.Y).filter (fun S => ¬ (Disjoint S T.Y ∧ T.c ∉ S))
  have hA2 : A2 ⊆ MoleProp.ladderCells T.post := by
    intro S hS
    obtain ⟨hS0, hdis, hc⟩ := mem_filter.mp hS
    have hS1 := (mem_filter.mp hS0).1
    have hcell := (mem_filter.mp hS1).2
    have hpost := (T.isLadderCell_post_iff hc).mpr ⟨hcell, hdis⟩
    refine mem_filter.mpr ⟨?_, hpost⟩
    rw [mem_powerset, T.post_atoms]
    intro a ha
    exact mem_sdiff.mpr ⟨MoleProp.isLadderCell_subset_atoms N hcell ha, disjoint_left.mp hdis ha⟩
  have h2 : ∏ S ∈ A2, f S ≤ MoleProp.cellProduct T.post L γ δ P' := by
    unfold MoleProp.cellProduct
    have heq : ∏ S ∈ A2, f S = ∏ S ∈ A2, Molecule.ladderWeight L γ δ (P' S) := by
      refine prod_congr rfl fun S hS => ?_
      rw [hf, hagree S (hA2 hS) (mem_filter.mp hS).2.2]
    rw [heq, ← prod_sdiff hA2]
    have hone : 1 ≤ ∏ S ∈ MoleProp.ladderCells T.post \ A2, Molecule.ladderWeight L γ δ (P' S) := by
      calc (1 : ℝ) = ∏ _S ∈ MoleProp.ladderCells T.post \ A2, (1 : ℝ) := prod_const_one.symm
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun S hS =>
          MoleProp.ladderWeight_one_le hL hlog hδ (hP' S (mem_sdiff.mp hS).1)
    have hnn : 0 ≤ ∏ S ∈ A2, Molecule.ladderWeight L γ δ (P' S) :=
      prod_nonneg fun S hS => ladderWeight_nonneg hL hδ (hP' S (hA2 hS))
    exact le_mul_of_one_le_left hnn hone
  -- the exceptional cells
  have hA3 : A3 ⊆ (CN.filter fun S => N.atom T.x ∈ S) ∪ (CN.filter fun S => N.atom T.y ∈ S) ∪
      (CN.filter fun S => T.c ∈ S) := by
    intro S hS
    obtain ⟨hS1, hno⟩ := mem_filter.mp hS
    obtain ⟨hcell, hnsub⟩ := mem_filter.mp hS1
    by_cases hdis : Disjoint S T.Y
    · have hc : T.c ∈ S := by by_contra h; exact hno ⟨hdis, h⟩
      exact mem_union_right _ (mem_filter.mpr ⟨hcell, hc⟩)
    · have hin : ∃ a ∈ S, a ∈ T.Y := by
        by_contra h; push Not at h; exact hdis (disjoint_left.mpr h)
      have hout : ∃ a ∈ S, a ∉ T.Y := by
        by_contra h; push Not at h; exact hnsub h
      rcases T.straddle_mem_exit (mem_filter.mp hcell).2 hin hout with h | h
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hcell, h⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hcell, h⟩))
  have hcard3 : A3.card ≤ 6 := by
    refine (card_le_card hA3).trans ((card_union_le _ _).trans ?_)
    have e1 : (CN.filter fun S => N.atom T.x ∈ S).card ≤ 2 := card_cells_containing_le_two hloop hdeg _
    have e2 : (CN.filter fun S => N.atom T.y ∈ S).card ≤ 2 := card_cells_containing_le_two hloop hdeg _
    have e3 : (CN.filter fun S => T.c ∈ S).card ≤ 2 := card_cells_containing_le_two hloop hdeg _
    have := card_union_le (CN.filter fun S => N.atom T.x ∈ S) (CN.filter fun S => N.atom T.y ∈ S)
    omega
  have h3 : ∏ S ∈ A3, f S ≤ (Real.log L ^ 2) ^ 6 := by
    calc ∏ S ∈ A3, f S ≤ ∏ _S ∈ A3, Real.log L ^ 2 :=
          Finset.prod_le_prod₀ (fun S hS => hf0 S (mem_filter.mp (mem_filter.mp hS).1).1)
            (fun S _ => ladderWeight_le_log_sq L γ δ (P S))
      _ = (Real.log L ^ 2) ^ A3.card := prod_const _
      _ ≤ _ := pow_le_pow_right₀ hlog2 hcard3
  have h2n : 0 ≤ ∏ S ∈ A2, f S := prod_nonneg fun S hS => hf0 S (mem_filter.mp (mem_filter.mp hS).1).1
  have h1n : 0 ≤ MoleProp.cellProduct (piece N T.Y) L γ δ P := by
    rw [← h1]; exact prod_nonneg fun S hS => hf0 S (mem_filter.mp hS).1
  rw [hsplit, h1]
  calc MoleProp.cellProduct (piece N T.Y) L γ δ P * ((∏ S ∈ A2, f S) * ∏ S ∈ A3, f S)
      ≤ MoleProp.cellProduct (piece N T.Y) L γ δ P * (MoleProp.cellProduct T.post L γ δ P' *
          (Real.log L ^ 2) ^ 6) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h2 h3
          (prod_nonneg fun S hS => hf0 S (mem_filter.mp (mem_filter.mp hS).1).1)
          ((h2n.trans h2))) h1n
    _ = _ := by ring

end TwoExit
end WaveTurbulence.MoleProp4
