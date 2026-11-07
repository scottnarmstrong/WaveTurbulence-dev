/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeFiberBound
public import WaveTurbulence.Foundations.FinalCount.ErasePair
import Mathlib.Tactic

/-! # Normalization across a merge: cells and circuit rank -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

/-- `cellProduct M P ≤ cellProduct (merge M) P' · (log L)^8` when `P'` agrees with `P` away from the merged atom. -/
theorem cellProduct_le_merge (hv₂ : v₂ ∈ M.atoms) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4) {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hlog : 1 ≤ Real.log L)
    (P P' : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S)
    (hP' : ∀ S ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), 0 ≤ P' S)
    (hagree : ∀ S ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), v₁ ∉ S → P' S = P S) :
    MoleProp.cellProduct M L γ δ P ≤
      MoleProp.cellProduct (mergePair M v₁ v₂ hv₁ hne) L γ δ P' * (Real.log L ^ 2) ^ 4 := by
  classical
  set N := mergePair M v₁ v₂ hv₁ hne with hN
  set f := fun S => Molecule.ladderWeight L γ δ (P S) with hf
  have hf0 : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ f S := fun S hS => ladderWeight_nonneg hL hδ (hP S hS)
  have hlog2 : 1 ≤ Real.log L ^ 2 := by nlinarith
  have hsplit : MoleProp.cellProduct M L γ δ P =
      (∏ S ∈ (MoleProp.ladderCells M).filter (fun S => Disjoint S {v₁, v₂}), f S) *
        ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S {v₁, v₂}), f S := by
    unfold MoleProp.cellProduct
    rw [prod_filter_mul_prod_filter_not]
  -- the cells avoiding the pair are the cells of `N` avoiding `v₁`
  set A2 := (MoleProp.ladderCells N).filter (fun S => v₁ ∉ S) with hA2
  have hAeq : (MoleProp.ladderCells M).filter (fun S => Disjoint S {v₁, v₂}) = A2 := by
    ext S
    simp only [hA2, MoleProp.ladderCells, mem_filter, mem_powerset]
    constructor
    · rintro ⟨⟨hsub, hc⟩, hd⟩
      have h1 : v₁ ∉ S := fun h => (disjoint_left.mp hd h) (by simp)
      have h2 : v₂ ∉ S := fun h => (disjoint_left.mp hd h) (by simp)
      refine ⟨⟨fun a ha => mem_erase.mpr ⟨fun e => h2 (e ▸ ha), hsub ha⟩, ?_⟩, h1⟩
      exact (isLadderCell_merge_iff (hv₁ := hv₁) (hne := hne) h1 h2).mpr hc
    · rintro ⟨⟨hsub, hc⟩, h1⟩
      have h2 : v₂ ∉ S := fun h => (mem_erase.mp (hsub h)).1 rfl
      refine ⟨⟨fun a ha => (mem_erase.mp (hsub ha)).2, ?_⟩, ?_⟩
      · exact (isLadderCell_merge_iff (hv₁ := hv₁) (hne := hne) h1 h2).mp hc
      · rw [disjoint_left]
        intro a haS ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact h1 haS
        · exact h2 haS
  have h2 : ∏ S ∈ A2, f S ≤ MoleProp.cellProduct N L γ δ P' := by
    unfold MoleProp.cellProduct
    have heq : ∏ S ∈ A2, f S = ∏ S ∈ A2, Molecule.ladderWeight L γ δ (P' S) := by
      refine prod_congr rfl fun S hS => ?_
      rw [hf, hagree S (mem_filter.mp hS).1 (mem_filter.mp hS).2]
    rw [heq, ← prod_sdiff (show A2 ⊆ MoleProp.ladderCells N from filter_subset _ _)]
    have hone : 1 ≤ ∏ S ∈ MoleProp.ladderCells N \ A2, Molecule.ladderWeight L γ δ (P' S) := by
      calc (1 : ℝ) = ∏ _S ∈ MoleProp.ladderCells N \ A2, (1 : ℝ) := prod_const_one.symm
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun S hS =>
          MoleProp.ladderWeight_one_le hL hlog hδ (hP' S (mem_sdiff.mp hS).1)
    have hnn : 0 ≤ ∏ S ∈ A2, Molecule.ladderWeight L γ δ (P' S) :=
      prod_nonneg fun S hS => ladderWeight_nonneg hL hδ (hP' S (mem_filter.mp hS).1)
    exact le_mul_of_one_le_left hnn hone
  have hcard : ((MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S {v₁, v₂})).card ≤ 4 := by
    have hsub : (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S {v₁, v₂}) ⊆
        ({v₁, v₂} : Finset V).biUnion fun c => (MoleProp.ladderCells M).filter fun S => c ∈ S := by
      intro S hS
      obtain ⟨hSC, hnd⟩ := mem_filter.mp hS
      obtain ⟨c, hcS, hcY⟩ := Finset.not_disjoint_iff.mp hnd
      exact mem_biUnion.mpr ⟨c, hcY, mem_filter.mpr ⟨hSC, hcS⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ c ∈ ({v₁, v₂} : Finset V), ((MoleProp.ladderCells M).filter fun S => c ∈ S).card
        ≤ ∑ _c ∈ ({v₁, v₂} : Finset V), 2 :=
          sum_le_sum fun c _ => card_cells_containing_le_two hloop hdeg c
      _ = 2 * ({v₁, v₂} : Finset V).card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 4 := by have := card_le_two (a := v₁) (b := v₂); omega
  have h3 : ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S {v₁, v₂}), f S ≤ (Real.log L ^ 2) ^ 4 := by
    calc ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S {v₁, v₂}), f S
        ≤ ∏ _S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S {v₁, v₂}), Real.log L ^ 2 :=
          prod_le_prod₀ (fun S hS => hf0 S (mem_filter.mp hS).1) fun S _ => ladderWeight_le_log_sq L γ δ (P S)
      _ = (Real.log L ^ 2) ^ ((MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S {v₁, v₂})).card := prod_const _
      _ ≤ (Real.log L ^ 2) ^ 4 := pow_le_pow_right₀ hlog2 hcard
  have hc : 0 ≤ MoleProp.cellProduct N L γ δ P' := by
    unfold MoleProp.cellProduct
    exact prod_nonneg fun S hS => ladderWeight_nonneg hL hδ (hP' S hS)
  rw [hsplit, hAeq]
  calc (∏ S ∈ A2, f S) * ∏ S ∈ (MoleProp.ladderCells M).filter (fun S => ¬ Disjoint S {v₁, v₂}), f S
      ≤ MoleProp.cellProduct N L γ δ P' * (Real.log L ^ 2) ^ 4 :=
        mul_le_mul h2 h3 (prod_nonneg fun S hS => hf0 S (mem_filter.mp hS).1) hc

end MergeSum
end WaveTurbulence.FinalCountG8
