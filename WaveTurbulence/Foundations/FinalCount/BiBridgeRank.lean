/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.BiBridgeCount
import Mathlib.Tactic

/-! # Ranks and cells for a set attached by two bonds (any ends)

`χ(N) = χ(N[Y]) + χ(N ∖ Y) + 1` when the three molecules are connected, and a cell of `N` is a cell of `N[Y]`, a cell
of `N ∖ Y`, or contains an exit atom (at most four such cells).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Exits2
variable {N : Molecule V D} (T : Exits2 N)

/-- Darts: those of the piece, of the rest, and the four exit darts. -/
theorem card_darts4 :
    Fintype.card D = Fintype.card (Degen.RetainedDart N (N.atoms \ T.Y)) +
      Fintype.card (Degen.RetainedDart N T.Y) + 4 := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hin : (univ.filter fun z : D => N.atom z ∉ N.atoms \ T.Y ∧ N.atom (N.mate z) ∉ N.atoms \ T.Y) =
      univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y := by
    ext z; simp only [mem_filter, mem_univ, true_and, mem_sdiff, not_and, not_not]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1 (N.atom_mem _), h2 (N.atom_mem _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun _ => h1, fun _ => h2⟩
  rw [hin]
  have hwY : N.atom (N.mate T.x) ∉ T.Y := (mem_crossDarts.mp T.x_mem).2
  have hwY' : N.atom (N.mate T.y) ∉ T.Y := (mem_crossDarts.mp T.y_mem).2
  have hex : ({T.x, T.y, N.mate T.x, N.mate T.y} : Finset D).card = 4 := by
    have h1 : T.x ≠ N.mate T.x := fun h => (N.mate_ne T.x) h.symm
    have h2 : T.x ≠ N.mate T.y := by intro h; have := T.atom_x; rw [h] at this; exact hwY' this
    have h3 : T.y ≠ N.mate T.x := by intro h; have := T.atom_y; rw [h] at this; exact hwY this
    have h4 : T.y ≠ N.mate T.y := fun h => (N.mate_ne T.y) h.symm
    rw [card_insert_of_notMem (by simp [T.ne, h1, h2]), card_insert_of_notMem (by simp [h3, h4]),
      card_insert_of_notMem (by simp [T.mate_x_ne_mate_y]), card_singleton]
  have hex_not : ∀ z ∈ ({T.x, T.y, N.mate T.x, N.mate T.y} : Finset D),
      ¬(N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∧ ¬(N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨fun h => hwY h.2, fun h => h.1 T.atom_x⟩
    · exact ⟨fun h => hwY' h.2, fun h => h.1 T.atom_y⟩
    · rw [N.mate_mate]; exact ⟨fun h => hwY h.1, fun h => h.2 T.atom_x⟩
    · rw [N.mate_mate]; exact ⟨fun h => hwY' h.1, fun h => h.2 T.atom_y⟩
  have hpart : (univ : Finset D) = (univ.filter fun z => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∪
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) ∪ {T.x, T.y, N.mate T.x, N.mate T.y} := by
    ext z
    simp only [mem_univ, mem_union, mem_filter, true_and, mem_insert, mem_singleton, true_iff]
    rcases T.dart_cases z with h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    all_goals right; tauto
  have hd1 : Disjoint (univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y)
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) := by
    rw [disjoint_filter]; intro z _ h h'; exact h'.1 h.1
  have hd2 : Disjoint ((univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∪
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y)) {T.x, T.y, N.mate T.x, N.mate T.y} := by
    rw [disjoint_right]
    intro z hz hzf
    rcases mem_union.mp hzf with h | h
    · exact (hex_not z hz).1 (mem_filter.mp h).2
    · exact (hex_not z hz).2 (mem_filter.mp h).2
  have htot := congrArg Finset.card hpart
  rw [← card_univ, htot, card_union_of_disjoint hd2, card_union_of_disjoint hd1, hex]



theorem bonds_eq4 : N.bonds.card =
    (piece N T.Y).bonds.card + (Degen.eraseAtoms N T.Y).bonds.card + 2 := by
  have h1 := Mole.two_mul_card_bonds N
  have h2 := Mole.two_mul_card_bonds (piece N T.Y)
  have h3 := Mole.two_mul_card_bonds (Degen.eraseAtoms N T.Y)
  have h4 := T.card_darts4
  omega

theorem circuitRank_eq4 (hF : N.numComponents = 1) (hF1 : (piece N T.Y).numComponents = 1)
    (hF2 : (Degen.eraseAtoms N T.Y).numComponents = 1) :
    N.circuitRank = (piece N T.Y).circuitRank + (Degen.eraseAtoms N T.Y).circuitRank + 1 := by
  classical
  have hat : N.atoms.card = T.Y.card + (N.atoms \ T.Y).card := by
    rw [card_sdiff_of_subset T.sub]; have := card_le_card T.sub; omega
  unfold Molecule.circuitRank
  rw [T.bonds_eq4, hF, hF1, hF2, hat, piece_atoms T.sub]
  change _ = _ + (((Degen.eraseAtoms N T.Y).bonds.card : ℤ) - ((N.atoms \ T.Y).card : ℤ) + _) + 1
  push_cast
  ring

theorem ladderCells_piece_eq' :
    MoleProp.ladderCells (piece N T.Y) = (MoleProp.ladderCells N).filter (fun S => S ⊆ T.Y) := by
  classical
  ext S
  simp only [MoleProp.ladderCells, mem_filter, mem_powerset, isLadderCell_piece_iff, piece_atoms T.sub]
  constructor
  · rintro ⟨hSY, hc, _⟩; exact ⟨⟨hSY.trans T.sub, hc⟩, hSY⟩
  · rintro ⟨⟨_, hc⟩, hSY⟩; exact ⟨hSY, hc, hSY⟩

/-- **Cell products across a two-bond removal.** -/
theorem cellProduct_le4 (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hlog : 1 ≤ Real.log L) (P : Finset V → ℝ)
    (hP : ∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) :
    MoleProp.cellProduct N L γ δ P ≤
      MoleProp.cellProduct (piece N T.Y) L γ δ P * MoleProp.cellProduct (Degen.eraseAtoms N T.Y) L γ δ P *
        (Real.log L ^ 2) ^ 4 := by
  classical
  set f := fun S => Molecule.ladderWeight L γ δ (P S) with hf
  set CN := MoleProp.ladderCells N
  have hf0 : ∀ S ∈ CN, 0 ≤ f S := fun S hS => ladderWeight_nonneg hL hδ (hP S hS)
  have hlog2 : 1 ≤ Real.log L ^ 2 := by nlinarith
  have hsplit : MoleProp.cellProduct N L γ δ P =
      (∏ S ∈ CN.filter (fun S => S ⊆ T.Y), f S) *
        ((∏ S ∈ (CN.filter fun S => ¬ S ⊆ T.Y).filter (fun S => Disjoint S T.Y), f S) *
          ∏ S ∈ (CN.filter fun S => ¬ S ⊆ T.Y).filter (fun S => ¬ Disjoint S T.Y), f S) := by
    unfold MoleProp.cellProduct
    rw [prod_filter_mul_prod_filter_not, prod_filter_mul_prod_filter_not]
  have h1 : ∏ S ∈ CN.filter (fun S => S ⊆ T.Y), f S = MoleProp.cellProduct (piece N T.Y) L γ δ P := by
    unfold MoleProp.cellProduct; rw [T.ladderCells_piece_eq']
  set A2 := (CN.filter fun S => ¬ S ⊆ T.Y).filter (fun S => Disjoint S T.Y)
  set A3 := (CN.filter fun S => ¬ S ⊆ T.Y).filter (fun S => ¬ Disjoint S T.Y)
  have hA2 : A2 ⊆ MoleProp.ladderCells (Degen.eraseAtoms N T.Y) := by
    intro S hS
    obtain ⟨hS0, hdis⟩ := mem_filter.mp hS
    have hcell := (mem_filter.mp (mem_filter.mp hS0).1).2
    have hc : MoleProp.IsLadderCell (Degen.eraseAtoms N T.Y) S := (MoleProp.isLadderCell_erase_iff N T.Y S).mpr ⟨hcell, hdis⟩
    refine mem_filter.mpr ⟨?_, hc⟩
    rw [mem_powerset]
    exact MoleProp.isLadderCell_subset_atoms _ hc
  have h2 : ∏ S ∈ A2, f S ≤ MoleProp.cellProduct (Degen.eraseAtoms N T.Y) L γ δ P := by
    unfold MoleProp.cellProduct
    rw [← prod_sdiff hA2]
    have hone : 1 ≤ ∏ S ∈ MoleProp.ladderCells (Degen.eraseAtoms N T.Y) \ A2,
        Molecule.ladderWeight L γ δ (P S) := by
      calc (1 : ℝ) = ∏ _S ∈ MoleProp.ladderCells (Degen.eraseAtoms N T.Y) \ A2, (1 : ℝ) := prod_const_one.symm
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun S hS => by
          have := (MoleProp.isLadderCell_erase_iff N T.Y S).mp (mem_filter.mp (mem_sdiff.mp hS).1).2
          exact MoleProp.ladderWeight_one_le hL hlog hδ (hP S (mem_filter.mpr
            ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N this.1), this.1⟩))
    have hnn : 0 ≤ ∏ S ∈ A2, Molecule.ladderWeight L γ δ (P S) :=
      prod_nonneg fun S hS => hf0 S (mem_filter.mp (mem_filter.mp hS).1).1
    exact le_mul_of_one_le_left hnn hone
  have hA3 : A3 ⊆ (CN.filter fun S => N.atom T.x ∈ S) ∪ (CN.filter fun S => N.atom T.y ∈ S) := by
    intro S hS
    obtain ⟨hS1, hno⟩ := mem_filter.mp hS
    obtain ⟨hcell, hnsub⟩ := mem_filter.mp hS1
    have hin : ∃ a ∈ S, a ∈ T.Y := by
      by_contra h; push Not at h; exact hno (disjoint_left.mpr h)
    have hout : ∃ a ∈ S, a ∉ T.Y := by
      by_contra h; push Not at h; exact hnsub h
    rcases T.straddle_mem_exit (mem_filter.mp hcell).2 hin hout with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hcell, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hcell, h⟩)
  have hcard3 : A3.card ≤ 4 := by
    refine (card_le_card hA3).trans ((card_union_le _ _).trans ?_)
    have e1 : (CN.filter fun S => N.atom T.x ∈ S).card ≤ 2 := card_cells_containing_le_two hloop hdeg _
    have e2 : (CN.filter fun S => N.atom T.y ∈ S).card ≤ 2 := card_cells_containing_le_two hloop hdeg _
    omega
  have h3 : ∏ S ∈ A3, f S ≤ (Real.log L ^ 2) ^ 4 := by
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
      ≤ MoleProp.cellProduct (piece N T.Y) L γ δ P * (MoleProp.cellProduct (Degen.eraseAtoms N T.Y) L γ δ P *
          (Real.log L ^ 2) ^ 4) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h2 h3
          (prod_nonneg fun S hS => hf0 S (mem_filter.mp (mem_filter.mp hS).1).1)
          (h2n.trans h2)) h1n
    _ = _ := by ring

end Exits2
end WaveTurbulence.FinalCountG8
