/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeCount
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
import Mathlib.Tactic

/-! # DH23 per-position ladder factors in the relaxed-charge counting problem

A cell is one actual pair of consecutive double rungs and its two rails.
Its parameter is a separate P at that position, as required at DH23 L1831;
no zero-charge equation or conservation of gaps along the ladder is assumed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The literal selected-rung/rail cells, allowing additional end chords. -/
def IsLadderCell (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ u v : Fin 2 → V, Degen.SourceLadder M u v ∧ Molecule.ladderAtoms u v = S

noncomputable def ladderCells (M : Molecule V D) : Finset (Finset V) := by
  classical
  exact M.atoms.powerset.filter (IsLadderCell M)

noncomputable def cellProduct (M : Molecule V D) (L γ δ : ℝ) (P : Finset V → ℝ) : ℝ :=
  ∏ S ∈ ladderCells M, Molecule.ladderWeight L γ δ (P S)

/-- DH23 def A, with unrestricted c and a separate factor for each ladder position. -/
noncomputable def countAFree (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) : ℝ≥0∞ :=
  (countEFree M L γ δ w Adm : ℝ≥0∞) * ENNReal.ofReal
    (L ^ (-((d : ℝ) - γ) * M.circuitRank) *
      (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank * cellProduct M L γ δ P)

/-- The source-prescribed dyadic (or zero) scale is imposed on each actual cell gap. -/
def CellGapRestriction (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d)
    (P : Finset V → ℝ) (R : ℝ → ℝ → Prop) (κ : D → (Fin d → ℤ)) : Prop :=
  ∀ (u v : Fin 2 → V) (h : Degen.SourceLadder M u v) (r : Mom d),
    M.IsLadderGap L w κ u v h.1 r → R (P (Molecule.ladderAtoms u v)) ‖r‖

theorem isLadderCell_subset_atoms (M : Molecule V D) {S : Finset V} (h : IsLadderCell M S) :
    S ⊆ M.atoms := by
  obtain ⟨u,v,h,rfl⟩ := h
  exact Degen.sourceLadderSet_atoms_subset M ⟨1,u,v,h,rfl⟩

theorem isLadderCell_erase_iff (M : Molecule V D) (Y S : Finset V) :
    IsLadderCell (Degen.eraseAtoms M Y) S ↔ IsLadderCell M S ∧ Disjoint S Y := by
  classical
  constructor
  · rintro ⟨u,v,h,rfl⟩
    have hset : Degen.SourceLadderSet (Degen.eraseAtoms M Y) (Molecule.ladderAtoms u v) := ⟨1,u,v,h,rfl⟩
    obtain ⟨_,hdis⟩ := (Degen.sourceLadderSet_erase_iff M Y _).mp hset
    have hn : ∀ i, u i ∉ Y ∧ v i ∉ Y := by
      intro i
      exact ⟨fun hi => disjoint_left.mp hdis (mem_union_left _ (mem_image_of_mem u (mem_univ i))) hi,
        fun hi => disjoint_left.mp hdis (mem_union_right _ (mem_image_of_mem v (mem_univ i))) hi⟩
    exact ⟨⟨u,v,(Degen.sourceLadder_erase_iff M Y u v hn).mp h,rfl⟩,hdis⟩
  · rintro ⟨⟨u,v,h,rfl⟩,hdis⟩
    have hn : ∀ i, u i ∉ Y ∧ v i ∉ Y := by
      intro i
      exact ⟨fun hi => disjoint_left.mp hdis (mem_union_left _ (mem_image_of_mem u (mem_univ i))) hi,
        fun hi => disjoint_left.mp hdis (mem_union_right _ (mem_image_of_mem v (mem_univ i))) hi⟩
    exact ⟨u,v,(Degen.sourceLadder_erase_iff M Y u v hn).mpr h,rfl⟩

theorem ladderCells_erase_eq_filter (M : Molecule V D) (Y : Finset V) :
    ladderCells (Degen.eraseAtoms M Y) = (ladderCells M).filter (fun S => Disjoint S Y) := by
  classical
  ext S
  simp only [ladderCells,mem_filter,mem_powerset,isLadderCell_erase_iff]
  constructor
  · rintro ⟨hsub,h,hdis⟩
    exact ⟨⟨isLadderCell_subset_atoms M h,h⟩,hdis⟩
  · rintro ⟨⟨hsub,h⟩,hdis⟩
    refine ⟨?_,h,hdis⟩
    intro x hx
    exact mem_sdiff.mpr ⟨hsub hx,fun hxy => disjoint_left.mp hdis hx hxy⟩

theorem cellGapRestriction_erase (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d)
    (Y : Finset V) (P : Finset V → ℝ) (R : ℝ → ℝ → Prop)
    {κ : D → (Fin d → ℤ)} (hκ : CellGapRestriction M L w P R κ) :
    CellGapRestriction (Degen.eraseAtoms M Y) L w P R (fun x => κ x.val) := by
  intro u v h r hr
  have hs : Degen.SourceLadderSet (Degen.eraseAtoms M Y) (Molecule.ladderAtoms u v) := ⟨1,u,v,h,rfl⟩
  have hd := ((Degen.sourceLadderSet_erase_iff M Y _).mp hs).2
  have hn : ∀ i, u i ∉ Y ∧ v i ∉ Y := by
    intro i
    exact ⟨fun hi => disjoint_left.mp hd (mem_union_left _ (mem_image_of_mem u (mem_univ i))) hi,
      fun hi => disjoint_left.mp hd (mem_union_right _ (mem_image_of_mem v (mem_univ i))) hi⟩
  have hOld := (Degen.sourceLadder_erase_iff M Y u v hn).mp h
  exact hκ u v hOld r ((Degen.isLadderGap_erase_iff M Y L w κ u v h.1 hn r).mp hr)

end WaveTurbulence.MoleProp
