/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PinchCells
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCellProduct
import Mathlib.Tactic

/-! # Ladders of the contracted molecule of a pinch, and its gap restriction -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Pinch
variable {N : Molecule V D} (T : Pinch N)

theorem ladderAtoms_comp_some (u v : Fin 2 → V) :
    Molecule.ladderAtoms (fun j => some (u j)) (fun j => some (v j)) = (Molecule.ladderAtoms u v).image some := by
  ext o
  simp only [Molecule.ladderAtoms, mem_union, mem_image, mem_univ, true_and]
  constructor
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨u j, Or.inl ⟨j, rfl⟩, rfl⟩
    · exact ⟨v j, Or.inr ⟨j, rfl⟩, rfl⟩
  · rintro ⟨a, (⟨j, rfl⟩ | ⟨j, rfl⟩), rfl⟩
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨j, rfl⟩

/-- A ladder of `N` inside `Y` is a ladder of the contracted molecule. -/
theorem aux_sourceLadder_of {u v : Fin 2 → V} (hY : ∀ j, u j ∈ T.Y ∧ v j ∈ T.Y) (h : Degen.SourceLadder N u v) :
    Degen.SourceLadder T.aux (fun j => some (u j)) (fun j => some (v j)) := by
  obtain ⟨h1, hinj, _, hrung, hrail⟩ := h
  refine ⟨h1, ?_, fun j => ⟨T.some_mem (hY j).1, T.some_mem (hY j).2⟩, fun j => ?_, fun j => ?_⟩
  · intro a b hab
    apply hinj
    rcases a with a | a <;> rcases b with b | b <;> simpa using hab
  · rw [T.aux_bondsBetween (hY j).1 (hY j).2]; exact hrung j
  · obtain ⟨r1, r2, r3⟩ := hrail j
    refine ⟨?_, ?_, ?_⟩
    · rw [T.aux_bondsBetween (hY _).1 (hY _).1]; exact r1
    · rw [T.aux_bondsBetween (hY _).2 (hY _).2]; exact r2
    · rw [T.aux_directed_iff (hY _).1 (hY _).1, T.aux_directed_iff (hY _).2 (hY _).2]; exact r3

/-- A ladder of the contracted molecule comes from a ladder of `N` inside `Y`. -/
theorem aux_sourceLadder_to (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) {u v : Fin 2 → Option V}
    (hL : Degen.SourceLadder T.aux u v) :
    ∃ u' v' : Fin 2 → V, u = (fun j => some (u' j)) ∧ v = (fun j => some (v' j)) ∧
      (∀ j, u' j ∈ T.Y ∧ v' j ∈ T.Y) ∧ Degen.SourceLadder N u' v' := by
  classical
  have hcell : Molecule.ladderAtoms u v ∈ MoleProp.ladderCells T.aux :=
    mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms T.aux ⟨u, v, hL, rfl⟩), ⟨u, v, hL, rfl⟩⟩
  have hnone := T.none_notMem_cell hloop hcell
  have hsome : ∀ o ∈ Molecule.ladderAtoms u v, ∃ a ∈ T.Y, o = some a := by
    intro o ho
    have hoA := MoleProp.isLadderCell_subset_atoms T.aux ⟨u, v, hL, rfl⟩ ho
    rcases T.mem_aux_atoms.mp hoA with rfl | h
    · exact absurd ho hnone
    · exact h
  have hu := fun j => hsome (u j) (mem_union_left _ (mem_image_of_mem _ (mem_univ j)))
  have hv := fun j => hsome (v j) (mem_union_right _ (mem_image_of_mem _ (mem_univ j)))
  choose u' hu'Y hu'e using hu
  choose v' hv'Y hv'e using hv
  have hue : u = fun j => some (u' j) := funext hu'e
  have hve : v = fun j => some (v' j) := funext hv'e
  refine ⟨u', v', hue, hve, fun j => ⟨hu'Y j, hv'Y j⟩, ?_⟩
  subst hue; subst hve
  obtain ⟨h1, hinj, _, hrung, hrail⟩ := hL
  refine ⟨h1, ?_, fun j => ⟨T.sub (hu'Y j), T.sub (hv'Y j)⟩, fun j => ?_, fun j => ?_⟩
  · intro a b hab
    apply hinj
    rcases a with a | a <;> rcases b with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab ⊢ <;> rw [hab]
  · rw [← T.aux_bondsBetween (hu'Y j) (hv'Y j)]; exact hrung j
  · obtain ⟨r1, r2, r3⟩ := hrail j
    refine ⟨?_, ?_, ?_⟩
    · rw [← T.aux_bondsBetween (hu'Y _) (hu'Y _)]; exact r1
    · rw [← T.aux_bondsBetween (hv'Y _) (hv'Y _)]; exact r2
    · rw [← T.aux_directed_iff (hu'Y _) (hu'Y _), ← T.aux_directed_iff (hv'Y _) (hv'Y _)]; exact r3

/-- **The cell-gap restriction passes to the contracted molecule.** -/
theorem aux_cgr (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) {d : ℕ} {L : ℝ} {P : Finset V → ℝ}
    {κ : D → (Fin d → ℤ)} (hCGR : MoleProp.CellGapRestriction N L 0 P (MoleProp.GapScale L) κ) :
    MoleProp.CellGapRestriction T.aux L 0 (auxScale P) (MoleProp.GapScale L) (MoleProp.deletedLabels N T.Y κ) := by
  intro u v hL r hr
  obtain ⟨u', v', rfl, rfl, hY, hN⟩ := T.aux_sourceLadder_to hloop hL
  obtain ⟨x, y, hxe, hye, hxa, hya, rfl⟩ := hr
  have hxa' : N.atom x.val = u' 0 := (T.aux_atom_some.mp hxa).1
  have hya' : N.atom y.val = v' 0 := (T.aux_atom_some.mp hya).1
  have hxm : N.atom (N.mate x.val) = u' 1 := by
    have : T.aux.atom (T.aux.mate x) = some (u' 1) := by
      have h := hxe
      change s(T.aux.atom x, T.aux.atom (T.aux.mate x)) = s(some (u' 0), some (u' 1)) at h
      rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exfalso; rw [hxa] at h1
        have := hN.2.1 (a₁ := .inl 0) (a₂ := .inl 1) (by simpa using Option.some_injective V h1); simp at this
    exact (T.aux_atom_some.mp this).1
  have hym : N.atom (N.mate y.val) = v' 1 := by
    have : T.aux.atom (T.aux.mate y) = some (v' 1) := by
      have h := hye
      change s(T.aux.atom y, T.aux.atom (T.aux.mate y)) = s(some (v' 0), some (v' 1)) at h
      rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exfalso; rw [hya] at h1
        have := hN.2.1 (a₁ := .inr 0) (a₂ := .inr 1) (by simpa using Option.some_injective V h1); simp at this
    exact (T.aux_atom_some.mp this).1
  have hscale : auxScale P (Molecule.ladderAtoms (fun j => some (u' j)) (fun j => some (v' j))) =
      P (Molecule.ladderAtoms u' v') := by
    unfold auxScale; rw [ladderAtoms_comp_some, preimage_image_some]
  rw [hscale]
  refine hCGR u' v' hN _ ⟨x.val, y.val, ?_, ?_, hxa', hya', rfl⟩
  · change s(N.atom x.val, N.atom (N.mate x.val)) = _; rw [hxa', hxm]; rfl
  · change s(N.atom y.val, N.atom (N.mate y.val)) = _; rw [hya', hym]; rfl

/-- **The piece's ladder factors are among those of the contracted molecule.** -/
theorem cellProduct_piece_le {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hlog : 1 ≤ Real.log L)
    (P : Finset V → ℝ) (hPa : ∀ S ∈ MoleProp.ladderCells T.aux, 0 ≤ auxScale P S) :
    MoleProp.cellProduct (piece N T.Y) L γ δ P ≤ MoleProp.cellProduct T.aux L γ δ (auxScale P) := by
  classical
  unfold MoleProp.cellProduct
  have himg : (MoleProp.ladderCells (piece N T.Y)).image (fun S => S.image some) ⊆ MoleProp.ladderCells T.aux := by
    intro S' hS'
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hS'
    obtain ⟨hcell, hSY⟩ := (isLadderCell_piece_iff S).mp (mem_filter.mp hS).2
    obtain ⟨u, v, hL', rfl⟩ := hcell
    have hY : ∀ j, u j ∈ T.Y ∧ v j ∈ T.Y := fun j =>
      ⟨hSY (mem_union_left _ (mem_image_of_mem _ (mem_univ j))),
        hSY (mem_union_right _ (mem_image_of_mem _ (mem_univ j)))⟩
    rw [← ladderAtoms_comp_some]
    exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms T.aux
      ⟨_, _, T.aux_sourceLadder_of hY hL', rfl⟩), ⟨_, _, T.aux_sourceLadder_of hY hL', rfl⟩⟩
  have heq : ∏ S ∈ MoleProp.ladderCells (piece N T.Y), Molecule.ladderWeight L γ δ (P S) =
      ∏ S' ∈ (MoleProp.ladderCells (piece N T.Y)).image (fun S => S.image some),
        Molecule.ladderWeight L γ δ (auxScale P S') := by
    rw [prod_image fun a _ b _ h => by
      have := congrArg (fun S => S.preimage some (Option.some_injective V).injOn) h
      simpa only [preimage_image_some] using this]
    refine prod_congr rfl fun S _ => ?_
    unfold auxScale; rw [preimage_image_some]
  rw [heq, ← prod_sdiff himg]
  have hone : 1 ≤ ∏ S ∈ MoleProp.ladderCells T.aux \ (MoleProp.ladderCells (piece N T.Y)).image
      (fun S => S.image some), Molecule.ladderWeight L γ δ (auxScale P S) := by
    calc (1 : ℝ) = ∏ _S ∈ MoleProp.ladderCells T.aux \ (MoleProp.ladderCells (piece N T.Y)).image
          (fun S => S.image some), (1 : ℝ) := prod_const_one.symm
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun S hS =>
          MoleProp.ladderWeight_one_le hL hlog hδ (hPa S (mem_sdiff.mp hS).1)
  have hnn : 0 ≤ ∏ S' ∈ (MoleProp.ladderCells (piece N T.Y)).image (fun S => S.image some),
      Molecule.ladderWeight L γ δ (auxScale P S') :=
    prod_nonneg fun S hS => ladderWeight_nonneg hL hδ (hPa S (himg hS))
  exact le_mul_of_one_le_left hnn hone

end Pinch
end WaveTurbulence.MoleProp4
