/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeCells
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitScaleFamily
import Mathlib.Tactic

/-! # Gap scales for the cells of the merged molecule through the merged atom

As `TwoExit.scaleFamily`: the cells of `mergePair M v₁ v₂` avoiding `v₁` are cells of `M` with the same gaps and keep the
scales `P`; the at most two cells through `v₁` get a dyadic scale fitting the gap (a good cell has a well-defined gap norm).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

theorem isLadderCell_merge_iff {S : Finset V} (hS1 : v₁ ∉ S) (hS2 : v₂ ∉ S) :
    MoleProp.IsLadderCell (mergePair M v₁ v₂ hv₁ hne) S ↔ MoleProp.IsLadderCell M S := by
  have hmem : ∀ (u v : Fin 2 → V) j, u j ∈ Molecule.ladderAtoms u v ∧ v j ∈ Molecule.ladderAtoms u v := fun u v j =>
    ⟨mem_union_left _ (mem_image_of_mem _ (mem_univ j)), mem_union_right _ (mem_image_of_mem _ (mem_univ j))⟩
  constructor
  · rintro ⟨u, v, h, rfl⟩
    refine ⟨u, v, (sourceLadder_merge_iff (hv₁ := hv₁) (hne := hne) u v (fun j => ?_)).mp h, rfl⟩
    exact ⟨fun e => hS1 (e ▸ (hmem u v j).1), fun e => hS2 (e ▸ (hmem u v j).1),
      fun e => hS1 (e ▸ (hmem u v j).2), fun e => hS2 (e ▸ (hmem u v j).2)⟩
  · rintro ⟨u, v, h, rfl⟩
    refine ⟨u, v, (sourceLadder_merge_iff (hv₁ := hv₁) (hne := hne) u v (fun j => ?_)).mpr h, rfl⟩
    exact ⟨fun e => hS1 (e ▸ (hmem u v j).1), fun e => hS2 (e ▸ (hmem u v j).1),
      fun e => hS1 (e ▸ (hmem u v j).2), fun e => hS2 (e ▸ (hmem u v j).2)⟩

/-- The cells of the merged molecule through the merged atom. -/
noncomputable def cellsW (M : Molecule V D) (v₁ v₂ : V) (hv₁ : v₁ ∈ M.atoms) (hne : v₁ ≠ v₂) : Finset (Finset V) :=
  (MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne)).filter fun S => v₁ ∈ S

/-- The scale functions: a dyadic scale on each cell through the merged atom, `P` elsewhere. -/
noncomputable def scaleFam (M : Molecule V D) (v₁ v₂ : V) (hv₁ : v₁ ∈ M.atoms) (hne : v₁ ≠ v₂) (L : ℝ)
    (P : Finset V → ℝ) : Finset (Finset V → ℝ) := by
  classical
  exact ((cellsW M v₁ v₂ hv₁ hne).pi fun _ => scaleSet L).image
    fun σ S => if h : S ∈ cellsW M v₁ v₂ hv₁ hne then σ S h else P S

theorem scaleFam_nonneg {L : ℝ} {P P' : Finset V → ℝ} (hP' : P' ∈ scaleFam M v₁ v₂ hv₁ hne L P)
    (hP : ∀ S ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), v₁ ∉ S → 0 ≤ P S) :
    ∀ S ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), 0 ≤ P' S := by
  classical
  unfold scaleFam at hP'
  obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hP'
  intro S hS
  by_cases hc : S ∈ cellsW M v₁ v₂ hv₁ hne
  · simp only [hc, ↓reduceDIte]; exact scaleSet_nonneg (mem_pi.mp hσ S hc)
  · simp only [hc, ↓reduceDIte]
    exact hP S hS fun h => hc (mem_filter.mpr ⟨hS, h⟩)

theorem scaleFam_agree {L : ℝ} {P P' : Finset V → ℝ} (hP' : P' ∈ scaleFam M v₁ v₂ hv₁ hne L P) :
    ∀ S ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), v₁ ∉ S → P' S = P S := by
  classical
  unfold scaleFam at hP'
  obtain ⟨σ, _, rfl⟩ := mem_image.mp hP'
  intro S _ hc
  have : S ∉ cellsW M v₁ v₂ hv₁ hne := fun h => hc (mem_filter.mp h).2
  simp only [this, ↓reduceDIte]

theorem card_scaleFam_le (hloopN : ∀ z, (mergePair M v₁ v₂ hv₁ hne).atom z ≠ (mergePair M v₁ v₂ hv₁ hne).atom
      ((mergePair M v₁ v₂ hv₁ hne).mate z))
    (hdegN : ∀ a ∈ (mergePair M v₁ v₂ hv₁ hne).atoms, (mergePair M v₁ v₂ hv₁ hne).deg a ≤ 4) (L : ℝ)
    (P : Finset V → ℝ) : (scaleFam M v₁ v₂ hv₁ hne L P).card ≤ (scaleSet L).card ^ 2 := by
  classical
  unfold scaleFam
  refine card_image_le.trans ?_
  rw [card_pi, prod_const]
  have hc : (cellsW M v₁ v₂ hv₁ hne).card ≤ 2 := card_cells_containing_le_two hloopN hdegN v₁
  have h1 : 1 ≤ (scaleSet L).card := card_pos.mpr ⟨0, by simp [scaleSet]⟩
  exact pow_le_pow_right₀ h1 hc

/-- If neither end of a dart of the merged molecule is the merged atom, its ends are those of the underlying dart. -/
theorem ends_N_eq (z : OffPair M v₁ v₂) (h : v₁ ∉ (mergePair M v₁ v₂ hv₁ hne).ends z) :
    M.ends z.val = (mergePair M v₁ v₂ hv₁ hne).ends z := by
  have hnm : ∀ a : V, mergeMap v₁ v₂ a ≠ v₁ → mergeMap v₁ v₂ a = a := by
    intro a ha
    exact Merge.mergeMap_of_ne (fun e => ha (by rw [e, mergeMap, if_pos rfl]))
  have h1 : mergeMap v₁ v₂ (M.atom z.val) ≠ v₁ := fun e => h (by
    have hm : (mergePair M v₁ v₂ hv₁ hne).atom z ∈ (mergePair M v₁ v₂ hv₁ hne).ends z := Sym2.mem_mk_left _ _
    have : (mergePair M v₁ v₂ hv₁ hne).atom z = v₁ := e
    rw [this] at hm; exact hm)
  have h2 : mergeMap v₁ v₂ (M.atom (M.mate z.val)) ≠ v₁ := fun e => h (by
    have hm : (mergePair M v₁ v₂ hv₁ hne).atom ((mergePair M v₁ v₂ hv₁ hne).mate z) ∈
        (mergePair M v₁ v₂ hv₁ hne).ends z := Sym2.mem_mk_right _ _
    have : (mergePair M v₁ v₂ hv₁ hne).atom ((mergePair M v₁ v₂ hv₁ hne).mate z) = v₁ := e
    rw [this] at hm; exact hm)
  unfold Molecule.ends
  change s(M.atom z.val, M.atom (M.mate z.val)) = s(mergeMap v₁ v₂ (M.atom z.val), mergeMap v₁ v₂ (M.atom (M.mate z.val)))
  rw [hnm _ h1, hnm _ h2]

/-- **The restricted decoration satisfies the cell-gap restriction for some scale function of the family.** -/
theorem exists_mergeFam_cgr (hloopN : ∀ z, (mergePair M v₁ v₂ hv₁ hne).atom z ≠ (mergePair M v₁ v₂ hv₁ hne).atom
      ((mergePair M v₁ v₂ hv₁ hne).mate z))
    (hdegN : ∀ a ∈ (mergePair M v₁ v₂ hv₁ hne).atoms, (mergePair M v₁ v₂ hv₁ hne).deg a ≤ 4)
    (hopen : ∀ S ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), v₁ ∈ S →
      GoodCell (mergePair M v₁ v₂ hv₁ hne) S) {L : ℝ} (hL : 1 ≤ L) {d : ℕ} {P : Finset V → ℝ}
    {κ : D → (Fin d → ℤ)} (hb : ∀ z, κ (M.mate z) = κ z)
    (hCGR : MoleProp.CellGapRestriction M L 0 P (MoleProp.GapScale L) κ) :
    ∃ P' ∈ scaleFam M v₁ v₂ hv₁ hne L P, MoleProp.CellGapRestriction (mergePair M v₁ v₂ hv₁ hne) L 0 P'
      (MoleProp.GapScale L) (fun y => κ y.val) := by
  classical
  have hLp : 0 < L := by linarith
  set N := mergePair M v₁ v₂ hv₁ hne with hN
  set κ' : OffPair M v₁ v₂ → (Fin d → ℤ) := fun y => κ y.val with hκ'
  have hb' : ∀ z, κ' (N.mate z) = κ' z := fun z => hb z.val
  have hex : ∀ S ∈ cellsW M v₁ v₂ hv₁ hne, ∃ P0 ∈ scaleSet L, ∀ (u v : Fin 2 → V) (h : Degen.SourceLadder N u v),
      Molecule.ladderAtoms u v = S → ∀ r, N.IsLadderGap L 0 κ' u v h.1 r → MoleProp.GapScale L P0 ‖r‖ := by
    intro S hS
    obtain ⟨hS1, hcS⟩ := mem_filter.mp hS
    obtain ⟨_, u0, v0, h0, hS0⟩ := mem_filter.mp hS1
    have hinj := h0.2.1
    have hu : u0 0 ≠ u0 1 := fun e => by have := hinj (a₁ := .inl 0) (a₂ := .inl 1) e; simp at this
    have hv : v0 0 ≠ v0 1 := fun e => by have := hinj (a₁ := .inr 0) (a₂ := .inr 1) e; simp at this
    obtain ⟨su, sv, _⟩ := h0.2.2.2.2 0
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at su sv
    obtain ⟨x, hx⟩ : (Degen.neighborDarts N (u0 0) (u0 1)).Nonempty := by
      rw [← card_pos, Degen.card_neighborDarts _ hu, su]; norm_num
    obtain ⟨y, hy⟩ : (Degen.neighborDarts N (v0 0) (v0 1)).Nonempty := by
      rw [← card_pos, Degen.card_neighborDarts _ hv, sv]; norm_num
    obtain ⟨hxa, hxm⟩ := (Degen.mem_neighborDarts _ _ _ _).mp hx
    obtain ⟨hya, hym⟩ := (Degen.mem_neighborDarts _ _ _ _).mp hy
    have hr0 : N.IsLadderGap L 0 κ' u0 v0 h0.1 (Molecule.gapAt L 0 κ' x y) :=
      ⟨x, y, by change s(_, _) = _; rw [hxa, hxm]; rfl, by change s(_, _) = _; rw [hya, hym]; rfl, hxa, hya, rfl⟩
    have hcase := gap_norm_cases hLp κ' x y
    obtain ⟨P0, hP0, hgs⟩ := exists_scale hL (by
      rcases hcase with h | h
      · left; exact h
      · right; exact h)
    refine ⟨P0, hP0, fun u v h hSu r hr => ?_⟩
    have heq := cell_gap_norm_eq_of_good hloopN hdegN hb' h0 h (hSu.trans hS0.symm)
      (by rw [hS0]; exact hopen S hS1 hcS) hr0 hr
    rw [← heq]
    exact hgs
  let σ : (S : Finset V) → S ∈ cellsW M v₁ v₂ hv₁ hne → ℝ := fun S hS => Classical.choose (hex S hS)
  have hσ : ∀ S hS, σ S hS ∈ scaleSet L ∧ _ := fun S hS => Classical.choose_spec (hex S hS)
  refine ⟨fun S => if h : S ∈ cellsW M v₁ v₂ hv₁ hne then σ S h else P S,
    mem_image.mpr ⟨σ, mem_pi.mpr fun S hS => (hσ S hS).1, rfl⟩, ?_⟩
  intro u v h r hr
  have hScell : Molecule.ladderAtoms u v ∈ MoleProp.ladderCells N := by
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ⟨u, v, h, rfl⟩⟩
    exact MoleProp.isLadderCell_subset_atoms N ⟨u, v, h, rfl⟩
  by_cases hcS : v₁ ∈ Molecule.ladderAtoms u v
  · have hmem : Molecule.ladderAtoms u v ∈ cellsW M v₁ v₂ hv₁ hne := mem_filter.mpr ⟨hScell, hcS⟩
    simp only [hmem, ↓reduceDIte]
    exact (hσ _ hmem).2 u v h rfl r hr
  · have hmem : Molecule.ladderAtoms u v ∉ cellsW M v₁ v₂ hv₁ hne := fun hm => hcS (mem_filter.mp hm).2
    simp only [hmem, ↓reduceDIte]
    have hmemu : ∀ j, u j ∈ Molecule.ladderAtoms u v := fun j => mem_union_left _ (mem_image_of_mem _ (mem_univ j))
    have hmemv : ∀ j, v j ∈ Molecule.ladderAtoms u v := fun j => mem_union_right _ (mem_image_of_mem _ (mem_univ j))
    have hnot : ∀ j, u j ≠ v₁ ∧ u j ≠ v₂ ∧ v j ≠ v₁ ∧ v j ≠ v₂ := by
      intro j
      exact ⟨fun e => hcS (e ▸ hmemu j), (mem_erase.mp (h.2.2.1 j).1).1, fun e => hcS (e ▸ hmemv j),
        (mem_erase.mp (h.2.2.1 j).2).1⟩
    have hM : Degen.SourceLadder M u v := (sourceLadder_merge_iff (hv₁ := hv₁) (hne := hne) u v hnot).mp h
    obtain ⟨x, y, hxe, hye, hxa, hya, hr⟩ := hr
    have hxv : v₁ ∉ N.ends x := by
      rw [hxe]; intro hm
      rcases Sym2.mem_iff.mp hm with e | e
      · exact (hnot 0).1 e.symm
      · exact (hnot ⟨1, by omega⟩).1 e.symm
    have hyv : v₁ ∉ N.ends y := by
      rw [hye]; intro hm
      rcases Sym2.mem_iff.mp hm with e | e
      · exact (hnot 0).2.2.1 e.symm
      · exact (hnot ⟨1, by omega⟩).2.2.1 e.symm
    refine hCGR u v hM r ⟨x.val, y.val, ?_, ?_, ?_, ?_, hr⟩
    · rw [ends_N_eq x hxv]; exact hxe
    · rw [ends_N_eq y hyv]; exact hye
    · exact (atom_N_iff x (hnot 0).1 (hnot 0).2.1).mp hxa
    · exact (atom_N_iff y (hnot 0).2.2.1 (hnot 0).2.2.2).mp hya

end MergeSum
end WaveTurbulence.FinalCountG8
