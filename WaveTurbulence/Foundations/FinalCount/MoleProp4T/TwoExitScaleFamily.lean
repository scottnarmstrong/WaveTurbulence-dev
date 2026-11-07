/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCellProduct
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitDecor
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Scales
import Mathlib.Tactic

/-! # Gap scales for the cells of the post molecule through `c`

The cells of the post molecule avoiding `c` are cells of `N` with the same gaps, so they keep the scales `P`. The at
most two cells through `c` get a dyadic scale (`scaleSet`) fitting the gap of the transported decoration. This needs
the gap to be independent of the parametrization, which holds for open cells (`cell_gap_norm_eq_of_good`). The
resulting scale functions form a family of at most `|scaleSet|²` functions, independent of the decoration.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem latticePoint_sub' {d : ℕ} (L : ℝ) (m n : Fin d → ℤ) :
    latticePoint L (m - n) = latticePoint L m - latticePoint L n := by
  ext i
  simp only [latticePoint, PiLp.sub_apply, Pi.sub_apply, Int.cast_sub]
  ring

/-- A nonzero lattice point of `ℤ_L^d` has norm at least `L⁻¹`. -/
theorem inv_le_norm_latticePoint {d : ℕ} {L : ℝ} (hL : 0 < L) {n : Fin d → ℤ} (hn : n ≠ 0) :
    L⁻¹ ≤ ‖latticePoint L n‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  have h1 : |(latticePoint L n) i| ≤ ‖latticePoint L n‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L n) i
  have h2 : (latticePoint L n) i = (n i : ℝ) / L := rfl
  have h3 : (1 : ℝ) ≤ |(n i : ℝ)| := by
    have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast this
  rw [h2, abs_div, abs_of_pos hL] at h1
  calc L⁻¹ = 1 / L := (one_div L).symm
    _ ≤ |(n i : ℝ)| / L := div_le_div_of_nonneg_right h3 hL.le
    _ ≤ _ := h1

/-- The norm of a difference of lattice vectors is `0` or at least `L⁻¹`. -/
theorem gap_norm_cases {d : ℕ} {L : ℝ} (hL : 0 < L) {E : Type*} (κ : E → (Fin d → ℤ)) (x y : E) :
    ‖Molecule.kvec L 0 κ x - Molecule.kvec L 0 κ y‖ = 0 ∨
      L⁻¹ ≤ ‖Molecule.kvec L 0 κ x - Molecule.kvec L 0 κ y‖ := by
  simp only [Molecule.kvec, zero_add]
  rw [← latticePoint_sub']
  by_cases h : κ x - κ y = 0
  · left
    have h0 : latticePoint L (0 : Fin d → ℤ) = 0 := by ext i; simp [latticePoint]
    rw [h, h0, norm_zero]
  · right; exact inv_le_norm_latticePoint hL h

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- The cells of the post molecule through `c`. -/
noncomputable def cellsThroughC : Finset (Finset V) := (MoleProp.ladderCells T.post).filter fun S => T.c ∈ S

/-- The scale functions: a dyadic scale on each cell through `c`, `P` elsewhere. -/
noncomputable def scaleFamily (L : ℝ) (P : Finset V → ℝ) : Finset (Finset V → ℝ) := by
  classical
  exact (T.cellsThroughC.pi fun _ => scaleSet L).image fun σ S => if h : S ∈ T.cellsThroughC then σ S h else P S

theorem card_scaleFamily_le (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (L : ℝ) (P : Finset V → ℝ) : (T.scaleFamily L P).card ≤ (scaleSet L).card ^ 2 := by
  classical
  unfold scaleFamily
  refine card_image_le.trans ?_
  rw [card_pi, prod_const]
  have hc : T.cellsThroughC.card ≤ 2 := by
    unfold cellsThroughC
    refine card_cells_containing_le_two (T.post_loop_free hloop) (fun a ha => ?_) T.c
    rw [T.post_atoms] at ha
    rw [T.post_deg (mem_sdiff.mp ha).2]
    exact hdeg a (mem_sdiff.mp ha).1
  have h1 : 1 ≤ (scaleSet L).card := card_pos.mpr ⟨0, by simp [scaleSet]⟩
  exact pow_le_pow_right₀ h1 hc

theorem scaleFamily_nonneg {L : ℝ} {P : Finset V → ℝ} {P' : Finset V → ℝ} (hP' : P' ∈ T.scaleFamily L P)
    (hP : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∉ S → 0 ≤ P S) :
    ∀ S ∈ MoleProp.ladderCells T.post, 0 ≤ P' S := by
  classical
  unfold scaleFamily at hP'
  obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hP'
  intro S hS
  by_cases hc : S ∈ T.cellsThroughC
  · simp only [hc, ↓reduceDIte]; exact scaleSet_nonneg (mem_pi.mp hσ S hc)
  · simp only [hc, ↓reduceDIte]
    exact hP S hS fun h => hc (mem_filter.mpr ⟨hS, h⟩)

theorem scaleFamily_agree {L : ℝ} {P P' : Finset V → ℝ} (hP' : P' ∈ T.scaleFamily L P) :
    ∀ S ∈ MoleProp.ladderCells T.post, T.c ∉ S → P' S = P S := by
  classical
  unfold scaleFamily at hP'
  obtain ⟨σ, _, rfl⟩ := mem_image.mp hP'
  intro S _ hc
  have : S ∉ T.cellsThroughC := fun h => hc (mem_filter.mp h).2
  simp only [this, ↓reduceDIte]

theorem postLabels_mate {d : ℕ} {κ : D → (Fin d → ℤ)} (hb : ∀ z, κ (N.mate z) = κ z) (g : ℤ) :
    ∀ z, T.postLabels κ g (T.post.mate z) = T.postLabels κ g z := by
  rintro (z | t)
  · exact hb z.val
  · rfl

/-- A ladder rail of the post molecule avoiding `c` is a dart of `N`. -/
theorem rail_dart_inl {a b : V} (hc : T.c ≠ a ∧ T.c ≠ b) {x : Degen.RetainedDart N T.Y ⊕ Bool}
    (hx : T.post.ends x = s(a, b)) : ∃ z, x = Sum.inl z := by
  rcases x with z | t
  · exact ⟨z, rfl⟩
  · exfalso
    cases t
    · have h : s(T.c, T.d) = s(a, b) := hx
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hc.1 h1
      · exact hc.2 h1
    · have h : s(T.d, T.c) = s(a, b) := hx
      rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact hc.2 h2
      · exact hc.1 h2

/-- **The transported decoration satisfies the cell-gap restriction for some scale function of the family.** -/
theorem exists_scaleFamily_cgr (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) {L : ℝ} (hL : 1 ≤ L) {d : ℕ}
    {P : Finset V → ℝ} {κ : D → (Fin d → ℤ)} (hb : ∀ z, κ (N.mate z) = κ z)
    (hCGR : MoleProp.CellGapRestriction N L 0 P (MoleProp.GapScale L) κ) (g : ℤ) :
    ∃ P' ∈ T.scaleFamily L P, MoleProp.CellGapRestriction T.post L 0 P' (MoleProp.GapScale L) (T.postLabels κ g) := by
  classical
  have hLp : 0 < L := by linarith
  set κ' := T.postLabels κ g
  have hb' := T.postLabels_mate hb g
  have hloop' := T.post_loop_free hloop
  have hdeg' : ∀ a ∈ T.post.atoms, T.post.deg a ≤ 4 := fun a ha => by
    rw [T.post_atoms] at ha; rw [T.post_deg (mem_sdiff.mp ha).2]; exact hdeg a (mem_sdiff.mp ha).1
  -- a scale for every cell through `c`
  have hex : ∀ S ∈ T.cellsThroughC, ∃ P0 ∈ scaleSet L, ∀ (u v : Fin 2 → V) (h : Degen.SourceLadder T.post u v),
      Molecule.ladderAtoms u v = S → ∀ r, T.post.IsLadderGap L 0 κ' u v h.1 r → MoleProp.GapScale L P0 ‖r‖ := by
    intro S hS
    obtain ⟨hS1, hcS⟩ := mem_filter.mp hS
    obtain ⟨_, u0, v0, h0, hS0⟩ := mem_filter.mp hS1
    have hinj := h0.2.1
    have hu : u0 0 ≠ u0 1 := fun e => by have := hinj (a₁ := .inl 0) (a₂ := .inl 1) e; simp at this
    have hv : v0 0 ≠ v0 1 := fun e => by have := hinj (a₁ := .inr 0) (a₂ := .inr 1) e; simp at this
    obtain ⟨su, sv, _⟩ := h0.2.2.2.2 0
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at su sv
    obtain ⟨x, hx⟩ : (Degen.neighborDarts T.post (u0 0) (u0 1)).Nonempty := by
      rw [← card_pos, Degen.card_neighborDarts _ hu, su]; norm_num
    obtain ⟨y, hy⟩ : (Degen.neighborDarts T.post (v0 0) (v0 1)).Nonempty := by
      rw [← card_pos, Degen.card_neighborDarts _ hv, sv]; norm_num
    obtain ⟨hxa, hxm⟩ := (Degen.mem_neighborDarts _ _ _ _).mp hx
    obtain ⟨hya, hym⟩ := (Degen.mem_neighborDarts _ _ _ _).mp hy
    have hr0 : T.post.IsLadderGap L 0 κ' u0 v0 h0.1 (Molecule.gapAt L 0 κ' x y) :=
      ⟨x, y, by change s(_, _) = _; rw [hxa, hxm]; rfl, by change s(_, _) = _; rw [hya, hym]; rfl, hxa, hya, rfl⟩
    have hcase := gap_norm_cases hLp κ' x y
    obtain ⟨P0, hP0, hgs⟩ := exists_scale hL (by
      rcases hcase with h | h
      · left; exact h
      · right; exact h)
    refine ⟨P0, hP0, fun u v h hSu r hr => ?_⟩
    have heq := cell_gap_norm_eq_of_good hloop' hdeg' hb' h0 h (hSu.trans hS0.symm)
      (by rw [hS0]; exact hopen S hS1 hcS) hr0 hr
    rw [← heq]
    exact hgs
  let σ : (S : Finset V) → S ∈ T.cellsThroughC → ℝ := fun S hS => Classical.choose (hex S hS)
  have hσ : ∀ S hS, σ S hS ∈ scaleSet L ∧ _ := fun S hS => Classical.choose_spec (hex S hS)
  refine ⟨fun S => if h : S ∈ T.cellsThroughC then σ S h else P S,
    mem_image.mpr ⟨σ, mem_pi.mpr fun S hS => (hσ S hS).1, rfl⟩, ?_⟩
  intro u v h r hr
  have hScell : Molecule.ladderAtoms u v ∈ MoleProp.ladderCells T.post := by
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ⟨u, v, h, rfl⟩⟩
    exact MoleProp.isLadderCell_subset_atoms T.post ⟨u, v, h, rfl⟩
  by_cases hcS : T.c ∈ Molecule.ladderAtoms u v
  · have hmem : Molecule.ladderAtoms u v ∈ T.cellsThroughC := mem_filter.mpr ⟨hScell, hcS⟩
    simp only [hmem, ↓reduceDIte]
    exact (hσ _ hmem).2 u v h rfl r hr
  · have hmem : Molecule.ladderAtoms u v ∉ T.cellsThroughC := fun hm => hcS (mem_filter.mp hm).2
    simp only [hmem, ↓reduceDIte]
    -- transfer to `N`
    have hE : Degen.SourceLadder (Degen.eraseAtoms N T.Y) u v :=
      (sourceLadder_addBond_iff _ T.d_mem T.c_mem hcS).mp h
    have hnot : ∀ j, u j ∉ T.Y ∧ v j ∉ T.Y := fun j =>
      ⟨(mem_sdiff.mp (hE.2.2.1 j).1).2, (mem_sdiff.mp (hE.2.2.1 j).2).2⟩
    have hN : Degen.SourceLadder N u v := (Degen.sourceLadder_erase_iff N T.Y u v hnot).mp hE
    obtain ⟨x, y, hxe, hye, hxa, hya, hr⟩ := hr
    have hmemu : ∀ j, u j ∈ Molecule.ladderAtoms u v := fun j => mem_union_left _ (mem_image_of_mem _ (mem_univ j))
    have hmemv : ∀ j, v j ∈ Molecule.ladderAtoms u v := fun j => mem_union_right _ (mem_image_of_mem _ (mem_univ j))
    have hu : u 0 ≠ u 1 := fun e => by have := h.2.1 (a₁ := .inl 0) (a₂ := .inl 1) e; simp at this
    have hv : v 0 ≠ v 1 := fun e => by have := h.2.1 (a₁ := .inr 0) (a₂ := .inr 1) e; simp at this
    obtain ⟨zx, rfl⟩ := T.rail_dart_inl ⟨fun e => hcS (e ▸ hmemu 0), fun e => hcS (e ▸ hmemu 1)⟩ hxe
    obtain ⟨zy, rfl⟩ := T.rail_dart_inl ⟨fun e => hcS (e ▸ hmemv 0), fun e => hcS (e ▸ hmemv 1)⟩ hye
    exact hCGR u v hN r ⟨zx.val, zy.val, hxe, hye, hxa, hya, hr⟩

end TwoExit
end WaveTurbulence.MoleProp4
