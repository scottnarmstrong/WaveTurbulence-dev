/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCounting
public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadderIntervals
import Mathlib.Tactic

/-! # Individual selected ladder links for Appendix B

A link is a length-one selected source ladder. There is one weight per
adjacent pair of double rungs. This intermediate invariant has a distinct
name; its comparison with the source maximal-ladder product is separate.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two disjoint double rungs joined by opposite single rails, with the
source allowance for additional end chords. -/
def AppbLink (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ u v : Fin 2 → V, Degen.SourceLadder (m := 1) M u v ∧ Molecule.ladderAtoms u v = S

noncomputable def appbLinks (M : Molecule V D) : Finset (Finset V) := by
  classical
  exact M.atoms.powerset.filter (AppbLink M)

/-- Every link is an actual selected source ladder. -/
theorem AppbLink.sourceLadderSet {M : Molecule V D} {S : Finset V} (h : AppbLink M S) :
    Degen.SourceLadderSet M S := by
  obtain ⟨u,v,h,rfl⟩ := h
  exact ⟨1,u,v,h,rfl⟩

theorem AppbLink.subset_atoms {M : Molecule V D} {S : Finset V} (h : AppbLink M S) : S ⊆ M.atoms :=
  Degen.sourceLadderSet_atoms_subset M h.sourceLadderSet

theorem AppbLink.card {M : Molecule V D} {S : Finset V} (h : AppbLink M S) : S.card = 4 := by
  obtain ⟨u,v,h,rfl⟩ := h
  exact Degen.ladderAtoms_card_of_injective h.2.1

theorem mem_appbLinks (M : Molecule V D) (S : Finset V) : S ∈ appbLinks M ↔ AppbLink M S := by
  classical
  simp only [appbLinks,mem_filter,mem_powerset]
  exact ⟨fun h => h.2,fun h => ⟨h.subset_atoms,h⟩⟩

noncomputable def appbLinkProduct (M : Molecule V D) (L γ δ : ℝ) (P : Finset V → ℝ) : ℝ :=
  ∏ S ∈ appbLinks M, Molecule.ladderWeight L γ δ (P S)

/-- A distinct normalized intermediate invariant; it does not redefine
current B2 countA or the source-facing appbCountA. -/
noncomputable def appbLinkCountA (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) : ℝ≥0∞ :=
  (appbCountE M L γ δ w Adm : ℝ≥0∞) * ENNReal.ofReal
    (L ^ (-((d : ℝ) - γ) * M.circuitRank) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
      appbLinkProduct M L γ δ P)

/-- Every nonnegative scale gives a factor between one and log squared,
in the source large-L regime. -/
theorem appb_link_weight_bounds {L δ P : ℝ} (hL : 0 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : 0 ≤ δ) (hP : 0 ≤ P) (γ : ℝ) :
    1 ≤ Molecule.ladderWeight L γ δ P ∧ Molecule.ladderWeight L γ δ P ≤ Real.log L^2 := by
  unfold Molecule.ladderWeight
  constructor
  · apply le_min
    · nlinarith only [hlog,sq_nonneg (Real.log L-1)]
    · have h := mul_nonneg (mul_nonneg hδ (Real.rpow_nonneg hL (2*γ))) hP
      linarith only [h]
  · exact min_le_left _ _

/-- Assigning zero to a newly formed link gives weight one without any
condition that its actual physical gap vanish. -/
theorem appb_link_weight_zero {L : ℝ} (hlog : 1 ≤ Real.log L) (γ δ : ℝ) :
    Molecule.ladderWeight L γ δ 0 = 1 := by
  unfold Molecule.ladderWeight
  rw [mul_zero,add_zero,min_eq_right]
  nlinarith only [hlog,sq_nonneg (Real.log L-1)]

end WaveTurbulence.Mole
