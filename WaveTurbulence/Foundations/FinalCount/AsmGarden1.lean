/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass3
/-! **FINALCOUNT-ASSEMBLY (garden level, 1): the ladder scale.**  `countA` reads the scale only on the maximal ladders (`countA_congr_scale`).
If overlapping maximal ladders carry equal scales (`LadderScaleCoherent`, a NAMED INPUT: Degen.MaximalLadderDisjoint's `chordLadder` shows
that distinct maximal induced ladders may overlap), the hereditary scale `heredScale` agrees with `P` on the maximal ladders and satisfies
`LadderHered`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem countA_congr_scale (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    {P P' : Finset V → ℝ} (h : ∀ S ∈ M.maximalLadders, P S = P' S) :
    M.countA L γ δ C₁ w Adm P = M.countA L γ δ C₁ w Adm P' := by
  unfold Molecule.countA
  congr 3
  refine Finset.prod_congr rfl fun S hS => ?_
  rw [h S hS]

/-- Overlapping maximal ladders carry equal scales. -/
def LadderScaleCoherent (M : Molecule V D) (P : Finset V → ℝ) : Prop :=
  ∀ S₁ ∈ M.maximalLadders, ∀ S₂ ∈ M.maximalLadders, ¬ Disjoint S₁ S₂ → P S₁ = P S₂

/-- The hereditary extension of `P` from the maximal ladders. -/
noncomputable def heredScale (M : Molecule V D) (P : Finset V → ℝ) (S : Finset V) : ℝ :=
  if h : ∃ S₁ ∈ M.maximalLadders, S ⊆ S₁ then P (Classical.choose h) else 0

theorem heredScale_eq (M : Molecule V D) {P : Finset V → ℝ} (hc : LadderScaleCoherent M P) {S : Finset V}
    (hS : S ∈ M.maximalLadders) : heredScale M P S = P S := by
  unfold heredScale
  have h : ∃ S₁ ∈ M.maximalLadders, S ⊆ S₁ := ⟨S, hS, subset_rfl⟩
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  have hne : S.Nonempty := by
    obtain ⟨m, u, v, hl, rfl⟩ := (Finset.mem_filter.1 hS).2.1
    refine ⟨u 0, ?_⟩
    unfold Molecule.ladderAtoms
    simp
  refine hc _ h1 S hS ?_
  rw [Finset.not_disjoint_iff]
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, h2 hx, hx⟩

theorem ladderHered_heredScale (M : Molecule V D) {P : Finset V → ℝ} (hc : LadderScaleCoherent M P) :
    LadderHered M (heredScale M P) := by
  intro S' S hS' hS hsub
  have e1 := exists_maximalLadder hS'
  have e2 := exists_maximalLadder hS
  have hne : S'.Nonempty := by
    obtain ⟨m, u, v, hl, rfl⟩ := hS'
    refine ⟨u 0, ?_⟩
    unfold Molecule.ladderAtoms
    simp
  unfold heredScale
  rw [dif_pos e1, dif_pos e2]
  obtain ⟨a1, a2⟩ := Classical.choose_spec e1
  obtain ⟨b1, b2⟩ := Classical.choose_spec e2
  refine hc _ a1 _ b1 ?_
  rw [Finset.not_disjoint_iff]
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, a2 hx, b2 (hsub hx)⟩

theorem heredScale_nonneg (M : Molecule V D) {P : Finset V → ℝ} (hP : ∀ S ∈ M.maximalLadders, 0 ≤ P S) (S : Finset V) :
    0 ≤ heredScale M P S := by
  unfold heredScale
  split_ifs with h
  · exact hP _ (Classical.choose_spec h).1
  · exact le_rfl

end WaveTurbulence.FinalCountAsm
