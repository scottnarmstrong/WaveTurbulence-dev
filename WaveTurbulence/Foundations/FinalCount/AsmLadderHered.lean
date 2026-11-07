/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGarden1
public import WaveTurbulence.Foundations.FinalCount.VCSubLadder
public import WaveTurbulence.Foundations.FinalCount.VCScale
/-! **FINALCOUNT-ASSEMBLY (R49 Q1): `LadderHered` from admissibility.**  Two maximal ladders of `M` that contain a common ladder set
`S'` have the same gap norm on every decoration (`subLadder_gap_norm` twice).  Let `ladClass S` be the `EqvGen`-class (of `LadShare`)
of the maximal ladders containing the ladder set `S`; `heredScale' P S := sup (P '' ladClass S)`.  Then `heredScale` is hereditary
(`ladderHered_heredScale'`) and satisfies the ladder-gap clause `SourceLadderGaps` whenever `P` does and the decoration set is
nonempty-class-consistent (`sourceLadderGaps_hered`); `P ≤ heredScale'` on maximal ladders, hence `countA P ≤ countA heredScale'`.  No premise `LadderScaleCoherent`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

/-- Two maximal ladders sharing a ladder set. -/
def LadShare (M : Molecule V D) (S₁ S₂ : Finset V) : Prop :=
  S₁ ∈ M.maximalLadders ∧ S₂ ∈ M.maximalLadders ∧ ∃ S', M.IsLadderSet S' ∧ S' ⊆ S₁ ∧ S' ⊆ S₂

/-- The class of the maximal ladders connected to a maximal ladder containing `S`. -/
def ladClass (M : Molecule V D) (S : Finset V) : Set (Finset V) :=
  {S₂ | S₂ ∈ M.maximalLadders ∧ ∃ S₁ ∈ M.maximalLadders, S ⊆ S₁ ∧ Relation.EqvGen (LadShare M) S₁ S₂}

/-- The hereditary scale: the supremum of `P` over the class (so `P ≤ heredScale'` on maximal ladders: no constant loss in `countA`). -/
noncomputable def heredScale' (M : Molecule V D) (P : Finset V → ℝ) (S : Finset V) : ℝ :=
  sSup (P '' ladClass M S)

theorem ladClass_finite (M : Molecule V D) (S : Finset V) : (ladClass M S).Finite :=
  (M.maximalLadders.finite_toSet).subset fun _ h => h.1

theorem exists_maximalLadder' {M : Molecule V D} {S : Finset V} (hS : M.IsLadderSet S) :
    ∃ S₁ ∈ M.maximalLadders, S ⊆ S₁ := exists_maximalLadder hS

theorem ladClass_nonempty {M : Molecule V D} {S : Finset V} (hS : M.IsLadderSet S) : (ladClass M S).Nonempty := by
  obtain ⟨S₁, h1, h2⟩ := exists_maximalLadder' hS
  exact ⟨S₁, h1, S₁, h1, h2, Relation.EqvGen.refl _⟩

theorem ladClass_eq {M : Molecule V D} {S' S : Finset V} (hS' : M.IsLadderSet S') (hS : M.IsLadderSet S) (hsub : S' ⊆ S) :
    ladClass M S' = ladClass M S := by
  ext S₂
  constructor
  · rintro ⟨h2, S₁, h1, hS1, he⟩
    obtain ⟨T, hT, hST⟩ := exists_maximalLadder' hS
    refine ⟨h2, T, hT, hST, ?_⟩
    have hsh : Relation.EqvGen (LadShare M) S₁ T := Relation.EqvGen.rel _ _ ⟨h1, hT, S', hS', hS1, hsub.trans hST⟩
    exact (hsh.symm).trans _ _ _ he |>.symm.symm
  · rintro ⟨h2, S₁, h1, hS1, he⟩
    refine ⟨h2, S₁, h1, hsub.trans hS1, he⟩

theorem ladderHered_heredScale' (M : Molecule V D) (P : Finset V → ℝ) : LadderHered M (heredScale' M P) := by
  intro S' S hS' hS hsub
  unfold heredScale'
  rw [ladClass_eq hS' hS hsub]

theorem exists_gap_of_ladder {M : Molecule V D} {m : ℕ} {u v : Fin (m + 1) → V} (hl : M.IsLadder u v) {d : ℕ} (L : ℝ)
    (w : Mom d) (κ : D → (Fin d → ℤ)) : ∃ r : Mom d, M.IsLadderGap L w κ u v hl.1 r := by
  obtain ⟨hne_u, hne_v, -⟩ := ladder_ne hl
  have hm := hl.1
  have h0 : (0 : Fin (m + 1)) ≠ ⟨1, by omega⟩ := fun e => by have := congrArg Fin.val e; simp at this
  obtain ⟨hr1, hr2, -⟩ := hl.2.2.2.2 ⟨0, hm⟩
  have hr1' : M.bondsBetween (u 0) (u ⟨1, by omega⟩) = 1 := hr1
  have hr2' : M.bondsBetween (v 0) (v ⟨1, by omega⟩) = 1 := hr2
  obtain ⟨x, hx1, hx2⟩ := exists_dart_pair (hne_u _ _ h0) (by rw [hr1']; exact Nat.one_pos)
  obtain ⟨y, hy1, hy2⟩ := exists_dart_pair (hne_v _ _ h0) (by rw [hr2']; exact Nat.one_pos)
  exact ⟨Molecule.gapAt L w κ x y, x, y, hx1, hy1, hx2, hy2, rfl⟩

theorem eqvGen_mem {M : Molecule V D} {a b : Finset V} (h : Relation.EqvGen (LadShare M) a b) :
    a = b ∨ (a ∈ M.maximalLadders ∧ b ∈ M.maximalLadders) := by
  induction h with
  | rel a b hab => exact Or.inr ⟨hab.1, hab.2.1⟩
  | refl a => exact Or.inl rfl
  | symm a b _ ih => rcases ih with rfl | ⟨h1, h2⟩; exacts [Or.inl rfl, Or.inr ⟨h2, h1⟩]
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with rfl | ⟨h1, h2⟩
    · exact ih2
    · rcases ih2 with rfl | ⟨h3, h4⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h4⟩

/-- **Gap norms agree along a `LadShare` chain** (the replacement of `LadderScaleCoherent`, R49 Q1). -/
theorem gap_norm_eq_of_eqvGen {M : Molecule V D} (hMol : M.IsMolecule) {L : ℝ} {w : Mom d} {c : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hdec : M.IsDecoration L w c κ) (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0)
    {S₁ S₂ : Finset V} (h : Relation.EqvGen (LadShare M) S₁ S₂) (h1 : S₁ ∈ M.maximalLadders) (h2 : S₂ ∈ M.maximalLadders)
    {m n : ℕ} {U W : Fin (m + 1) → V} {u v : Fin (n + 1) → V} (hU : M.IsLadder U W) (hu : M.IsLadder u v)
    (hUa : Molecule.ladderAtoms U W = S₁) (hua : Molecule.ladderAtoms u v = S₂) {R r : Mom d}
    (hR : M.IsLadderGap L w κ U W hU.1 R) (hr : M.IsLadderGap L w κ u v hu.1 r) : ‖r‖ = ‖R‖ := by
  induction h generalizing m n U W u v R r with
  | refl a =>
    refine subLadder_gap_norm hMol hdec hc hU hu ?_ hR hr
    rw [hUa, ← hua]
    unfold Molecule.ladderAtoms
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  | symm a b hab ih => exact (ih h2 h1 hu hU hua hUa hr hR).symm
  | rel a b hab =>
    obtain ⟨-, -, S', ⟨k, u', v', hl', hat'⟩, hs1, hs2⟩ := hab
    obtain ⟨r', hr'⟩ := exists_gap_of_ladder hl' L w κ
    have hm1 : u' 0 ∈ Molecule.ladderAtoms U W := by
      rw [hUa]; apply hs1; rw [← hat']; unfold Molecule.ladderAtoms
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    have hm2 : u' 0 ∈ Molecule.ladderAtoms u v := by
      rw [hua]; apply hs2; rw [← hat']; unfold Molecule.ladderAtoms
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    have e1 := subLadder_gap_norm hMol hdec hc hU hl' hm1 hR hr'
    have e2 := subLadder_gap_norm hMol hdec hc hu hl' hm2 hr hr'
    rw [← e2, e1]
  | trans a b c hab hbc ih1 ih2 =>
    have hb : b ∈ M.maximalLadders := by
      rcases eqvGen_mem hab with rfl | ⟨-, hb⟩
      · exact h1
      · exact hb
    obtain ⟨k, u', v', hl', hat'⟩ := (Finset.mem_filter.1 hb).2.1
    obtain ⟨r', hr'⟩ := exists_gap_of_ladder hl' L w κ
    exact (ih2 hb h2 hl' hu hat' hua hr' hr).trans (ih1 h1 hb hU hl' hUa hat' hR hr')

theorem ladClass_mem_self {M : Molecule V D} {S : Finset V} (hS : S ∈ M.maximalLadders) : S ∈ ladClass M S :=
  ⟨hS, S, hS, subset_rfl, Relation.EqvGen.refl _⟩

theorem le_heredScale' {M : Molecule V D} {P : Finset V → ℝ} {S : Finset V} (hS : S ∈ M.maximalLadders) :
    P S ≤ heredScale' M P S :=
  le_csSup ((ladClass_finite M S).image P).bddAbove ⟨S, ladClass_mem_self hS, rfl⟩

theorem heredScale'_attained {M : Molecule V D} {P : Finset V → ℝ} {S : Finset V} (hS : S ∈ M.maximalLadders) :
    ∃ S₂ ∈ ladClass M S, heredScale' M P S = P S₂ := by
  have hne : (P '' ladClass M S).Nonempty := ⟨_, S, ladClass_mem_self hS, rfl⟩
  obtain ⟨S₂, h2, e⟩ := Set.Nonempty.csSup_mem hne ((ladClass_finite M S).image P)
  exact ⟨S₂, h2, e.symm⟩

/-- **The ladder-gap clause survives the hereditary replacement** (R49 Q1). -/
theorem sourceLadderGaps_hered {M : Molecule V D} (hMol : M.IsMolecule) {L : ℝ} {w : Mom d} {c : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hdec : M.IsDecoration L w c κ) (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0)
    {P : Finset V → ℝ} (hP : SourceLadderGaps M L w P κ) : SourceLadderGaps M L w (heredScale' M P) κ := by
  intro S hS
  obtain ⟨S₂, hcl, he⟩ := heredScale'_attained (P := P) hS
  obtain ⟨hS₂, S₁, hS₁, hsub, heq⟩ := hcl
  have hS1S : S₁ = S := (Finset.mem_filter.1 hS).2.2 S₁ (Finset.mem_filter.1 hS₁).2.1 hsub |>.symm ▸ rfl
  subst hS1S
  rw [he]
  obtain ⟨hP1, m, u, v, hm, hl, hat, r, hr, h0, h1, h2⟩ := hP S₁ hS
  obtain ⟨hP2, m', u', v', hm', hl', hat', r', hr', h0', h1', h2'⟩ := hP S₂ hS₂
  have hn : ‖r'‖ = ‖r‖ := gap_norm_eq_of_eqvGen hMol hdec hc heq hS hS₂ hl hl' hat hat' hr hr'
  refine ⟨hP2, m, u, v, hm, hl, hat, r, hr, fun h => ?_, fun a b => ?_, fun h => ?_⟩
  · have := h0' h
    rw [this, norm_zero] at hn
    exact norm_eq_zero.mp hn.symm
  · rw [← hn]; exact h1' a b
  · rw [← hn]; exact h2' h

theorem ladderWeight_mono' (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 ≤ δ) {a b : ℝ} (hab : a ≤ b) :
    Molecule.ladderWeight L γ δ a ≤ Molecule.ladderWeight L γ δ b := by
  unfold Molecule.ladderWeight
  have hc : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ (Real.rpow_nonneg hL.le _)
  exact min_le_min le_rfl (by nlinarith)

theorem ladderWeight_nonneg' (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 ≤ δ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ Molecule.ladderWeight L γ δ a := by
  unfold Molecule.ladderWeight
  have hc : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ (Real.rpow_nonneg hL.le _)
  exact le_min (sq_nonneg _) (by nlinarith)

/-- **`countA` for `P` is at most `countA` for the hereditary replacement** (no constant loss). -/
theorem countA_le_hered (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    {P : Finset V → ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) (hC₁ : 0 ≤ C₁) (hP0 : ∀ S ∈ M.maximalLadders, 0 ≤ P S) :
    M.countA L γ δ C₁ w Adm P ≤ M.countA L γ δ C₁ w Adm (heredScale' M P) := by
  unfold Molecule.countA
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have hX : 0 ≤ L ^ (-((d : ℝ) - γ) * M.circuitRank) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank := by
    have := Real.rpow_nonneg hL.le (-((d : ℝ) - γ) * M.circuitRank)
    have h2 : 0 ≤ C₁⁻¹ * δ ^ (1 / 2 : ℝ) := mul_nonneg (inv_nonneg.mpr hC₁) (Real.rpow_nonneg hδ _)
    positivity
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun S hS => ?_) (fun S hS => ?_)) hX
  · exact pow_nonneg (ladderWeight_nonneg' L γ δ hL hδ (hP0 S hS)) _
  · exact pow_le_pow_left₀ (ladderWeight_nonneg' L γ δ hL hδ (hP0 S hS))
      (ladderWeight_mono' L γ δ hL hδ (le_heredScale' hS)) _

theorem heredScale'_nonneg (M : Molecule V D) {P : Finset V → ℝ} (hP0 : ∀ S ∈ M.maximalLadders, 0 ≤ P S) (S : Finset V) :
    0 ≤ heredScale' M P S := by
  unfold heredScale'
  refine Real.sSup_nonneg ?_
  rintro _ ⟨S₂, hS₂, rfl⟩
  exact hP0 S₂ hS₂.1

end WaveTurbulence.FinalCountAsm
