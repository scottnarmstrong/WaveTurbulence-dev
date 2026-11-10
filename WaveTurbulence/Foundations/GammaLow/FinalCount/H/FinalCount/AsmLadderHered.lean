/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmLadderHered
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmTopClass3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmLadderHered`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (R49 Q1): `LadderHered` from admissibility.**  Two maximal ladders of `M` that contain a common ladder set
`S'` have the same gap norm on every decoration (`subLadder_gap_norm` twice).  Let `ladClass S` be the `EqvGen`-class (of `LadShare`)
of the maximal ladders containing the ladder set `S`; `heredScale' P S := sup (P '' ladClass S)`.  Then `heredScale` is hereditary
(`ladderHered_heredScale'`) and satisfies the ladder-gap clause `SourceLadderGaps` whenever `P` does and the decoration set is
nonempty-class-consistent (`sourceLadderGaps_hered`); `P ≤ heredScale'` on maximal ladders, hence `countA P ≤ countA heredScale'`.  No premise `LadderScaleCoherent`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem exists_gap_of_ladder {M : Molecule V D} {m : ℕ} {u v : Fin (m + 1) → V} (hl : M.IsLadder u v) {d : ℕ} (L : ℝ)
    (w : Mom d) (κ : D → (Fin d → ℤ)) : ∃ r : Mom d, M.IsLadderGap L w κ u v hl.1 r := by
  obtain ⟨hne_u, hne_v, -⟩ := ladder_ne hl
  have hm := hl.1
  have h0 : (0 : Fin (m + 1)) ≠ ⟨1, by omega⟩ := fun e => by have := congrArg Fin.val e; simp at this
  obtain ⟨hr1, hr2, -⟩ := hl.2.2.2.2 ⟨0, hm⟩
  have hr1' : M.bondsBetween (u 0) (u ⟨1, by omega⟩) = 1 := hr1
  have hr2' : M.bondsBetween (v 0) (v ⟨1, by omega⟩) = 1 := hr2
  obtain ⟨x, hx1, hx2⟩ := Step1.exists_dart_pair (hne_u _ _ h0) (by rw [hr1']; exact Nat.one_pos)
  obtain ⟨y, hy1, hy2⟩ := Step1.exists_dart_pair (hne_v _ _ h0) (by rw [hr2']; exact Nat.one_pos)
  exact ⟨Molecule.gapAt L w κ x y, x, y, hx1, hy1, hx2, hy2, rfl⟩

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

end WaveTurbulence.GammaLow.FinalCount.H
