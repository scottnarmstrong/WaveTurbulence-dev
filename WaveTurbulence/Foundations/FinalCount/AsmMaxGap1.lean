/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3SrcGaps
public import WaveTurbulence.Foundations.FinalCount.AdmBridge
public import WaveTurbulence.Foundations.FinalCount.AsmRho1
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ScaleConditions
/-! **FINALCOUNT-ASSEMBLY, ladder-gap clauses 1: a ladder of a sub-molecule of a state has the gap scale of its maximal parent.**
`gapScale_of_embed`: for a state `s` with `LCtx M₀ s`, the canonical clause `SourceLadderGaps M₀ L w P k0`, and a molecule `N` embedded
into `s.M` by a dart map `j` (atoms and mates preserved, ladders of `N` are ladders of `s.M`), every ladder `(u, v)` of `N` with gap `r`
(for the decoration `k0 ∘ s.down ∘ j`) satisfies `GapScale L (P (ladderAtoms u v)) ‖r‖`.  Proof: lift to `M₀` (`isLadder_lift`,
`ladderGap_lift`), compare with the maximal ladder containing it (`subLadder_gap_norm`), and use `LadderHered`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem gapScale_of_embed {M₀ : Molecule V D₀} {s : St.{u} V D₀} (hc : LCtx M₀ s) {L : ℝ} {w : Mom d} {P : Finset V → ℝ}
    (hP : LadderHered M₀ P) (hMol0 : M₀.IsMolecule) {k0 : D₀ → (Fin d → ℤ)} {c0 : V → Mom d}
    (hdec : M₀.IsDecoration L w c0 k0) (hc0 : ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (hsrc : SourceLadderGaps M₀ L w P k0) {D' : Type*} [Fintype D'] [DecidableEq D'] (N : Molecule V D') (j : D' → s.D)
    (hlad : ∀ {m : ℕ} {u v : Fin (m + 1) → V}, N.IsLadder u v → s.M.IsLadder u v)
    (hatom : ∀ x, s.M.atom (j x) = N.atom x) (hmate : ∀ x, s.M.mate (j x) = j (N.mate x))
    {m : ℕ} {u v : Fin (m + 1) → V} (hL : N.IsLadder u v) {r : Mom d}
    (hr : N.IsLadderGap L w (k0 ∘ s.down ∘ j) u v hL.1 r) :
    MoleProp.GapScale L (P (Molecule.ladderAtoms u v)) ‖r‖ := by
  obtain ⟨a, hA⟩ := hc.anc
  have hl := hlad hL
  have hgap : s.M.IsLadderGap L w (k0 ∘ s.down) u v hl.1 r := by
    obtain ⟨x, y, hx1, hy1, hx2, hy2, hrr⟩ := hr
    refine ⟨j x, j y, ?_, ?_, ?_, ?_, ?_⟩
    · unfold Molecule.ends at hx1 ⊢; rw [hatom, hmate, hatom]; exact hx1
    · unfold Molecule.ends at hy1 ⊢; rw [hatom, hmate, hatom]; exact hy1
    · rw [hatom]; exact hx2
    · rw [hatom]; exact hy2
    · exact hrr
  have hl0 := isLadder_lift hA hc.rel hc.eps hl
  have hgap0 := (ladderGap_lift hA hc.rel hc.eps hl).1 hgap
  have hSet0 : M₀.IsLadderSet (Molecule.ladderAtoms u v) := ⟨m, u, v, hl0, rfl⟩
  obtain ⟨S1, hS1, hSS1⟩ := exists_maximalLadder hSet0
  have hPe : P (Molecule.ladderAtoms u v) = P S1 := hP _ S1 hSet0 (Finset.mem_filter.1 hS1).2.1 hSS1
  obtain ⟨hP1, n, U, W, hn, hlad0, hatS1, R, hR, h0, h1, h2⟩ := hsrc S1 hS1
  have hmem : u 0 ∈ Molecule.ladderAtoms U W := by
    rw [hatS1]; apply hSS1
    unfold Molecule.ladderAtoms
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩)
  have hnorm := subLadder_gap_norm hMol0 hdec hc0 hlad0 hl0 hmem hR hgap0
  rw [hPe]
  rcases hP1 with hP0 | ⟨⟨z, hz⟩, hlo, hhi⟩
  · left
    refine ⟨hP0, ?_⟩
    have := h0 hP0
    rw [this, norm_zero] at hnorm
    exact hnorm
  · have hpos : 0 < P S1 := by rw [hz]; positivity
    rcases lt_or_eq_of_le hhi with hlt | heq
    · right; left
      have := (h1 hpos hlt)
      rw [hnorm]
      exact ⟨hlo, hlt, this.1, this.2⟩
    · right; right
      have := h2 heq
      rw [hnorm]
      exact ⟨heq, by linarith⟩

end WaveTurbulence.FinalCountAsm
