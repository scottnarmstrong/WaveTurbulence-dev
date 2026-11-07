/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ctx
public import WaveTurbulence.Foundations.FinalCount.VCSubLadder
public import WaveTurbulence.Foundations.FinalCount.VCSource
public import WaveTurbulence.Foundations.FinalCount.VCScale
/-! **FINALCOUNT-G3: the canonical ladder-gap clause of `Adm` at a state** (`SourceLadderGaps`, DH23 `kqmainest2` (ii), L1692,
the premise `DecScale` of VINE-COUNT's `prop94_vine_all`).

`SourceLadderGaps M₀ k0` (the clause for `M_sub`) transfers to `SourceLadderGaps s.M (k0 ∘ s.down)`: a maximal ladder of the
state is a ladder of `M₀` inside a maximal one (`P` is constant along them, `LadderHered`), and the gap of a sub-ladder has
the norm of the gap of the ladder containing its first rung (`subLadder_gap_norm`, decoration of `M₀` with `c = 0` at
degree `4`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀}

theorem sourceGaps_state {s : St.{u} V D₀} (hc : LCtx M₀ s) {L : ℝ} {w : Mom d} {P : Finset V → ℝ}
    (hP : LadderHered M₀ P) (hMol0 : M₀.IsMolecule) {k0 : D₀ → (Fin d → ℤ)} {c0 : V → Mom d}
    (hdec : M₀.IsDecoration L w c0 k0) (hc0 : ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (hsrc : SourceLadderGaps M₀ L w P k0) : SourceLadderGaps s.M L w P (k0 ∘ s.down) := by
  obtain ⟨a, hA⟩ := hc.anc
  intro S hS
  have hS' := (Finset.mem_filter.1 hS).2.1
  obtain ⟨m, u, v, hl, hat⟩ := hS'
  have hl0 := isLadder_lift hA hc.rel hc.eps hl
  have hSet0 : M₀.IsLadderSet S := ⟨m, u, v, hl0, hat⟩
  obtain ⟨S1, hS1, hSS1⟩ := exists_maximalLadder hSet0
  have hPe : P S = P S1 := hP S S1 hSet0 (Finset.mem_filter.1 hS1).2.1 hSS1
  obtain ⟨hP1, n, U, W, hn, hlad, hatS1, R, hR, h0, h1, h2⟩ := hsrc S1 hS1
  -- the gap of `(u, v)` in the state
  have hm := hl.1
  have hu01 : u 0 ≠ u ⟨1, by omega⟩ := fun e => by
    have := @hl.2.1 (Sum.inl 0) (Sum.inl ⟨1, by omega⟩) e
    simp at this
  have hv01 : v 0 ≠ v ⟨1, by omega⟩ := fun e => by
    have := @hl.2.1 (Sum.inr 0) (Sum.inr ⟨1, by omega⟩) e
    simp at this
  have hr1 := hl.2.2.2.2 ⟨0, hm⟩
  obtain ⟨x, hx1, hx2⟩ := exists_dart_pair (M := s.M) hu01 (by
    have := hr1.1; show 0 < s.M.bondsBetween (u 0) (u ⟨1, by omega⟩); rw [show s.M.bondsBetween (u 0) (u ⟨1, by omega⟩) = 1 from this]; exact Nat.one_pos)
  obtain ⟨y, hy1, hy2⟩ := exists_dart_pair (M := s.M) hv01 (by
    have := hr1.2.1; show 0 < s.M.bondsBetween (v 0) (v ⟨1, by omega⟩); rw [show s.M.bondsBetween (v 0) (v ⟨1, by omega⟩) = 1 from this]; exact Nat.one_pos)
  have hgap : s.M.IsLadderGap L w (k0 ∘ s.down) u v hm (Molecule.gapAt L w (k0 ∘ s.down) x y) :=
    ⟨x, y, hx1, hy1, hx2, hy2, rfl⟩
  have hgap0 := (ladderGap_lift hA hc.rel hc.eps hl).1 hgap
  have hmem : u 0 ∈ Molecule.ladderAtoms U W := by
    rw [hatS1]; apply hSS1; rw [← hat]
    unfold Molecule.ladderAtoms
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩)
  have hnorm := subLadder_gap_norm hMol0 hdec hc0 hlad hl0 hmem hR hgap0
  refine ⟨by rw [hPe]; exact hP1, m, u, v, hm, hl, hat, _, hgap, ?_, ?_, ?_⟩
  · intro h
    rw [hPe] at h
    have := h0 h
    rw [this, norm_zero] at hnorm
    exact norm_eq_zero.1 hnorm
  · intro hp hp1
    rw [hPe] at hp hp1 ⊢
    rw [hnorm]; exact h1 hp hp1
  · intro hp
    rw [hPe] at hp
    rw [hnorm]; exact h2 hp

end WaveTurbulence.FinalCountG3
