/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceMaximalLaddersExist
public import WaveTurbulence.Foundations.Spine.SourceGapDyadics
/-! Every actual source ladder has a first-rail gap and an admissible dyadic scale. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

private theorem source_adj_of_bondsBetween_pos {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] (M : Molecule V D) (a b : V) (h : 0 < M.bondsBetween a b) : M.Adj a b := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  have he := (Finset.mem_filter.mp hx).2
  have hh := Sym2.eq_iff.mp he
  change (M.atom x = a ∧ M.atom (M.mate x) = b) ∨
    (M.atom x = b ∧ M.atom (M.mate x) = a) at hh
  rcases hh with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · exact ⟨x, ha, hb⟩
  · exact ⟨M.mate x, ha, by simpa only [M.mate_mate] using hb⟩

/-- The gap uses genuine first rail bonds, with darts based at the first rung. -/
theorem exists_sourceLadderGap {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d m : ℕ} (L : ℝ) (base : Mom d) (κ : D → (Fin d → ℤ))
    (u v : Fin (m + 1) → V) (h : M.IsLadder u v) :
    ∃ r, M.IsLadderGap L base κ u v h.1 r := by
  have hm : 1 ≤ m := h.1
  have hr := h.2.2.2.2 ⟨0, h.1⟩
  have hz : (⟨0, hm⟩ : Fin m).castSucc = (0 : Fin (m + 1)) := by ext; simp
  have ho : (⟨0, hm⟩ : Fin m).succ = (⟨1, by omega⟩ : Fin (m + 1)) := by ext; rfl
  rw [hz, ho] at hr
  have hu : 0 < M.bondsBetween (u 0) (u ⟨1, by omega⟩) := by rw [hr.1]; decide
  have hv : 0 < M.bondsBetween (v 0) (v ⟨1, by omega⟩) := by rw [hr.2.1]; decide
  obtain ⟨x, hxa, hxb⟩ := source_adj_of_bondsBetween_pos M _ _ hu
  obtain ⟨y, hya, hyb⟩ := source_adj_of_bondsBetween_pos M _ _ hv
  refine ⟨Molecule.gapAt L base κ x y, x, y, ?_, ?_, hxa, hya, rfl⟩
  · simp only [Molecule.ends, hxa, hxb]
  · simp only [Molecule.ends, hya, hyb]

/-- All actual maximal ladders can be assigned scales simultaneously, independently
of the other fixed counting choices. No uniform gap-existence hypothesis is assumed. -/
theorem exists_counting_ladderScales {w d : ℕ} (G : Garden w)
    (C : SourceVine.CountingChoices G d) {L : ℝ} (hL : 2 ≤ L) (γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) :
    ∃ scale : Finset (GBranch G.tree) → ℝ,
      ({C with ladderScale := scale}).LadderGaps L γ η base κ := by
  classical
  obtain ⟨A⟩ := sourceMaximalLadderData_nonempty G
  have hex (S : {S // S ∈ G.molecule.maximalLadders}) :=
    exists_sourceLadderGap G.molecule L base κ (A.upper S) (A.lower S) (A.ladder S)
  choose r hr using hex
  have hp (S : {S // S ∈ G.molecule.maximalLadders}) :=
    exists_ladder_gap_scale G.molecule hL base κ (A.upper S) (A.lower S) (A.ladder S).1 (r S) (hr S)
  choose P hP using hp
  let scale (S : Finset (GBranch G.tree)) : ℝ := if h : S ∈ G.molecule.maximalLadders then P ⟨S,h⟩ else 0
  refine ⟨scale, ?_⟩
  intro S hS
  have he : scale S = P ⟨S,hS⟩ := by simp only [scale, dite_eq_left hS]
  dsimp only
  rw [he]
  exact ⟨(hP ⟨S,hS⟩).1, A.length ⟨S,hS⟩, A.upper ⟨S,hS⟩, A.lower ⟨S,hS⟩,
    (A.ladder ⟨S,hS⟩).1, A.ladder ⟨S,hS⟩, A.atoms ⟨S,hS⟩, r ⟨S,hS⟩,
      hr ⟨S,hS⟩, (hP ⟨S,hS⟩).2⟩

end WaveTurbulence.LGSpine
