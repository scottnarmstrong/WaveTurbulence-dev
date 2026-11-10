/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.LadderGapPropagation
public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadderIntervals
public import WaveTurbulence.Foundations.FinalCount.Degen.CommonParameters
public import WaveTurbulence.Foundations.FinalCount.MoleculeRestrictedCount
public import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic

/-! # Physical gap scales for conditioned post-removal ladders

Actual contained ladders inherit the old gap norm even when their first
rails are exchanged or reversed. Conditioned completions retain exactly
the physical conservation equations needed for this transport.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The first physical gap of any contained selected ladder has the same
norm as the old first gap. Alignment is derived from source geometry. -/
theorem sourceLadder_contained_gap_norm_eq (M : Molecule V D) (hM : M.IsMolecule)
    {d m n : ℕ} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c : V → Mom d}
    (hd : M.IsDecoration L w c κ) (hc : ∀ z ∈ M.atoms, M.deg z = 4 → c z = 0)
    {u v : Fin (m+1) → V} {p q : Fin (n+1) → V}
    (hOld : SourceLadder M u v) (hNew : SourceLadder M p q)
    (hsub : Molecule.ladderAtoms p q ⊆ Molecule.ladderAtoms u v)
    {r s : Mom d} (hr : M.IsLadderGap L w κ u v hOld.1 r)
    (hs : M.IsLadderGap L w κ p q hNew.1 s) : ‖r‖ = ‖s‖ := by
  have hm : 0 < m := by have := hOld.1; omega
  have hr' := (isLadderGap_iff_railGapAt_zero M L w κ u v hOld.1 r).mp hr
  obtain ⟨x,y,hx,hxm,hy,hym,hs⟩ :=
    (isLadderGap_iff_railGapAt_zero M L w κ p q hNew.1 s).mp hs
  obtain ⟨i,halign⟩ := sourceLadder_first_pair_alignment M hM hOld hNew hsub
  rcases halign with h | h | h | h
  · have hgap : RailGapAt M L w κ u v i s := by
      refine ⟨x,y,?_,?_,?_,?_,hs⟩
      · exact hx.trans h.1
      · exact hxm.trans h.2.2.1
      · exact hy.trans h.2.1
      · exact hym.trans h.2.2.2
    exact sourceLadder_railGapAt_norm_eq M hM hd hc hOld ⟨0,hm⟩ i hr' hgap
  · have hgap : RailGapAt M L w κ u v i (Molecule.gapAt L w κ y x) :=
      ⟨y,x,hy.trans h.2.1,hym.trans h.2.2.2,hx.trans h.1,hxm.trans h.2.2.1,rfl⟩
    have he := sourceLadder_railGapAt_norm_eq M hM hd hc hOld ⟨0,hm⟩ i hr' hgap
    rw [hs]
    exact he.trans (norm_sub_rev _ _)
  · have hgap : RailGapAt M L w κ u v i (Molecule.gapAt L w κ (M.mate x) (M.mate y)) := by
      refine ⟨M.mate x,M.mate y,hxm.trans h.2.2.1,?_,hym.trans h.2.2.2,?_,rfl⟩
      · rw [M.mate_mate]; exact hx.trans h.1
      · rw [M.mate_mate]; exact hy.trans h.2.1
    have he := sourceLadder_railGapAt_norm_eq M hM hd hc hOld ⟨0,hm⟩ i hr' hgap
    simpa only [hs,Molecule.gapAt,Molecule.kvec,hd.1 x,hd.1 y] using he
  · have hgap : RailGapAt M L w κ u v i (Molecule.gapAt L w κ (M.mate y) (M.mate x)) := by
      refine ⟨M.mate y,M.mate x,hym.trans h.2.2.2,?_,hxm.trans h.2.2.1,?_,rfl⟩
      · rw [M.mate_mate]; exact hy.trans h.2.1
      · rw [M.mate_mate]; exact hx.trans h.1
    have he := sourceLadder_railGapAt_norm_eq M hM hd hc hOld ⟨0,hm⟩ i hr' hgap
    have he' : ‖r‖ = ‖Molecule.gapAt L w κ y x‖ := by
      simpa only [Molecule.gapAt,Molecule.kvec,hd.1 x,hd.1 y] using he
    rw [hs]
    exact he'.trans (norm_sub_rev _ _)

end WaveTurbulence.Degen
