/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.CellStepEquivalence
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderGapPropagation
import Mathlib.Tactic

/-! # Per-position physical gap restrictions without zero-charge assumptions -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The physical norm of one cell gap is independent of its row and
traversal representation. Only actual bond consistency is required;
no conservation equation at degree-four atoms is used. -/
theorem cell_gap_norm_eq (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (hb : ∀ x, κ (M.mate x) = κ x) {u v p q : Fin 2 → V}
    (hOld : SourceLadder M u v) (hNew : SourceLadder M p q)
    (hsub : Molecule.ladderAtoms p q ⊆ Molecule.ladderAtoms u v)
    {r s : Mom d} (hr : M.IsLadderGap L w κ u v hOld.1 r)
    (hs : M.IsLadderGap L w κ p q hNew.1 s) : ‖r‖ = ‖s‖ := by
  have hr' := (isLadderGap_iff_railGapAt_zero M L w κ u v hOld.1 r).mp hr
  obtain ⟨x,y,hx,hxm,hy,hym,hs⟩ :=
    (isLadderGap_iff_railGapAt_zero M L w κ p q hNew.1 s).mp hs
  obtain ⟨i,halign⟩ := sourceLadder_first_pair_alignment M hM hOld hNew hsub
  have hnorm (t : Mom d) (ht : RailGapAt M L w κ u v i t) : ‖r‖ = ‖t‖ := by
    have hi : (⟨0,by have := hOld.1; omega⟩ : Fin 1) = i := Subsingleton.elim _ _
    exact congrArg norm (sourceLadder_railGapAt_unique M L w κ hOld i (hi ▸ hr') ht)
  rcases halign with h | h | h | h
  · exact hnorm s ⟨x,y,hx.trans h.1,hxm.trans h.2.2.1,hy.trans h.2.1,hym.trans h.2.2.2,hs⟩
  · have he := hnorm (Molecule.gapAt L w κ y x)
      ⟨y,x,hy.trans h.2.1,hym.trans h.2.2.2,hx.trans h.1,hxm.trans h.2.2.1,rfl⟩
    rw [hs]
    exact he.trans (norm_sub_rev _ _)
  · have he := hnorm (Molecule.gapAt L w κ (M.mate x) (M.mate y))
      ⟨M.mate x,M.mate y,hxm.trans h.2.2.1,by rw [M.mate_mate]; exact hx.trans h.1,
        hym.trans h.2.2.2,by rw [M.mate_mate]; exact hy.trans h.2.1,rfl⟩
    simpa only [hs,Molecule.gapAt,Molecule.kvec,hb x,hb y] using he
  · have he := hnorm (Molecule.gapAt L w κ (M.mate y) (M.mate x))
      ⟨M.mate y,M.mate x,hym.trans h.2.2.2,by rw [M.mate_mate]; exact hy.trans h.2.1,
        hxm.trans h.2.2.1,by rw [M.mate_mate]; exact hx.trans h.1,rfl⟩
    have he' : ‖r‖ = ‖Molecule.gapAt L w κ y x‖ := by
      simpa only [Molecule.gapAt,Molecule.kvec,hb x,hb y] using he
    rw [hs]
    exact he'.trans (norm_sub_rev _ _)

/-- The physical gap at any actual maximal-ladder position is realized
by the literal consecutive two-rung cell, with its original orientation. -/
theorem exists_step_cell_gap (M : Molecule V D) {d m : ℕ} (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) {u v : Fin (m+1) → V} (hL : SourceLadder M u v)
    (i : Fin m) {r : Mom d} (hr : RailGapAt M L w κ u v i r) :
    ∃ (p q : Fin 2 → V) (hC : SourceLadder M p q),
      Molecule.ladderAtoms p q = ladderStepAtoms u v i ∧ M.IsLadderGap L w κ p q hC.1 r := by
  let E := ladderIntervalEmbedding m i.val 1 (by have := i.isLt; omega)
  let p := fun j => u (E j)
  let q := fun j => v (E j)
  have hC : SourceLadder M p q := sourceLadder_interval M hL i.val 1
    (by have := i.isLt; omega) (by omega)
  have h0 : E 0 = i.castSucc := Fin.ext rfl
  have h1 : E 1 = i.succ := Fin.ext rfl
  have hAtoms : Molecule.ladderAtoms p q = ladderStepAtoms u v i := by
    have he : (univ : Finset (Fin 2)) = {0,1} := by decide
    change univ.image p ∪ univ.image q = _
    rw [he]
    ext x
    simp only [image_insert,image_singleton,mem_union,mem_insert,mem_singleton,p,q,h0,h1,ladderStepAtoms]
    tauto
  refine ⟨p,q,hC,hAtoms,?_⟩
  apply (isLadderGap_iff_railGapAt_zero M L w κ p q hC.1 r).mpr
  change RailGapAt M L w κ p q (0 : Fin 1) r
  have h0' : E (0 : Fin 1).castSucc = i.castSucc := Fin.ext rfl
  have h1' : E (0 : Fin 1).succ = i.succ := Fin.ext rfl
  simpa only [RailGapAt,p,q,h0',h1'] using hr

/-- The universal cell restriction is exactly the original per-position
restriction on any actual maximal-ladder enumeration. It imposes no extra
condition from alternative cell representations or from zero charges. -/
theorem cellGapRestriction_iff_maximal_steps (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (hb : ∀ x, κ (M.mate x) = κ x)
    (m : {S // S ∈ sourceMaximalLadders M} → ℕ)
    (u v : ∀ S : {S // S ∈ sourceMaximalLadders M}, Fin (m S+1) → V)
    (hrep : ∀ S, SourceLadder M (u S) (v S) ∧ Molecule.ladderAtoms (u S) (v S) = S.val)
    (P : Finset V → ℝ) (R : ℝ → ℝ → Prop) :
    CellGapRestriction M L w P R κ ↔
      ∀ S, ∀ i : Fin (m S), ∀ r, RailGapAt M L w κ (u S) (v S) i r →
        R (P (ladderStepAtoms (u S) (v S) i)) ‖r‖ := by
  classical
  constructor
  · intro h S i r hr
    obtain ⟨p,q,hC,hAtoms,hgap⟩ := exists_step_cell_gap M L w κ (hrep S).1 i hr
    simpa only [hAtoms] using h p q hC r hgap
  · intro h p q hC r hr
    let C := Molecule.ladderAtoms p q
    have hset : SourceLadderSet M C := ⟨1,p,q,hC,rfl⟩
    obtain ⟨S,hS,hCS⟩ := exists_sourceMaximalLadder_superset M hset
    let S' : {S // S ∈ sourceMaximalLadders M} := ⟨S,hS⟩
    have hsub : C ⊆ Molecule.ladderAtoms (u S') (v S') := (hrep S').2.symm ▸ hCS
    obtain ⟨i,hi⟩ := exists_step_eq_of_cell_subset M hM (hrep S').1 ⟨p,q,hC,rfl⟩ hsub
    obtain ⟨s,hs⟩ := sourceLadder_exists_railGapAt M L w κ (hrep S').1 i
    obtain ⟨a,b,hAB,hAtoms,hgap⟩ := exists_step_cell_gap M L w κ (hrep S').1 i hs
    have hsame : Molecule.ladderAtoms p q ⊆ Molecule.ladderAtoms a b := by
      rw [hAtoms,← hi]
    have hn := cell_gap_norm_eq M hM L w κ hb hAB hC hsame hgap hr
    have hh := h S' i s hs
    rw [← hi] at hh
    rw [hn] at hh
    exact hh

end WaveTurbulence.MoleProp
