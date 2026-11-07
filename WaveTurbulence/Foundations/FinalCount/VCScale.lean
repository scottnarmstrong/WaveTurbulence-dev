/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCLadProd
public import WaveTurbulence.Foundations.FinalCount.VCInj
/-! # VINE-COUNT part 17: ladder scales in `Adm`, and the scale of the vine gap seen from a chart rung.

`VCLadderScale` is the ladder-scale restriction of the class `Adm` (DH23 `kqmainest2` (ii), L1692: "the gap `r_j` of each
ladder `𝕃_j` satisfies `|r_j| ∼ P_j`"; dyadic comparison constant `2`; `P_j ∈ [L⁻¹, 1] ∪ {0}`, and `r_j = 0` when
`P_j = 0`), stated for the maximal ladders of the removed vine `K.vc`.  Session 3: only the LOWER comparison `P/2 ≤ ‖r‖` is
kept (no upper bound, in particular none at `P = 1`): main's `coupledPair_bound` needs only `c⁻¹ P ≤ ‖r‖`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **The ladder-scale restriction of `Adm`** (R17): every maximal ladder `𝕃 = S'` of the removed vine has a first-rail gap
`r` with (`P S' = 0` and `r = 0`) or (`L⁻¹ ≤ P S' ≤ 1` and `P S' / 2 ≤ |r|`). -/
def VCLadderScale {M : Molecule V D} (K : VineCut M) (L : ℝ) (w : Mom d) (P : Finset V → ℝ)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∀ S' ∈ K.vc.maximalLadders, ∀ (m : ℕ) (u v : Fin (m + 1) → V) (h : K.vc.IsLadder u v),
    Molecule.ladderAtoms u v = S' → ∀ r : Mom d, K.vc.IsLadderGap L w (fun x => κ x.1) u v h.1 r →
      (P S' = 0 ∧ r = 0) ∨ (L⁻¹ ≤ P S' ∧ P S' ≤ 1 ∧ 2⁻¹ * P S' ≤ ‖r‖)

/-- **A hypothesis on the admissible class used at decorations only.**  `Q κ` is required for every label `κ` that is a
`c`-decoration of `M` (conservation; `c = 0` at the degree-`4` atoms) satisfying `Adm`.  (Realisation independence of a
sub-ladder's gap needs the conservation law, so the ladder-gap clause of the source is a statement about decorations.) -/
def DecScale {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (L : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Q : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ (c : V → Mom d) (κ : D → (Fin d → ℤ)), M.IsDecoration L w c κ → (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) →
    Adm κ → Q κ

section Scale
variable {M : Molecule V D} (K : VineCut M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)

omit hB in
theorem exists_dart_pair {a b : V} (hab : a ≠ b) (h : 0 < M.bondsBetween a b) :
    ∃ x, M.ends x = s(a, b) ∧ M.atom x = a := by
  obtain ⟨x, hx1, hx2⟩ := Stage1.exists_dart hab (by omega)
  exact ⟨x, by unfold Molecule.ends; rw [hx1, hx2], hx1⟩

include hB in
/-- Every ladder of the removed vine has a first-rail gap, computed in `K.vc` and in `M` alike. -/
theorem exists_ladderGap {m : ℕ} {u v : Fin (m + 1) → V} (h : K.vc.IsLadder u v) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) :
    ∃ r : Mom d, K.vc.IsLadderGap L w (fun x => κ x.1) u v h.1 r ∧
      M.IsLadderGap L w κ u v (vc_isLadder K hB h).1.1 r := by
  obtain ⟨hlad, hS⟩ := vc_isLadder K hB h
  obtain ⟨hne_u, hne_v, hnuv⟩ := ladder_ne hlad
  have hm := h.1
  have h0 : (0 : Fin (m + 1)) ≠ ⟨1, by omega⟩ := fun e => by have := congrArg Fin.val e; simp at this
  obtain ⟨hr1, hr2, -⟩ := hlad.2.2.2.2 ⟨0, hm⟩
  have hr1' : M.bondsBetween (u 0) (u ⟨1, by omega⟩) = 1 := hr1
  have hr2' : M.bondsBetween (v 0) (v ⟨1, by omega⟩) = 1 := hr2
  obtain ⟨x, hx1, hx2⟩ := exists_dart_pair (hne_u _ _ h0) (by rw [hr1']; exact Nat.one_pos)
  obtain ⟨y, hy1, hy2⟩ := exists_dart_pair (hne_v _ _ h0) (by rw [hr2']; exact Nat.one_pos)
  have hgx : M.InGroup K.C.atoms x := by
    have he := atom_cases hx1
    rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ (hS 0).1, e2 ▸ (hS ⟨1, by omega⟩).1⟩
    · exact ⟨e1 ▸ (hS ⟨1, by omega⟩).1, e2 ▸ (hS 0).1⟩
  have hgy : M.InGroup K.C.atoms y := by
    have he := atom_cases hy1
    rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ (hS 0).2, e2 ▸ (hS ⟨1, by omega⟩).2⟩
    · exact ⟨e1 ▸ (hS ⟨1, by omega⟩).2, e2 ▸ (hS 0).2⟩
  refine ⟨Molecule.gapAt L w κ x y, ⟨⟨x, (vc_dart_iff K hB x).mpr hgx⟩, ⟨y, (vc_dart_iff K hB y).mpr hgy⟩, ?_, ?_, ?_, ?_, rfl⟩,
    ⟨x, y, hx1, hy1, hx2, hy2, rfl⟩⟩
  · rw [vc_ends_eq K hB]; exact hx1
  · rw [vc_ends_eq K hB]; exact hy1
  · rw [vc_atom_eq K hB]; exact hx2
  · rw [vc_atom_eq K hB]; exact hy2

variable (hMol : M.IsMolecule) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {X : VineType}
  (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower) (P : Finset V → ℝ)
include hB hMol hM

/-- **Scale of the vine gap seen from a chart rung inside a ladder of nonzero scale.** -/
theorem gain_scale {j : Fin A.indexing.shape.m} {S' : Finset V} (hj : gl K A P j = some S') (L : ℝ) (hL0 : 0 < L)
    (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (hscale : VCLadderScale K L w P κ) :
    (L⁻¹ ≤ P S' ∧ P S' ≤ 1) ∧ 8⁻¹ * P S' ≤ ‖Molecule.gapAt L w κ K.x₁ K.x₂‖ ∧
      (A.ζc j 0 ≠ 0 ∨ A.ζc j 1 ≠ 0) := by
  obtain ⟨hML, hP, hrx, hjn⟩ := gl_spec K A P hj
  obtain ⟨m, u, v, hlad, hat⟩ := mem_maximalLadders_isLadderSet hML
  obtain ⟨hlad', hS⟩ := vc_isLadder K hB hlad
  have hmem : rx A j ∈ Molecule.ladderAtoms u v := by rw [hat]; exact hrx
  rw [mem_ladderAtoms] at hmem
  have hch : ∃ i, ChartAt A u v i j := by
    rcases hmem with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨i, chartRung_of_mem hB A hlad' hS i hjn (Or.inl hi)⟩
    · exact ⟨i, chartRung_of_mem hB A hlad' hS i hjn (Or.inr hi)⟩
  obtain ⟨i, hi⟩ := hch
  obtain ⟨lam, hl4, hlz, hid⟩ := rung_scale K hB hMol hM A hlad' hS i j hi
  obtain ⟨r, hrvc, hrM⟩ := exists_ladderGap K hB hlad L w κ
  have hnorm := hid L w c κ hdec hc r hrM
  rcases hscale S' hML m u v hlad hat r hrvc with ⟨h0, -⟩ | ⟨hlo, hhi, hs1⟩
  · exact absurd h0 hP
  · have hPpos : 0 < P S' := lt_of_lt_of_le (inv_pos.mpr hL0) hlo
    have hlam : lam ≠ 0 := by
      intro h0
      rw [h0] at hnorm
      simp at hnorm
      rw [hnorm, norm_zero] at hs1
      linarith
    have hlam1 : (1 : ℝ) ≤ |(lam : ℝ)| := by
      have : 1 ≤ |lam| := Int.one_le_abs hlam
      have h2 : (1 : ℝ) ≤ ((|lam| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h2
    have hlam4 : |(lam : ℝ)| ≤ 4 := by
      have : ((|lam| : ℤ) : ℝ) ≤ 4 := by exact_mod_cast hl4
      simpa using this
    have hg0 : 0 ≤ ‖Molecule.gapAt L w κ K.x₁ K.x₂‖ := norm_nonneg _
    refine ⟨⟨hlo, hhi⟩, ?_, hlz hlam⟩
    rw [hnorm] at hs1
    nlinarith

end Scale

end WaveTurbulence.VineCount
