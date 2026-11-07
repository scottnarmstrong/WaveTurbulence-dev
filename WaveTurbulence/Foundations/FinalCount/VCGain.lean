/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCSpecial2
public import WaveTurbulence.Foundations.FinalCount.S1LadderMain
/-! # VINE-COUNT part 12: scale of a chart rung inside a ladder.

If a rung of a ladder of `M` inside the vine `S` is the chart rung `j`, then (all `κ`) the rail gap `r_lad` of the ladder
and the vine gap `r = gapAt x₁ x₂` satisfy `‖r_lad‖ = |λ_j| ‖r‖` for a fixed integer `|λ_j| ≤ 4`, and `λ_j ≠ 0`
forces `(ζ₀, ζ₁) ≠ 0` (this is the link lemma (b) of R17, `ingredient_gap_eq`/`railGap_norm_eq` replaced by the
chart identity `rung_lambda`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section SquareAt
variable {M : Molecule V D} {S : Finset V} {m : ℕ} {u v : Fin (m + 1) → V}

theorem square_of_lo (h : M.IsLadder u v) (hS : ∀ j, u j ∈ S ∧ v j ∈ S) (jj : Fin m) :
    ∃ (t' s' : V) (Q : Square M S (u jj.castSucc) (v jj.castSucc) t' s'),
      M.ends Q.p = s(u jj.castSucc, u jj.succ) ∧ M.ends Q.p' = s(v jj.castSucc, v jj.succ) := by
  obtain ⟨Q⟩ := ladder_square h hS jj
  exact ⟨_, _, Q, Q.p_ends, Q.p'_ends⟩

theorem square_of_hi (h : M.IsLadder u v) (hS : ∀ j, u j ∈ S ∧ v j ∈ S) (jj : Fin m) :
    ∃ (t' s' : V) (Q : Square M S (u jj.succ) (v jj.succ) t' s'),
      M.ends Q.p = s(u jj.castSucc, u jj.succ) ∧ M.ends Q.p' = s(v jj.castSucc, v jj.succ) := by
  obtain ⟨Q⟩ := ladder_square h hS jj
  exact ⟨_, _, Q.flip, Q.p_ends, Q.p'_ends⟩

theorem ladder_square_at' (h : M.IsLadder u v) (hS : ∀ j, u j ∈ S ∧ v j ∈ S) (i : Fin (m + 1)) :
    ∃ (t' s' : V) (Q : Square M S (u i) (v i) t' s') (jj : Fin m),
      M.ends Q.p = s(u jj.castSucc, u jj.succ) ∧ M.ends Q.p' = s(v jj.castSucc, v jj.succ) := by
  have hm : 1 ≤ m := h.1
  by_cases hi : i.val < m
  · obtain ⟨jj, hjj⟩ : ∃ jj : Fin m, jj.castSucc = i := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    subst hjj
    obtain ⟨t', s', Q, e1, e2⟩ := square_of_lo h hS jj
    exact ⟨t', s', Q, jj, e1, e2⟩
  · have hj : m - 1 < m := by omega
    obtain ⟨jj, hjj⟩ : ∃ jj : Fin m, jj.succ = i := ⟨⟨m - 1, hj⟩, Fin.ext (by simp; omega)⟩
    subst hjj
    obtain ⟨t', s', Q, e1, e2⟩ := square_of_hi h hS jj
    exact ⟨t', s', Q, jj, e1, e2⟩

/-- A bond with ends `s(a,b)` has a dart at `a` with the same vector. -/
theorem exists_dart_at {e : D} {a b : V} (he : M.ends e = s(a, b)) :
    ∃ x, M.ends x = s(a, b) ∧ M.atom x = a ∧ (x = e ∨ x = M.mate e) := by
  rcases atom_cases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨e, he, h1, Or.inl rfl⟩
  · refine ⟨M.mate e, ?_, h2, Or.inr rfl⟩
    show s(M.atom (M.mate e), M.atom (M.mate (M.mate e))) = s(a, b)
    rw [M.mate_mate, h1, h2, Sym2.eq_swap]

end SquareAt

section RungScale
variable {M : Molecule V D} (K : VineCut M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower) (hMol : M.IsMolecule)
  (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)
  {m : ℕ} {u v : Fin (m + 1) → V}
include hB hMol hM

theorem rung_scale (h : M.IsLadder u v) (hS : ∀ j, u j ∈ K.C.atoms ∧ v j ∈ K.C.atoms) (i : Fin (m + 1))
    (j : Fin A.indexing.shape.m)
    (hj : (u i = rx A j ∧ v i = ry A j) ∨ (u i = ry A j ∧ v i = rx A j)) :
    ∃ lam : ℤ, |lam| ≤ 4 ∧ (lam ≠ 0 → A.ζc j 0 ≠ 0 ∨ A.ζc j 1 ≠ 0) ∧
      ∀ (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)), M.IsDecoration L w c κ →
        (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) → ∀ r : Mom d, M.IsLadderGap L w κ u v h.1 r →
        ‖r‖ = |(lam : ℝ)| * ‖Molecule.gapAt L w κ K.x₁ K.x₂‖ := by
  obtain ⟨t', s', Q, jj, he1, he2⟩ := ladder_square_at' h hS i
  have hj' : ((A.indexing.atom (A.indexing.shape.xSlot j)).1 = u i ∧
        (A.indexing.atom (A.indexing.shape.ySlot j)).1 = v i) ∨
      ((A.indexing.atom (A.indexing.shape.xSlot j)).1 = v i ∧
        (A.indexing.atom (A.indexing.shape.ySlot j)).1 = u i) := by
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  obtain ⟨lam, hl4, hlz, hid⟩ := rung_lambda A Q j hj'
  refine ⟨lam, hl4, hlz, fun L w c κ hdec hc r hr => ?_⟩
  have h1 := hid d w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc)
  have hk : ∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    intro x; simp [Molecule.kvec, hdec.1 x]
  have hι : (incidence M (u i) Q.p : ℝ) = 1 ∨ (incidence M (u i) Q.p : ℝ) = -1 := by
    rcases Square.inc_pm (M := M) Q.htt Q.p_ends with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hn : ‖Molecule.kvec L w κ Q.p - Molecule.kvec L w κ Q.p'‖ = |(lam : ℝ)| * ‖Molecule.gapAt L w κ K.x₁ K.x₂‖ := by
    have h2 := congrArg norm h1
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg] at h2
    have h3 : |(incidence M (u i) Q.p : ℝ)| = 1 := by rcases hι with h | h <;> rw [h] <;> simp
    rw [h3, one_mul] at h2
    exact h2
  -- the rail gap `kvec p - kvec p'`
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_dart_at (M := M) he1
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_dart_at (M := M) he2
  have hkx : Molecule.kvec L w κ x = Molecule.kvec L w κ Q.p := by
    rcases hx3 with rfl | rfl
    · rfl
    · exact hk _
  have hky : Molecule.kvec L w κ y = Molecule.kvec L w κ Q.p' := by
    rcases hy3 with rfl | rfl
    · rfl
    · exact hk _
  have hrail : Stage1.IsRailGap M L w κ u v jj (Molecule.kvec L w κ Q.p - Molecule.kvec L w κ Q.p') :=
    ⟨x, y, hx1, hy1, hx2, hy2, by unfold Molecule.gapAt; rw [hkx, hky]⟩
  have hr0 : Stage1.IsRailGap M L w κ u v ⟨0, h.1⟩ r := (Stage1.isLadderGap_iff_railGap h.1).mp hr
  have := Stage1.railGap_norm_eq hMol h hdec hc hr0 hrail
  rw [this, hn]

end RungScale

end WaveTurbulence.VineCount
