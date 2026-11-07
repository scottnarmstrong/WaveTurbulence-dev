/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecDispU
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMerge

/-! # P4-W2 (session 18, step 3a): merging the exceptional pieces into one row family

`PieceRepW`: the content of `PieceRepU` for explicit rows `RK`, `RL`.  `rows_merge`: given a native row family and, for every record `k` of a finite index set, a `PieceRepU` at distinct rows
`vpf k` (pair row) and `vbf k` (branch row), there is one row family which is native off the exceptional rows and carries the `PieceRepW` of every record at its rows.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate

variable {P : WTParams}

/-- `PieceRepU` for explicit rows. -/
def PieceRepW {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) {vp vb : D.S.VIdx}
    (RK : RowData D (6 * P.η ^ 6) (Sum.inl vp)) (RL : RowData D (6 * P.η ^ 6) (Sum.inr vb)) (ε : ℝ)
    (f0 : (D.S.TVar → ℝ) → Mom P.d → ℂ) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (bnd : ℝ≥0∞)
    (Bx : Set (Fin 3 → ℝ)) : Prop :=
  RK.Ae hI ∧ RL.Ae hI ∧
    (∀ cl r k, RK.W cl r k = ∑' m, RK.c m r k * fsPhase m cl) ∧
    (∀ cl r k, RL.W cl r k = ∑' m, RL.c m r k * fsPhase m cl) ∧ RK.b * RL.b ≤ bnd ∧
    ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
      X τ tt r k = f0 τ r * (RK.W (RK.clk τ tt) r k * RL.W (RL.clk τ tt) r (k + ε • r))

theorem pieceRepU_iff {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (vp vb : D.S.VIdx) (ε : ℝ)
    (f0 : (D.S.TVar → ℝ) → Mom P.d → ℂ) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (bnd : ℝ≥0∞)
    (Bx : Set (Fin 3 → ℝ)) :
    PieceRepU hI vp vb ε f0 X bnd Bx ↔ ∃ (RK : RowData D (6 * P.η ^ 6) (Sum.inl vp)) (RL : RowData D (6 * P.η ^ 6) (Sum.inr vb)),
      PieceRepW hI RK RL ε f0 X bnd Bx := Iff.rfl

open Classical in
theorem rows_merge {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Rw : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ)
    {κ : Type*} (S : Finset κ) (vpf vbf : κ → D.S.VIdx)
    (hinjp : ∀ k ∈ S, ∀ k' ∈ S, vpf k = vpf k' → k = k') (hinjb : ∀ k ∈ S, ∀ k' ∈ S, vbf k = vbf k' → k = k')
    (ε : κ → ℝ) (f0 : κ → (D.S.TVar → ℝ) → Mom P.d → ℂ)
    (X : κ → (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (bnd : κ → ℝ≥0∞) (Bx : Set (Fin 3 → ℝ))
    (hP : ∀ k ∈ S, PieceRepU hI (vpf k) (vbf k) (ε k) (f0 k) (X k) (bnd k) Bx) :
    ∃ Rw' : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ,
      (∀ ρ, (∀ k ∈ S, ρ ≠ Sum.inl (vpf k) ∧ ρ ≠ Sum.inr (vbf k)) → Rw' ρ = Rw ρ) ∧
      ∀ k ∈ S, PieceRepW hI (Rw' (Sum.inl (vpf k))) (Rw' (Sum.inr (vbf k))) (ε k) (f0 k) (X k) (bnd k) Bx := by
  have hP' : ∀ k, ∃ (RK : k ∈ S → RowData D (6 * P.η ^ 6) (Sum.inl (vpf k))) (RL : k ∈ S → RowData D (6 * P.η ^ 6) (Sum.inr (vbf k))),
      ∀ hk : k ∈ S, PieceRepW hI (RK hk) (RL hk) (ε k) (f0 k) (X k) (bnd k) Bx := by
    intro k
    by_cases hk : k ∈ S
    · obtain ⟨RK, RL, h⟩ := hP k hk
      exact ⟨fun _ => RK, fun _ => RL, fun _ => h⟩
    · exact ⟨fun h => absurd h hk, fun h => absurd h hk, fun h => absurd h hk⟩
  choose RK RL hRKL using hP'
  let idx : κ ⊕ κ → Row D := Sum.elim (fun k => Sum.inl (vpf k)) (fun k => Sum.inr (vbf k))
  have hinj : ∀ k ∈ S.disjSum S, ∀ k' ∈ S.disjSum S, idx k = idx k' → k = k' := by
    intro k hk k' hk' h
    rcases k with k | k <;> rcases k' with k' | k' <;> simp only [idx, Sum.elim_inl, Sum.elim_inr, reduceCtorEq] at h
    · exact congrArg Sum.inl (hinjp k (by simpa using hk) k' (by simpa using hk') (Sum.inl.inj h))
    · exact congrArg Sum.inr (hinjb k (by simpa using hk) k' (by simpa using hk') (Sum.inr.inj h))
  let Rk : ∀ k ∈ S.disjSum S, RowData D (6 * P.η ^ 6) (idx k) := fun k hk =>
    match k, hk with
    | Sum.inl k, hk => RK k (by simpa using hk)
    | Sum.inr k, hk => RL k (by simpa using hk)
  obtain ⟨Rw', h1, h2⟩ := exists_row_merge Rw (S.disjSum S) idx hinj Rk
  refine ⟨Rw', fun ρ hρ => h1 ρ fun k hk => ?_, fun k hk => ?_⟩
  · rcases k with k | k
    · exact (hρ k (by simpa using hk)).1 ∘ Eq.symm
    · exact (hρ k (by simpa using hk)).2 ∘ Eq.symm
  · have e1 := h2 (Sum.inl k) (by simpa using hk)
    have e2 := h2 (Sum.inr k) (by simpa using hk)
    have := hRKL k hk
    simp only [idx, Sum.elim_inl, Sum.elim_inr] at e1 e2
    rw [e1, e2]
    exact this

end WaveTurbulence.VineEstS5C.P4.W2
