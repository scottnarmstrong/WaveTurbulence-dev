/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Admiss
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintAlgebraicHypotheses
public import WaveTurbulence.Foundations.SumintPar.Final

/-! # P2: the concrete `SumintPar` datum of a level (step 5)

* `pieceDatum D₀ a b wN wDec`: the field-by-field copy `SumintPar.ofOrig D₀ a b` of a `WaveTurbulence.SumintDatum` (e.g. `sourceSumintDatum`;
  `a, b` the core signs of the assembly, `assemblyCoreFirstSign`, `assemblyCoreSign`) with the regularity numerals `wN`, `wDec` of the piece
  (`wN = A ≤ 30 d - 1`, `wDec = 30 d`, R30).
* `modPiece D bk cons g g'`: update of `badKind`, `constraints`, `g`, `g'` (the clause data of the piece).
* `structAdm_of_algebraic`: `StructAdm (pieceDatum ..)` from `SumintAlgebraicHypotheses D₀ A` (proved for `sourceSumintDatum` by
  `sourceSumintDatum_algebraic_hypotheses`), the bounds of the unit intervals and `d + 1 ≤ wN`, `d < wDec`.
* `structAdm_modPiece`: `StructAdm` is unaffected by `modPiece`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A

variable {d : ℕ}

/-- The piece datum: the copy of `D₀` with the regularity numerals of the piece. -/
noncomputable def pieceDatum (D₀ : WaveTurbulence.SumintDatum d) (a b : Fin D₀.S.I → ℤˣ) (wN wDec : ℕ) :
    SumintPar.SumintDatum d :=
  { SumintPar.ofOrig D₀ a b with wN := wN, wDec := wDec }

/-- The clause data of a piece: `badKind`, order constraints, and the exponents `g`, `g'`. -/
noncomputable def modPiece (D : SumintPar.SumintDatum d) (bk : Fin D.S.I → Fin 4)
    (cons : Finset (D.S.TVar × D.S.TVar)) (g g' : D.S.VIdx → ℕ) : SumintPar.SumintDatum d :=
  { D with badKind := bk, constraints := cons, g := g, g' := g' }

theorem structAdm_modPiece {D : SumintPar.SumintDatum d} {A L γ η : ℝ} {Dsteps : ℕ}
    (hS : StructAdm D A L γ η Dsteps) (bk : Fin D.S.I → Fin 4) (cons : Finset (D.S.TVar × D.S.TVar))
    (g g' : D.S.VIdx → ℕ) : StructAdm (modPiece D bk cons g g') A L γ η Dsteps := by
  obtain ⟨h1, h2, h3, h4, h6a, h6b, h7, h8, h10⟩ := hS
  exact ⟨h1, h2, h3, h4, h6a, h6b, h7, h8, h10⟩

theorem rowTf_eq {S : WaveTurbulence.SumintShape} (T₁ T₂ : S.VIdx → S.VIdx → ℤ) :
    rowTf T₁ T₂ = WaveTurbulence.VineEstS2.sumintFormRowT T₁ T₂ := by
  funext z; rcases z with w | w | c <;> rfl

theorem rowHf_eq {S : WaveTurbulence.SumintShape} (H₁ H₂ : S.VIdx → Fin 4 → ℤ) :
    rowHf H₁ H₂ = WaveTurbulence.VineEstS2.sumintFormRowH H₁ H₂ := by
  funext z; rcases z with w | w | c <;> rfl

theorem structAdm_of_algebraic (D₀ : WaveTurbulence.SumintDatum d) (a b : Fin D₀.S.I → ℤˣ) (wN wDec : ℕ) {A L γ η : ℝ}
    {Dsteps : ℕ} (hA : WaveTurbulence.VineEstS2.SumintAlgebraicHypotheses D₀ A)
    (hq : ∀ v, D₀.q v + 1 ≤ Dsteps) (hqo : ∀ c, D₀.qOut c + 1 ≤ Dsteps) (hN : d + 1 ≤ wN) (hD : d < wDec) :
    StructAdm (pieceDatum D₀ a b wN wDec) A L γ η Dsteps := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
  refine ⟨?_, h2, h3, ?_, h5, h6, hq, hqo, hN, hD⟩
  · intro v
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ := h1 v
    exact ⟨u1, u2, u3, u4, u5, u6⟩
  · intro v
    obtain ⟨p, q, hp⟩ := h4 v
    refine ⟨p, q, ?_⟩
    simp only [pieceDatum, SumintPar.ofOrig, rowTf_eq, rowHf_eq]
    refine ⟨fun j => ?_, hp.2⟩
    convert hp.1 j
    all_goals first | rfl | exact congrFun (congrFun (rowTf_eq _ _) _) _ | exact Subsingleton.elim _ _

/-- The bad-case clause of `BadClauseP` at one block. -/
def BadAt (D : SumintPar.SumintDatum d) (i : Fin D.S.I) : Prop :=
  (D.badKind i = 0 → ∃ h : 0 < D.S.m i,
      let t0 : D.S.TVar := .inl ⟨i, 0⟩
      let t1 : D.S.TVar := .inl ⟨i, ⟨1, by omega⟩⟩
      let s1 : D.S.TVar := .inr (.inl ⟨i, ⟨0, h⟩⟩)
      ((s1, t0) ∈ D.constraints ∧ (t0, t1) ∈ D.constraints) ∨
        ((t1, t0) ∈ D.constraints ∧ (t0, s1) ∈ D.constraints)) ∧
    (D.badKind i = 2 → 0 < D.S.m i) ∧
    (D.badKind i = 3 → ∃ j : Fin (D.S.n i), 1 ≤ max (D.g ⟨i, j⟩) (D.g' ⟨i, j⟩))

theorem badAt_kind1 {D : SumintPar.SumintDatum d} {i : Fin D.S.I} (h : D.badKind i = 1) : BadAt D i :=
  ⟨fun h0 => absurd (h0.symm.trans h) (by decide), fun h2 => absurd (h2.symm.trans h) (by decide),
    fun h3 => absurd (h3.symm.trans h) (by decide)⟩

theorem badAt_kind2 {D : SumintPar.SumintDatum d} {i : Fin D.S.I} (h : D.badKind i = 2) (hm : 0 < D.S.m i) :
    BadAt D i :=
  ⟨fun h0 => absurd (h0.symm.trans h) (by decide), fun _ => hm, fun h3 => absurd (h3.symm.trans h) (by decide)⟩

theorem badAt_kind3 {D : SumintPar.SumintDatum d} {i : Fin D.S.I} (h : D.badKind i = 3)
    (hj : ∃ j : Fin (D.S.n i), 1 ≤ max (D.g ⟨i, j⟩) (D.g' ⟨i, j⟩)) : BadAt D i :=
  ⟨fun h0 => absurd (h0.symm.trans h) (by decide), fun h2 => absurd (h2.symm.trans h) (by decide), fun _ => hj⟩

theorem badAt_kind0' {D : SumintPar.SumintDatum d} {i : Fin D.S.I} (h : D.badKind i = 0) (hm : 0 < D.S.m i)
    (hc : (((.inr (.inl ⟨i, ⟨0, hm⟩⟩) : D.S.TVar), (.inl ⟨i, 0⟩ : D.S.TVar)) ∈ D.constraints ∧
        ((.inl ⟨i, 0⟩ : D.S.TVar), (.inl ⟨i, ⟨1, by omega⟩⟩ : D.S.TVar)) ∈ D.constraints) ∨
      (((.inl ⟨i, ⟨1, by omega⟩⟩ : D.S.TVar), (.inl ⟨i, 0⟩ : D.S.TVar)) ∈ D.constraints ∧
        ((.inl ⟨i, 0⟩ : D.S.TVar), (.inr (.inl ⟨i, ⟨0, hm⟩⟩) : D.S.TVar)) ∈ D.constraints)) : BadAt D i :=
  ⟨fun _ => ⟨hm, hc⟩, fun h2 => absurd (h2.symm.trans h) (by decide), fun h3 => absurd (h3.symm.trans h) (by decide)⟩

theorem modPiece_badKind_self (D : SumintPar.SumintDatum d) (i₀ : Fin D.S.I) (k : Fin 4)
    (cons : Finset (D.S.TVar × D.S.TVar)) (g g' : D.S.VIdx → ℕ) :
    (modPiece D (Function.update D.badKind i₀ k) cons g g').badKind i₀ = k := by
  show Function.update D.badKind i₀ k i₀ = k
  exact Function.update_self _ _ _

theorem badClauseP_iff (D : SumintPar.SumintDatum d) : BadClauseP D ↔ ∀ i, D.S.nor i = false → BadAt D i := Iff.rfl

/-- **The bad-case clause of the piece datum.**  The blocks other than `i₀` keep their kind and clause (the constraints and the
exponents only grow); at `i₀` the clause `BadAt` of the new datum is the hypothesis `hi₀` (kind `0`: the two order constraints of clause (a),
supplied in `extra`, `badAt_kind0`; kind `2`: `0 < m i₀`; kind `3`: an exponent `≥ 1`). -/
theorem badClauseP_modPiece {D : SumintPar.SumintDatum d} (hb : BadClauseP D) (i₀ : Fin D.S.I) (k : Fin 4)
    (extra : Finset (D.S.TVar × D.S.TVar)) (g g' : D.S.VIdx → ℕ) (hg : ∀ v, D.g v ≤ g v) (hg' : ∀ v, D.g' v ≤ g' v)
    (hi₀ : D.S.nor i₀ = false →
      BadAt (modPiece D (Function.update D.badKind i₀ k) (D.constraints ∪ extra) g g') i₀) :
    BadClauseP (modPiece D (Function.update D.badKind i₀ k) (D.constraints ∪ extra) g g') := by
  rw [badClauseP_iff]
  intro i hi
  by_cases hii : i = i₀
  · exact hii ▸ hi₀ (hii ▸ hi)
  · have hk : (modPiece D (Function.update D.badKind i₀ k) (D.constraints ∪ extra) g g').badKind i = D.badKind i := by
      show Function.update D.badKind i₀ k i = D.badKind i
      exact Function.update_of_ne hii _ _
    obtain ⟨b0, b2, b3⟩ := hb i hi
    refine ⟨fun h0 => ?_, fun h2 => ?_, fun h3 => ?_⟩
    · rw [hk] at h0
      obtain ⟨hm, hc⟩ := b0 h0
      refine ⟨hm, ?_⟩
      simp only [modPiece]
      rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
      · exact Or.inl ⟨Finset.mem_union_left _ c1, Finset.mem_union_left _ c2⟩
      · exact Or.inr ⟨Finset.mem_union_left _ c1, Finset.mem_union_left _ c2⟩
    · rw [hk] at h2; exact b2 h2
    · rw [hk] at h3
      obtain ⟨j, hj⟩ := b3 h3
      exact ⟨j, hj.trans (max_le_max (hg _) (hg' _))⟩

end WaveTurbulence.VineEstS5C.P2
