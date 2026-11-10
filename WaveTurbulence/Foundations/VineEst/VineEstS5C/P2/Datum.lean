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

end WaveTurbulence.VineEstS5C.P2
