/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.LevelSS
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.LevelJS
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.LevelR
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Pieces
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Mono
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.ConjNorm
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Space

/-! # P2: the piece bounds, uniform output form (V5 Step 4d part C, step 7)

`Amb A P D`: the ambient engine data of one level (the hypotheses common to `level_SS/JS/SR/RS/RR`).  `PieceBound Z Kw Ks Lw Ls bK bL`: there are
rows `K, L` of the vine `Z.v0` with weights `Kw`, `Lw` (functions of the three clocks `c`, of `r` and of `k`) at the slots `Ks`, `Ls` whose merged
clocked expression obeys the engine bound with the row sizes `bK`, `bL`.  The theorems `piece_*` deliver this for each type of piece of
`zpPieces` from the separated data `(c, J, M)` of the approximants and the gate remainders.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal ComplexConjugate

/-- The `D`-independent hypotheses of the engine data of a level (a `Prop`, so constants depending on it depend on `(A, P)` only). -/
structure AmbP (A : ℝ) (P : WTParams) : Prop where
  hdb : SumintMixParDoubledAt A P
  hL : 0 < P.L
  hη0 : 0 < P.η
  hη1 : P.η ≤ 1 / 2
  hη4 : P.η < 1 / 4
  hC1 : 0 ≤ P.C₁
  hδ : 0 < P.δ
  hd1 : 1 ≤ P.d
  hθ' : 6 * P.η ^ 6 ≤ 1 - P.η
  hθη : 6 * P.η ^ 6 ≤ P.η
  hη3 : 3 * P.η ≤ 1

/-- The ambient engine data of one operative vine level. -/
structure Amb (A : ℝ) (P : WTParams) (D : SumintPar.SumintDatum P.d) extends AmbP A P where
  hI : 0 < D.S.I
  Mx : CharMix D.S P.d
  Cph : ℝ
  hCph0 : 0 ≤ Cph
  hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph
  hreg : P.d < D.wDec
  hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
    WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D
  hM : D.S.M ≤ P.N 1 ^ 4
  cr0 : ClockedRows3 D
  M0 : ClockedModes3 D (6 * P.η ^ 6)
  v0 : D.S.VIdx
  h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
    ρ ≠ Sum.inl v0 → ρ ≠ Sum.inr v0 → ∀ r k : Mom P.d,
      HasSum (fun m => M0.c ρ m r k * fsPhase m (cr0.clock τ tt ρ)) (cr0.W ρ (cr0.clock τ tt ρ) r k)

variable {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d}

/-- The engine prefactor of the single-level bound. -/
noncomputable def Amb.pre (Z : Amb A P D) : ℝ≥0∞ :=
  (ccη P.η + 1) * ENNReal.ofReal (Z.Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
    sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)))

/-- The product of the sizes of the rows of the other vines. -/
noncomputable def Amb.others (Z : Amb A P D) : ℝ≥0∞ :=
  ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl Z.v0)).erase (Sum.inr Z.v0), Z.M0.b ρ

/-- **The uniform output of a piece bound**: rows `K, L` of the vine with the given weights and slots, such that the merged clocked
expression is bounded by `pre * (bK * bL * others)`. -/
def PieceBound (Z : Amb A P D) (Kw : (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (Ks : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
    (Lw : (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (Ls : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (bK bL : ℝ≥0∞) : Prop :=
  ∃ (K : RowData D (6 * P.η ^ 6) (Sum.inl Z.v0)) (L : RowData D (6 * P.η ^ 6) (Sum.inr Z.v0)),
    (∀ c r k, K.W c r k = Kw c r k) ∧ (∀ i, K.slot i = Ks i) ∧ (∀ c r k, L.W c r k = Lw c r k) ∧ (∀ i, L.slot i = Ls i) ∧
    K.Ae Z.hI ∧ L.Ae Z.hI ∧
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Z.Mx (mergeCR Z.cr0 Z.v0 K L) Z.hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      Z.pre * (bK * bL * Z.others)

theorem PieceBound.mono {Z : Amb A P D} {Kw Lw : (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {Ks Ls : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D}
    {bK bL bK' bL' : ℝ≥0∞} (h : PieceBound Z Kw Ks Lw Ls bK bL) (hK : bK ≤ bK') (hL : bL ≤ bL') :
    PieceBound Z Kw Ks Lw Ls bK' bL' := by
  obtain ⟨K, L, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨K, L, h1, h2, h3, h4, h5, h6, h7.trans (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' hK hL) le_rfl))⟩

theorem bound_aux {a a' b b' : ℝ≥0∞} (ha : a ≤ a') (hb : b ≤ b') (pre o : ℝ≥0∞) :
    pre * (a * b * o) ≤ pre * (a' * b' * o) := mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' ha hb) le_rfl)

/-- The `𝔖`-bound at the numerals of the datum from the `SNormR (30 d)` bound of a real spatial factor. -/
theorem sn_of_snormR {W Λ Λ₂ : ℕ} {M : Mom P.d → ℝ} {β : ℝ} (hβ : 0 ≤ β) (hd : 1 ≤ P.d) (hΛ : Λ ≤ 30 * P.d) (hW : W ≤ Λ₂)
    (h : SNormR (30 * P.d) Λ₂ M ≤ ENNReal.ofReal β) : SNorm Λ W (cm M) ≤ ENNReal.ofReal β :=
  snorm_lower (by omega) hΛ hW hβ h

end WaveTurbulence.VineEstS5C.P2
