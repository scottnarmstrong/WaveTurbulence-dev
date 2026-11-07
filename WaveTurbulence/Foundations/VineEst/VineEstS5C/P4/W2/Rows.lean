/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceRem
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceJoint
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.RemAe

/-! # P4-W2: the rows of the pieces, exported one by one (with their a.e. mode expansion)

P2's `piece_*` theorems build the two rows `K, L` of a piece inside a `PieceBound`, i.e. for the rows `Sum.inl v₀`, `Sum.inr v₀` of ONE
vine `v₀` merged into an ambient family.  A term of the unrolled class sum has a piece at every operative vine, and the `𝒦` row of a piece
sits at the vine of the exceptional pair while its `ℒ` row sits at the vine of the lower joint (design point W2-D3: the two need not be the
same sumint row, R22's pair bijection is free).  So the rows are exported here one at a time, for an arbitrary row `ρ` of an arbitrary datum,
with uniform constants (depending on `P` only), each with its `Ae` (a.e. mode expansion on the time domain):

* `sepRowW`: the separated row `J(c₀,c₁) · M(r,k)` (rows of the pieces A1, A2, KQ, KT and the ℒ rows of TQ, TT, with the spatial factors
  `spPlain`, `spDiff`, `spProdDiff`, `spOne` and the bounds `supK_*`, `supL_*` of P2);
* `jointRowW`: the joint three-clock row of clause (c) (𝒦 rows of TQ, TT, spatial factors `spShift`, `spProd`);
* `remRowW`: the remainder row (pieces SR, RS, RR), a.e.-continuous representative.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

variable {A : ℝ} {P : WTParams}

/-- **A separated row, exported** (any row `ρ` of any datum): `W = J(c₀,c₁) M(r,k)` at the clocks `(v 0, v 1)`, size `≤ C · CJ · Cm`. -/
theorem sepRowW (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (ρ : Row D) (v : Fin 2 → D.S.TVar)
      (_hv : Function.Injective v) (q : Fin 2 → ℝ) (B2 : Set (Fin 2 → ℝ)) (J : (Fin 2 → ℝ) → ℂ) (CJ Cm : ℝ)
      (M : Mom P.d → Mom P.d → ℂ), B2 ⊆ cell q → B2 ⊆ closure (interior B2) →
      XNorm00Restr (V := Unit) (1 - P.η) B2 Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D ρ) (M r)) ≤ ENNReal.ofReal Cm →
      (∀ w, ρ = Sum.inr w → ∀ r r' k : Mom P.d, M r k = M r' k) →
      (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (v i)) ∈ B2) →
      ∃ R : RowData D (6 * P.η ^ 6) ρ,
        (∀ c r k, R.W c r k = J ![c 0, c 1] * M r k) ∧
        (∀ i, R.slot i = Sum.inl (![v 0, v 1, v 0] i)) ∧
        R.b ≤ C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ∧ R.Ae hI := by
  obtain ⟨C, hC, h⟩ := sepRow2_exists (d := P.d) (by have := G.hη0; positivity) G.hθ'
  refine ⟨C, hC, fun D hI ρ v hv q B2 J CJ Cm M hc hi hJ hM hind hclock => ?_⟩
  obtain ⟨R, hW, hs, hb, hae⟩ := h D hI ρ v hv q B2 J (ENNReal.ofReal CJ) M ENNReal.ofReal_ne_top hc hi hJ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM) hind hclock
  exact ⟨R, hW, hs, hb.le.trans (mul_le_mul' le_rfl hM), hae⟩

/-- **The joint three-clock row of clause (c), exported** (any `𝒦` row): `W = |c₀-c₁|^{-(1-3η)} (J(c₀,c₂) - J(c₁,c₂)) M(r,k)`. -/
theorem jointRowW (G : AmbP A P) (Rb : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx) (v : Fin 3 → D.S.TVar)
      (_hv : Function.Injective v) (q : Fin 3 → ℝ) (B2 : Set (Fin 2 → ℝ)) (B3 : Set (Fin 3 → ℝ))
      (J : (Fin 2 → ℝ) → ℂ) (CJ Cm : ℝ) (M : Mom P.d → Mom P.d → ℂ), B3 ⊆ cell q →
      B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) → (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      XNorm00Restr (V := Unit) (1 - P.η) B2 Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r)) ≤ ENNReal.ofReal Cm →
      (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (v i)) ∈ B3) →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀),
        (∀ c r k, R.W c r k = ((((|c 0 - c 1| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) * (J ![c 0, c 2] - J ![c 1, c 2])) * M r k)) ∧
        (∀ i, R.slot i = Sum.inl (v i)) ∧
        R.b ≤ C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ∧ R.Ae hI := by
  obtain ⟨C, hC, h⟩ := jointRow_exists (d := P.d) G.hη0 G.hη4 (by have := G.hη0; positivity) G.hθη Rb
  refine ⟨C, hC, fun D hI w₀ v hv q B2 B3 J CJ Cm M hc hi hR hB hJ hM hclock => ?_⟩
  obtain ⟨R, hW, hs, hb, hae⟩ := h D hI w₀ v hv q B2 B3 J (ENNReal.ofReal CJ) M ENNReal.ofReal_ne_top hc hi hR hB hJ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM) hclock
  exact ⟨R, hW, hs, hb.le.trans (mul_le_mul' le_rfl hM), hae⟩

/-- **A remainder row, exported** (any row with `D.wN = Λ₁`, `rowOrder D ρ = Λ₂`): `W = f(c₀,c₁,k)` with `f` a.e. equal on the box to a
time-continuous `f'` and `‖f‖_{X^{6η⁶}_{Λ₁,Λ₂}(B)} < b`; size `C · b`. -/
theorem remRowW (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) (hη0 : 0 < P.η) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (ρ : Row D), D.wN = Λ₁ → rowOrder D ρ = Λ₂ →
      ∀ (v : Fin 2 → D.S.TVar) (_hv : Function.Injective v) (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ))
      (f f' : (Fin 2 → ℝ) → Mom P.d → ℂ) (b : ℝ≥0∞),
      b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → (∀ k, Continuous fun t => f' t k) →
      (∀ᵐ t, t ∈ B → ∀ k, f t k = f' t k) →
      XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ B Set.univ f < b →
      (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (v i)) ∈ B) →
      ∃ R : RowData D (6 * P.η ^ 6) ρ, (∀ c r k, R.W c r k = f ![c 0, c 1] k) ∧
        (∀ i, R.slot i = Sum.inl (![v 0, v 1, v 0] i)) ∧ R.b = C * b ∧ R.Ae hI :=
  remRow_ae_exists (d := P.d) (by positivity) Λ₁ Λ₂ hΛ

end WaveTurbulence.VineEstS5C.P4.W2
