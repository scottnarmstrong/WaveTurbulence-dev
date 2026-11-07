/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceSS

/-! # P2: piece bounds with a joint (clause (c)) 𝒦 row: TQ and TT

The 𝒦 row is `|c₀-c₁|^{-(1-3η)} (J(c₀,c₂) - J(c₁,c₂)) · M(r,k)` at three clocks (`jointRow_exists`); the ℒ row is a separated row. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal ComplexConjugate

variable {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d}
variable {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}

/-- **Piece TQ** (clause (c), couple): the 𝒦 row is the joint row of `conj Jq` with the spatial factor `spShift cq Mq ε`, the ℒ row `Jt · spPlain`. -/
theorem piece_TQ (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d) {ε : ℝ} (hε : |ε| ≤ 1)
    (sq : SepT P (30 * P.d) Bq qq CJq CMq) (st : SepT P 0 Bt qt CJt CMt) 
    (vK : Fin 3 → D.S.TVar) (vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
    (qK : Fin 3 → ℝ) (BK : Set (Fin 3 → ℝ)) (hcK : BK ⊆ cell qK) (iK : BK ⊆ closure (interior BK)) (hRb : ∀ τ ∈ BK, ‖τ‖ ≤ Rb)
    (hB2 : ∀ τ ∈ BK, ![τ 0, τ 2] ∈ Bq ∧ ![τ 1, τ 2] ∈ Bq)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ BK)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Bt),
    PieceBound Z
      (fun c r k => ((((|c 0 - c 1| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) * (cJ sq.J ![c 0, c 2] - cJ sq.J ![c 1, c 2])) * spShift sq.c sq.M ε r k))
      (fun i => Sum.inl (vK i))
      (fun c r k => st.J ![c 0, c 1] * spPlain st.c st.M r k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
      (C' * ENNReal.ofReal CJq * ENNReal.ofReal (|sq.c| * ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ D.wN * CMq)))
      (C * ENNReal.ofReal CJt * ENNReal.ofReal (|st.c| * CMt)) := by
  obtain ⟨C, C', hC, hC', h⟩ := level_JS G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1 G.hη4 (by have := G.hη0; positivity) G.hθ' G.hθη Rb
  refine ⟨C, C', hC, hC', ?_⟩
  intro D Z Bq Bt qq qt CJq CMq CJt CMt hwN hwDec ε hε sq st vK vL hvK hvL qK BK hcK iK hRb hB2 hclK hclL
  have hK := supK_shift hwN hwDec G.hd1 Z.v0 sq hε
  have hL := supL_plain hwN hwDec G.hd1 Z.v0 st
  obtain ⟨K, L, hKW, hLW, hKs, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM Z.cr0 Z.M0 Z.v0 Z.h0
    vK vL hvK hvL qK qt Bq BK Bt (cJ sq.J) st.J (ENNReal.ofReal CJq) (ENNReal.ofReal CJt) (spShift sq.c sq.M ε) (spPlain st.c st.M)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hcK iK hRb hB2 st.hcell st.hint sq.hJc st.hJ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL) (fun _ _ _ => rfl) hclK hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb.trans (bound_aux (mul_le_mul' le_rfl hK) (mul_le_mul' le_rfl hL) _ _)⟩

/-- **Piece TT** (clause (c), tree): the 𝒦 row is the joint row of `conj Jt` with `spProd (cq ct) Mq Mt`, the ℒ row `Jq · spOne`. -/
theorem piece_TT (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
    (sq : SepT P (30 * P.d) Bq qq CJq CMq) (st : SepT P 0 Bt qt CJt CMt) 
    (vK : Fin 3 → D.S.TVar) (vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
    (qK : Fin 3 → ℝ) (BK : Set (Fin 3 → ℝ)) (hcK : BK ⊆ cell qK) (iK : BK ⊆ closure (interior BK)) (hRb : ∀ τ ∈ BK, ‖τ‖ ≤ Rb)
    (hB2 : ∀ τ ∈ BK, ![τ 0, τ 2] ∈ Bt ∧ ![τ 1, τ 2] ∈ Bt)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ BK)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Bq),
    PieceBound Z
      (fun c r k => ((((|c 0 - c 1| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) * (cJ st.J ![c 0, c 2] - cJ st.J ![c 1, c 2])) * spProd (sq.c * st.c) sq.M st.M r k))
      (fun i => Sum.inl (vK i))
      (fun c r k => sq.J ![c 0, c 1] * spOne r k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
      (C' * ENNReal.ofReal CJt * ENNReal.ofReal (|sq.c * st.c| * ((2 : ℝ) ^ D.wN * (P.d : ℝ) ^ D.wN * CMt * CMq)))
      (C * ENNReal.ofReal CJq * ENNReal.ofReal 1) := by
  obtain ⟨C, C', hC, hC', h⟩ := level_JS G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1 G.hη4 (by have := G.hη0; positivity) G.hθ' G.hθη Rb
  refine ⟨C, C', hC, hC', ?_⟩
  intro D Z Bq Bt qq qt CJq CMq CJt CMt hwN hwDec sq st vK vL hvK hvL qK BK hcK iK hRb hB2 hclK hclL
  have hK := supK_prod hwN hwDec G.hd1 Z.v0 sq st
  have hL := supL_one hwN hwDec G.hd1 (D := D) Z.v0
  obtain ⟨K, L, hKW, hLW, hKs, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM Z.cr0 Z.M0 Z.v0 Z.h0
    vK vL hvK hvL qK qq Bt BK Bq (cJ st.J) sq.J (ENNReal.ofReal CJt) (ENNReal.ofReal CJq) (spProd (sq.c * st.c) sq.M st.M) spOne
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hcK iK hRb hB2 sq.hcell sq.hint st.hJc sq.hJ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL) (fun _ _ _ => rfl) hclK hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb.trans (bound_aux (mul_le_mul' le_rfl hK) (mul_le_mul' le_rfl hL) _ _)⟩

end WaveTurbulence.VineEstS5C.P2
