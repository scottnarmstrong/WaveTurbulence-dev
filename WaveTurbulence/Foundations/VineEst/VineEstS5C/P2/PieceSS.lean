/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceBound

/-! # P2: piece bounds, separated 𝒦 and ℒ rows (pieces A1, A2, KQ, KT)

`SepT`: one separated term `c · J(t,s) · M(k)` of an approximant on a time box, with the bounds of `LeafwiseSeparated` (strict for `J`).
`sup_*`: the `sup_r 𝔖`-bounds of the spatial weights at the numerals `wN + 1 = 30 d`, `wDec = 30 d`.
`piece_A1`, `piece_A2`, `piece_KQ`, `piece_KT`: the rows of the pieces (a), (b) of `zpPieces` (`Pieces`: `pieceA1_term` …) with
`PieceBound`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal ComplexConjugate

/-- One separated term of an approximant on the time box `B`: `c · J(t,s) · M(k)` with `‖J‖_{X^{1-η}_0(B)} < CJ` and `‖M‖_{𝔖R(30d, Wm)} ≤ CM`. -/
structure SepT (P : WTParams) (Wm : ℕ) (B : Set (Fin 2 → ℝ)) (q : Fin 2 → ℝ) (CJ CM : ℝ) where
  c : ℝ
  J : (Fin 2 → ℝ) → ℂ
  M : Mom P.d → ℝ
  hcell : B ⊆ cell q
  hint : B ⊆ closure (interior B)
  hCJ : 0 ≤ CJ
  hCM : 0 ≤ CM
  hJ : XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ
  hM : SNormR (30 * P.d) Wm M ≤ ENNReal.ofReal CM

variable {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d}

theorem SepT.hJc {Wm : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ} (s : SepT P Wm B q CJ CM) :
    XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => cJ s.J ts) < ENNReal.ofReal CJ := by
  have := XNorm00Restr_conj (1 - P.η) B (Set.univ : Set Unit) (fun ts _ => s.J ts)
  exact this.symm ▸ s.hJ

theorem sn_lo (hd1 : 1 ≤ P.d) {A W Wm : ℕ} (hA : A ≤ 30 * P.d) (hW : W ≤ Wm) {M : Mom P.d → ℝ} {CM : ℝ}
    (hM : SNormR (30 * P.d) Wm M ≤ ENNReal.ofReal CM) (hCM : 0 ≤ CM) : SNorm A W (cm M) ≤ ENNReal.ofReal CM :=
  snorm_lower (by omega) hA hW hCM hM

section Sup
variable (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d) (hd1 : 1 ≤ P.d) {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ}
include hwN hwDec hd1

theorem supK_plain (v0 : D.S.VIdx) (s : SepT P (30 * P.d) B q CJ CM) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v0)) (spPlain s.c s.M r)) ≤ ENNReal.ofReal (|s.c| * CM) :=
  snorm_plain_le (A := D.wN) (W := D.wDec) (by omega) s.c s.hCM (sn_lo hd1 (by omega) (by omega) s.hM s.hCM)

theorem supL_plain (v0 : D.S.VIdx) (s : SepT P 0 B q CJ CM) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inr v0)) (spPlain s.c s.M r)) ≤ ENNReal.ofReal (|s.c| * CM) :=
  snorm_plain_le (A := D.wN) (W := 0) (by omega) s.c s.hCM (sn_lo hd1 (by omega) le_rfl s.hM s.hCM)

theorem supL_one (v0 : D.S.VIdx) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inr v0)) (spOne r)) ≤ ENNReal.ofReal 1 :=
  snorm_one_le' D.wN

theorem supK_diff (v0 : D.S.VIdx) (s : SepT P (30 * P.d) B q CJ CM) {ε : ℝ} (hε : |ε| ≤ 1) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v0)) (spDiff (-s.c) s.M ε r)) ≤
      ENNReal.ofReal (|-s.c| * ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ (D.wN + 1) * CM)) :=
  snorm_diff_le (A := D.wN) (W := D.wDec) (-s.c) s.hCM hε (sn_lo hd1 (by omega) (by omega) s.hM s.hCM)

theorem supK_shift (v0 : D.S.VIdx) (s : SepT P (30 * P.d) B q CJ CM) {ε : ℝ} (hε : |ε| ≤ 1) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v0)) (spShift s.c s.M ε r)) ≤
      ENNReal.ofReal (|s.c| * ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ D.wN * CM)) :=
  snorm_shift_le (A := D.wN) (W := D.wDec) hd1 (by omega) s.c s.hCM hε (sn_lo hd1 (by omega) (by omega) s.hM s.hCM)

theorem supK_prodDiff {B' : Set (Fin 2 → ℝ)} {q' : Fin 2 → ℝ} {CJ' CM' : ℝ} (v0 : D.S.VIdx) (sq : SepT P (30 * P.d) B q CJ CM)
    (st : SepT P 0 B' q' CJ' CM') {ε : ℝ} (hε : |ε| ≤ 1) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v0)) (spProdDiff (-(sq.c * st.c)) sq.M st.M ε r)) ≤
      ENNReal.ofReal (|-(sq.c * st.c)| * ((2 : ℝ) ^ D.wN * (P.d : ℝ) ^ D.wN * ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ (D.wN + 1) * CM') * CM)) :=
  snorm_prodDiff_le (A := D.wN) (W := D.wDec) hd1 (by omega) (-(sq.c * st.c)) sq.hCM st.hCM hε
    (sn_lo hd1 (by omega) (by omega) sq.hM sq.hCM) (sn_lo hd1 (by omega) le_rfl st.hM st.hCM)

theorem supK_prod {B' : Set (Fin 2 → ℝ)} {q' : Fin 2 → ℝ} {CJ' CM' : ℝ} (v0 : D.S.VIdx) (sq : SepT P (30 * P.d) B q CJ CM)
    (st : SepT P 0 B' q' CJ' CM') :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v0)) (spProd (sq.c * st.c) sq.M st.M r)) ≤
      ENNReal.ofReal (|sq.c * st.c| * ((2 : ℝ) ^ D.wN * (P.d : ℝ) ^ D.wN * CM' * CM)) :=
  snorm_prod_le (A := D.wN) (W := D.wDec) hd1 (by omega) (sq.c * st.c) sq.hCM st.hCM
    (sn_lo hd1 (by omega) (by omega) sq.hM sq.hCM) (sn_lo hd1 (by omega) le_rfl st.hM st.hCM)

end Sup


section Pieces
variable {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}

/-- **Piece A1** (`conj Q(s₁,t₀,y) T(t₁,t₀,x)`, 𝒦 at the clocks `vK`, ℒ at `vL`). -/
theorem piece_A1 (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
    (sq : SepT P (30 * P.d) Bq qq CJq CMq) (st : SepT P 0 Bt qt CJt CMt)
    (vK vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ Bq)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Bt),
    PieceBound Z (fun c r k => cJ sq.J ![c 0, c 1] * spPlain sq.c sq.M r k)
      (fun i => Sum.inl (![vK 0, vK 1, vK 0] i))
      (fun c r k => st.J ![c 0, c 1] * spPlain st.c st.M r k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
      (C * ENNReal.ofReal CJq * ENNReal.ofReal (|sq.c| * CMq)) (C * ENNReal.ofReal CJt * ENNReal.ofReal (|st.c| * CMt)) := by
  obtain ⟨C, hC, h⟩ := level_SS G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1 (by have := G.hη0; positivity) G.hθ'
  refine ⟨C, hC, ?_⟩
  intro D Z Bq Bt qq qt CJq CMq CJt CMt hwN hwDec sq st vK vL hvK hvL hclK hclL
  have hK := supK_plain hwN hwDec G.hd1 Z.v0 sq
  have hL := supL_plain hwN hwDec G.hd1 Z.v0 st
  obtain ⟨K, L, hKW, hLW, hKs, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM Z.cr0 Z.M0 Z.v0 Z.h0
    vK vL hvK hvL qq qt Bq Bt (cJ sq.J) st.J (ENNReal.ofReal CJq) (ENNReal.ofReal CJt) (spPlain sq.c sq.M) (spPlain st.c st.M)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top sq.hcell sq.hint st.hcell st.hint sq.hJc st.hJ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL) (fun _ _ _ => rfl) hclK hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb.trans (bound_aux (mul_le_mul' le_rfl hK) (mul_le_mul' le_rfl hL) _ _)⟩

/-- **Piece A2** (`Q(t₁,t₀,x) conj T(s₁,t₀,y)`, 𝒦 at `x`, ℒ at `y`). -/
theorem piece_A2 (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
    (sq : SepT P (30 * P.d) Bq qq CJq CMq) (st : SepT P 0 Bt qt CJt CMt)
    (vK vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ Bq)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Bt),
    PieceBound Z (fun c r k => sq.J ![c 0, c 1] * spPlain sq.c sq.M r k)
      (fun i => Sum.inl (![vK 0, vK 1, vK 0] i))
      (fun c r k => cJ st.J ![c 0, c 1] * spPlain st.c st.M r k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
      (C * ENNReal.ofReal CJq * ENNReal.ofReal (|sq.c| * CMq)) (C * ENNReal.ofReal CJt * ENNReal.ofReal (|st.c| * CMt)) := by
  obtain ⟨C, hC, h⟩ := level_SS G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1 (by have := G.hη0; positivity) G.hθ'
  refine ⟨C, hC, ?_⟩
  intro D Z Bq Bt qq qt CJq CMq CJt CMt hwN hwDec sq st vK vL hvK hvL hclK hclL
  have hK := supK_plain hwN hwDec G.hd1 Z.v0 sq
  have hL := supL_plain hwN hwDec G.hd1 Z.v0 st
  obtain ⟨K, L, hKW, hLW, hKs, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM Z.cr0 Z.M0 Z.v0 Z.h0
    vK vL hvK hvL qq qt Bq Bt sq.J (cJ st.J) (ENNReal.ofReal CJq) (ENNReal.ofReal CJt) (spPlain sq.c sq.M) (spPlain st.c st.M)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top sq.hcell sq.hint st.hcell st.hint sq.hJ st.hJc
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL) (fun _ _ _ => rfl) hclK hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb.trans (bound_aux (mul_le_mul' le_rfl hK) (mul_le_mul' le_rfl hL) _ _)⟩

/-- **Piece KQ** (clause (b), couple: `conj(Q(s₁,t₀,y) - Q(s₁,t₀,x)) T(t₁,t₀,x)`, the 𝒦 row carries the difference quotient). -/
theorem piece_KQ (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d) {ε : ℝ} (hε : |ε| ≤ 1)
    (sq : SepT P (30 * P.d) Bq qq CJq CMq) (st : SepT P 0 Bt qt CJt CMt)
    (vK vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ Bq)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Bt),
    PieceBound Z (fun c r k => cJ sq.J ![c 0, c 1] * spDiff (-sq.c) sq.M ε r k)
      (fun i => Sum.inl (![vK 0, vK 1, vK 0] i))
      (fun c r k => st.J ![c 0, c 1] * spPlain st.c st.M r k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
      (C * ENNReal.ofReal CJq * ENNReal.ofReal (|-sq.c| * ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ (D.wN + 1) * CMq)))
      (C * ENNReal.ofReal CJt * ENNReal.ofReal (|st.c| * CMt)) := by
  obtain ⟨C, hC, h⟩ := level_SS G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1 (by have := G.hη0; positivity) G.hθ'
  refine ⟨C, hC, ?_⟩
  intro D Z Bq Bt qq qt CJq CMq CJt CMt hwN hwDec ε hε sq st vK vL hvK hvL hclK hclL
  have hK := supK_diff hwN hwDec G.hd1 Z.v0 sq hε
  have hL := supL_plain hwN hwDec G.hd1 Z.v0 st
  obtain ⟨K, L, hKW, hLW, hKs, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM Z.cr0 Z.M0 Z.v0 Z.h0
    vK vL hvK hvL qq qt Bq Bt (cJ sq.J) st.J (ENNReal.ofReal CJq) (ENNReal.ofReal CJt) (spDiff (-sq.c) sq.M ε) (spPlain st.c st.M)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top sq.hcell sq.hint st.hcell st.hint sq.hJc st.hJ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL) (fun _ _ _ => rfl) hclK hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb.trans (bound_aux (mul_le_mul' le_rfl hK) (mul_le_mul' le_rfl hL) _ _)⟩

/-- **Piece KT** (clause (b), tree: `Q(t₁,t₀,x) conj(T(s₁,t₀,x) - T(s₁,t₀,y))`; the 𝒦 row carries `Jq · (N(k+εr)-N(k))/|r| · M(k)`,
the ℒ row is `conj Jt`). -/
theorem piece_KT (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d) {ε : ℝ} (hε : |ε| ≤ 1)
    (sq : SepT P (30 * P.d) Bq qq CJq CMq) (st : SepT P 0 Bt qt CJt CMt)
    (vK vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ Bq)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Bt),
    PieceBound Z (fun c r k => sq.J ![c 0, c 1] * spProdDiff (-(sq.c * st.c)) sq.M st.M ε r k)
      (fun i => Sum.inl (![vK 0, vK 1, vK 0] i))
      (fun c r k => cJ st.J ![c 0, c 1] * spOne r k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
      (C * ENNReal.ofReal CJq * ENNReal.ofReal (|-(sq.c * st.c)| * ((2 : ℝ) ^ D.wN * (P.d : ℝ) ^ D.wN *
        ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ (D.wN + 1) * CMt) * CMq)))
      (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) := by
  obtain ⟨C, hC, h⟩ := level_SS G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1 (by have := G.hη0; positivity) G.hθ'
  refine ⟨C, hC, ?_⟩
  intro D Z Bq Bt qq qt CJq CMq CJt CMt hwN hwDec ε hε sq st vK vL hvK hvL hclK hclL
  have hK := supK_prodDiff hwN hwDec G.hd1 Z.v0 sq st hε
  have hL := supL_one hwN hwDec G.hd1 (D := D) Z.v0
  obtain ⟨K, L, hKW, hLW, hKs, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM Z.cr0 Z.M0 Z.v0 Z.h0
    vK vL hvK hvL qq qt Bq Bt sq.J (cJ st.J) (ENNReal.ofReal CJq) (ENNReal.ofReal CJt) (spProdDiff (-(sq.c * st.c)) sq.M st.M ε) spOne
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top sq.hcell sq.hint st.hcell st.hint sq.hJ st.hJc
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL) (fun _ _ _ => rfl) hclK hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb.trans (bound_aux (mul_le_mul' le_rfl hK) (mul_le_mul' le_rfl hL) _ _)⟩

end Pieces

end WaveTurbulence.VineEstS5C.P2
