/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceJoint
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.KCont
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.DefectRows

/-! # P2: piece bounds with a remainder row (the types of `remA`, `remB`)

`RemT`: a gate remainder (a kernel `f` which agrees a.e. in time on the box with a time-continuous `f'`, with finite `XNormRestr` bound).  `piece_SR`
(separated 𝒦, remainder ℒ), `piece_RS` (remainder 𝒦, separated ℒ), `piece_RR` (both remainders). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal ComplexConjugate

/-- A remainder kernel on the time box `B`: a.e. equal to a time-continuous `f'`, with `‖f‖_{𝔛^{6η^6, 30d, Λ₂}(B)} < CR`. -/
structure RemT (P : WTParams) (Λ₂ : ℕ) (B : Set (Fin 2 → ℝ)) (q : Fin 2 → ℝ) (CR : ℝ) where
  f : (Fin 2 → ℝ) → Mom P.d → ℂ
  f' : (Fin 2 → ℝ) → Mom P.d → ℂ
  hcell : B ⊆ cell q
  hint : B ⊆ closure (interior B)
  hcont : ∀ k, Continuous fun t => f' t k
  hae : ∀ᵐ t, t ∈ B → ∀ k, f t k = f' t k
  hCR : 0 ≤ CR
  hX : XNormRestr (6 * P.η ^ 6) (30 * P.d) Λ₂ B Set.univ f < ENNReal.ofReal CR

/-- The conjugate of a tree-type (order `Λ₂`) remainder at the same arguments. -/
def RemT.conj {P : WTParams} {Λ₂ : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CR : ℝ} (R : RemT P Λ₂ B q CR) :
    RemT P Λ₂ B q CR where
  f := fun ts k => conj (R.f ts k)
  f' := fun ts k => conj (R.f' ts k)
  hcell := R.hcell
  hint := R.hint
  hcont := fun k => Complex.continuous_conj.comp (R.hcont k)
  hae := R.hae.mono fun t ht htB k => by rw [ht htB k]
  hCR := R.hCR
  hX := by rw [VineEstS4c.XNormRestr_conj]; exact R.hX

variable {A : ℝ} {P : WTParams}

theorem RemT.hXidx {Λ₂ : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CR : ℝ} (R : RemT P Λ₂ B q CR) {Λ₁ : ℕ} (h : Λ₁ ≤ 30 * P.d) :
    XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ B Set.univ R.f < ENNReal.ofReal CR :=
  lt_of_le_of_lt (XNormRestr_mono_idx h le_rfl B _ _) R.hX

/-- **Piece type SR** (`Q_i · RT`-term of `remA`/`remB`): separated couple 𝒦 row, tree-remainder ℒ row. -/
theorem piece_SR (G : AmbP A P) :
    ∃ C CL : ℝ≥0∞, C ≠ ⊤ ∧ CL ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Bq Br : Set (Fin 2 → ℝ)} {qq qr : Fin 2 → ℝ}
      {CJq CMq CR : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (sq : SepT P (30 * P.d) Bq qq CJq CMq) (rr : RemT P 0 Br qr CR)
      (vK vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
      (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ Bq)
      (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Br),
      PieceBound Z (fun c r k => sq.J ![c 0, c 1] * spPlain sq.c sq.M r k) (fun i => Sum.inl (![vK 0, vK 1, vK 0] i))
        (fun c _ k => rr.f ![c 0, c 1] k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (|sq.c| * CMq)) (CL * ENNReal.ofReal CR) := by
  obtain ⟨C, CK, CL, hC, hCK, hCL, h⟩ := level_SR (A := A) G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1
    (by have := G.hη0; positivity) G.hθ' (30 * P.d - 1) (30 * P.d) (by have := G.hd1; omega)
  refine ⟨C, CL, hC, hCL, ?_⟩
  intro D Z Bq Br qq qr CJq CMq CR hwN hwDec sq rr vK vL hvK hvL hclK hclL
  have hK := supK_plain hwN hwDec G.hd1 Z.v0 sq
  obtain ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM (by omega) (by omega) Z.cr0 Z.M0 Z.v0
    Z.h0 vK hvK qq Bq sq.J (ENNReal.ofReal CJq) (spPlain sq.c sq.M) ENNReal.ofReal_ne_top sq.hcell sq.hint sq.hJ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK) hclK vL hvL qr Br rr.f rr.f' (ENNReal.ofReal CR) ENNReal.ofReal_ne_top rr.hcell rr.hint
    rr.hcont rr.hae (rr.hXidx (by omega)) hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb.trans (bound_aux (mul_le_mul' le_rfl hK) le_rfl _ _)⟩

/-- **Piece type RS** (`RQ · T_j`-term): couple-remainder 𝒦 row, separated tree ℒ row. -/
theorem piece_RS (G : AmbP A P) :
    ∃ C CK : ℝ≥0∞, C ≠ ⊤ ∧ CK ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Br Bt : Set (Fin 2 → ℝ)} {qr qt : Fin 2 → ℝ}
      {CR CJt CMt : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (rq : RemT P (30 * P.d) Br qr CR) (st : SepT P 0 Bt qt CJt CMt)
      (vK vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
      (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ Br)
      (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Bt),
      PieceBound Z (fun c _ k => rq.f ![c 0, c 1] k) (fun i => Sum.inl (![vK 0, vK 1, vK 0] i))
        (fun c r k => st.J ![c 0, c 1] * spPlain st.c st.M r k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
        (CK * ENNReal.ofReal CR) (C * ENNReal.ofReal CJt * ENNReal.ofReal (|st.c| * CMt)) := by
  obtain ⟨C, CK, CL, hC, hCK, hCL, h⟩ := level_RS (A := A) G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1
    (by have := G.hη0; positivity) G.hθ' (30 * P.d - 1) (30 * P.d) (by have := G.hd1; omega)
  refine ⟨C, CK, hC, hCK, ?_⟩
  intro D Z Br Bt qr qt CR CJt CMt hwN hwDec rq st vK vL hvK hvL hclK hclL
  have hL := supL_plain hwN hwDec G.hd1 Z.v0 st
  obtain ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM (by omega) (by omega) Z.cr0 Z.M0 Z.v0
    Z.h0 vK hvK qr Br rq.f rq.f' (ENNReal.ofReal CR) ENNReal.ofReal_ne_top rq.hcell rq.hint rq.hcont rq.hae (rq.hXidx (by omega)) hclK
    vL hvL qt Bt st.J (ENNReal.ofReal CJt) (spPlain st.c st.M) ENNReal.ofReal_ne_top st.hcell st.hint st.hJ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL) (fun _ _ _ => rfl) hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb.trans (bound_aux le_rfl (mul_le_mul' le_rfl hL) _ _)⟩

/-- **Piece type RR** (`RQ · RT`-term): couple-remainder 𝒦 row, tree-remainder ℒ row. -/
theorem piece_RR (G : AmbP A P) :
    ∃ CK CL : ℝ≥0∞, CK ≠ ⊤ ∧ CL ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (Z : Amb A P D) {Bq Br : Set (Fin 2 → ℝ)} {qq qr : Fin 2 → ℝ}
      {CQ CT : ℝ} (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (rq : RemT P (30 * P.d) Bq qq CQ) (rt : RemT P 0 Br qr CT)
      (vK vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
      (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ Bq)
      (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom Z.hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ Br),
      PieceBound Z (fun c _ k => rq.f ![c 0, c 1] k) (fun i => Sum.inl (![vK 0, vK 1, vK 0] i))
        (fun c _ k => rt.f ![c 0, c 1] k) (fun i => Sum.inl (![vL 0, vL 1, vL 0] i))
        (CK * ENNReal.ofReal CQ) (CL * ENNReal.ofReal CT) := by
  obtain ⟨C, CK, CL, hC, hCK, hCL, h⟩ := level_RR (A := A) G.hdb G.hL G.hη0 G.hη1 G.hC1 G.hδ G.hd1
    (by have := G.hη0; positivity) G.hθ' (30 * P.d - 1) (30 * P.d) (by have := G.hd1; omega)
  refine ⟨CK, CL, hCK, hCL, ?_⟩
  intro D Z Bq Br qq qr CQ CT hwN hwDec rq rt vK vL hvK hvL hclK hclL
  obtain ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb⟩ := h Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM (by omega) (by omega) Z.cr0 Z.M0 Z.v0
    Z.h0 vK hvK qq Bq rq.f rq.f' (ENNReal.ofReal CQ) ENNReal.ofReal_ne_top rq.hcell rq.hint rq.hcont rq.hae (rq.hXidx (by omega)) hclK
    vL hvL qr Br rt.f rt.f' (ENNReal.ofReal CT) ENNReal.ofReal_ne_top rt.hcell rt.hint rt.hcont rt.hae (rt.hXidx (by omega)) hclL
  exact ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, hb⟩

end WaveTurbulence.VineEstS5C.P2
