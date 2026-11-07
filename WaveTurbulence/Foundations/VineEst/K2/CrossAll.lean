/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.CrossPieces
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll2

/-! # W2-KIND2 (cross, certified): the four kind-2 pieces from certified terms of the two windows with a common time factor

`pieceAll_TQx`, `pieceAll_TTx`, `pieceAll_MTQx`, `pieceAll_MTTx`: the versions of `pieceAll_TQ`, ... (PieceAll2) in which the differenced factor is given
by TWO certified terms of the same function (`cl`: the low window, `ch`: the high window), glued by one common time factor `xJ`
(`hc : ch.c = cl.c`, `hM : ch.M = cl.M`, `xJ = cl.J` on `cl.Bc`, `xJ = ch.J` on `ch.Bc`), with `‖xJ‖_{𝔛^{1-2η}(B2)} < CJx` on a set `B2`
containing both clock pairs.  Window assignment: case A (`TQ`, `TT`): `s₁` high, `t₁` low.  Case M (`MTQ`, `MTT`): `s₁` low, `t₁` high.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C.P4.W2
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

theorem sepTerm_glue {Wm : ℕ} {B1 B2' : Set (Fin 2 → ℝ)} {q1 q2' : Fin 2 → ℝ} {CJ1 CM1 CJ2 CM2 : ℝ}
    {f : ℝ → ℝ → Mom P.d → ℂ}
    (cl : CertTerm P Wm B1 q1 CJ1 CM1 f) (ch : CertTerm P Wm B2' q2' CJ2 CM2 f) (xJ : (Fin 2 → ℝ) → ℂ)
    (hc : ch.c = cl.c) (hM : ch.M = cl.M) (hxh : ∀ ts ∈ ch.Bc, xJ ts = ch.J ts) {s t : ℝ} (hv : ![s, t] ∈ ch.V)
    (hb : ![s, t] ∈ ch.Bc) (k : Mom P.d) : f s t k = sepTerm cl.c xJ cl.M s t k := by
  rw [ch.hV s t hv k]
  unfold sepTerm
  rw [hc, hM, hxh _ hb]

theorem pieceAll_TQx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar)
      (hsa : s1 = Sum.inl a) (hsb : t1 = Sum.inl b')
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BKh BL : Set (Fin 2 → ℝ)} {qK qKh qL : Fin 2 → ℝ} {CJq CMq CJqh CMqh CJt CMt : ℝ}
      (cql : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (cqh : CertTerm P (30 * P.d) BKh qKh CJqh CMqh (S.sQ b i))
      (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (hc : cqh.c = cql.c) (hM : cqh.M = cql.M)
      (xJ : (Fin 2 → ℝ) → ℂ) (B2 Bc2 : Set (Fin 2 → ℝ)) (CJx : ℝ) (hc2 : ContinuousOn xJ Bc2)
      (hx2 : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => xJ ts) < ENNReal.ofReal CJx)
      (hxl : ∀ ts ∈ cql.Bc, xJ ts = cql.J ts) (hxh : ∀ ts ∈ cqh.Bc, xJ ts = cqh.J ts)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      ∀ (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧ ![slotVal D τ tt s1, slotVal D τ tt t1, slotVal D τ tt t0] ∈ Bc3 ∧
        ((![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cqh.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cqh.Bc) ∧
          (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cql.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cql.Bc)) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
        (fun τ tt r k => tTQ S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) b i j)
        (C * ENNReal.ofReal CJx * ENNReal.ofReal (spConst P.d D.wN D.wDec (cql.c * ct.c) CMq CMt))
        (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_TQx (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb β S b i j BK BKh BL qK qKh qL CJq CMq CJqh CMqh CJt CMt cql cqh ct hc hM xJ B2 Bc2 CJx hc2 hx2 hxl hxh q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![s1, t1, t0] ![t1, t0] a b' hsa hsb rfl rfl cql.toSepTC ct.toSepTC xJ B2 Bc2 CJx hc2 hx2 q3 B3 Bc3
    h1 h2 h3 h4 h5 h6 h7 h8 Bx
    (fun τ tt r k => conj (sepTerm cql.c xJ cql.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ex • r) - sepTerm cql.c xJ cql.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r)) * sepTerm ct.c ct.J ct.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bK3, _, ⟨_, bL⟩⟩ := hg hd
      exact ⟨by rw [vec3_slot]; exact bK3, by rw [vec2_slot]; exact bL, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, _, ⟨⟨vh, bh⟩, ⟨vl, bl⟩⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tTQ, if_pos hi, sepTerm_glue cql cqh xJ hc hM hxh vh bh, sepTerm_glue cql cql xJ rfl rfl hxl vl bl, ct.hV _ _ vt]

theorem pieceAll_TTx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar)
      (hsa : t1 = Sum.inl a) (hsb : s1 = Sum.inl b')
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL BLh : Set (Fin 2 → ℝ)} {qK qL qLh : Fin 2 → ℝ} {CJq CMq CJt CMt CJth CMth : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ctl : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (cth : CertTerm P 0 BLh qLh CJth CMth (S.sT b j))
      (hc : cth.c = ctl.c) (hM : cth.M = ctl.M)
      (xJ : (Fin 2 → ℝ) → ℂ) (B2 Bc2 : Set (Fin 2 → ℝ)) (CJx : ℝ) (hc2 : ContinuousOn xJ Bc2)
      (hx2 : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => xJ ts) < ENNReal.ofReal CJx)
      (hxl : ∀ ts ∈ ctl.Bc, xJ ts = ctl.J ts) (hxh : ∀ ts ∈ cth.Bc, xJ ts = cth.J ts)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      ∀ (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧ ![slotVal D τ tt t1, slotVal D τ tt s1, slotVal D τ tt t0] ∈ Bc3 ∧
        ((![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ctl.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ctl.Bc) ∧
          (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cth.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cth.Bc)) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
        (fun τ tt r k => tTT S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) b i j)
        (C * ENNReal.ofReal CJx * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ctl.c) CMq CMt))
        (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_TTx (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb β S b i j BK BL BLh qK qL qLh CJq CMq CJt CMt CJth CMth cq ctl cth hc hM xJ B2 Bc2 CJx hc2 hx2 hxl hxh q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![t1, s1, t0] ![t1, t0] a b' hsa hsb rfl rfl cq.toSepTC ctl.toSepTC xJ B2 Bc2 CJx hc2 hx2 q3 B3 Bc3
    h1 h2 h3 h4 h5 h6 h7 h8 Bx
    (fun τ tt r k => sepTerm cq.c cq.J cq.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r) * conj (sepTerm ctl.c xJ ctl.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r) - sepTerm ctl.c xJ ctl.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ex • r)))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bK3, _, ⟨_, bL⟩⟩ := hg hd
      exact ⟨by rw [vec3_slot]; exact bK3, by rw [vec2_slot]; exact bL, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, _, ⟨⟨vl, bl⟩, ⟨vh, bh⟩⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tTT, if_pos hi, sepTerm_glue ctl cth xJ hc hM hxh vh bh, sepTerm_glue ctl ctl xJ rfl rfl hxl vl bl, cq.hV _ _ vt]

theorem pieceAll_MTQx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar)
      (hsa : t1 = Sum.inl a) (hsb : s1 = Sum.inl b')
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BKh BL : Set (Fin 2 → ℝ)} {qK qKh qL : Fin 2 → ℝ} {CJq CMq CJqh CMqh CJt CMt : ℝ}
      (cql : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (cqh : CertTerm P (30 * P.d) BKh qKh CJqh CMqh (S.sQ b i))
      (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (hc : cqh.c = cql.c) (hM : cqh.M = cql.M)
      (xJ : (Fin 2 → ℝ) → ℂ) (B2 Bc2 : Set (Fin 2 → ℝ)) (CJx : ℝ) (hc2 : ContinuousOn xJ Bc2)
      (hx2 : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => xJ ts) < ENNReal.ofReal CJx)
      (hxl : ∀ ts ∈ cql.Bc, xJ ts = cql.J ts) (hxh : ∀ ts ∈ cqh.Bc, xJ ts = cqh.J ts)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      ∀ (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧ ![slotVal D τ tt t1, slotVal D τ tt s1, slotVal D τ tt t0] ∈ Bc3 ∧
        ((![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cqh.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cqh.Bc) ∧
          (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cql.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cql.Bc)) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
        (fun τ tt r k => -(starRingEnd ℂ) (tTQ S (slotVal D τ tt t0) (slotVal D τ tt t1) (slotVal D τ tt s1) (k + ey • r) b i j))
        (C * ENNReal.ofReal CJx * ENNReal.ofReal (spConst P.d D.wN D.wDec (cql.c * ct.c * -1) CMq CMt))
        (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_MTQx (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb β S b i j BK BKh BL qK qKh qL CJq CMq CJqh CMqh CJt CMt cql cqh ct hc hM xJ B2 Bc2 CJx hc2 hx2 hxl hxh q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![t1, s1, t0] ![s1, t0] a b' hsa hsb rfl rfl cql.toSepTC ct.toSepTC xJ B2 Bc2 CJx hc2 hx2 q3 B3 Bc3
    h1 h2 h3 h4 h5 h6 h7 h8 Bx
    (fun τ tt r k => -((sepTerm cql.c xJ cql.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ey • r) - sepTerm cql.c xJ cql.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r)) * conj (sepTerm ct.c ct.J ct.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r))))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bK3, _, ⟨_, bL⟩⟩ := hg hd
      exact ⟨by rw [vec3_slot]; exact bK3, by rw [vec2_slot]; exact bL, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, _, ⟨⟨vh, bh⟩, ⟨vl, bl⟩⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tTQ, if_pos hi, sepTerm_glue cql cqh xJ hc hM hxh vh bh, sepTerm_glue cql cql xJ rfl rfl hxl vl bl, ct.hV _ _ vt, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

theorem pieceAll_MTTx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar)
      (hsa : s1 = Sum.inl a) (hsb : t1 = Sum.inl b')
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL BLh : Set (Fin 2 → ℝ)} {qK qL qLh : Fin 2 → ℝ} {CJq CMq CJt CMt CJth CMth : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ctl : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (cth : CertTerm P 0 BLh qLh CJth CMth (S.sT b j))
      (hc : cth.c = ctl.c) (hM : cth.M = ctl.M)
      (xJ : (Fin 2 → ℝ) → ℂ) (B2 Bc2 : Set (Fin 2 → ℝ)) (CJx : ℝ) (hc2 : ContinuousOn xJ Bc2)
      (hx2 : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => xJ ts) < ENNReal.ofReal CJx)
      (hxl : ∀ ts ∈ ctl.Bc, xJ ts = ctl.J ts) (hxh : ∀ ts ∈ cth.Bc, xJ ts = cth.J ts)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      ∀ (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧ ![slotVal D τ tt s1, slotVal D τ tt t1, slotVal D τ tt t0] ∈ Bc3 ∧
        ((![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ctl.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ctl.Bc) ∧
          (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cth.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cth.Bc)) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
        (fun τ tt r k => -(starRingEnd ℂ) (tTT S (slotVal D τ tt t0) (slotVal D τ tt t1) (slotVal D τ tt s1) (k + ey • r) b i j))
        (C * ENNReal.ofReal CJx * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ctl.c * -1) CMq CMt))
        (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_MTTx (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb β S b i j BK BL BLh qK qL qLh CJq CMq CJt CMt CJth CMth cq ctl cth hc hM xJ B2 Bc2 CJx hc2 hx2 hxl hxh q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![s1, t1, t0] ![s1, t0] a b' hsa hsb rfl rfl cq.toSepTC ctl.toSepTC xJ B2 Bc2 CJx hc2 hx2 q3 B3 Bc3
    h1 h2 h3 h4 h5 h6 h7 h8 Bx
    (fun τ tt r k => -(conj (sepTerm cq.c cq.J cq.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r)) * (sepTerm ctl.c xJ ctl.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r) - sepTerm ctl.c xJ ctl.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ey • r))))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bK3, _, ⟨_, bL⟩⟩ := hg hd
      exact ⟨by rw [vec3_slot]; exact bK3, by rw [vec2_slot]; exact bL, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, _, ⟨⟨vl, bl⟩, ⟨vh, bh⟩⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tTT, if_pos hi, sepTerm_glue ctl cth xJ hc hM hxh vh bh, sepTerm_glue ctl ctl xJ rfl rfl hxl vl bl, cq.hV _ _ vt, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

end WaveTurbulence.VineEstS5C.P4.W2.K2
