/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll1

/-! # P4-W2 (R82 step 2): the dispatch of the kind-2 pieces `tTQ`, `tTT` and their case-M mirrors

As `PieceAll1`, with the joint three-clock `K` row (`pieceRep_TQ/TT/MTQ/MTT`): the slots `s₁`, `t₁` must be sumint clocks (`s₁ = inl a`, `t₁ = inl b`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

theorem vec3_slot {D : SumintPar.SumintDatum P.d} (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) (a b c : WaveTurbulence.VineEstS3Par.Eng.Slot D) :
    (fun i => slotVal D τ tt (![a, b, c] i)) = ![slotVal D τ tt a, slotVal D τ tt b, slotVal D τ tt c] := by
  funext i; fin_cases i <;> rfl

theorem pieceAll_TQ (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar)
      (hsa : s1 = Sum.inl a) (hsb : t1 = Sum.inl b')
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ BK ∧ ![τ 1, τ 2] ∈ BK) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ cq.Bc ∧ ![τ 1, τ 2] ∈ cq.Bc) →
      ∀ (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧ ![slotVal D τ tt s1, slotVal D τ tt t1, slotVal D τ tt t0] ∈ Bc3 ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
        (fun τ tt r k => tTQ S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) b i j)
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c) CMq CMt))
        (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_TQ (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb β S b i j BK BL qK qL CJq CMq CJt CMt cq ct q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![s1, t1, t0] ![t1, t0] a b' hsa hsb rfl rfl cq.toSepTC ct.toSepTC q3 B3 Bc3
    h1 h2 h3 h4 h5 h6 h7 h8 Bx
    (fun τ tt r k => conj (sepTerm cq.c cq.J cq.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ex • r) - sepTerm cq.c cq.J cq.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r)) * sepTerm ct.c ct.J ct.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bK3, _, ⟨_, bL⟩⟩ := hg hd
      exact ⟨by rw [vec3_slot]; exact bK3, by rw [vec2_slot]; exact bL, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, _, ⟨vj1, vj2⟩, ⟨vl, _⟩⟩ := hg hd
  simp only [tTQ, if_pos hi, cq.hV _ _ vj1, cq.hV _ _ vj2, ct.hV _ _ vl, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

theorem pieceAll_TT (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar)
      (hsa : t1 = Sum.inl a) (hsb : s1 = Sum.inl b')
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ BL ∧ ![τ 1, τ 2] ∈ BL) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ ct.Bc ∧ ![τ 1, τ 2] ∈ ct.Bc) →
      ∀ (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧ ![slotVal D τ tt t1, slotVal D τ tt s1, slotVal D τ tt t0] ∈ Bc3 ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
        (fun τ tt r k => tTT S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) b i j)
        (C * ENNReal.ofReal CJt * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c) CMq CMt))
        (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_TT (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb β S b i j BK BL qK qL CJq CMq CJt CMt cq ct q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![t1, s1, t0] ![t1, t0] a b' hsa hsb rfl rfl cq.toSepTC ct.toSepTC q3 B3 Bc3
    h1 h2 h3 h4 h5 h6 h7 h8 Bx
    (fun τ tt r k => sepTerm cq.c cq.J cq.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r) * conj (sepTerm ct.c ct.J ct.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r) - sepTerm ct.c ct.J ct.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ex • r)))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bK3, _, ⟨_, bL⟩⟩ := hg hd
      exact ⟨by rw [vec3_slot]; exact bK3, by rw [vec2_slot]; exact bL, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, _, ⟨vj1, vj2⟩, ⟨vl, _⟩⟩ := hg hd
  simp only [tTT, if_pos hi, ct.hV _ _ vj1, ct.hV _ _ vj2, cq.hV _ _ vl, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

theorem pieceAll_MTQ (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar)
      (hsa : t1 = Sum.inl a) (hsb : s1 = Sum.inl b')
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ BK ∧ ![τ 1, τ 2] ∈ BK) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ cq.Bc ∧ ![τ 1, τ 2] ∈ cq.Bc) →
      ∀ (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧ ![slotVal D τ tt t1, slotVal D τ tt s1, slotVal D τ tt t0] ∈ Bc3 ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
        (fun τ tt r k => -(starRingEnd ℂ) (tTQ S (slotVal D τ tt t0) (slotVal D τ tt t1) (slotVal D τ tt s1) (k + ey • r) b i j))
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c * -1) CMq CMt))
        (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_MTQ (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb β S b i j BK BL qK qL CJq CMq CJt CMt cq ct q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![t1, s1, t0] ![s1, t0] a b' hsa hsb rfl rfl cq.toSepTC ct.toSepTC q3 B3 Bc3
    h1 h2 h3 h4 h5 h6 h7 h8 Bx
    (fun τ tt r k => -((sepTerm cq.c cq.J cq.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ey • r) - sepTerm cq.c cq.J cq.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r)) * conj (sepTerm ct.c ct.J ct.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r))))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bK3, _, ⟨_, bL⟩⟩ := hg hd
      exact ⟨by rw [vec3_slot]; exact bK3, by rw [vec2_slot]; exact bL, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, _, ⟨vj1, vj2⟩, ⟨vl, _⟩⟩ := hg hd
  simp only [tTQ, if_pos hi, cq.hV _ _ vj1, cq.hV _ _ vj2, ct.hV _ _ vl, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

theorem pieceAll_MTT (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar)
      (hsa : s1 = Sum.inl a) (hsb : t1 = Sum.inl b')
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ BL ∧ ![τ 1, τ 2] ∈ BL) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ ct.Bc ∧ ![τ 1, τ 2] ∈ ct.Bc) →
      ∀ (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧ ![slotVal D τ tt s1, slotVal D τ tt t1, slotVal D τ tt t0] ∈ Bc3 ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.V) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
        (fun τ tt r k => -(starRingEnd ℂ) (tTT S (slotVal D τ tt t0) (slotVal D τ tt t1) (slotVal D τ tt s1) (k + ey • r) b i j))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c * -1) CMq CMt))
        (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_MTT (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb β S b i j BK BL qK qL CJq CMq CJt CMt cq ct q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![s1, t1, t0] ![s1, t0] a b' hsa hsb rfl rfl cq.toSepTC ct.toSepTC q3 B3 Bc3
    h1 h2 h3 h4 h5 h6 h7 h8 Bx
    (fun τ tt r k => -(conj (sepTerm cq.c cq.J cq.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r)) * (sepTerm ct.c ct.J ct.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r) - sepTerm ct.c ct.J ct.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ey • r))))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bK3, _, ⟨_, bL⟩⟩ := hg hd
      exact ⟨by rw [vec3_slot]; exact bK3, by rw [vec2_slot]; exact bL, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, _, ⟨vj1, vj2⟩, ⟨vl, _⟩⟩ := hg hd
  simp only [tTT, if_pos hi, ct.hV _ _ vj1, ct.hV _ _ vj2, cq.hV _ _ vl, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

end WaveTurbulence.VineEstS5C.P4.W2
