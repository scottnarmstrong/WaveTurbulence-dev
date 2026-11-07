/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRowsR
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRowsJ
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Expand

/-! # P4-W2 (R82 step 2): the dispatch of the separated pieces of the bundle

`CertTerm`: a `SepTC` with the identity set `V` on which a point function `f` is the separated term.  For each separated piece (`tA1`, `tA2`, `tKQ`, `tKT` and the case-M mirrors `-conj` of the swapped pieces) the lemma `pieceAll_*` turns the point-level summand of the bundle
(at the clock slots `t₀, s₁, t₁` and the momenta `k + eₓ r`, `k + e_y r`) into a `PieceRep`, from the indicator of the piece and the memberships of the
clock pairs in the identity and continuity sets (an a.e. hypothesis on `τ ∈ timeDom`, `tt ∈ Bx`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

/-- A certified separated term: a `SepTC` with the identity set `V` on which the point function `f` is the separated term. -/
structure CertTerm (P : WTParams) (Wm : ℕ) (B : Set (Fin 2 → ℝ)) (q : Fin 2 → ℝ) (CJ CM : ℝ) (f : ℝ → ℝ → Mom P.d → ℂ)
    extends SepTC P Wm B q CJ CM where
  V : Set (Fin 2 → ℝ)
  hV : ∀ s t : ℝ, ![s, t] ∈ V → ∀ k, f s t k = sepTerm c J M s t k

theorem vec2_slot {D : SumintPar.SumintDatum P.d} (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) (a b : WaveTurbulence.VineEstS3Par.Eng.Slot D) :
    (fun i => slotVal D τ tt (![a, b] i)) = ![slotVal D τ tt a, slotVal D τ tt b] := by
  funext i; fin_cases i <;> rfl

/-- Piece A1: `tA1 = 1_{s₁ ≤ t₀ < t₁} conj Q(s₁,t₀,y) T(t₁,t₀,x)`. -/
theorem pieceAll_A1 (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt s1 ≤ slotVal D τ tt t0 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => tA1 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) b i j)
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c) CMq CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_A1 (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![s1, t0] ![t1, t0] rfl cq.toSepTC ct.toSepTC Bx
    (fun τ tt r k => conj (sepTerm cq.c cq.J cq.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r)) *
      sepTerm ct.c ct.J ct.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, ⟨_, bq⟩, ⟨_, bt⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, ⟨vq, _⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tA1, if_pos hi, cq.hV _ _ vq, ct.hV _ _ vt]

/-- Piece A2: `tA2 = 1_{t₁ ≤ t₀ < s₁} Q(t₁,t₀,x) conj T(s₁,t₀,y)`. -/
theorem pieceAll_A2 (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t1 ≤ slotVal D τ tt t0 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => tA2 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) b i j)
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c) CMq CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_A2 (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![t1, t0] ![s1, t0] rfl cq.toSepTC ct.toSepTC Bx
    (fun τ tt r k => sepTerm cq.c cq.J cq.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r) *
      conj (sepTerm ct.c ct.J ct.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r)))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, ⟨_, bq⟩, ⟨_, bt⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, ⟨vq, _⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tA2, if_pos hi, cq.hV _ _ vq, ct.hV _ _ vt]


/-- Piece KQ (kind 1): `tKQ = 1_{t₀<t₁, t₀<s₁} conj(Q(s₁,t₀,y) - Q(s₁,t₀,x)) T(t₁,t₀,x)`. -/
theorem pieceAll_KQ (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ))
        (fun τ tt r k => tKQ S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) b i j)
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c * flagSign ex) ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ (D.wN + 1) * CMq) CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_KQ (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![s1, t0] ![t1, t0] rfl cq.toSepTC ct.toSepTC Bx
    (fun τ tt r k => conj (sepTerm cq.c cq.J cq.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r) - sepTerm cq.c cq.J cq.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ex • r)) * sepTerm ct.c ct.J ct.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, ⟨_, bq⟩, ⟨_, bt⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, ⟨vq, _⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tKQ, if_pos hi, cq.hV _ _ vq, ct.hV _ _ vt, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

/-- Piece KT (kind 1): `tKT = 1_{t₀<t₁, t₀<s₁} Q(t₁,t₀,x) conj(T(s₁,t₀,x) - T(s₁,t₀,y))`. -/
theorem pieceAll_KT (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ))
        (fun τ tt r k => tKT S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) b i j)
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c * -flagSign ex) CMq ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ (D.wN + 1) * CMt)))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_KT (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![t1, t0] ![s1, t0] rfl cq.toSepTC ct.toSepTC Bx
    (fun τ tt r k => sepTerm cq.c cq.J cq.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r) * conj (sepTerm ct.c ct.J ct.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ex • r) - sepTerm ct.c ct.J ct.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r)))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, ⟨_, bq⟩, ⟨_, bt⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, ⟨vq, _⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tKT, if_pos hi, cq.hV _ _ vq, ct.hV _ _ vt, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

/-- Piece MKQ (case M): `-conj(tKQ t₀ t₁ s₁ y x)`. -/
theorem pieceAll_MKQ (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ))
        (fun τ tt r k => -(starRingEnd ℂ) (tKQ S (slotVal D τ tt t0) (slotVal D τ tt t1) (slotVal D τ tt s1) (k + ey • r) (k + ex • r) b i j))
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c * flagSign ex) ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ (D.wN + 1) * CMq) CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_MKQ (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![t1, t0] ![s1, t0] rfl cq.toSepTC ct.toSepTC Bx
    (fun τ tt r k => -((sepTerm cq.c cq.J cq.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r) - sepTerm cq.c cq.J cq.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ey • r)) * conj (sepTerm ct.c ct.J ct.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r))))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, ⟨_, bq⟩, ⟨_, bt⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, ⟨vq, _⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tKQ, if_pos hi, cq.hV _ _ vq, ct.hV _ _ vt, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

/-- Piece MKT (case M): `-conj(tKT t₀ t₁ s₁ y x)`. -/
theorem pieceAll_MKT (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ))
        (fun τ tt r k => -(starRingEnd ℂ) (tKT S (slotVal D τ tt t0) (slotVal D τ tt t1) (slotVal D τ tt s1) (k + ey • r) (k + ex • r) b i j))
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c * -flagSign ex) CMq ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ (D.wN + 1) * CMt)))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_MKT (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl ![s1, t0] ![t1, t0] rfl cq.toSepTC ct.toSepTC Bx
    (fun τ tt r k => -(conj (sepTerm cq.c cq.J cq.M (slotVal D τ tt s1) (slotVal D τ tt t0) (k + ey • r)) * (sepTerm ct.c ct.J ct.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ey • r) - sepTerm ct.c ct.J ct.M (slotVal D τ tt t1) (slotVal D τ tt t0) (k + ex • r))))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, ⟨_, bq⟩, ⟨_, bt⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, ⟨vq, _⟩, ⟨vt, _⟩⟩ := hg hd
  simp only [tKT, if_pos hi, cq.hV _ _ vq, ct.hV _ _ vt, map_neg, map_mul, map_sub, Complex.conj_conj, neg_mul, mul_neg, neg_neg]

end WaveTurbulence.VineEstS5C.P4.W2
