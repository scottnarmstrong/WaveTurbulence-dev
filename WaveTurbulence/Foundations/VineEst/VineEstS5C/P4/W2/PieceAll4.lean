/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll2

/-! # P4-W2 (R82 step 2): signs and the case-M mirrors of the clause-(a) pieces

`PieceRep.smul`: a constant factor is absorbed in `fac`.  `pieceAll_MA1`: the case-M summand of the A1 slot, `-conj(tA1 t₀ t₁ s₁ y x) = -tA2 t₀ s₁ t₁ x y`;
`pieceAll_MA2`: the case-M summand of the A2 slot, `-conj(-tA2 t₀ t₁ s₁ y x) = tA1 t₀ s₁ t₁ x y`; `pieceAll_PA2`: the case-A summand of the A2 slot `-tA2`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

theorem PieceRep.smul {D : SumintPar.SumintDatum P.d} {hI : 0 < D.S.I} {vp vb : D.S.VIdx} {ε : ℝ} {fac : (D.S.TVar → ℝ) → Mom P.d → ℂ}
    {X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {bK bL : ℝ≥0∞} {Bx : Set (Fin 3 → ℝ)}
    (h : PieceRep (P := P) hI vp vb ε fac X bK bL Bx) (c : ℂ) :
    PieceRep (P := P) hI vp vb ε (fun τ r => c * fac τ r) (fun τ tt r k => c * X τ tt r k) bK bL Bx := by
  obtain ⟨RK, RL, h1, h2, h3, h4, h5⟩ := h
  refine ⟨RK, RL, h1, h2, h3, h4, fun tt htt => ?_⟩
  filter_upwards [h5 tt htt] with τ hτ hd r k hr
  rw [hτ hd r k hr]; ring

theorem tA2_swap_conj {β : Type*} {d : ℕ} (S : SepTerms β d) (t0 s1 t1 : ℝ) (x y : Mom d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b)) :
    (starRingEnd ℂ) (tA2 S t0 t1 s1 y x b i j) = tA1 S t0 s1 t1 x y b i j := by
  unfold tA2 tA1
  by_cases h : s1 ≤ t0 ∧ t0 < t1
  · simp [h]
  · simp [h]

theorem tA1_swap_conj {β : Type*} {d : ℕ} (S : SepTerms β d) (t0 s1 t1 : ℝ) (x y : Mom d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b)) :
    (starRingEnd ℂ) (tA1 S t0 t1 s1 y x b i j) = tA2 S t0 s1 t1 x y b i j := by
  unfold tA2 tA1
  by_cases h : t1 ≤ t0 ∧ t0 < s1
  · simp [h]
  · simp [h]

/-- Case A, A2 slot: the summand `-tA2`. -/
theorem pieceAll_PA2 (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t1 ≤ slotVal D τ tt t0 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => (-1 : ℂ) * 1)
        (fun τ tt r k => -(tA2 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) b i j))
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c) CMq CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx  := by
  obtain ⟨C, hC, h⟩ := pieceAll_A2 (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := (h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 S b i j cq ct Bx hG).smul (-1)
  refine h0.congr (fun tt htt => Filter.Eventually.of_forall fun τ hd r k hr => ?_)
  simp

/-- Case M, A1 slot: `-conj(tA1 t₀ t₁ s₁ y x) = -tA2 t₀ s₁ t₁ x y`. -/
theorem pieceAll_MA1 (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t1 ≤ slotVal D τ tt t0 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => (-1 : ℂ) * 1)
        (fun τ tt r k => -(starRingEnd ℂ) (tA1 S (slotVal D τ tt t0) (slotVal D τ tt t1) (slotVal D τ tt s1) (k + ey • r) (k + ex • r) b i j))
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c) CMq CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx  := by
  obtain ⟨C, hC, h⟩ := pieceAll_A2 (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := (h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 S b i j cq ct Bx hG).smul (-1)
  refine h0.congr (fun tt htt => Filter.Eventually.of_forall fun τ hd r k hr => ?_)
  rw [tA1_swap_conj]; simp

/-- Case M, A2 slot: `-conj(-tA2 t₀ t₁ s₁ y x) = tA1 t₀ s₁ t₁ x y`. -/
theorem pieceAll_MA2 (G : AmbP A P) :
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
        (fun τ tt r k => -(starRingEnd ℂ) (-(tA2 S (slotVal D τ tt t0) (slotVal D τ tt t1) (slotVal D τ tt s1) (k + ey • r) (k + ex • r) b i j)))
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (cq.c * ct.c) CMq CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx  := by
  obtain ⟨C, hC, h⟩ := pieceAll_A1 (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S b i j BK BL qK qL CJq CMq CJt CMt cq ct Bx hG => ?_⟩
  have h0 := h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 S b i j cq ct Bx hG
  refine h0.congr (fun tt htt => Filter.Eventually.of_forall fun τ hd r k hr => ?_)
  rw [map_neg, neg_neg, tA2_swap_conj]

/-- The zero row (all modes `0`). -/
noncomputable def zeroRow {D : SumintPar.SumintDatum P.d} (ρ : Row D) (slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) :
    RowData D (6 * P.η ^ 6) ρ :=
  RowData.ofModes (θ := 6 * P.η ^ 6) ρ slot (fun _ _ _ => 0) 0 ENNReal.zero_ne_top
    (by
      unfold coefBound
      simp only [SNorm_zero_fun, iSup_const, mul_zero, tsum_zero, le_refl])
    (fun _ _ _ _ _ _ => rfl)

theorem zeroRow_W {D : SumintPar.SumintDatum P.d} (ρ : Row D) (slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
    (cl : Fin 3 → ℝ) (r k : Mom P.d) : (zeroRow (P := P) ρ slot).W cl r k = 0 := by
  simp [zeroRow, RowData.ofModes]

/-- A vanishing exceptional factor (for instance A1, A2, TQ, TT of a type-I record, where `s₁ = t₁`) has the trivial representation. -/
theorem pieceRep_zero (hη0 : 0 < P.η) {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (vp vb : D.S.VIdx) (ε : ℝ)
    (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (Bx : Set (Fin 3 → ℝ))
    (sK sL : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
    (hX : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k : Mom P.d, ‖r‖ ≤ 1 → X τ tt r k = 0) :
    PieceRep (P := P) hI vp vb ε fac X 0 0 Bx := by
  have hθ : 0 ≤ 6 * P.η ^ 6 := by positivity
  refine ⟨zeroRow (Sum.inl vp) sK, zeroRow (Sum.inr vb) sL, RowData.ofModes_ae hθ hI _ _ _ _ _ _ _,
    RowData.ofModes_ae hθ hI _ _ _ _ _ _ _, le_rfl, le_rfl, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ hd r k hr
  rw [hτ hd r k hr, zeroRow_W, zeroRow_W]; ring

section TypeI
variable {β : Type*} {d : ℕ} (S : SepTerms β d) (t0 t : ℝ) (x y : Mom d) (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b))

/-- Type I (`s₁ = t₁`): the pieces A1, A2, TQ, TT vanish. -/
theorem tA1_self : tA1 S t0 t t x y b i j = 0 := by
  unfold tA1
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact absurd (h1.trans_lt h2) (lt_irrefl _)

theorem tA2_self : tA2 S t0 t t x y b i j = 0 := by
  unfold tA2
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact absurd (h1.trans_lt h2) (lt_irrefl _)

theorem tTQ_self : tTQ S t0 t t x b i j = 0 := by
  unfold tTQ
  split_ifs <;> simp

theorem tTT_self : tTT S t0 t t x b i j = 0 := by
  unfold tTT
  split_ifs <;> simp

end TypeI

end WaveTurbulence.VineEstS5C.P4.W2
