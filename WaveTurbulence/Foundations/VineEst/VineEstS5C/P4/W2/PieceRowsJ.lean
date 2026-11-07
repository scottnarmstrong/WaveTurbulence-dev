/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRows

/-! # P4-W2 (b1): the kind-2 shapes (TQ, TT, MTQ, MTT) as two-row representations with the joint three-clock `𝒦` row

`K` clocks `(sK 0, sK 1, sK 2)` are sumint clocks `a = sK 0`, `b = sK 1` (TVars) and `t₀ = sK 2`; `fac = |τ_a - τ_b|^{1-3η}` is the kind-2 factor of the block (`k2c`).
The `𝒦` time factor is the `SepTC` of the `Q` (TQ, MTQ) or `T` (TT, MTT) factor, the `ℒ` row is separated with the other one.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS4c
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

/-- Piece TQ (kind 2): `conj(Q(s₁,t₀,x) - Q(t₁,t₀,x)) T(t₁,t₀,x)`; `K = (s₁,t₁,t₀)`, `L = (t₁,t₀)`. -/
theorem pieceRep_TQ (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b : D.S.TVar) (hs0 : sK 0 = Sum.inl a) (hs1 : sK 1 = Sum.inl b)
      (hL0 : sL 0 = sK 1) (hL1 : sL 1 = sK 2)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ BK ∧ ![τ 1, τ 2] ∈ BK) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ sq.Bc ∧ ![τ 1, τ 2] ∈ sq.Bc) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = conj (sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ex • r) - sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ex • r)) *
          sepTerm st.c st.J st.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ex • r)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c) CMq CMt))
        (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_joint (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl sK sL a b hs0 hs1 hL0 hL1 BK BL qK qL CJq CMq CJt CMt sq st q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx X hX => ?_⟩
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c) sq.toSepT st.toSepT ex ex hfl.abs_ex_le hfl.abs_ex_le
  have hfac' : ∀ (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ), slotVal D τ tt (sK 0) = τ a ∧ slotVal D τ tt (sK 1) = τ b := by
    intro τ tt; simp [hs0, hs1, slotVal]
  refine h D hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) sK sL q3 qL BK sq.Bc B3 Bc3 BL st.Bc (cJ sq.J) st.J
    CJq CJt _ (spS (sq.c * st.c) (plainF sq.M) (plainF st.M) ex ex) (fun τ r => by simp [hs0, hs1, slotVal])
    h1 h2 h3 h4 h5 h6 h7 (continuousOn_cJ sq.hcont) h8 st.hcell st.hint st.hBcB st.hBci st.hcont sq.hJc st.hJ hsp Bx X ?_
  intro tt htt
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  refine ⟨m1, m2, fun r k hr => ?_⟩
  obtain ⟨e0, e1⟩ := hfac' τ tt
  rw [hid r k hr, hL0, hL1, sp_ident_TQ hr ex P.η]
  simp only [e0, e1]

/-- Piece TT (kind 2): `Q(t₁,t₀,x) conj(T(t₁,t₀,x) - T(s₁,t₀,x))`; `K = (t₁,s₁,t₀)`, `L = (t₁,t₀)`. -/
theorem pieceRep_TT (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b : D.S.TVar) (hs0 : sK 0 = Sum.inl a) (hs1 : sK 1 = Sum.inl b)
      (hL0 : sL 0 = sK 0) (hL1 : sL 1 = sK 2)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ BL ∧ ![τ 1, τ 2] ∈ BL) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ st.Bc ∧ ![τ 1, τ 2] ∈ st.Bc) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ sq.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ex • r) *
          conj (sepTerm st.c st.J st.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ex • r) - sepTerm st.c st.J st.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ex • r))) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJt * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c) CMq CMt))
        (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_joint (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl sK sL a b hs0 hs1 hL0 hL1 BK BL qK qL CJq CMq CJt CMt sq st q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx X hX => ?_⟩
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c) sq.toSepT st.toSepT ex ex hfl.abs_ex_le hfl.abs_ex_le
  have hfac' : ∀ (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ), slotVal D τ tt (sK 0) = τ a ∧ slotVal D τ tt (sK 1) = τ b := by
    intro τ tt; simp [hs0, hs1, slotVal]
  refine h D hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) sK sL q3 qK BL st.Bc B3 Bc3 BK sq.Bc (cJ st.J) sq.J
    CJt CJq _ (spS (sq.c * st.c) (plainF sq.M) (plainF st.M) ex ex) (fun τ r => by simp [hs0, hs1, slotVal])
    h1 h2 h3 h4 h5 h6 h7 (continuousOn_cJ st.hcont) h8 sq.hcell sq.hint sq.hBcB sq.hBci sq.hcont st.hJc sq.hJ hsp Bx X ?_
  intro tt htt
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  refine ⟨m1, m2, fun r k hr => ?_⟩
  obtain ⟨e0, e1⟩ := hfac' τ tt
  rw [hid r k hr, hL0, hL1, sp_ident_TT hr ex P.η]
  simp only [e0, e1]

/-- Piece MTQ (case M, kind 2): `-((Q(t₁,t₀,y) - Q(s₁,t₀,y)) conj T(s₁,t₀,y))`; `K = (t₁,s₁,t₀)`, `L = (s₁,t₀)`. -/
theorem pieceRep_MTQ (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b : D.S.TVar) (hs0 : sK 0 = Sum.inl a) (hs1 : sK 1 = Sum.inl b)
      (hL0 : sL 0 = sK 1) (hL1 : sL 1 = sK 2)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ BK ∧ ![τ 1, τ 2] ∈ BK) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ sq.Bc ∧ ![τ 1, τ 2] ∈ sq.Bc) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = -((sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ey • r) - sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ey • r)) *
          conj (sepTerm st.c st.J st.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ey • r)))) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c * -1) CMq CMt))
        (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_joint (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl sK sL a b hs0 hs1 hL0 hL1 BK BL qK qL CJq CMq CJt CMt sq st q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx X hX => ?_⟩
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c * -1) sq.toSepT st.toSepT ey ey hfl.abs_ey_le hfl.abs_ey_le
  have hfac' : ∀ (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ), slotVal D τ tt (sK 0) = τ a ∧ slotVal D τ tt (sK 1) = τ b := by
    intro τ tt; simp [hs0, hs1, slotVal]
  refine h D hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) sK sL q3 qL BK sq.Bc B3 Bc3 BL st.Bc sq.J (cJ st.J)
    CJq CJt _ (spS (sq.c * st.c * -1) (plainF sq.M) (plainF st.M) ey ey) (fun τ r => by simp [hs0, hs1, slotVal])
    h1 h2 h3 h4 h5 h6 h7 sq.hcont h8 st.hcell st.hint st.hBcB st.hBci (continuousOn_cJ st.hcont) sq.hJ st.hJc hsp Bx X ?_
  intro tt htt
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  refine ⟨m1, m2, fun r k hr => ?_⟩
  obtain ⟨e0, e1⟩ := hfac' τ tt
  rw [hid r k hr, hL0, hL1, sp_ident_MTQ hr ey P.η]
  simp only [e0, e1]

/-- Piece MTT (case M, kind 2): `-(conj Q(s₁,t₀,y) (T(s₁,t₀,y) - T(t₁,t₀,y)))`; `K = (s₁,t₁,t₀)`, `L = (s₁,t₀)`. -/
theorem pieceRep_MTT (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b : D.S.TVar) (hs0 : sK 0 = Sum.inl a) (hs1 : sK 1 = Sum.inl b)
      (hL0 : sL 0 = sK 0) (hL1 : sL 1 = sK 2)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ BL ∧ ![τ 1, τ 2] ∈ BL) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ st.Bc ∧ ![τ 1, τ 2] ∈ st.Bc) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ sq.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = -(conj (sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ey • r)) *
          (sepTerm st.c st.J st.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ey • r) - sepTerm st.c st.J st.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ey • r)))) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJt * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c * -1) CMq CMt))
        (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_joint (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl sK sL a b hs0 hs1 hL0 hL1 BK BL qK qL CJq CMq CJt CMt sq st q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx X hX => ?_⟩
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c * -1) sq.toSepT st.toSepT ey ey hfl.abs_ey_le hfl.abs_ey_le
  have hfac' : ∀ (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ), slotVal D τ tt (sK 0) = τ a ∧ slotVal D τ tt (sK 1) = τ b := by
    intro τ tt; simp [hs0, hs1, slotVal]
  refine h D hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) sK sL q3 qK BL st.Bc B3 Bc3 BK sq.Bc st.J (cJ sq.J)
    CJt CJq _ (spS (sq.c * st.c * -1) (plainF sq.M) (plainF st.M) ey ey) (fun τ r => by simp [hs0, hs1, slotVal])
    h1 h2 h3 h4 h5 h6 h7 st.hcont h8 sq.hcell sq.hint sq.hBcB sq.hBci (continuousOn_cJ sq.hcont) st.hJ sq.hJc hsp Bx X ?_
  intro tt htt
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  refine ⟨m1, m2, fun r k hr => ?_⟩
  obtain ⟨e0, e1⟩ := hfac' τ tt
  rw [hid r k hr, hL0, hL1, sp_ident_MTT hr ey P.η]
  simp only [e0, e1]

end WaveTurbulence.VineEstS5C.P4.W2
