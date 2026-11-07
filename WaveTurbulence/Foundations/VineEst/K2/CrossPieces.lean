/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.Rows2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRowsJ

/-! # W2-KIND2 (cross pieces): the kind-2 shapes TQ, TT, MTQ, MTT with a COMMON time factor across the two windows

`pieceRep_TQx`, `pieceRep_TTx`, `pieceRep_MTQx`, `pieceRep_MTTx`: the versions of `pieceRep_TQ`, ... (PieceRowsJ) in which the differenced factor
(`Q` for TQ/MTQ, `T` for TT/MTT) is given by ONE time factor `xJ` with `‖xJ‖_{𝔛^{1-2η}(B2)} < CJx` on a set `B2` containing both clock pairs
(`B2` need not lie in a unit cell), `xJ` continuous on `Bc2`.  The spatial part of the differenced factor and the other factor are as before.
The proofs are those of PieceRowsJ, with `pieceRep_joint` replaced by `pieceRep_joint2` (Lemma B).
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

/-- Piece TQ (kind 2): `conj(Q(s₁,t₀,x) - Q(t₁,t₀,x)) T(t₁,t₀,x)`; `K = (s₁,t₁,t₀)`, `L = (t₁,t₀)`. -/
theorem pieceRep_TQx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b : D.S.TVar) (hs0 : sK 0 = Sum.inl a) (hs1 : sK 1 = Sum.inl b)
      (hL0 : sL 0 = sK 1) (hL1 : sL 1 = sK 2)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt) (xJ : (Fin 2 → ℝ) → ℂ) (B2 Bc2 : Set (Fin 2 → ℝ)) (CJx : ℝ) (hc2 : ContinuousOn xJ Bc2)
      (hx2 : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => xJ ts) < ENNReal.ofReal CJx)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = conj (sepTerm sq.c xJ sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ex • r) - sepTerm sq.c xJ sq.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ex • r)) *
          sepTerm st.c st.J st.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ex • r)) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJx * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c) CMq CMt))
        (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_joint2 (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl sK sL a b hs0 hs1 hL0 hL1 BK BL qK qL CJq CMq CJt CMt sq st xJ B2 Bc2 CJx hc2 hx2 q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx X hX => ?_⟩
  have hxc : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => cJ xJ ts) < ENNReal.ofReal CJx := by
    have := XNorm00Restr_conj (1 - 2 * P.η) B2 (Set.univ : Set Unit) (fun ts _ => xJ ts)
    exact this.symm ▸ hx2
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c) sq.toSepT st.toSepT ex ex hfl.abs_ex_le hfl.abs_ex_le
  have hfac' : ∀ (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ), slotVal D τ tt (sK 0) = τ a ∧ slotVal D τ tt (sK 1) = τ b := by
    intro τ tt; simp [hs0, hs1, slotVal]
  refine h D hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) sK sL q3 qL B2 Bc2 B3 Bc3 BL st.Bc (cJ xJ) st.J
    CJx CJt _ (spS (sq.c * st.c) (plainF sq.M) (plainF st.M) ex ex) (fun τ r => by simp [hs0, hs1, slotVal])
    h1 h2 h3 h4 h5 h6 h7 (continuousOn_cJ hc2) h8 st.hcell st.hint st.hBcB st.hBci st.hcont hxc st.hJ hsp Bx X ?_
  intro tt htt
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  refine ⟨m1, m2, fun r k hr => ?_⟩
  obtain ⟨e0, e1⟩ := hfac' τ tt
  rw [hid r k hr, hL0, hL1, sp_ident_TQ hr ex P.η]
  simp only [e0, e1]

/-- Piece MTQ (case M, kind 2): `-((Q(t₁,t₀,y) - Q(s₁,t₀,y)) conj T(s₁,t₀,y))`; `K = (t₁,s₁,t₀)`, `L = (s₁,t₀)`. -/
theorem pieceRep_MTQx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b : D.S.TVar) (hs0 : sK 0 = Sum.inl a) (hs1 : sK 1 = Sum.inl b)
      (hL0 : sL 0 = sK 1) (hL1 : sL 1 = sK 2)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt) (xJ : (Fin 2 → ℝ) → ℂ) (B2 Bc2 : Set (Fin 2 → ℝ)) (CJx : ℝ) (hc2 : ContinuousOn xJ Bc2)
      (hx2 : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => xJ ts) < ENNReal.ofReal CJx)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = -((sepTerm sq.c xJ sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ey • r) - sepTerm sq.c xJ sq.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ey • r)) *
          conj (sepTerm st.c st.J st.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ey • r)))) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJx * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c * -1) CMq CMt))
        (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_joint2 (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl sK sL a b hs0 hs1 hL0 hL1 BK BL qK qL CJq CMq CJt CMt sq st xJ B2 Bc2 CJx hc2 hx2 q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx X hX => ?_⟩
  have hxc : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => cJ xJ ts) < ENNReal.ofReal CJx := by
    have := XNorm00Restr_conj (1 - 2 * P.η) B2 (Set.univ : Set Unit) (fun ts _ => xJ ts)
    exact this.symm ▸ hx2
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c * -1) sq.toSepT st.toSepT ey ey hfl.abs_ey_le hfl.abs_ey_le
  have hfac' : ∀ (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ), slotVal D τ tt (sK 0) = τ a ∧ slotVal D τ tt (sK 1) = τ b := by
    intro τ tt; simp [hs0, hs1, slotVal]
  refine h D hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) sK sL q3 qL B2 Bc2 B3 Bc3 BL st.Bc xJ (cJ st.J)
    CJx CJt _ (spS (sq.c * st.c * -1) (plainF sq.M) (plainF st.M) ey ey) (fun τ r => by simp [hs0, hs1, slotVal])
    h1 h2 h3 h4 h5 h6 h7 hc2 h8 st.hcell st.hint st.hBcB st.hBci (continuousOn_cJ st.hcont) hx2 st.hJc hsp Bx X ?_
  intro tt htt
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  refine ⟨m1, m2, fun r k hr => ?_⟩
  obtain ⟨e0, e1⟩ := hfac' τ tt
  rw [hid r k hr, hL0, hL1, sp_ident_MTQ hr ey P.η]
  simp only [e0, e1]

/-- Piece TT (kind 2): `Q(t₁,t₀,x) conj(T(t₁,t₀,x) - T(s₁,t₀,x))`; `K = (t₁,s₁,t₀)`, `L = (t₁,t₀)`. -/
theorem pieceRep_TTx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b : D.S.TVar) (hs0 : sK 0 = Sum.inl a) (hs1 : sK 1 = Sum.inl b)
      (hL0 : sL 0 = sK 0) (hL1 : sL 1 = sK 2)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt) (xJ : (Fin 2 → ℝ) → ℂ) (B2 Bc2 : Set (Fin 2 → ℝ)) (CJx : ℝ) (hc2 : ContinuousOn xJ Bc2)
      (hx2 : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => xJ ts) < ENNReal.ofReal CJx)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ sq.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ex • r) *
          conj (sepTerm st.c xJ st.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ex • r) - sepTerm st.c xJ st.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ex • r))) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJx * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c) CMq CMt))
        (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_joint2 (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl sK sL a b hs0 hs1 hL0 hL1 BK BL qK qL CJq CMq CJt CMt sq st xJ B2 Bc2 CJx hc2 hx2 q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx X hX => ?_⟩
  have hxc : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => cJ xJ ts) < ENNReal.ofReal CJx := by
    have := XNorm00Restr_conj (1 - 2 * P.η) B2 (Set.univ : Set Unit) (fun ts _ => xJ ts)
    exact this.symm ▸ hx2
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c) sq.toSepT st.toSepT ex ex hfl.abs_ex_le hfl.abs_ex_le
  have hfac' : ∀ (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ), slotVal D τ tt (sK 0) = τ a ∧ slotVal D τ tt (sK 1) = τ b := by
    intro τ tt; simp [hs0, hs1, slotVal]
  refine h D hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) sK sL q3 qK B2 Bc2 B3 Bc3 BK sq.Bc (cJ xJ) sq.J
    CJx CJq _ (spS (sq.c * st.c) (plainF sq.M) (plainF st.M) ex ex) (fun τ r => by simp [hs0, hs1, slotVal])
    h1 h2 h3 h4 h5 h6 h7 (continuousOn_cJ hc2) h8 sq.hcell sq.hint sq.hBcB sq.hBci sq.hcont hxc sq.hJ hsp Bx X ?_
  intro tt htt
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  refine ⟨m1, m2, fun r k hr => ?_⟩
  obtain ⟨e0, e1⟩ := hfac' τ tt
  rw [hid r k hr, hL0, hL1, sp_ident_TT hr ex P.η]
  simp only [e0, e1]

/-- Piece MTT (case M, kind 2): `-(conj Q(s₁,t₀,y) (T(s₁,t₀,y) - T(t₁,t₀,y)))`; `K = (s₁,t₁,t₀)`, `L = (s₁,t₀)`. -/
theorem pieceRep_MTTx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b : D.S.TVar) (hs0 : sK 0 = Sum.inl a) (hs1 : sK 1 = Sum.inl b)
      (hL0 : sL 0 = sK 0) (hL1 : sL 1 = sK 2)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt) (xJ : (Fin 2 → ℝ) → ℂ) (B2 Bc2 : Set (Fin 2 → ℝ)) (CJx : ℝ) (hc2 : ContinuousOn xJ Bc2)
      (hx2 : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => xJ ts) < ENNReal.ofReal CJx)
      (q3 : Fin 3 → ℝ) (B3 Bc3 : Set (Fin 3 → ℝ)),
      B3 ⊆ cell q3 → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ sq.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = -(conj (sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ey • r)) *
          (sepTerm st.c xJ st.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 2)) (k + ey • r) - sepTerm st.c xJ st.M (slotVal D τ tt (sK 1)) (slotVal D τ tt (sK 2)) (k + ey • r)))) →
      PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJx * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c * -1) CMq CMt))
        (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_joint2 (A := A) (P := P) G Rb
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl sK sL a b hs0 hs1 hL0 hL1 BK BL qK qL CJq CMq CJt CMt sq st xJ B2 Bc2 CJx hc2 hx2 q3 B3 Bc3 h1 h2 h3 h4 h5 h6 h7 h8 Bx X hX => ?_⟩
  have hxc : XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => cJ xJ ts) < ENNReal.ofReal CJx := by
    have := XNorm00Restr_conj (1 - 2 * P.η) B2 (Set.univ : Set Unit) (fun ts _ => xJ ts)
    exact this.symm ▸ hx2
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c * -1) sq.toSepT st.toSepT ey ey hfl.abs_ey_le hfl.abs_ey_le
  have hfac' : ∀ (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ), slotVal D τ tt (sK 0) = τ a ∧ slotVal D τ tt (sK 1) = τ b := by
    intro τ tt; simp [hs0, hs1, slotVal]
  refine h D hI vp vb ε (fun τ _ => ((|τ a - τ b| ^ (1 - 3 * P.η) : ℝ) : ℂ)) sK sL q3 qK B2 Bc2 B3 Bc3 BK sq.Bc xJ (cJ sq.J)
    CJx CJq _ (spS (sq.c * st.c * -1) (plainF sq.M) (plainF st.M) ey ey) (fun τ r => by simp [hs0, hs1, slotVal])
    h1 h2 h3 h4 h5 h6 h7 hc2 h8 sq.hcell sq.hint sq.hBcB sq.hBci (continuousOn_cJ sq.hcont) hx2 sq.hJc hsp Bx X ?_
  intro tt htt
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  refine ⟨m1, m2, fun r k hr => ?_⟩
  obtain ⟨e0, e1⟩ := hfac' τ tt
  rw [hid r k hr, hL0, hL1, sp_ident_MTT hr ey P.η]
  simp only [e0, e1]

end WaveTurbulence.VineEstS5C.P4.W2.K2
