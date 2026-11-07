/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceSp
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont

/-! # P4-W2 (b1): the exceptional factors of the ten non-remainder shapes as two-row representations

For each shape of `bundlePt` (A1, A2, KQ, KT, MKQ, MKT: separated rows; TQ, TT, MTQ, MTT: joint three-clock `𝒦` row, kind 2) the explicit separated form of the shape, evaluated at the
clocks `τ_{v}` and the momenta `x = k + ex r`, `y = k + ey r` (`FlagXY`), is a `PieceRep` (`PieceRep.lean`) from the raw `SepT` data of the couple and tree factors (boxes, `XNorm` bound of the time factors,
`SNormR` bounds of the spatial factors) with the constants:  `K` size `C · CJ · spConst`, `L` size `C · CJ · 1`.  The kind-1 shapes carry `fac = ‖r‖`, the kind-2 shapes the factor `|a|^{1-3η}`.
The identities are those of `PieceSp` (`sp_ident_*`); the hypotheses `hv0` (the `t₀` clock slots of the two rows coincide) etc. are the clock identifications of the shape.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS4c
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

/-- The constant of the spatial weight `spS` at the numerals of the datum. -/
noncomputable def spConst (d wN wDec : ℕ) (c βF βG : ℝ) : ℝ :=
  |c| * ((2 : ℝ) ^ wN * (d : ℝ) ^ wN * ((2 : ℝ) ^ 0 * (d : ℝ) ^ wN * βG) * ((2 : ℝ) ^ wDec * (d : ℝ) ^ wN * βF))

theorem continuousOn_cJ {J : (Fin 2 → ℝ) → ℂ} {S : Set (Fin 2 → ℝ)} (h : ContinuousOn J S) : ContinuousOn (cJ J) S :=
  Complex.continuous_conj.comp_continuousOn h

section Sup
variable {D : SumintPar.SumintDatum P.d}

theorem spS_sup_pp (G : AmbP A P) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d) (vp : D.S.VIdx) (c : ℝ)
    {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
    (sq : SepT P (30 * P.d) BK qK CJq CMq) (st : SepT P 0 BL qL CJt CMt) (e1 e2 : ℝ) (h1 : |e1| ≤ 1) (h2 : |e2| ≤ 1) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (spS c (plainF sq.M) (plainF st.M) e1 e2 r)) ≤
      ENNReal.ofReal (spConst P.d D.wN D.wDec c CMq CMt) :=
  spS_bound (A := D.wN) (W := D.wDec) G.hd1 (by omega) c _ _ h1 h2 sq.hCM st.hCM
    (plainF_snorm (sn_lo G.hd1 (by omega) (by omega) sq.hM sq.hCM))
    (plainF_snorm (sn_lo G.hd1 (by omega) le_rfl st.hM st.hCM))

theorem spS_sup_dp (G : AmbP A P) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d) (vp : D.S.VIdx) (c : ℝ)
    {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
    (sq : SepT P (30 * P.d) BK qK CJq CMq) (st : SepT P 0 BL qL CJt CMt) (ε e1 e2 : ℝ) (hε : |ε| = 1) (h1 : |e1| ≤ 1) (h2 : |e2| ≤ 1) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (spS c (diffF ε sq.M) (plainF st.M) e1 e2 r)) ≤
      ENNReal.ofReal (spConst P.d D.wN D.wDec c ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ (D.wN + 1) * CMq) CMt) :=
  spS_bound (A := D.wN) (W := D.wDec) G.hd1 (by omega) c _ _ h1 h2 (by have := sq.hCM; positivity) st.hCM
    (diffF_snorm sq.hCM hε (sn_lo G.hd1 (by omega) (by omega) sq.hM sq.hCM))
    (plainF_snorm (sn_lo G.hd1 (by omega) le_rfl st.hM st.hCM))

theorem spS_sup_pd (G : AmbP A P) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d) (vp : D.S.VIdx) (c : ℝ)
    {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
    (sq : SepT P (30 * P.d) BK qK CJq CMq) (st : SepT P 0 BL qL CJt CMt) (ε e1 e2 : ℝ) (hε : |ε| = 1) (h1 : |e1| ≤ 1) (h2 : |e2| ≤ 1) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (spS c (plainF sq.M) (diffF ε st.M) e1 e2 r)) ≤
      ENNReal.ofReal (spConst P.d D.wN D.wDec c CMq ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ (D.wN + 1) * CMt)) :=
  spS_bound (A := D.wN) (W := D.wDec) G.hd1 (by omega) c _ _ h1 h2 sq.hCM (by have := st.hCM; positivity)
    (plainF_snorm (sn_lo G.hd1 (by omega) (by omega) sq.hM sq.hCM))
    (diffF_snorm st.hCM hε (sn_lo G.hd1 (by omega) le_rfl st.hM st.hCM))

end Sup

/-- Piece A1: `conj Q(s₁,t₀,y) T(t₁,t₀,x)`; `K = (s₁,t₀)`, `L = (t₁,t₀)`. -/
theorem pieceRep_A1 (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (hv0 : sK 1 = sL 1)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt),
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ sq.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = conj (sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 1)) (k + ey • r)) *
          sepTerm st.c st.J st.M (slotVal D τ tt (sL 0)) (slotVal D τ tt (sL 1)) (k + ex • r)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1) X
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c) CMq CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_sep (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl sK sL hv0 BK BL qK qL CJq CMq CJt CMt sq st Bx X hX => ?_⟩
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c) sq.toSepT st.toSepT ey ex hfl.abs_ey_le hfl.abs_ex_le
  exact h D hI vp vb ε (fun _ _ => 1) sK sL qK qL BK sq.Bc BL st.Bc (cJ sq.J) st.J CJq CJt _ (spS (sq.c * st.c) (plainF sq.M) (plainF st.M) ey ex)
    sq.hcell sq.hint sq.hBcB sq.hBci (continuousOn_cJ sq.hcont) st.hcell st.hint st.hBcB st.hBci st.hcont sq.hJc st.hJ hsp Bx X
    (fun tt htt => by
      filter_upwards [hX tt htt] with τ hτ' hd
      obtain ⟨m1, m2, hid⟩ := hτ' hd
      refine ⟨m1, m2, fun r k hr => ?_⟩
      rw [hid r k hr, ← hv0, sp_ident_A1 (ε := ε) hr]; simp)
/-- Piece A2: `Q(t₁,t₀,x) conj T(s₁,t₀,y)`; `K = (t₁,t₀)`, `L = (s₁,t₀)`. -/
theorem pieceRep_A2 (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (hv0 : sK 1 = sL 1)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt),
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ sq.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 1)) (k + ex • r) *
          conj (sepTerm st.c st.J st.M (slotVal D τ tt (sL 0)) (slotVal D τ tt (sL 1)) (k + ey • r))) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1) X
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c) CMq CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_sep (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl sK sL hv0 BK BL qK qL CJq CMq CJt CMt sq st Bx X hX => ?_⟩
  have hsp := spS_sup_pp G hwN hwDec vp (sq.c * st.c) sq.toSepT st.toSepT ex ey hfl.abs_ex_le hfl.abs_ey_le
  exact h D hI vp vb ε (fun _ _ => 1) sK sL qK qL BK sq.Bc BL st.Bc sq.J (cJ st.J) CJq CJt _ (spS (sq.c * st.c) (plainF sq.M) (plainF st.M) ex ey)
    sq.hcell sq.hint sq.hBcB sq.hBci sq.hcont st.hcell st.hint st.hBcB st.hBci (continuousOn_cJ st.hcont) sq.hJ st.hJc hsp Bx X
    (fun tt htt => by
      filter_upwards [hX tt htt] with τ hτ' hd
      obtain ⟨m1, m2, hid⟩ := hτ' hd
      refine ⟨m1, m2, fun r k hr => ?_⟩
      rw [hid r k hr, ← hv0, sp_ident_A2 hr ex ey]; simp)
/-- Piece KQ (kind 1): `conj(Q(s₁,t₀,y) - Q(s₁,t₀,x)) T(t₁,t₀,x)`; `K = (s₁,t₀)`, `L = (t₁,t₀)`; `fac = ‖r‖`. -/
theorem pieceRep_KQ (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (hv0 : sK 1 = sL 1)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt),
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ sq.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = conj (sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 1)) (k + ey • r) - sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 1)) (k + ex • r)) *
          sepTerm st.c st.J st.M (slotVal D τ tt (sL 0)) (slotVal D τ tt (sL 1)) (k + ex • r)) →
      PieceRep (P := P) hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c * flagSign ex) ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ (D.wN + 1) * CMq) CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_sep (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl sK sL hv0 BK BL qK qL CJq CMq CJt CMt sq st Bx X hX => ?_⟩
  have hsp := spS_sup_dp G hwN hwDec vp (sq.c * st.c * flagSign ex) sq.toSepT st.toSepT ε 0 ex hfl.1 (by simp) hfl.abs_ex_le
  exact h D hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ)) sK sL qK qL BK sq.Bc BL st.Bc (cJ sq.J) st.J CJq CJt _ (spS (sq.c * st.c * flagSign ex) (diffF ε sq.M) (plainF st.M) 0 ex)
    sq.hcell sq.hint sq.hBcB sq.hBci (continuousOn_cJ sq.hcont) st.hcell st.hint st.hBcB st.hBci st.hcont sq.hJc st.hJ hsp Bx X
    (fun tt htt => by
      filter_upwards [hX tt htt] with τ hτ' hd
      obtain ⟨m1, m2, hid⟩ := hτ' hd
      refine ⟨m1, m2, fun r k hr => ?_⟩
      rw [hid r k hr, ← hv0, sp_ident_KQ hfl hr])
/-- Piece KT (kind 1): `Q(t₁,t₀,x) conj(T(s₁,t₀,x) - T(s₁,t₀,y))`; `K = (t₁,t₀)`, `L = (s₁,t₀)`; `fac = ‖r‖`. -/
theorem pieceRep_KT (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (hv0 : sK 1 = sL 1)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt),
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ sq.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 1)) (k + ex • r) *
          conj (sepTerm st.c st.J st.M (slotVal D τ tt (sL 0)) (slotVal D τ tt (sL 1)) (k + ex • r) - sepTerm st.c st.J st.M (slotVal D τ tt (sL 0)) (slotVal D τ tt (sL 1)) (k + ey • r))) →
      PieceRep (P := P) hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c * -flagSign ex) CMq ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ (D.wN + 1) * CMt)))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_sep (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl sK sL hv0 BK BL qK qL CJq CMq CJt CMt sq st Bx X hX => ?_⟩
  have hsp := spS_sup_pd G hwN hwDec vp (sq.c * st.c * -flagSign ex) sq.toSepT st.toSepT ε ex 0 hfl.1 hfl.abs_ex_le (by simp)
  exact h D hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ)) sK sL qK qL BK sq.Bc BL st.Bc sq.J (cJ st.J) CJq CJt _ (spS (sq.c * st.c * -flagSign ex) (plainF sq.M) (diffF ε st.M) ex 0)
    sq.hcell sq.hint sq.hBcB sq.hBci sq.hcont st.hcell st.hint st.hBcB st.hBci (continuousOn_cJ st.hcont) sq.hJ st.hJc hsp Bx X
    (fun tt htt => by
      filter_upwards [hX tt htt] with τ hτ' hd
      obtain ⟨m1, m2, hid⟩ := hτ' hd
      refine ⟨m1, m2, fun r k hr => ?_⟩
      rw [hid r k hr, ← hv0, sp_ident_KT hfl hr])
/-- Piece MKQ (case M, kind 1): `-((Q(t₁,t₀,x) - Q(t₁,t₀,y)) conj T(s₁,t₀,y))`; `K = (t₁,t₀)`, `L = (s₁,t₀)`; `fac = ‖r‖`. -/
theorem pieceRep_MKQ (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (hv0 : sK 1 = sL 1)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt),
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ sq.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = -((sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 1)) (k + ex • r) - sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 1)) (k + ey • r)) *
          conj (sepTerm st.c st.J st.M (slotVal D τ tt (sL 0)) (slotVal D τ tt (sL 1)) (k + ey • r)))) →
      PieceRep (P := P) hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c * flagSign ex) ((2 : ℝ) ^ D.wDec * (P.d : ℝ) ^ (D.wN + 1) * CMq) CMt))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_sep (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl sK sL hv0 BK BL qK qL CJq CMq CJt CMt sq st Bx X hX => ?_⟩
  have hsp := spS_sup_dp G hwN hwDec vp (sq.c * st.c * flagSign ex) sq.toSepT st.toSepT ε 0 ey hfl.1 (by simp) hfl.abs_ey_le
  exact h D hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ)) sK sL qK qL BK sq.Bc BL st.Bc sq.J (cJ st.J) CJq CJt _ (spS (sq.c * st.c * flagSign ex) (diffF ε sq.M) (plainF st.M) 0 ey)
    sq.hcell sq.hint sq.hBcB sq.hBci sq.hcont st.hcell st.hint st.hBcB st.hBci (continuousOn_cJ st.hcont) sq.hJ st.hJc hsp Bx X
    (fun tt htt => by
      filter_upwards [hX tt htt] with τ hτ' hd
      obtain ⟨m1, m2, hid⟩ := hτ' hd
      refine ⟨m1, m2, fun r k hr => ?_⟩
      rw [hid r k hr, ← hv0, sp_ident_MKQ hfl hr])
/-- Piece MKT (case M, kind 1): `-(conj Q(s₁,t₀,y) (T(t₁,t₀,y) - T(t₁,t₀,x)))`; `K = (s₁,t₀)`, `L = (t₁,t₀)`; `fac = ‖r‖`. -/
theorem pieceRep_MKT (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (hv0 : sK 1 = sL 1)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}
      (sq : SepTC P (30 * P.d) BK qK CJq CMq) (st : SepTC P 0 BL qL CJt CMt),
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ sq.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ st.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = -(conj (sepTerm sq.c sq.J sq.M (slotVal D τ tt (sK 0)) (slotVal D τ tt (sK 1)) (k + ey • r)) *
          (sepTerm st.c st.J st.M (slotVal D τ tt (sL 0)) (slotVal D τ tt (sL 1)) (k + ey • r) - sepTerm st.c st.J st.M (slotVal D τ tt (sL 0)) (slotVal D τ tt (sL 1)) (k + ex • r)))) →
      PieceRep (P := P) hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ)) X
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (spConst P.d D.wN D.wDec (sq.c * st.c * -flagSign ex) CMq ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ (D.wN + 1) * CMt)))
        (C * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_sep (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl sK sL hv0 BK BL qK qL CJq CMq CJt CMt sq st Bx X hX => ?_⟩
  have hsp := spS_sup_pd G hwN hwDec vp (sq.c * st.c * -flagSign ex) sq.toSepT st.toSepT ε ey 0 hfl.1 hfl.abs_ey_le (by simp)
  exact h D hI vp vb ε (fun _ r => ((‖r‖ : ℝ) : ℂ)) sK sL qK qL BK sq.Bc BL st.Bc (cJ sq.J) st.J CJq CJt _ (spS (sq.c * st.c * -flagSign ex) (plainF sq.M) (diffF ε st.M) ey 0)
    sq.hcell sq.hint sq.hBcB sq.hBci (continuousOn_cJ sq.hcont) st.hcell st.hint st.hBcB st.hBci st.hcont sq.hJc st.hJ hsp Bx X
    (fun tt htt => by
      filter_upwards [hX tt htt] with τ hτ' hd
      obtain ⟨m1, m2, hid⟩ := hτ' hd
      refine ⟨m1, m2, fun r k hr => ?_⟩
      rw [hid r k hr, ← hv0, sp_ident_MKT hfl hr])

end WaveTurbulence.VineEstS5C.P4.W2
