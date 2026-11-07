/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemRowsC
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemShift
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemProd

/-! # P4-W2 (R78, F-REM-ORIENT): the remainder pieces as two-row representations

`RemC P Λ₂ B q CR`: a remainder kernel on the window `B` that is `ContinuousOn Bc` (`Bc ⊆ B ⊆ cell q`, `Bc ⊆ closure (interior Bc)`), with `‖f‖_{𝔛^{6η^6, 30d, Λ₂}(B)} < CR`.
The six row shapes of the remainder pieces `rA1…rB3` (both orientations of `FlagXY`), as `PieceRep`s (`fac = 1`; the `𝒦` row sits at momentum `k` (ret), the `ℒ` row at `k + ε r` (low)):

* `pieceRep_SR`   : `𝒦` separated (`J_K · M`) × `ℒ` remainder at `k + ε r`;
* `pieceRep_RmS`  : `𝒦` shifted couple remainder `f(k + u r)` times a weight-`0` multiplier `M(r,k)`, `ℒ` separated;
* `pieceRep_RR`   : `𝒦` couple remainder × `ℒ` remainder at `k + ε r`;
* `pieceRep_RmDS` : `𝒦` tree remainder times a DECAYING multiplier `M(r,k)`, `ℒ` separated;
* `pieceRep_RP`   : `𝒦` three-clock product (shifted couple remainder) × (tree remainder), `ℒ` the constant `1`. -/

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

/-- A remainder kernel on the window `B`, continuous on the continuity set `Bc`. -/
structure RemC (P : WTParams) (Λ₂ : ℕ) (B : Set (Fin 2 → ℝ)) (q : Fin 2 → ℝ) (CR : ℝ) where
  f : (Fin 2 → ℝ) → Mom P.d → ℂ
  Bc : Set (Fin 2 → ℝ)
  hcell : B ⊆ cell q
  hint : B ⊆ closure (interior B)
  hBcB : Bc ⊆ B
  hBci : Bc ⊆ closure (interior Bc)
  hcont : ∀ k, ContinuousOn (fun t => f t k) Bc
  hCR : 0 ≤ CR
  hX : XNormRestr (6 * P.η ^ 6) (30 * P.d) Λ₂ B Set.univ f < ENNReal.ofReal CR

/-- The conjugate remainder. -/
def RemC.conj {Λ₂ : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CR : ℝ} (R : RemC P Λ₂ B q CR) : RemC P Λ₂ B q CR where
  f := fun ts k => starRingEnd ℂ (R.f ts k)
  Bc := R.Bc
  hcell := R.hcell
  hint := R.hint
  hBcB := R.hBcB
  hBci := R.hBci
  hcont := fun k => Complex.continuous_conj.comp_continuousOn (R.hcont k)
  hCR := R.hCR
  hX := by rw [VineEstS4c.XNormRestr_conj]; exact R.hX

theorem RemC.hXidx {Λ₂ : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CR : ℝ} (R : RemC P Λ₂ B q CR) {Λ₁ : ℕ} (h : Λ₁ ≤ 30 * P.d) :
    XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ B Set.univ R.f < ENNReal.ofReal CR :=
  lt_of_le_of_lt (XNormRestr_mono_idx h le_rfl B _ _) R.hX

theorem wN_ne_zero (G : AmbP A P) {D : SumintPar.SumintDatum P.d} (hwN : D.wN + 1 = 30 * P.d) : 30 * P.d - 1 ≠ 0 := by
  have := G.hd1; omega

theorem clk2_mem {D : SumintPar.SumintDatum P.d} {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ)
    (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (hs : ∀ i, R.slot i = ![s 0, s 1, s 0] i) (τ : D.S.TVar → ℝ)
    (tt : Fin 3 → ℝ) {B : Set (Fin 2 → ℝ)} (h : (fun i => slotVal D τ tt (s i)) ∈ B) : ![R.clk τ tt 0, R.clk τ tt 1] ∈ B := by
  have e : ![R.clk τ tt 0, R.clk τ tt 1] = fun i => slotVal D τ tt (s i) := by
    funext i; fin_cases i <;> simp [RowData.clk, hs, slotVal]
  rw [e]; exact h

theorem clk3_eq {D : SumintPar.SumintDatum P.d} {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ)
    (s : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (hs : ∀ i, R.slot i = s i) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) (i : Fin 3) :
    R.clk τ tt i = slotVal D τ tt (s i) := by
  simp [RowData.clk, hs]

/-- Piece SR: `𝒦` separated, `ℒ` remainder at `k + ε r`. -/
theorem pieceRep_SR (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d)
      (vp vb : D.S.VIdx) (ε : ℝ) (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ) (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {qK qL : Fin 2 → ℝ} {BK BcK BL : Set (Fin 2 → ℝ)} (JK : (Fin 2 → ℝ) → ℂ) {CJK Cm CR : ℝ} (M : Mom P.d → Mom P.d → ℂ)
      (rt : RemC P 0 BL qL CR),
      BK ⊆ cell qK → BK ⊆ closure (interior BK) → BcK ⊆ BK → BcK ⊆ closure (interior BcK) → ContinuousOn JK BcK →
      XNorm00Restr (V := Unit) (1 - P.η) BK Set.univ (fun ts _ => JK ts) < ENNReal.ofReal CJK →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (M r)) ≤ ENNReal.ofReal Cm →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ BcK ∧ (fun i => slotVal D τ tt (sL i)) ∈ rt.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = fac τ r * (JK ![slotVal D τ tt (sK 0), slotVal D τ tt (sK 1)] * M r k *
          rt.f ![slotVal D τ tt (sL 0), slotVal D τ tt (sL 1)] (k + ε • r))) →
      PieceRep (P := P) hI vp vb ε fac X
        (C * ENNReal.ofReal CJK * ENNReal.ofReal Cm) (C' * ENNReal.ofReal CR) Bx := by
  obtain ⟨C, hC, h⟩ := sepRowWS G
  obtain ⟨C', hC', h'⟩ := remRowC (P := P) (30 * P.d - 1) 0 (by have := G.hd1; omega) G.hη0
  refine ⟨C, C', hC, hC', fun D hI hwN vp vb ε fac sK sL qK qL BK BcK BL JK CJK Cm CR M rt g1 g2 g3 g4 g5 hJK hM Bx X hX => ?_⟩
  obtain ⟨RK, hKW, hKs, hKb, hKae⟩ := h D hI (Sum.inl vp) sK qK BK BcK JK CJK Cm M g1 g2 g3 g4 g5 hJK hM
    (fun w hw => absurd hw (by simp))
  obtain ⟨RL, hLW, hLs, hLb, hLae⟩ := h' D hI (Sum.inr vb) (by omega) rfl sL qL BL rt.Bc rt.f (ENNReal.ofReal CR)
    ENNReal.ofReal_ne_top rt.hcell rt.hint rt.hBcB rt.hBci rt.hcont (rt.hXidx (by omega))
  refine ⟨RK, RL, hKae, hLae, hKb, hLb.le, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  intro r k hr
  rw [hKW _ r k (clk2_mem RK sK hKs τ tt m1), hLW _ r (k + ε • r) (clk2_mem RL sL hLs τ tt m2), clk_sep RK sK hKs,
    clk_sep RL sL hLs, hid r k hr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Piece RmS: `𝒦` shifted couple remainder `f(k + u r)` times a weight-`0` multiplier, `ℒ` separated (time only). -/
theorem pieceRep_RmS (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d)
      (hwDec : D.wDec = 30 * P.d) (vp vb : D.S.VIdx) (ε u : ℝ) (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ)
      (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {qK qL : Fin 2 → ℝ} {BK BL BcL : Set (Fin 2 → ℝ)} (JL : (Fin 2 → ℝ) → ℂ) {CR CJL Cm : ℝ} (M : Mom P.d → Mom P.d → ℂ)
      (rq : RemC P (30 * P.d) BK qK CR),
      |u| ≤ 1 → BL ⊆ cell qL → BL ⊆ closure (interior BL) → BcL ⊆ BL → BcL ⊆ closure (interior BcL) → ContinuousOn JL BcL →
      XNorm00Restr (V := Unit) (1 - P.η) BL Set.univ (fun ts _ => JL ts) < ENNReal.ofReal CJL →
      (∀ r : Mom P.d, ‖r‖ ≤ 1 → SNorm D.wN 0 (M r) ≤ ENNReal.ofReal Cm) →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ rq.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ BcL ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = fac τ r * (rq.f ![slotVal D τ tt (sK 0), slotVal D τ tt (sK 1)] (k + u • r) * M r k *
          JL ![slotVal D τ tt (sL 0), slotVal D τ tt (sL 1)])) →
      PieceRep (P := P) hI vp vb ε fac X
        (C * ENNReal.ofReal CR * ENNReal.ofReal Cm) (C' * ENNReal.ofReal CJL * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := remRowShiftMul (P := P) (30 * P.d - 1) (30 * P.d) (by have := G.hd1; omega) G.hη0 G.hd1
  obtain ⟨C', hC', h'⟩ := sepRowWS G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε u fac sK sL qK qL BK BL BcL JL CR CJL Cm M rq hu g1 g2 g3 g4 g5 hJL hM Bx X hX => ?_⟩
  obtain ⟨RK, hKW, hKs, hKb, hKae⟩ := h D hI vp (by omega) hwDec sK qK BK rq.Bc rq.f M u (ENNReal.ofReal CR) Cm hu
    ENNReal.ofReal_ne_top rq.hcell rq.hint rq.hBcB rq.hBci rq.hcont (rq.hXidx (by omega))
    (by rw [show 30 * P.d - 1 = D.wN by omega]; exact hM)
  obtain ⟨RL, hLW, hLs, hLb, hLae⟩ := h' D hI (Sum.inr vb) sL qL BL BcL JL CJL 1 (fun _ _ => 1) g1 g2 g3 g4 g5 hJL
    (snorm_one_le' (d := P.d) D.wN) (fun _ _ _ _ _ => rfl)
  refine ⟨RK, RL, hKae, hLae, hKb, hLb, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  intro r k hr
  rw [hKW _ r k hr (clk2_mem RK sK hKs τ tt m1), hLW _ r (k + ε • r) (clk2_mem RL sL hLs τ tt m2), clk_sep RK sK hKs,
    clk_sep RL sL hLs, hid r k hr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]

/-- Piece RR: `𝒦` couple remainder, `ℒ` tree remainder at `k + ε r`. -/
theorem pieceRep_RR (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d)
      (hwDec : D.wDec = 30 * P.d) (vp vb : D.S.VIdx) (ε : ℝ) (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ)
      (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) {qK qL : Fin 2 → ℝ} {BK BL : Set (Fin 2 → ℝ)} {CQ CT : ℝ}
      (rq : RemC P (30 * P.d) BK qK CQ) (rt : RemC P 0 BL qL CT),
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ rq.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ rt.Bc ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = fac τ r * (rq.f ![slotVal D τ tt (sK 0), slotVal D τ tt (sK 1)] k *
          rt.f ![slotVal D τ tt (sL 0), slotVal D τ tt (sL 1)] (k + ε • r))) →
      PieceRep (P := P) hI vp vb ε fac X
        (C * ENNReal.ofReal CQ) (C' * ENNReal.ofReal CT) Bx := by
  obtain ⟨C, hC, h⟩ := remRowC (P := P) (30 * P.d - 1) (30 * P.d) (by have := G.hd1; omega) G.hη0
  obtain ⟨C', hC', h'⟩ := remRowC (P := P) (30 * P.d - 1) 0 (by have := G.hd1; omega) G.hη0
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε fac sK sL qK qL BK BL CQ CT rq rt Bx X hX => ?_⟩
  obtain ⟨RK, hKW, hKs, hKb, hKae⟩ := h D hI (Sum.inl vp) (by omega) hwDec sK qK BK rq.Bc rq.f (ENNReal.ofReal CQ)
    ENNReal.ofReal_ne_top rq.hcell rq.hint rq.hBcB rq.hBci rq.hcont (rq.hXidx (by omega))
  obtain ⟨RL, hLW, hLs, hLb, hLae⟩ := h' D hI (Sum.inr vb) (by omega) rfl sL qL BL rt.Bc rt.f (ENNReal.ofReal CT)
    ENNReal.ofReal_ne_top rt.hcell rt.hint rt.hBcB rt.hBci rt.hcont (rt.hXidx (by omega))
  refine ⟨RK, RL, hKae, hLae, hKb.le, hLb.le, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  intro r k hr
  rw [hKW _ r k (clk2_mem RK sK hKs τ tt m1), hLW _ r (k + ε • r) (clk2_mem RL sL hLs τ tt m2), clk_sep RK sK hKs,
    clk_sep RL sL hLs, hid r k hr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Piece RmDS: `𝒦` tree remainder times a DECAYING multiplier, `ℒ` separated (time only). -/
theorem pieceRep_RmDS (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d)
      (hwDec : D.wDec = 30 * P.d) (vp vb : D.S.VIdx) (ε : ℝ) (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ)
      (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {qK qL : Fin 2 → ℝ} {BK BL BcL : Set (Fin 2 → ℝ)} (JL : (Fin 2 → ℝ) → ℂ) {CR CJL Cm : ℝ} (M : Mom P.d → Mom P.d → ℂ)
      (rt : RemC P 0 BK qK CR),
      BL ⊆ cell qL → BL ⊆ closure (interior BL) → BcL ⊆ BL → BcL ⊆ closure (interior BcL) → ContinuousOn JL BcL →
      XNorm00Restr (V := Unit) (1 - P.η) BL Set.univ (fun ts _ => JL ts) < ENNReal.ofReal CJL →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (M r)) ≤ ENNReal.ofReal Cm →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ rt.Bc ∧ (fun i => slotVal D τ tt (sL i)) ∈ BcL ∧ ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = fac τ r * (rt.f ![slotVal D τ tt (sK 0), slotVal D τ tt (sK 1)] k * M r k *
          JL ![slotVal D τ tt (sL 0), slotVal D τ tt (sL 1)])) →
      PieceRep (P := P) hI vp vb ε fac X
        (C * ENNReal.ofReal CR * ENNReal.ofReal Cm) (C' * ENNReal.ofReal CJL * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := remRowMulDC (P := P) (30 * P.d - 1) (30 * P.d) (by have := G.hd1; omega) G.hη0 G.hd1
  obtain ⟨C', hC', h'⟩ := sepRowWS G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε fac sK sL qK qL BK BL BcL JL CR CJL Cm M rt g1 g2 g3 g4 g5 hJL hM Bx X hX => ?_⟩
  obtain ⟨RK, hKW, hKs, hKb, hKae⟩ := h D hI vp (by omega) hwDec sK qK BK rt.Bc rt.f M (ENNReal.ofReal CR) Cm
    ENNReal.ofReal_ne_top rt.hcell rt.hint rt.hBcB rt.hBci rt.hcont (rt.hXidx (by omega))
    (by rw [show 30 * P.d - 1 = D.wN by omega, show 30 * P.d = rowOrder D (Sum.inl vp) from hwDec.symm]; exact hM)
  obtain ⟨RL, hLW, hLs, hLb, hLae⟩ := h' D hI (Sum.inr vb) sL qL BL BcL JL CJL 1 (fun _ _ => 1) g1 g2 g3 g4 g5 hJL
    (snorm_one_le' (d := P.d) D.wN) (fun _ _ _ _ _ => rfl)
  refine ⟨RK, RL, hKae, hLae, hKb, hLb, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨m1, m2, hid⟩ := hτ' hd
  intro r k hr
  rw [hKW _ r k (clk2_mem RK sK hKs τ tt m1), hLW _ r (k + ε • r) (clk2_mem RL sL hLs τ tt m2), clk_sep RK sK hKs,
    clk_sep RL sL hLs, hid r k hr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]

/-- Piece RP: `𝒦` three-clock product `f(c₀,c₂,k + u r) g(c₁,c₂,k)` (couple remainder × tree remainder), `ℒ` the constant `1`. -/
theorem pieceRep_RP (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d)
      (hwDec : D.wDec = 30 * P.d) (vp vb : D.S.VIdx) (ε u : ℝ) (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ)
      (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (sL : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {qf qg : Fin 2 → ℝ} {Bf Bg : Set (Fin 2 → ℝ)} {CQ CT : ℝ}
      (rq : RemC P (30 * P.d) Bf qf CQ) (rt : RemC P 0 Bg qg CT),
      |u| ≤ 1 →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (![slotVal D τ tt (sK 0), slotVal D τ tt (sK 2)] ∈ rq.Bc ∧ ![slotVal D τ tt (sK 1), slotVal D τ tt (sK 2)] ∈ rt.Bc) ∧
        ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = fac τ r * (rq.f ![slotVal D τ tt (sK 0), slotVal D τ tt (sK 2)] (k + u • r) *
          rt.f ![slotVal D τ tt (sK 1), slotVal D τ tt (sK 2)] k)) →
      PieceRep (P := P) hI vp vb ε fac X (C * ENNReal.ofReal CQ * ENNReal.ofReal CT) (ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := remRowProd (P := P) (30 * P.d - 1) (30 * P.d) (by have := G.hd1; omega) G.hη0 G.hd1
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε u fac sK sL qf qg Bf Bg CQ CT rq rt hu Bx X hX => ?_⟩
  obtain ⟨RK, hKW, hKs, hKb, hKae⟩ := h D hI vp (by omega) hwDec sK qf qg Bf Bg rq.Bc rt.Bc rq.f rt.f u
    (ENNReal.ofReal CQ) (ENNReal.ofReal CT) hu ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top rq.hcell rq.hint rt.hcell rt.hint
    rq.hBcB rq.hBci rt.hBcB rt.hBci rq.hcont rt.hcont (rq.hXidx (by omega)) (rt.hXidx (by omega))
  obtain ⟨RL, hLW, hLs, hLb, hLae⟩ := oneRowC G.hη0 D hI vb sL
  refine ⟨RK, RL, hKae, hLae, hKb, hLb, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ' hd
  obtain ⟨⟨m1, m2⟩, hid⟩ := hτ' hd
  intro r k hr
  have c0 := clk3_eq RK sK hKs τ tt 0
  have c1 := clk3_eq RK sK hKs τ tt 1
  have c2 := clk3_eq RK sK hKs τ tt 2
  rw [hKW _ r k hr (by rw [c0, c2]; exact m1) (by rw [c1, c2]; exact m2), hLW, clk_joint RK sK hKs, hid r k hr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one]

end WaveTurbulence.VineEstS5C.P4.W2
