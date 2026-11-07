/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Rows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxMul
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.SpaceG

/-! # P4-W2 (b1): the two-row representation of an exceptional factor

`PieceRep hI vp vb ε fac X bK bL Bx` (R82 form: for `tt ∈ Bx` and a.e. `τ` of the time domain; the rows are Fourier sums, valid at every clock): the exceptional factor `X(τ, tt, r, k)` of a record (a function of the engine point and of the momentum `k` of the pair row and the gap `r`)
is, on the engine time domain and for `‖r‖ ≤ 1`, `fac(τ, r)` (the kind-2 factor `|t₁ - s₁|^{1-3η}` of the block, the kind-1 factor `‖r‖`, else `1`) times the product of a `𝒦` row `RK` at the pair row `vp` (momentum `k`) and an `ℒ` row `RL` at the branch row `vb`
(momentum `k + ε r`, the lower joint), with the row sizes bounded by `bK`, `bL`.

`pieceRep_sep`: `X = J_K(clocks) M(r, k) · J_L(clocks)` (separated rows).  The joint (three-clock) and remainder variants are in `PieceRepJ`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

variable {A : ℝ} {P : WTParams}

/-- **A two-row representation of an exceptional factor** (see the module docstring): for `tt ∈ Bx` and a.e. `τ` of the time domain. -/
def PieceRep {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (vp vb : D.S.VIdx) (ε : ℝ) (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ)
    (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (bK bL : ℝ≥0∞) (Bx : Set (Fin 3 → ℝ)) : Prop :=
  ∃ (RK : RowData D (6 * P.η ^ 6) (Sum.inl vp)) (RL : RowData D (6 * P.η ^ 6) (Sum.inr vb)),
    RK.Ae hI ∧ RL.Ae hI ∧ RK.b ≤ bK ∧ RL.b ≤ bL ∧
    ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
      X τ tt r k = fac τ r * (RK.W (RK.clk τ tt) r k * RL.W (RL.clk τ tt) r (k + ε • r))

theorem PieceRep.mono {D : SumintPar.SumintDatum P.d} {hI : 0 < D.S.I} {vp vb : D.S.VIdx} {ε : ℝ} {fac : (D.S.TVar → ℝ) → Mom P.d → ℂ}
    {X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {bK bL bK' bL' : ℝ≥0∞} {Bx : Set (Fin 3 → ℝ)}
    (h : PieceRep (P := P) hI vp vb ε fac X bK bL Bx) (hK : bK ≤ bK') (hL : bL ≤ bL') :
    PieceRep (P := P) hI vp vb ε fac X bK' bL' Bx := by
  obtain ⟨RK, RL, h1, h2, h3, h4, h5⟩ := h
  exact ⟨RK, RL, h1, h2, h3.trans hK, h4.trans hL, h5⟩

theorem PieceRep.congr {D : SumintPar.SumintDatum P.d} {hI : 0 < D.S.I} {vp vb : D.S.VIdx} {ε : ℝ} {fac : (D.S.TVar → ℝ) → Mom P.d → ℂ}
    {X X' : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {bK bL : ℝ≥0∞} {Bx : Set (Fin 3 → ℝ)}
    (h : PieceRep (P := P) hI vp vb ε fac X bK bL Bx)
    (hX : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k : Mom P.d, ‖r‖ ≤ 1 → X' τ tt r k = X τ tt r k) :
    PieceRep (P := P) hI vp vb ε fac X' bK bL Bx := by
  obtain ⟨RK, RL, h1, h2, h3, h4, h5⟩ := h
  refine ⟨RK, RL, h1, h2, h3, h4, fun tt htt => ?_⟩
  filter_upwards [hX tt htt, h5 tt htt] with τ hτ hτ' hd r k hr
  exact (hτ hd r k hr).trans (hτ' hd r k hr)

theorem clk_sep {D : SumintPar.SumintDatum P.d} {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ) (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
    (hs : ∀ i, R.slot i = ![s 0, s 1, s 0] i) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) :
    R.clk τ tt = ![slotVal D τ tt (s 0), slotVal D τ tt (s 1), slotVal D τ tt (s 0)] := by
  funext i; fin_cases i <;> simp [RowData.clk, hs, slotVal]

theorem clk_joint {D : SumintPar.SumintDatum P.d} {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ) (s : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
    (hs : ∀ i, R.slot i = s i) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) :
    R.clk τ tt = ![slotVal D τ tt (s 0), slotVal D τ tt (s 1), slotVal D τ tt (s 2)] := by
  funext i; fin_cases i <;> simp [RowData.clk, hs, slotVal]

/-- **The separated representation** `X = fac · J_K(clocks) M(r, k) · J_L(clocks)` with slot-general clocks (exterior clocks allowed; `Bc` = continuity sets); the clocks must lie in the continuity sets only for `tt ∈ Bx` and a.e. `τ`, as part of the identity hypothesis. -/
theorem pieceRep_sep (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (vp vb : D.S.VIdx) (ε : ℝ)
      (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ) (sK sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (qK qL : Fin 2 → ℝ) (BK BcK BL BcL : Set (Fin 2 → ℝ)) (JK JL : (Fin 2 → ℝ) → ℂ) (CJK CJL Cm : ℝ)
      (M : Mom P.d → Mom P.d → ℂ),
      BK ⊆ cell qK → BK ⊆ closure (interior BK) → BcK ⊆ BK → BcK ⊆ closure (interior BcK) → ContinuousOn JK BcK →
      BL ⊆ cell qL → BL ⊆ closure (interior BL) → BcL ⊆ BL → BcL ⊆ closure (interior BcL) → ContinuousOn JL BcL →
      XNorm00Restr (V := Unit) (1 - P.η) BK Set.univ (fun ts _ => JK ts) < ENNReal.ofReal CJK →
      XNorm00Restr (V := Unit) (1 - P.η) BL Set.univ (fun ts _ => JL ts) < ENNReal.ofReal CJL →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (M r)) ≤ ENNReal.ofReal Cm →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ BcK ∧ (fun i => slotVal D τ tt (sL i)) ∈ BcL ∧
        ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
          X τ tt r k = fac τ r * (JK ![slotVal D τ tt (sK 0), slotVal D τ tt (sK 1)] * M r k *
            JL ![slotVal D τ tt (sL 0), slotVal D τ tt (sL 1)])) →
      PieceRep (P := P) hI vp vb ε fac X (C * ENNReal.ofReal CJK * ENNReal.ofReal Cm) (C * ENNReal.ofReal CJL * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := sepRowWS G
  refine ⟨C, hC, fun D hI vp vb ε fac sK sL qK qL BK BcK BL BcL JK JL CJK CJL Cm M h1 h2 h1' h2' h3 g1 g2 g1' g2' g3 hJK hJL hM Bx X hX => ?_⟩
  obtain ⟨RK, hKW, hKs, hKb, hKae⟩ := h D hI (Sum.inl vp) sK qK BK BcK JK CJK Cm M h1 h2 h1' h2' h3 hJK hM
    (fun w hw => absurd hw (by simp))
  obtain ⟨RL, hLW, hLs, hLb, hLae⟩ := h D hI (Sum.inr vb) sL qL BL BcL JL CJL 1 (fun _ _ => 1) g1 g2 g1' g2' g3 hJL
    (snorm_one_le' (d := P.d) D.wN) (fun _ _ _ _ _ => rfl)
  refine ⟨RK, RL, hKae, hLae, hKb, hLb, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ hd
  obtain ⟨m1, m2, hid⟩ := hτ hd
  intro r k hr
  have e1 : ![RK.clk τ tt 0, RK.clk τ tt 1] = fun i => slotVal D τ tt (sK i) := by
    funext i; fin_cases i <;> simp [RowData.clk, hKs, slotVal]
  have e2 : ![RL.clk τ tt 0, RL.clk τ tt 1] = fun i => slotVal D τ tt (sL i) := by
    funext i; fin_cases i <;> simp [RowData.clk, hLs, slotVal]
  rw [hKW _ r k (e1 ▸ m1), hLW _ r (k + ε • r) (e2 ▸ m2), clk_sep RK sK hKs, clk_sep RL sL hLs, hid r k hr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]

/-- **The joint representation** (kind-2 pieces), slot-general. -/
theorem pieceRep_joint (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (vp vb : D.S.VIdx) (ε : ℝ)
      (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ)
      (sK : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (sL : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      (qK : Fin 3 → ℝ) (qL : Fin 2 → ℝ) (B2 Bc2 : Set (Fin 2 → ℝ)) (B3 Bc3 : Set (Fin 3 → ℝ)) (BL BcL : Set (Fin 2 → ℝ))
      (JK JL : (Fin 2 → ℝ) → ℂ) (CJK CJL Cm : ℝ) (M : Mom P.d → Mom P.d → ℂ),
      (∀ τ r, fac τ r = ((|slotVal D τ (fun _ => 0) (sK 0) - slotVal D τ (fun _ => 0) (sK 1)| ^ (1 - 3 * P.η) : ℝ) : ℂ)) →
      B3 ⊆ cell qK → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) → ContinuousOn JK Bc2 →
      (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      BL ⊆ cell qL → BL ⊆ closure (interior BL) → BcL ⊆ BL → BcL ⊆ closure (interior BcL) → ContinuousOn JL BcL →
      XNorm00Restr (V := Unit) (1 - P.η) B2 Set.univ (fun ts _ => JK ts) < ENNReal.ofReal CJK →
      XNorm00Restr (V := Unit) (1 - P.η) BL Set.univ (fun ts _ => JL ts) < ENNReal.ofReal CJL →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (M r)) ≤ ENNReal.ofReal Cm →
      ∀ (Bx : Set (Fin 3 → ℝ)) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (fun i => slotVal D τ tt (sK i)) ∈ Bc3 ∧ (fun i => slotVal D τ tt (sL i)) ∈ BcL ∧
        ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
          X τ tt r k = fac τ r * (((((|slotVal D τ tt (sK 0) - slotVal D τ tt (sK 1)| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) *
                (JK ![slotVal D τ tt (sK 0), slotVal D τ tt (sK 2)] - JK ![slotVal D τ tt (sK 1), slotVal D τ tt (sK 2)])) * M r k) *
              JL ![slotVal D τ tt (sL 0), slotVal D τ tt (sL 1)])) →
      PieceRep (P := P) hI vp vb ε fac X (C * ENNReal.ofReal CJK * ENNReal.ofReal Cm) (C' * ENNReal.ofReal CJL * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := jointRowWS G Rb
  obtain ⟨C', hC', h'⟩ := sepRowWS G
  refine ⟨C, C', hC, hC', fun D hI vp vb ε fac sK sL qK qL B2 Bc2 B3 Bc3 BL BcL JK JL CJK CJL Cm M _ h1 h2 h3 h4 h5 h6 h7 h8 h9 g1 g2 g3 g4 g5 hJK hJL hM Bx X hX => ?_⟩
  obtain ⟨RK, hKW, hKs, hKb, hKae⟩ := h D hI vp sK qK B2 Bc2 B3 Bc3 JK CJK Cm M h1 h2 h3 h4 h5 h6 h7 h8 h9 hJK hM
  obtain ⟨RL, hLW, hLs, hLb, hLae⟩ := h' D hI (Sum.inr vb) sL qL BL BcL JL CJL 1 (fun _ _ => 1) g1 g2 g3 g4 g5 hJL
    (snorm_one_le' (d := P.d) D.wN) (fun _ _ _ _ _ => rfl)
  refine ⟨RK, RL, hKae, hLae, hKb, hLb, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ hd
  obtain ⟨m1, m2, hid⟩ := hτ hd
  intro r k hr
  have e2 : ![RL.clk τ tt 0, RL.clk τ tt 1] = fun i => slotVal D τ tt (sL i) := by
    funext i; fin_cases i <;> simp [RowData.clk, hLs, slotVal]
  have e1 : RK.clk τ tt = fun i => slotVal D τ tt (sK i) := by
    funext i; simp [RowData.clk, hKs]
  rw [hKW _ r k (e1 ▸ m1), hLW _ r (k + ε • r) (e2 ▸ m2), clk_joint RK sK hKs, clk_sep RL sL hLs, hid r k hr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one]

end WaveTurbulence.VineEstS5C.P4.W2
