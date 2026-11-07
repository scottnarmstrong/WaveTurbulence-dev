/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.TimeDiff2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Joint

/-! # W2-KIND2 (rows): the joint three-clock row from an `𝔛^{1-2η}` time factor

`jointTime_modes2`, `jointRowWS2`, `pieceRep_joint2`: the versions of `jointTime_modes` (VineEstS5A), `jointRowWS` (AuxRows) and `pieceRep_joint`
(PieceRep) whose time factor `J` is bounded in `𝔛^{1-2η}(B2)` instead of `𝔛^{1-η}(B2)` (Lemma B of `K2.TimeDiff2`).  The hypotheses
on the boxes are unchanged: `B3 ⊆ cell q` is the three-clock box, `B2` is an arbitrary set containing both clock pairs, so the cross-window
dispatch applies with `B3 = Bc3 = crossBox`.  An `𝔛^{1-η}` bound implies an `𝔛^{1-2η}` bound (`XNorm00Restr_mono_theta`), so this single version
serves the far and the adjacent case.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W2
  WaveTurbulence.Fourier WaveTurbulence.NormBridgeScratch MeasureTheory Set
open WaveTurbulence.VineEstS5A
open scoped ENNReal

variable {A : ℝ} {P : WTParams}

/-- `2 · (6 η⁶) ≤ η` for `0 < η < 1/4`. -/
theorem two_theta_le_of {η : ℝ} (h0 : 0 < η) (h4 : η < 1 / 4) : 2 * (6 * η ^ 6) ≤ η := by
  have h5 : η ^ 5 ≤ (1 / 4) ^ 5 := pow_le_pow_left₀ h0.le h4.le 5
  have : η ^ 6 = η * η ^ 5 := by ring
  nlinarith [mul_le_mul_of_nonneg_left h5 h0.le]

theorem two_theta_le (G : AmbP A P) : 2 * (6 * P.η ^ 6) ≤ P.η := two_theta_le_of G.hη0 G.hη4

/-- **The joint time factor.** -/
theorem jointTime_modes2 {η θ : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) (hθ0 : 0 ≤ θ) (hθη : 2 * θ ≤ η) (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (J : (Fin 2 → ℝ) → ℂ) (B2 : Set (Fin 2 → ℝ)) (B3 : Set (Fin 3 → ℝ))
      (q : Fin 3 → ℝ) (β : ℝ≥0∞),
      β ≠ ⊤ → B3 ⊆ cell q → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ R) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      XNorm00Restr (V := Unit) (1 - 2 * η) B2 Set.univ (fun ts _ => J ts) < β →
      ∃ ĥ : (Fin 3 → ℤ) → ℂ,
        (∀ᵐ τ : Fin 3 → ℝ, τ ∈ B3 → HasSum (fun m : Fin 3 → ℤ => ĥ m * fsPhase m τ)
          (((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (J ![τ 0, τ 2] - J ![τ 1, τ 2]))) ∧
        ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * ‖ĥ m‖ₑ ≤ C * β := by
  obtain ⟨Ctd, hCtd, hTd⟩ := VineEstS4c.TimeDiff.timeDiff_extraction2 (V := Unit) hη0 hη4 hθ0 hθη R
  obtain ⟨Cfs, hCfs, hFs⟩ := hcoef_sum_le (r := 3) hθ0
  refine ⟨Cfs * (Ctd + 1), ENNReal.mul_ne_top hCfs (ENNReal.add_ne_top.2 ⟨hCtd, ENNReal.one_ne_top⟩),
    fun J B2 B3 q β hβ hcell hint hR hB hJ => ?_⟩
  have hX := hTd (fun ts _ => J ts) B2 B3 Set.univ hR hB
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hJ
  have hlt : XNorm00Restr θ B3 Set.univ (fun τ (v : Unit) => ((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) *
      (J ![τ 0, τ 2] - J ![τ 1, τ 2])) < (Ctd + 1) * β := by
    refine lt_of_le_of_lt hX ?_
    calc Ctd * XNorm00Restr (1 - 2 * η) B2 Set.univ (fun ts (_ : Unit) => J ts) ≤ Ctd * β :=
          mul_le_mul_right hJ.le _
      _ < (Ctd + 1) * β := by
          rw [mul_comm Ctd β, mul_comm (Ctd + 1) β]
          exact (ENNReal.mul_lt_mul_iff_right hβ0.ne' hβ).2 (ENNReal.lt_add_right hCtd one_ne_zero)
  unfold XNorm00Restr at hlt
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hGB, hGn⟩ := iInf_lt_iff.1 hG
  set g : (Fin 3 → ℝ) → ℂ := fun t => G t () with hg
  have hgn : timeFourierNorm θ g < ⊤ := by
    have : timeFourierNorm θ g = XNorm00 θ G := (XNorm00_unit_eq_timeFourierNorm θ g).symm
    rw [this]; exact lt_of_lt_of_le hGn le_top
  refine ⟨hcoef q g, ?_, ?_⟩
  · filter_upwards [scalar_fs_hasSum_ae hθ0 q hcell hint hgn] with τ hτ htB
    have := hτ htB
    simp only [hg] at this
    rwa [hGB τ htB () (Set.mem_univ _)] at this
  · refine (hFs q g).trans ?_
    have h1 : timeFourierNorm θ g = XNorm00 θ G := (XNorm00_unit_eq_timeFourierNorm θ g).symm
    rw [h1]
    rw [mul_assoc]; exact mul_le_mul_right hGn.le _


/-- **The joint three-clock row of clause (c) with arbitrary slots.** -/
theorem jointRowWS2 (G : AmbP A P) (Rb : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx)
      (s : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 3 → ℝ) (B2 Bc2 : Set (Fin 2 → ℝ))
      (B3 Bc3 : Set (Fin 3 → ℝ)) (J : (Fin 2 → ℝ) → ℂ) (CJ Cm : ℝ) (M : Mom P.d → Mom P.d → ℂ),
      B3 ⊆ cell q → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      ContinuousOn J Bc2 → (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r)) ≤ ENNReal.ofReal Cm →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀),
        (∀ cl r k, cl ∈ Bc3 → R.W cl r k = ((((|cl 0 - cl 1| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) * (J ![cl 0, cl 2] - J ![cl 1, cl 2])) * M r k)) ∧
        (∀ i, R.slot i = s i) ∧
        R.b ≤ C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by have := G.hη0; positivity
  obtain ⟨C, hC, hF⟩ := jointTime_modes2 G.hη0 G.hη4 hθ0 (two_theta_le G) Rb
  refine ⟨C, hC, fun D hI w₀ s q B2 Bc2 B3 Bc3 J CJ Cm M hc hi hR hB hBc3 hBci3 hne hJc hBc2 hJ hM => ?_⟩
  obtain ⟨ĥ, hae, hs⟩ := hF J B2 B3 q (ENNReal.ofReal CJ) ENNReal.ofReal_ne_top hc hi hR hB hJ
  have hbfin : C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hsum : Summable fun m => ‖ĥ m‖ :=
    summable_of_bracket hθ0 (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hs
  have hgc : ContinuousOn (fun τ : Fin 3 → ℝ => (((|τ 0 - τ 1| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) *
      (J ![τ 0, τ 2] - J ![τ 1, τ 2]))) Bc3 := by
    refine ContinuousOn.mul ?_ (ContinuousOn.sub ?_ ?_)
    · refine Complex.continuous_ofReal.comp_continuousOn fun τ hτ => ?_
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.rpow_const ?_ (Or.inl ?_)
      · exact ((continuous_apply 0).sub (continuous_apply 1)).abs.continuousAt
      · simpa [sub_eq_zero] using hne τ hτ
    · exact hJc.comp (cont_vec2 0 2).continuousOn fun τ hτ => (hBc2 τ hτ).1
    · exact hJc.comp (cont_vec2 1 2).continuousOn fun τ hτ => (hBc2 τ hτ).2
  have hall := hasSum_of_ae_contOn hsum hBc3 hBci3 hgc hae
  have hfs : coefBound (6 * P.η ^ 6) D.wN (rowOrder D (Sum.inl w₀)) (sepCoef ĥ M) ≤
      C * ENNReal.ofReal CJ * ENNReal.ofReal Cm :=
    (coefBound_sep_le _ _ _ _ _).trans (mul_le_mul' hs hM)
  exact ⟨RowData.ofModes (θ := 6 * P.η ^ 6) (Sum.inl w₀) s (sepCoef ĥ M) (C * ENNReal.ofReal CJ * ENNReal.ofReal Cm)
    hbfin hfs (fun w hw => absurd hw (by simp)),
    fun cl r k hcl => RowData.ofModes_W (hasSum_sepCoef (hall _ hcl) M r k), fun _ => rfl, le_rfl,
    RowData.ofModes_ae hθ0 hI (Sum.inl w₀) _ _ _ _ _ _⟩


/-- **The joint representation** (kind-2 pieces), slot-general. -/
theorem pieceRep_joint2 (G : AmbP A P) (Rb : ℝ) :
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
      XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => JK ts) < ENNReal.ofReal CJK →
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
  obtain ⟨C, hC, h⟩ := jointRowWS2 G Rb
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


end WaveTurbulence.VineEstS5C.P4.W2.K2
