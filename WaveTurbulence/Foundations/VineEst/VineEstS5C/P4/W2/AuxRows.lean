/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceRem
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.OfModes
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxAe

/-! # P4-W2 AUX (b): slot-general row lemmas (exterior clocks allowed)

Versions of `sepRowW`, `jointRowW`, `remRowW` whose clock slots `s : Fin k → Slot D` are arbitrary (`Sum.inr` = exterior times, as `natSlot` can
return; type I vines have exterior `s₁`, `t₁`).  The a.e. step of the TVar versions is replaced by the CONTINUITY of the time factor on a set
`Bc` (`hasSum_of_ae_contOn`): the slot values must lie in `Bc`, `J` is continuous on `Bc`, `Bc ⊆ B ∩ closure (interior Bc)`.  No injectivity
of the slots is needed.  The remainder row is `remRowS` (continuous `f`), re-exported as `remRowWS`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

variable {A : ℝ} {P : WTParams}

theorem summable_norm_of_tsum_enorm_ne_top {ι : Type*} {E : Type*} [NormedAddCommGroup E] {f : ι → E}
    (h : ∑' i, ‖f i‖ₑ ≠ ⊤) : Summable fun i => ‖f i‖ := by
  have := ENNReal.summable_toReal h
  simpa using this

theorem summable_of_bracket {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {h : (Fin r → ℤ) → ℂ} {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hs : ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ‖h m‖ₑ ≤ b) : Summable fun m => ‖h m‖ := by
  refine summable_norm_of_tsum_enorm_ne_top (ne_top_of_le_ne_top hb ((ENNReal.tsum_le_tsum fun m => ?_).trans hs))
  exact le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ _)

theorem cont_vec2 (i j : Fin 3) : Continuous fun τ : Fin 3 → ℝ => ![τ i, τ j] := by
  refine continuous_pi fun l => ?_
  fin_cases l <;> simp [continuous_apply]

/-- **A separated row with arbitrary slots.** -/
theorem sepRowWS (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (ρ : Row D)
      (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 2 → ℝ) (B2 Bc : Set (Fin 2 → ℝ))
      (J : (Fin 2 → ℝ) → ℂ) (CJ Cm : ℝ) (M : Mom P.d → Mom P.d → ℂ),
      B2 ⊆ cell q → B2 ⊆ closure (interior B2) → Bc ⊆ B2 → Bc ⊆ closure (interior Bc) → ContinuousOn J Bc →
      XNorm00Restr (V := Unit) (1 - P.η) B2 Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D ρ) (M r)) ≤ ENNReal.ofReal Cm →
      (∀ w, ρ = Sum.inr w → ∀ r r' k : Mom P.d, M r k = M r' k) →
      ∃ R : RowData D (6 * P.η ^ 6) ρ,
        (∀ cl r k, ![cl 0, cl 1] ∈ Bc → R.W cl r k = J ![cl 0, cl 1] * M r k) ∧
        (∀ i, R.slot i = ![s 0, s 1, s 0] i) ∧
        R.b ≤ C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by have := G.hη0; positivity
  obtain ⟨C, hC, hF⟩ := scalar_modes (θ := 6 * P.η ^ 6) (θ' := 1 - P.η) hθ0 G.hθ' 2
  refine ⟨C, hC, fun D hI ρ s q B2 Bc J CJ Cm M hc hi hBc hBci hJc hJ hM hind => ?_⟩
  obtain ⟨ĥ, hae, hs⟩ := hF q B2 J (ENNReal.ofReal CJ) hc hi hJ
  have hbfin : C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hsum : Summable fun m => ‖ĥ m‖ :=
    summable_of_bracket hθ0 (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hs
  have hall := hasSum_of_ae_contOn hsum hBc hBci hJc hae
  have hfs : coefBound (6 * P.η ^ 6) D.wN (rowOrder D ρ) (sepCoef (embed2 ĥ) M) ≤
      C * ENNReal.ofReal CJ * ENNReal.ofReal Cm := by
    refine (coefBound_sep_le _ _ _ _ _).trans ?_
    rw [tsum_embed2]
    exact mul_le_mul' hs hM
  exact ⟨RowData.ofModes (θ := 6 * P.η ^ 6) ρ ![s 0, s 1, s 0] (sepCoef (embed2 ĥ) M) (C * ENNReal.ofReal CJ * ENNReal.ofReal Cm)
    hbfin hfs (fun w hw m r r' k => by unfold sepCoef; rw [hind w hw r r' k]),
    fun cl r k hcl => RowData.ofModes_W (hasSum_sepCoef (hasSum_embed2 ĥ _ (hall _ hcl)) M r k), fun _ => rfl, le_rfl,
    RowData.ofModes_ae hθ0 hI ρ _ _ _ _ _ _⟩

/-- **The joint three-clock row of clause (c) with arbitrary slots.** -/
theorem jointRowWS (G : AmbP A P) (Rb : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx)
      (s : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 3 → ℝ) (B2 Bc2 : Set (Fin 2 → ℝ))
      (B3 Bc3 : Set (Fin 3 → ℝ)) (J : (Fin 2 → ℝ) → ℂ) (CJ Cm : ℝ) (M : Mom P.d → Mom P.d → ℂ),
      B3 ⊆ cell q → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      Bc3 ⊆ B3 → Bc3 ⊆ closure (interior Bc3) → (∀ τ ∈ Bc3, τ 0 ≠ τ 1) →
      ContinuousOn J Bc2 → (∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ Bc2 ∧ ![τ 1, τ 2] ∈ Bc2) →
      XNorm00Restr (V := Unit) (1 - P.η) B2 Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r)) ≤ ENNReal.ofReal Cm →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀),
        (∀ cl r k, cl ∈ Bc3 → R.W cl r k = ((((|cl 0 - cl 1| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) * (J ![cl 0, cl 2] - J ![cl 1, cl 2])) * M r k)) ∧
        (∀ i, R.slot i = s i) ∧
        R.b ≤ C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by have := G.hη0; positivity
  obtain ⟨C, hC, hF⟩ := jointTime_modes G.hη0 G.hη4 hθ0 G.hθη Rb
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

end WaveTurbulence.VineEstS5C.P4.W2
