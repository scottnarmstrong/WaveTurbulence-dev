/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.Rows2

/-! # W2-KIND2 (far case): the cross-window joint row `crossJointRow` (promoted from research-f11/F11Probe.lean)

`jointRowWS` on the cross box `s₁ ∈ (qh, qh+1)`, `t₁ ∈ (q4, q4+1)`, `t₀ ∈ (q2, q2+1)` with `q4 + 1 ≤ qh`: the only input is ONE time factor `J` bounded in `𝔛^{1-η}(B2)` on a set
`B2` containing both windows (`crossJointRow`); `crossJointRow2` is the same with the `𝔛^{1-2η}` bound (Lemma B).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W2
  MeasureTheory
open scoped ENNReal

variable {A : ℝ} {P : WTParams}

/-- The open cross box of the clocks `(s₁, t₁, t₀)` in case A with `qh ≠ q4`. -/
def crossBox (q2 q4 qh : ℝ) : Set (Fin 3 → ℝ) :=
  {τ | τ 0 ∈ Set.Ioo qh (qh + 1) ∧ τ 1 ∈ Set.Ioo q4 (q4 + 1) ∧ τ 2 ∈ Set.Ioo q2 (q2 + 1)}

theorem crossBox_isOpen (q2 q4 qh : ℝ) : IsOpen (crossBox q2 q4 qh) :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter ((isOpen_Ioo.preimage (continuous_apply 1)).inter
    (isOpen_Ioo.preimage (continuous_apply 2)))

theorem crossBox_sub_cell (q2 q4 qh : ℝ) : crossBox q2 q4 qh ⊆ cell ![qh, q4, q2] := by
  intro τ hτ i
  fin_cases i
  · exact ⟨hτ.1.1.le, hτ.1.2.le⟩
  · exact ⟨hτ.2.1.1.le, hτ.2.1.2.le⟩
  · exact ⟨hτ.2.2.1.le, hτ.2.2.2.le⟩

theorem crossBox_ne {q2 q4 qh : ℝ} (hgap : q4 + 1 ≤ qh) : ∀ τ ∈ crossBox q2 q4 qh, τ 0 ≠ τ 1 := by
  intro τ hτ h
  have h1 := hτ.1.1
  have h2 := hτ.2.1.2
  rw [h] at h1
  linarith

theorem crossBox_norm {q2 q4 qh Rb : ℝ} (hq4 : 0 ≤ q4) (hq2 : 0 ≤ q2) (hgap : q4 + 1 ≤ qh)
    (hRb : max (qh + 1) (q2 + 1) ≤ Rb) : ∀ τ ∈ crossBox q2 q4 qh, ‖τ‖ ≤ Rb := by
  intro τ hτ
  have hm1 := le_max_left (qh + 1) (q2 + 1)
  have hm2 := le_max_right (qh + 1) (q2 + 1)
  have hR0 : (0 : ℝ) ≤ Rb := by linarith
  refine (pi_norm_le_iff_of_nonneg hR0).2 fun i => ?_
  fin_cases i
  · show ‖τ 0‖ ≤ Rb
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hτ.1.1])]; linarith [hτ.1.2]
  · show ‖τ 1‖ ≤ Rb
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hτ.2.1.1])]; linarith [hτ.2.1.2]
  · show ‖τ 2‖ ≤ Rb
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hτ.2.2.1])]; linarith [hτ.2.2.2]

/-- **The cross-window joint row of clause (c).**  Given ONE time factor `J` with an `𝔛^{1-η}` bound on a set `B2` that contains
both windows, the divided difference across the two windows is a `RowData` on the cross box (the slots `s` are arbitrary). -/
theorem crossJointRow (G : AmbP A P) (Rb : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx)
      (s : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) {q2 q4 qh : ℝ} (_hq4 : 0 ≤ q4) (_hq2 : 0 ≤ q2)
      (_hgap : q4 + 1 ≤ qh) (_hRb : max (qh + 1) (q2 + 1) ≤ Rb)
      (B2 : Set (Fin 2 → ℝ)) (J : (Fin 2 → ℝ) → ℂ) (CJ Cm : ℝ) (M : Mom P.d → Mom P.d → ℂ),
      (∀ τ ∈ crossBox q2 q4 qh, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      ContinuousOn J B2 →
      XNorm00Restr (V := Unit) (1 - P.η) B2 Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r)) ≤ ENNReal.ofReal Cm →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀),
        (∀ cl r k, cl ∈ crossBox q2 q4 qh → R.W cl r k =
          ((((|cl 0 - cl 1| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) * (J ![cl 0, cl 2] - J ![cl 1, cl 2])) * M r k)) ∧
        (∀ i, R.slot i = s i) ∧ R.b ≤ C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ∧ R.Ae hI := by
  obtain ⟨C, hC, h⟩ := jointRowWS G Rb
  refine ⟨C, hC, fun D hI w₀ s q2 q4 qh hq4 hq2 hgap hRb B2 J CJ Cm M hB hJc hJ hM => ?_⟩
  have hop := crossBox_isOpen q2 q4 qh
  have hcl : crossBox q2 q4 qh ⊆ closure (interior (crossBox q2 q4 qh)) := by
    rw [hop.interior_eq]; exact subset_closure
  exact h D hI w₀ s ![qh, q4, q2] B2 B2 (crossBox q2 q4 qh) (crossBox q2 q4 qh) J CJ Cm M
    (crossBox_sub_cell q2 q4 qh) hcl (crossBox_norm hq4 hq2 hgap hRb) hB subset_rfl hcl (crossBox_ne hgap) hJc hB hJ hM


/-- The `𝔛^{1-2η}` version (Lemma B). -/
theorem crossJointRow2 (G : AmbP A P) (Rb : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx)
      (s : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) {q2 q4 qh : ℝ} (_hq4 : 0 ≤ q4) (_hq2 : 0 ≤ q2)
      (_hgap : q4 + 1 ≤ qh) (_hRb : max (qh + 1) (q2 + 1) ≤ Rb)
      (B2 : Set (Fin 2 → ℝ)) (J : (Fin 2 → ℝ) → ℂ) (CJ Cm : ℝ) (M : Mom P.d → Mom P.d → ℂ),
      (∀ τ ∈ crossBox q2 q4 qh, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      ContinuousOn J B2 →
      XNorm00Restr (V := Unit) (1 - 2 * P.η) B2 Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ →
      (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r)) ≤ ENNReal.ofReal Cm →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀),
        (∀ cl r k, cl ∈ crossBox q2 q4 qh → R.W cl r k =
          ((((|cl 0 - cl 1| ^ (-(1 - 3 * P.η)) : ℝ) : ℂ) * (J ![cl 0, cl 2] - J ![cl 1, cl 2])) * M r k)) ∧
        (∀ i, R.slot i = s i) ∧ R.b ≤ C * ENNReal.ofReal CJ * ENNReal.ofReal Cm ∧ R.Ae hI := by
  obtain ⟨C, hC, h⟩ := jointRowWS2 G Rb
  refine ⟨C, hC, fun D hI w₀ s q2 q4 qh hq4 hq2 hgap hRb B2 J CJ Cm M hB hJc hJ hM => ?_⟩
  have hop := crossBox_isOpen q2 q4 qh
  have hcl : crossBox q2 q4 qh ⊆ closure (interior (crossBox q2 q4 qh)) := by
    rw [hop.interior_eq]; exact subset_closure
  exact h D hI w₀ s ![qh, q4, q2] B2 B2 (crossBox q2 q4 qh) (crossBox q2 q4 qh) J CJ Cm M
    (crossBox_sub_cell q2 q4 qh) hcl (crossBox_norm hq4 hq2 hgap hRb) hB subset_rfl hcl (crossBox_ne hgap) hJc hB hJ hM

end WaveTurbulence.VineEstS5C.P4.W2.K2
