/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.PinData

/-! # D6a PROT-PTW: the protected paired tree, pointwise (normalized leaves, fixed parameters)

For a paired tree with normalized leaf profiles, the D6 kernel (terminal pin, at most one selected annular time, both
filter layers, star weights, dagger) is bounded at every pair of clocks and every output by
`∏ c_ω · 2 (C δ)^n L^{-(γ₁-2η) g} L^{3r} M₂^{-a}`, given D5a's one-link bounds (`hdec`) and main's cell cover (`hcov`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links
open WaveTurbulence.Flower.FiltSrc WaveTurbulence.Flower.FiltProd WaveTurbulence.Flower.FiltGate

variable {d : ℕ}

/-- The tree constant: cells, link filters, link masses. -/
def treeConst (d : ℕ) (C₀ Ccov : ℝ) : ℝ :=
  Ccov * max (leafLocalizationConstant d (40 * d)) 0 ^ 2 * halfCellFourierConstant d ^ 2 *
    (filtMomentConst ^ 4 * max C₀ ((5 : ℝ) ^ (2 * d)))

theorem treeConst_nonneg (d : ℕ) {C₀ Ccov : ℝ} (hCcov : 0 ≤ Ccov) : 0 ≤ treeConst d C₀ Ccov := by
  unfold treeConst
  have h5 : (0 : ℝ) ≤ max C₀ ((5 : ℝ) ^ (2 * d)) := le_max_of_le_right (by positivity)
  have := filtMomentConst_pow_pos
  positivity

/-- Link-by-link assembly of the final bound. -/
theorem assemble {n : ℕ} (T : Fin n → ℝ≥0∞) (c b : ℝ) (hb : 0 ≤ b) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (P : Fin n → Prop) [DecidablePred P] {L y : ℝ} (hL : 0 < L)
    (hper : ∀ i, ENNReal.ofReal (c ^ 2) * T i ≤ ENNReal.ofReal (b * (ρ i * (if P i then L ^ (-y) else 1))))
    {f Fm Cm A : ℝ≥0∞} (hf : f ≤ 2) (hFm : Fm ≤ A) {Cc : ℝ} (hCc : 0 ≤ Cc) (hCm : Cm ≤ ENNReal.ofReal (Cc ^ n))
    {R : ℝ} (hR : ∏ i, ρ i ≤ R) :
    ENNReal.ofReal (c ^ (2 * n)) * (f * (Fm * Cm * ∏ i, T i)) ≤
      A * ENNReal.ofReal (2 * (Cc * b) ^ n * L ^ (-y * ((Finset.univ.filter P).card : ℝ)) * R) := by
  have hw : ∀ i, 0 ≤ ρ i * (if P i then L ^ (-y) else 1) := fun i =>
    mul_nonneg (hρ i) (by split_ifs <;> positivity)
  have hlp := link_product_le (c ^ 2) b (sq_nonneg c) hb T _ hw hper
  rw [prod_incoh_weight hL y P ρ, ← pow_mul] at hlp
  have hLy : 0 ≤ L ^ (-y * ((Finset.univ.filter P).card : ℝ)) := Real.rpow_nonneg hL.le _
  have hρp : 0 ≤ ∏ i, ρ i := Finset.prod_nonneg fun i _ => hρ i
  calc ENNReal.ofReal (c ^ (2 * n)) * (f * (Fm * Cm * ∏ i, T i)) =
      f * Fm * Cm * (ENNReal.ofReal (c ^ (2 * n)) * ∏ i, T i) := by ring
    _ ≤ 2 * A * ENNReal.ofReal (Cc ^ n) * ENNReal.ofReal (b ^ n * ((∏ i, ρ i) *
        L ^ (-y * ((Finset.univ.filter P).card : ℝ)))) := by gcongr
    _ ≤ 2 * A * ENNReal.ofReal (Cc ^ n) * ENNReal.ofReal (b ^ n * (R *
        L ^ (-y * ((Finset.univ.filter P).card : ℝ)))) := by gcongr
    _ = A * ENNReal.ofReal (2 * (Cc * b) ^ n * L ^ (-y * ((Finset.univ.filter P).card : ℝ)) * R) := by
        rw [mul_comm (2 : ℝ≥0∞) A, mul_assoc A, mul_assoc A, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [mul_pow]; ring

theorem star_mass_le {n : ℕ} {LG : LayeredGarden 1} (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (cω : GNode LG.garden.tree → ℝ)
    (hω : ∀ a ∈ S, StarPresented (30 * d) (ω a) (cω a)) (row : GNode LG.garden.tree → (Fin n × Fin 2) → ℤ)
    (k : Mom d) :
    ENNReal.ofReal ((starRootMeasure (30 * d) S ω cω hω row).at k).mass ≤ ∏ a ∈ S, ENNReal.ofReal (cω a) := by
  refine le_trans ?_ (starRootMeasure_momentMass_le (30 * d) S ω cω hω row)
  rw [RootMeasure.at_mass, SpatialMeasure.mass,
    ofReal_integral_norm_eq_lintegral_enorm (starRootMeasure (30 * d) S ω cω hω row).base.amplitude_integrable,
    RootMeasure.momentMass]
  apply lintegral_mono
  intro a
  have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + ‖(starRootMeasure (30 * d) S ω cω hω row).root a‖) ^ (30 * d)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith [norm_nonneg ((starRootMeasure (30 * d) S ω cω hω
      row).root a)]))
  calc ‖(starRootMeasure (30 * d) S ω cω hω row).base.amplitude a‖ₑ =
      1 * ‖(starRootMeasure (30 * d) S ω cω hω row).base.amplitude a‖ₑ := (one_mul _).symm
    _ ≤ _ := mul_le_mul' this le_rfl

theorem cellMass_le (n : ℕ) {Ccov : ℝ} (hCcov : 0 ≤ Ccov) :
    cellMass d n (2 * n) (40 * d) Ccov 1 ≤ ENNReal.ofReal ((Ccov * max (leafLocalizationConstant d (40 * d)) 0 ^ 2 *
      halfCellFourierConstant d ^ 2) ^ n) := by
  have hΛ : 0 ≤ max (leafLocalizationConstant d (40 * d)) 0 := le_max_right _ _
  have hh := (halfCellFourierConstant_pos d).le
  calc cellMass d n (2 * n) (40 * d) Ccov 1 ≤ ENNReal.ofReal (Ccov ^ n) *
        (ENNReal.ofReal (max (leafLocalizationConstant d (40 * d)) 0) ^ (2 * n) *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) := by
        unfold cellMass
        gcongr
        rw [mul_one]; exact le_max_left _ _
    _ = _ := by
        rw [← ENNReal.ofReal_pow hΛ, ← ENNReal.ofReal_pow hh, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end WaveTurbulence.Flower.ProtPtw
