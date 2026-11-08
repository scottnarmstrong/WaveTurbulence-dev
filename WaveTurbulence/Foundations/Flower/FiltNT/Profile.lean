/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltNT.Pole

/-! # FILT-NT: the filtered profile `∏_{j∈J} g_{S_j}(Ω_j) · Ψ₁(Ω[Jᶜ])`, its Fourier representation and weighted bound

`g_S = χ_∞(u)/u · χ₀(u/S)` is continuous, compactly supported (`|u| ≤ S`) and has an integrable Fourier transform
(`filtPole_bound`), so Fourier inversion holds with no truncation. Main's `ApproxNT.isFourierRep_filtProf` and
`norm_filtHat_mul_le` carry over verbatim with `m̂_K` replaced by `ĝ_S`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset WithLp WaveTurbulence.ApproxNT
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.Flower.FiltNT

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `ĝ_S`. -/
def ghat (S : ℝ) : ℝ → ℂ := 𝓕 (gS S)

theorem gS_eq_zero_of_small {S u : ℝ} (hu : |u| ≤ 1 / 2) : gS S u = 0 := by
  simp [gS, Fourier.chiInfinity, Fourier.chi0_eq_one hu]

theorem gS_eq_zero_of_large {S u : ℝ} (hS : 0 < S) (hu : S ≤ |u|) : gS S u = 0 := by
  have : 1 ≤ |u / S| := by rw [abs_div, abs_of_pos hS, le_div_iff₀ hS]; linarith
  simp [gS, Fourier.chi0_eq_zero this]

theorem continuous_gS (S : ℝ) : Continuous (gS S) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  by_cases h0 : u₀ = 0
  · subst h0
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hu
    exact (gS_eq_zero_of_small hu.le).symm
  · have h1 : ContinuousAt (fun u : ℝ => Fourier.chiInfinity u / u * Fourier.chi0 (u / S)) u₀ := by
      have hc1 : Continuous Fourier.chiInfinity := by
        unfold Fourier.chiInfinity; exact continuous_const.sub (Fourier.chi0_contDiff (n := 0)).continuous
      have hc2 : Continuous (fun u : ℝ => Fourier.chi0 (u / S)) :=
        (Fourier.chi0_contDiff (n := 0)).continuous.comp (continuous_id.div_const S)
      exact (hc1.continuousAt.div continuousAt_id h0).mul hc2.continuousAt
    exact Complex.continuous_ofReal.continuousAt.comp h1

theorem hasCompactSupport_gS {S : ℝ} (hS : 0 < S) : HasCompactSupport (gS S) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) S) ?_
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h
  exact hu (gS_eq_zero_of_large hS (not_le.mp h).le)

theorem integrable_gS {S : ℝ} (hS : 0 < S) : Integrable (gS S) :=
  (continuous_gS S).integrable_of_hasCompactSupport (hasCompactSupport_gS hS)

theorem integrable_ghat {S : ℝ} (hS : 1 ≤ S) : Integrable (ghat S) := by
  obtain ⟨K, hK0, hK⟩ := filtPole_bound 1 le_rfl
  have hS0 : 0 < S := by linarith
  have hc : Continuous (ghat S) := by
    unfold ghat
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_gS hS0)
  refine (integrable_inv_one_add_sq.const_mul K).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun σ => ?_)
  have h := hK S hS σ
  have hp : 0 < (1 + σ ^ 2) ^ 1 := by positivity
  rw [pow_one] at h hp
  show ‖𝓕 (gS S) σ‖ ≤ K * (1 + σ ^ 2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  exact h

theorem gS_eq_integral {S : ℝ} (hS : 1 ≤ S) (v : ℝ) : gS S v = ∫ τ, ghat S τ * (𝐞 (τ * v) : ℂ) := by
  have hS0 : 0 < S := by linarith
  have h := Continuous.fourierInv_fourier_eq (continuous_gS S) (integrable_gS hS0)
    (integrable_ghat hS)
  have h2 := congrFun h v
  rw [Real.fourierInv_eq] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [ghat, Circle.smul_def, smul_eq_mul]
  rw [mul_comm]
  congr 3
  simp [RCLike.inner_apply, mul_comm]

/-- The filtered profile (same body as ProtDefs' `filtProfile`). -/
def filtProf (J : Finset ι) (S : ι → ℝ) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (Ω : ι → ℝ) : ℂ :=
  (∏ j ∈ J, gS (S j) (Ω j)) * Ψ₁ (toLp 2 (fun i : {j // j ∉ J} => Ω i))

/-- Its Fourier transform. -/
def filtHat (J : Finset ι) (S : ι → ℝ) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (s : ι → ℝ) : ℂ :=
  (∏ j ∈ J, ghat (S j) (s j)) * 𝓕 Ψ₁ (toLp 2 (fun i : {j // j ∉ J} => s i))

/-- The Fourier representation of the filtered profile. -/
theorem isFourierRep_filtProf {d : ℕ} (hd : 1 ≤ d) (J : Finset ι) (S : ι → ℝ) (hS : ∀ j, 1 ≤ S j)
    {Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ} {D : ℕ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ₁)
    (hD : WordDerivL1 Ψ₁ D) (hD0 : ∀ k, 0 ≤ D k) :
    IsFourierRep (filtProf J S Ψ₁) (filtHat J S Ψ₁) := by
  have hrep1 := isFourierRep_of_wordDerivL1 hΨ hD hD0 hd
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J)
  have hmp := measurePreserving_splitJ J
  have hsplit : ∀ s : ι → ℝ, filtHat J S Ψ₁ s =
      (∏ j : {j // j ∈ J}, ghat (S j) ((e s).1 j)) * 𝓕 Ψ₁ (toLp 2 (e s).2) := by
    intro s
    rw [filtHat, ← prod_coe_sort J]
    rfl
  constructor
  · have hG : Integrable (fun a : {j // j ∈ J} → ℝ => ∏ j : {j // j ∈ J}, ghat (S j) (a j))
        (Measure.pi fun _ => volume) :=
      Integrable.fintype_prod (f := fun (j : {j // j ∈ J}) (t : ℝ) => ghat (S j) t)
        fun j => integrable_ghat (hS j)
    have hprod : Integrable (fun z : ({j // j ∈ J} → ℝ) × ({j // j ∉ J} → ℝ) =>
        (∏ j : {j // j ∈ J}, ghat (S j) (z.1 j)) * 𝓕 Ψ₁ (toLp 2 z.2)) :=
      hG.mul_prod hrep1.1
    have h2 := (hmp.integrable_comp_emb e.measurableEmbedding).2 hprod
    refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply]
    rw [hsplit]
  · intro Ω
    have hpt : ∀ p : ({j // j ∈ J} → ℝ) × ({j // j ∉ J} → ℝ),
        filtHat J S Ψ₁ (e.symm p) * ∏ i, (𝐞 (e.symm p i * Ω i) : ℂ) =
        (∏ j : {j // j ∈ J}, ghat (S j) (p.1 j) * (𝐞 (p.1 j * Ω j) : ℂ)) *
          (𝓕 Ψ₁ (toLp 2 p.2) * ∏ i : {j // j ∉ J}, (𝐞 (p.2 i * Ω i) : ℂ)) := by
      intro p
      rw [hsplit, e.apply_symm_apply, ← prod_mul_prod_compl J (fun i => (𝐞 (e.symm p i * Ω i) : ℂ)),
        ← prod_coe_sort J, prod_subtype Jᶜ (p := (· ∉ J)) (fun x => by simp), prod_mul_distrib]
      have h1 : ∀ i : {j // j ∈ J}, e.symm p i = p.1 i := fun i => by
        rw [piSplit_symm_apply]; simp [i.2]
      have h2 : ∀ i : {j // j ∉ J}, e.symm p i = p.2 i := fun i => by
        rw [piSplit_symm_apply]; simp [i.2]
      simp_rw [h1, h2]
      ring
    rw [integral_split_J J]
    symm
    refine (integral_congr_ae (Filter.Eventually.of_forall fun p => hpt p)).trans ?_
    have hpm := integral_prod_mul (μ := (volume : Measure ({j // j ∈ J} → ℝ)))
      (ν := (volume : Measure ({j // j ∉ J} → ℝ)))
      (fun a => ∏ j : {j // j ∈ J}, ghat (S j) (a j) * (𝐞 (a j * Ω j) : ℂ))
      (fun b => 𝓕 Ψ₁ (toLp 2 b) * ∏ i, (𝐞 (b i * Ω i) : ℂ))
    refine hpm.trans ?_
    rw [integral_fintype_prod_volume_eq_prod
      (f := fun (j : {j // j ∈ J}) (t : ℝ) => ghat (S j) t * (𝐞 (t * Ω j) : ℂ)),
      ← hrep1.2, filtProf, ← prod_coe_sort J]
    congr 1
    exact prod_congr rfl fun j _ => (gS_eq_integral (hS j) _).symm

/-- The weighted bound of the filtered profile's Fourier transform. -/
theorem norm_filtHat_mul_le {d : ℕ} (J : Finset ι) (S : ι → ℝ) (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hb : ∀ (j : ι) (s : ℝ), ‖ghat (S j) s‖ * (1 + s ^ 2) ^ d ≤ Kp)
    {Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ} {D : ℕ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ₁)
    (hD : WordDerivL1 Ψ₁ D) (hD0 : ∀ k, 0 ≤ D k) (F : Finset ι) (s : ι → ℝ) :
    ‖filtHat J S Ψ₁ s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤
      Kp ^ J.card * (2 ^ (d * (F.subtype (· ∉ J)).card) *
        ∑ G ∈ (F.subtype (· ∉ J)).powerset, D (G.card * (2 * d))) := by
  have hK : 0 ≤ Kp := hKp
  have hsplitF : ∏ i ∈ F, (1 + s i ^ 2) ^ d =
      (∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d) *
        ∏ i ∈ F.subtype (· ∉ J), (1 + s i ^ 2) ^ d := by
    rw [← prod_filter_mul_prod_filter_not F (· ∈ J)]
    congr 1
    exact (prod_subtype_eq_prod_filter (fun i => (1 + s i ^ 2) ^ d)).symm
  have hJ : (∏ j ∈ J, ‖ghat (S j) (s j)‖) * ∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d ≤
      Kp ^ J.card := by
    have hsub : F.filter (· ∈ J) ⊆ J := fun i hi => (mem_filter.1 hi).2
    have hsd : ∏ j ∈ J, ‖ghat (S j) (s j)‖ = (∏ j ∈ F.filter (· ∈ J), ‖ghat (S j) (s j)‖) *
        ∏ j ∈ J \ F.filter (· ∈ J), ‖ghat (S j) (s j)‖ := by
      rw [mul_comm, prod_sdiff hsub]
    rw [hsd]
    calc (∏ j ∈ F.filter (· ∈ J), ‖ghat (S j) (s j)‖) *
          (∏ j ∈ J \ F.filter (· ∈ J), ‖ghat (S j) (s j)‖) *
          ∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d
        = (∏ j ∈ F.filter (· ∈ J), (‖ghat (S j) (s j)‖ * (1 + s j ^ 2) ^ d)) *
            ∏ j ∈ J \ F.filter (· ∈ J), ‖ghat (S j) (s j)‖ := by
          rw [prod_mul_distrib]; ring
      _ ≤ (∏ _j ∈ F.filter (· ∈ J), Kp) * ∏ _j ∈ J \ F.filter (· ∈ J), Kp := by
          refine mul_le_mul (prod_le_prod₀ (fun j _ => by positivity)
            fun j _ => hb j _) (prod_le_prod₀ (fun j _ => norm_nonneg _)
            fun j _ => ?_) (prod_nonneg fun j _ => norm_nonneg _) (prod_nonneg fun _ _ => hK)
          have := hb j (s j)
          have h1 : (1 : ℝ) ≤ (1 + s j ^ 2) ^ d := one_le_pow₀ (by nlinarith [sq_nonneg (s j)])
          nlinarith [norm_nonneg (ghat (S j) (s j))]
      _ = Kp ^ J.card := by
          rw [prod_const, prod_const, ← pow_add, add_comm, card_sdiff_add_card_eq_card hsub]
  have hΨ1 := norm_fourier_mul_prod_le hΨ hD hD0 d (F.subtype (· ∉ J))
    (toLp 2 (fun i : {j // j ∉ J} => s i))
  rw [filtHat, norm_mul, norm_prod, hsplitF]
  have hX : 0 ≤ ∏ i ∈ F.subtype (· ∉ J), (1 + s i ^ 2) ^ d := prod_nonneg fun _ _ => by positivity
  calc (∏ j ∈ J, ‖ghat (S j) (s j)‖) * ‖𝓕 Ψ₁ (toLp 2 fun i : {j // j ∉ J} => s i)‖ *
        ((∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d) * ∏ i ∈ F.subtype (· ∉ J), (1 + s i ^ 2) ^ d)
      = ((∏ j ∈ J, ‖ghat (S j) (s j)‖) * ∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d) *
          (‖𝓕 Ψ₁ (toLp 2 fun i : {j // j ∉ J} => s i)‖ *
            ∏ i ∈ F.subtype (· ∉ J), (1 + s i ^ 2) ^ d) := by ring
    _ ≤ Kp ^ J.card * (2 ^ (d * (F.subtype (· ∉ J)).card) *
          ∑ G ∈ (F.subtype (· ∉ J)).powerset, D (G.card * (2 * d))) := by
        refine mul_le_mul hJ ?_ (mul_nonneg (norm_nonneg _) hX) (pow_nonneg hK _)
        simpa using hΨ1


end WaveTurbulence.Flower.FiltNT
