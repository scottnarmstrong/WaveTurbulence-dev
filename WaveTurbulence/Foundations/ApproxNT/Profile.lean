/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Kernel
public import WaveTurbulence.Foundations.ApproxNT.PsiOne

/-!
# The truncated profile `∏_{j∈J} m_{K_j}(Ω_j) · Ψ₁(Ω[J^c])` (packet NT6)

DH23 (propertypsi1): `Ψ(Ω) = ∏_{j∈J} χ_∞(Ω_j)/Ω_j · Ψ₁(Ω[J^c])`. On the bounded range where the
cells live we replace `χ_∞(u)/u` by the truncated kernel `m_K` (`Kernel.lean`). The resulting
profile has the Fourier representation `∏_{j∈J} m̂_{K_j}(s_j) · Ψ̂₁(s[J^c])` and the weighted bounds

`|Φ̂(s)| ∏_{i∈F} ⟨sᵢ⟩^{2d} ≤ M^{|J|} 2^{d|F|} ∑_{G ⊆ F∖J} D(2d|G|)`,

uniform in the truncation levels `K_j`.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.ApproxNT

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The truncated profile. -/
@[expose] def truncProfile (J : Finset ι) (Kj : ι → ℕ) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (Ω : ι → ℝ) : ℂ :=
  (∏ j ∈ J, mKer (Kj j) (Ω j)) * Ψ₁ (toLp 2 (fun i : {j // j ∉ J} => Ω i))

/-- Its Fourier transform. -/
@[expose] def truncProfileHat (J : Finset ι) (Kj : ι → ℕ) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (s : ι → ℝ) : ℂ :=
  (∏ j ∈ J, mKerHat (Kj j) (s j)) * 𝓕 Ψ₁ (toLp 2 (fun i : {j // j ∉ J} => s i))

theorem continuous_mKerHat (K : ℕ) : Continuous (mKerHat K) :=
  continuous_finsetSum _ fun _ _ => psiHat.continuous.comp (continuous_const.mul continuous_id)

theorem integrable_mKerHat {d : ℕ} (hd : 1 ≤ d) (K : ℕ) : Integrable (mKerHat K) := by
  have h := (NTSP.integrable_inv_one_add_abs_pow (d := 2 * d) (by omega)).const_mul
    (kerConst d * 2 ^ d)
  refine h.mono' (continuous_mKerHat K).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hb := norm_mKerHat_mul_le hd K t
  have hpos : 0 < (1 + t ^ 2) ^ d := by positivity
  have key : (1 + |t|) ^ (2 * d) ≤ 2 ^ d * (1 + t ^ 2) ^ d := by
    rw [pow_mul]
    calc ((1 + |t|) ^ 2) ^ d ≤ (2 * (1 + t ^ 2)) ^ d := by
          refine pow_le_pow_left₀ (by positivity) ?_ d
          nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (1 - |t|)]
      _ = 2 ^ d * (1 + t ^ 2) ^ d := mul_pow _ _ _
  have hk : 0 ≤ kerConst d := le_trans (by positivity) hb
  calc ‖mKerHat K t‖ ≤ kerConst d / (1 + t ^ 2) ^ d := by rw [le_div_iff₀ hpos]; exact hb
    _ = kerConst d * 2 ^ d * (2 ^ d * (1 + t ^ 2) ^ d)⁻¹ := by field_simp
    _ ≤ kerConst d * 2 ^ d * ((1 + |t|) ^ (2 * d))⁻¹ := by gcongr

/-- The splitting of the time variables into `J` and its complement preserves volume. -/
theorem measurePreserving_splitJ (J : Finset ι) :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J))
      volume volume := by
  have h := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℝ)) (· ∈ J)
  convert h using 1
  rw [Measure.volume_eq_prod]
  congr 1
  rw [volume_pi]
  congr
  exact Subsingleton.elim _ _

theorem integral_split_J (J : Finset ι) (F : (ι → ℝ) → ℂ) :
    ∫ s, F s = ∫ p : ({j // j ∈ J} → ℝ) × ({j // j ∉ J} → ℝ),
      F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J)).symm p) :=
  ((measurePreserving_splitJ J).symm.integral_comp (MeasurableEquiv.measurableEmbedding _) F).symm

omit [Fintype ι] in
theorem piSplit_symm_apply (J : Finset ι) (p : ({j // j ∈ J} → ℝ) × ({j // j ∉ J} → ℝ)) (i : ι) :
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J)).symm p i =
      if h : i ∈ J then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩ := rfl

/-- The Fourier representation of the truncated profile. -/
theorem isFourierRep_truncProfile {d : ℕ} (hd : 1 ≤ d) (J : Finset ι) (Kj : ι → ℕ)
    {Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ} {D : ℕ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ₁)
    (hD : WordDerivL1 Ψ₁ D) (hD0 : ∀ k, 0 ≤ D k) :
    IsFourierRep (truncProfile J Kj Ψ₁) (truncProfileHat J Kj Ψ₁) := by
  have hrep1 := isFourierRep_of_wordDerivL1 hΨ hD hD0 hd
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J)
  have hmp := measurePreserving_splitJ J
  have hsplit : ∀ s : ι → ℝ, truncProfileHat J Kj Ψ₁ s =
      (∏ j : {j // j ∈ J}, mKerHat (Kj j) ((e s).1 j)) * 𝓕 Ψ₁ (toLp 2 (e s).2) := by
    intro s
    rw [truncProfileHat, ← prod_coe_sort J]
    rfl
  constructor
  · have hG : Integrable (fun a : {j // j ∈ J} → ℝ => ∏ j : {j // j ∈ J}, mKerHat (Kj j) (a j))
        (Measure.pi fun _ => volume) :=
      Integrable.fintype_prod (f := fun (j : {j // j ∈ J}) (t : ℝ) => mKerHat (Kj j) t)
        fun j => integrable_mKerHat hd _
    have hprod : Integrable (fun z : ({j // j ∈ J} → ℝ) × ({j // j ∉ J} → ℝ) =>
        (∏ j : {j // j ∈ J}, mKerHat (Kj j) (z.1 j)) * 𝓕 Ψ₁ (toLp 2 z.2)) :=
      hG.mul_prod hrep1.1
    have h2 := (hmp.integrable_comp_emb e.measurableEmbedding).2 hprod
    refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply]
    rw [hsplit]
  · intro Ω
    have hpt : ∀ p : ({j // j ∈ J} → ℝ) × ({j // j ∉ J} → ℝ),
        truncProfileHat J Kj Ψ₁ (e.symm p) * ∏ i, (𝐞 (e.symm p i * Ω i) : ℂ) =
        (∏ j : {j // j ∈ J}, mKerHat (Kj j) (p.1 j) * (𝐞 (p.1 j * Ω j) : ℂ)) *
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
      (fun a => ∏ j : {j // j ∈ J}, mKerHat (Kj j) (a j) * (𝐞 (a j * Ω j) : ℂ))
      (fun b => 𝓕 Ψ₁ (toLp 2 b) * ∏ i, (𝐞 (b i * Ω i) : ℂ))
    refine hpm.trans ?_
    rw [integral_fintype_prod_volume_eq_prod
      (f := fun (j : {j // j ∈ J}) (t : ℝ) => mKerHat (Kj j) t * (𝐞 (t * Ω j) : ℂ)),
      ← hrep1.2, truncProfile, ← prod_coe_sort J]
    congr 1
    exact prod_congr rfl fun j _ => (mKer_eq_integral _ _).symm

/-- The weighted bound of the truncated profile's Fourier transform. -/
theorem norm_truncProfileHat_mul_le {d : ℕ} (hd : 1 ≤ d) (J : Finset ι) (Kj : ι → ℕ)
    {Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ} {D : ℕ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ₁)
    (hD : WordDerivL1 Ψ₁ D) (hD0 : ∀ k, 0 ≤ D k) (F : Finset ι) (s : ι → ℝ) :
    ‖truncProfileHat J Kj Ψ₁ s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤
      kerConst d ^ J.card * (2 ^ (d * (F.subtype (· ∉ J)).card) *
        ∑ G ∈ (F.subtype (· ∉ J)).powerset, D (G.card * (2 * d))) := by
  have hK : 0 ≤ kerConst d := le_trans (by positivity) (norm_mKerHat_mul_le hd 0 0)
  have hsplitF : ∏ i ∈ F, (1 + s i ^ 2) ^ d =
      (∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d) *
        ∏ i ∈ F.subtype (· ∉ J), (1 + s i ^ 2) ^ d := by
    rw [← prod_filter_mul_prod_filter_not F (· ∈ J)]
    congr 1
    exact (prod_subtype_eq_prod_filter (fun i => (1 + s i ^ 2) ^ d)).symm
  have hJ : (∏ j ∈ J, ‖mKerHat (Kj j) (s j)‖) * ∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d ≤
      kerConst d ^ J.card := by
    have hsub : F.filter (· ∈ J) ⊆ J := fun i hi => (mem_filter.1 hi).2
    have hsd : ∏ j ∈ J, ‖mKerHat (Kj j) (s j)‖ = (∏ j ∈ F.filter (· ∈ J), ‖mKerHat (Kj j) (s j)‖) *
        ∏ j ∈ J \ F.filter (· ∈ J), ‖mKerHat (Kj j) (s j)‖ := by
      rw [mul_comm, prod_sdiff hsub]
    rw [hsd]
    calc (∏ j ∈ F.filter (· ∈ J), ‖mKerHat (Kj j) (s j)‖) *
          (∏ j ∈ J \ F.filter (· ∈ J), ‖mKerHat (Kj j) (s j)‖) *
          ∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d
        = (∏ j ∈ F.filter (· ∈ J), (‖mKerHat (Kj j) (s j)‖ * (1 + s j ^ 2) ^ d)) *
            ∏ j ∈ J \ F.filter (· ∈ J), ‖mKerHat (Kj j) (s j)‖ := by
          rw [prod_mul_distrib]; ring
      _ ≤ (∏ _j ∈ F.filter (· ∈ J), kerConst d) * ∏ _j ∈ J \ F.filter (· ∈ J), kerConst d := by
          refine mul_le_mul (prod_le_prod₀ (fun j _ => by positivity)
            fun j _ => norm_mKerHat_mul_le hd _ _) (prod_le_prod₀ (fun j _ => norm_nonneg _)
            fun j _ => ?_) (prod_nonneg fun j _ => norm_nonneg _) (prod_nonneg fun _ _ => hK)
          have := norm_mKerHat_mul_le hd (Kj j) (s j)
          have h1 : (1 : ℝ) ≤ (1 + s j ^ 2) ^ d := one_le_pow₀ (by nlinarith [sq_nonneg (s j)])
          nlinarith [norm_nonneg (mKerHat (Kj j) (s j))]
      _ = kerConst d ^ J.card := by
          rw [prod_const, prod_const, ← pow_add, add_comm, card_sdiff_add_card_eq_card hsub]
  have hΨ1 := norm_fourier_mul_prod_le hΨ hD hD0 d (F.subtype (· ∉ J))
    (toLp 2 (fun i : {j // j ∉ J} => s i))
  rw [truncProfileHat, norm_mul, norm_prod, hsplitF]
  have hX : 0 ≤ ∏ i ∈ F.subtype (· ∉ J), (1 + s i ^ 2) ^ d := prod_nonneg fun _ _ => by positivity
  calc (∏ j ∈ J, ‖mKerHat (Kj j) (s j)‖) * ‖𝓕 Ψ₁ (toLp 2 fun i : {j // j ∉ J} => s i)‖ *
        ((∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d) * ∏ i ∈ F.subtype (· ∉ J), (1 + s i ^ 2) ^ d)
      = ((∏ j ∈ J, ‖mKerHat (Kj j) (s j)‖) * ∏ i ∈ F.filter (· ∈ J), (1 + s i ^ 2) ^ d) *
          (‖𝓕 Ψ₁ (toLp 2 fun i : {j // j ∉ J} => s i)‖ *
            ∏ i ∈ F.subtype (· ∉ J), (1 + s i ^ 2) ^ d) := by ring
    _ ≤ kerConst d ^ J.card * (2 ^ (d * (F.subtype (· ∉ J)).card) *
          ∑ G ∈ (F.subtype (· ∉ J)).powerset, D (G.card * (2 * d))) := by
        refine mul_le_mul hJ ?_ (mul_nonneg (norm_nonneg _) hX) (pow_nonneg hK _)
        simpa using hΨ1

end WaveTurbulence.ApproxNT
