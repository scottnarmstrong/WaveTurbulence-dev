/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Core
public import WaveTurbulence.Foundations.WeylSums.CoordinateDerivativeBounds
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier bounds for the smooth profile `Ψ₁` (packet NT6)

DH23 (propertypsi2) assumes `‖∂^ρ Ψ₁‖_{L¹} ≤ C^n (4|ρ|)!` for every multi-index `ρ`. We write the
multi-index derivative `∂^ρ` as a coordinate word `v : Fin k → κ` (each coordinate repeated as
often as `ρ` requires; by the symmetry of derivatives of smooth functions the order does not
matter): `∂^v Ψ₁(Ω) = D^kΨ₁(Ω)(e_{v₁},…,e_{v_k})`.

From these bounds:
* every `D^kΨ₁` is integrable;
* `(2π)^k |∏ₘ σ_{vₘ}| |Ψ̂₁(σ)| ≤ ‖∂^v Ψ₁‖_{L¹}` (Fourier transform of derivatives);
* `|Ψ̂₁(σ)| ∏_{i∈F} ⟨σᵢ⟩^{2d} ≤ 2^{d|F|} ∑_{G⊆F} D(2d|G|)` where `D(k)` bounds the order-`k`
  derivatives (the weights required by the minor arcs);
* `Ψ₁` is the inverse Fourier transform of `Ψ̂₁`, in coordinates on `ℝ^κ`.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.ApproxNT

theorem fourierChar_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (𝐞 (∑ i ∈ s, a i) : ℂ) = ∏ i ∈ s, (𝐞 (a i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [sum_insert hj, prod_insert hj, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The coordinate-word derivative `∂^v f`. -/
@[expose] def wordDeriv (f : EuclideanSpace ℝ κ → ℂ) {k : ℕ} (v : Fin k → κ)
    (x : EuclideanSpace ℝ κ) : ℂ :=
  iteratedFDeriv ℝ k f x (fun m => EuclideanSpace.single (v m) 1)

/-- The hypothesis (propertypsi2), first half: `‖∂^v f‖_{L¹} ≤ D(k)` for every word `v`. -/
@[expose] def WordDerivL1 (f : EuclideanSpace ℝ κ → ℂ) (D : ℕ → ℝ) : Prop :=
  ∀ k (v : Fin k → κ), ∫⁻ x, ‖wordDeriv f v x‖ₑ ≤ ENNReal.ofReal (D k)

variable {f : EuclideanSpace ℝ κ → ℂ} {D : ℕ → ℝ}

theorem continuous_wordDeriv (hf : ContDiff ℝ ∞ f) {k : ℕ} (v : Fin k → κ) :
    Continuous (wordDeriv f v) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => EuclideanSpace ℝ κ) ℂ
    (fun m => EuclideanSpace.single (v m) 1)).continuous.comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))

theorem integrable_wordDeriv (hf : ContDiff ℝ ∞ f) (hD : WordDerivL1 f D) {k : ℕ}
    (v : Fin k → κ) : Integrable (wordDeriv f v) := by
  refine ⟨(continuous_wordDeriv hf v).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (hD k v) ENNReal.ofReal_lt_top

theorem integrable_iteratedFDeriv (hf : ContDiff ℝ ∞ f) (hD : WordDerivL1 f D) (k : ℕ) :
    Integrable (iteratedFDeriv ℝ k f) := by
  have hsum : Integrable (fun x => (Fintype.card κ : ℝ) ^ k *
      ∑ v : Fin k → κ, ‖wordDeriv f v x‖) :=
    (integrable_finsetSum _ fun v _ => (integrable_wordDeriv hf hD v).norm).const_mul _
  refine hsum.mono' (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  refine WeylSums.norm_multilinear_le_coordinate_bound k _ _
    (sum_nonneg fun v _ => norm_nonneg _) fun v => ?_
  exact single_le_sum (f := fun v => ‖wordDeriv f v x‖) (fun _ _ => norm_nonneg _) (mem_univ v)

theorem integrable_of_wordDerivL1 (hf : ContDiff ℝ ∞ f) (hD : WordDerivL1 f D) :
    Integrable f := by
  have h := integrable_wordDeriv hf hD (k := 0) Fin.elim0
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [wordDeriv, iteratedFDeriv_zero_apply]

theorem integral_norm_wordDeriv_le (hf : ContDiff ℝ ∞ f) (hD : WordDerivL1 f D) (hD0 : ∀ k, 0 ≤ D k)
    {k : ℕ} (v : Fin k → κ) : ∫ x, ‖wordDeriv f v x‖ ≤ D k := by
  rw [integral_norm_eq_lintegral_enorm (continuous_wordDeriv hf v).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (hD0 k) (hD k v)

/-- The Fourier transform of a coordinate-word derivative. -/
theorem norm_prod_mul_norm_fourier_le (hf : ContDiff ℝ ∞ f) (hD : WordDerivL1 f D)
    (hD0 : ∀ k, 0 ≤ D k) {k : ℕ} (v : Fin k → κ) (w : EuclideanSpace ℝ κ) :
    (2 * Real.pi) ^ k * (∏ m, |w (v m)|) * ‖𝓕 f w‖ ≤ D k := by
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) → Integrable (iteratedFDeriv ℝ n f) :=
    fun n _ => integrable_iteratedFDeriv hf hD n
  have h := Real.fourier_iteratedFDeriv (hf.of_le (by exact_mod_cast le_top)) hint
    (n := k) le_rfl
  have h2 := congrFun h w
  have h3 := congrArg (fun T => T (fun m => EuclideanSpace.single (v m) (1 : ℝ))) h2
  rw [Real.fourier_continuousMultilinearMap_apply (integrable_iteratedFDeriv hf hD k),
    VectorFourier.fourierPowSMulRight_apply] at h3
  have hn := Real.norm_fourier_le_integral_norm (wordDeriv f v) w
  have heq : 𝓕 (fun x => iteratedFDeriv ℝ k f x fun m => EuclideanSpace.single (v m) 1) w =
      𝓕 (wordDeriv f v) w := rfl
  rw [heq] at h3
  rw [h3] at hn
  refine le_trans (le_of_eq ?_) (hn.trans (integral_norm_wordDeriv_le hf hD hD0 v))
  rw [norm_smul, norm_smul, norm_pow, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, norm_prod]
  have hp : ∏ m, |w (v m)| = ∏ b, ‖((-innerSL ℝ) w) (EuclideanSpace.single (v b) (1 : ℝ))‖ :=
    Finset.prod_congr rfl fun m _ => by
      simp [EuclideanSpace.inner_single_right, Real.norm_eq_abs]
  rw [hp]; ring

/-- A coordinate word repeating each element of `G` exactly `r` times. -/
@[expose] def repWord (G : Finset κ) (r : ℕ) : Fin (G.card * r) → κ :=
  fun m => (G.equivFin.symm (finProdFinEquiv.symm m).1 : κ)

omit [Fintype κ] [DecidableEq κ] in
theorem prod_repWord (G : Finset κ) (r : ℕ) (g : κ → ℝ) :
    ∏ m, g (repWord G r m) = ∏ i ∈ G, g i ^ r := by
  rw [← Fintype.prod_equiv finProdFinEquiv (fun p : Fin G.card × Fin r =>
    g (G.equivFin.symm p.1 : κ)) _ (fun p => by simp [repWord])]
  rw [Fintype.prod_prod_type]
  simp only [prod_const, card_univ, Fintype.card_fin]
  rw [Fintype.prod_equiv G.equivFin.symm (fun a => g (G.equivFin.symm a : κ) ^ r)
    (fun i : G => g i ^ r) (fun a => rfl)]
  exact prod_coe_sort G (fun i => g i ^ r)

theorem one_add_sq_pow_le' (d : ℕ) (σ : ℝ) : (1 + σ ^ 2) ^ d ≤ 2 ^ d * (1 + |σ| ^ (2 * d)) := by
  have h1 : 1 + σ ^ 2 ≤ 2 * max 1 (σ ^ 2) := by
    have := le_max_left 1 (σ ^ 2); have := le_max_right 1 (σ ^ 2); linarith
  calc (1 + σ ^ 2) ^ d ≤ (2 * max 1 (σ ^ 2)) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = 2 ^ d * max 1 (σ ^ 2) ^ d := mul_pow _ _ _
    _ ≤ 2 ^ d * (1 + |σ| ^ (2 * d)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases max_cases 1 (σ ^ 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
        · rw [one_pow]; linarith [pow_nonneg (abs_nonneg σ) (2 * d)]
        · rw [pow_mul, sq_abs]; linarith

/-- The weighted decay of `Ψ̂₁` used for the minor arcs. -/
theorem norm_fourier_mul_prod_le (hf : ContDiff ℝ ∞ f) (hD : WordDerivL1 f D) (hD0 : ∀ k, 0 ≤ D k)
    (d : ℕ) (F : Finset κ) (w : EuclideanSpace ℝ κ) :
    ‖𝓕 f w‖ * ∏ i ∈ F, (1 + w i ^ 2) ^ d ≤ 2 ^ (d * F.card) * ∑ G ∈ F.powerset, D (G.card * (2 * d)) := by
  calc ‖𝓕 f w‖ * ∏ i ∈ F, (1 + w i ^ 2) ^ d
      ≤ ‖𝓕 f w‖ * ∏ i ∈ F, (2 ^ d * (1 + |w i| ^ (2 * d))) :=
        mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => by positivity)
          fun i _ => one_add_sq_pow_le' d (w i)) (norm_nonneg _)
    _ = 2 ^ (d * F.card) * ∑ G ∈ F.powerset, (∏ i ∈ G, |w i| ^ (2 * d)) * ‖𝓕 f w‖ := by
        rw [prod_mul_distrib, prod_const, prod_one_add, ← pow_mul, mul_left_comm, mul_sum]
        congr 1
        exact sum_congr rfl fun G _ => by ring
    _ ≤ 2 ^ (d * F.card) * ∑ G ∈ F.powerset, D (G.card * (2 * d)) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun G _ => ?_) (by positivity)
        have h := norm_prod_mul_norm_fourier_le hf hD hD0 (repWord G (2 * d)) w
        rw [prod_repWord G (2 * d) (fun i => |w i|)] at h
        refine le_trans ?_ h
        have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ (G.card * (2 * d)) :=
          one_le_pow₀ (by nlinarith [Real.pi_gt_three])
        have hX : 0 ≤ (∏ i ∈ G, |w i| ^ (2 * d)) * ‖𝓕 f w‖ := by positivity
        calc (∏ i ∈ G, |w i| ^ (2 * d)) * ‖𝓕 f w‖
            ≤ (2 * Real.pi) ^ (G.card * (2 * d)) * ((∏ i ∈ G, |w i| ^ (2 * d)) * ‖𝓕 f w‖) :=
              le_mul_of_one_le_left hX hpi
          _ = _ := by ring

omit [DecidableEq κ] in
theorem continuous_fourier_of_integrable (hfi : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hfi

/-- The Fourier representation of `Ψ₁` in coordinates. -/
theorem isFourierRep_of_wordDerivL1 (hf : ContDiff ℝ ∞ f) (hD : WordDerivL1 f D) (hD0 : ∀ k, 0 ≤ D k)
    {d : ℕ} (hd : 1 ≤ d) :
    IsFourierRep (fun Ω : κ → ℝ => f (toLp 2 Ω)) (fun s => 𝓕 f (toLp 2 s)) := by
  have hfi := integrable_of_wordDerivL1 hf hD
  have hcont := continuous_fourier_of_integrable hfi
  have hPi : Integrable (fun s : κ → ℝ => 𝓕 f (toLp 2 s)) := by
    have hw : Integrable (fun s : κ → ℝ => (2 ^ (d * (univ : Finset κ).card) *
        ∑ G ∈ (univ : Finset κ).powerset, D (G.card * (2 * d))) *
          ∏ i, 2 ^ d * ((1 + |s i|) ^ (2 * d))⁻¹) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.fintype_prod (f := fun _ (t : ℝ) => 2 ^ d * ((1 + |t|) ^ (2 * d))⁻¹)
        fun _ => ?_
      exact (NTSP.integrable_inv_one_add_abs_pow (by omega)).const_mul _
    refine hw.mono' (hcont.comp (PiLp.continuous_toLp 2 _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    have h := norm_fourier_mul_prod_le hf hD hD0 d univ (toLp 2 s)
    have hpos : 0 < ∏ i, (1 + s i ^ 2) ^ d := prod_pos fun i _ => by positivity
    have hle : ∏ i, ((1 + s i ^ 2) ^ d)⁻¹ ≤ ∏ i, 2 ^ d * ((1 + |s i|) ^ (2 * d))⁻¹ := by
      refine prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
      have key : (1 + |s i|) ^ (2 * d) ≤ 2 ^ d * (1 + s i ^ 2) ^ d := by
        rw [pow_mul]
        calc ((1 + |s i|) ^ 2) ^ d ≤ (2 * (1 + s i ^ 2)) ^ d := by
              refine pow_le_pow_left₀ (by positivity) ?_ d
              nlinarith [abs_nonneg (s i), sq_abs (s i), sq_nonneg (1 - |s i|)]
          _ = 2 ^ d * (1 + s i ^ 2) ^ d := mul_pow _ _ _
      calc ((1 + s i ^ 2) ^ d)⁻¹ = 2 ^ d * (2 ^ d * (1 + s i ^ 2) ^ d)⁻¹ := by field_simp
        _ ≤ 2 ^ d * ((1 + |s i|) ^ (2 * d))⁻¹ := by gcongr
    have hB : ‖𝓕 f (toLp 2 s)‖ ≤ (2 ^ (d * (univ : Finset κ).card) *
        ∑ G ∈ (univ : Finset κ).powerset, D (G.card * (2 * d))) * ∏ i, ((1 + s i ^ 2) ^ d)⁻¹ := by
      rw [prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
      exact h
    refine hB.trans (mul_le_mul_of_nonneg_left hle ?_)
    exact le_trans (by positivity) (h.trans' (mul_nonneg (norm_nonneg _) hpos.le))
  refine ⟨hPi, fun Ω => ?_⟩
  have hEi : Integrable (𝓕 f) := by
    have h := (PiLp.volume_preserving_toLp κ).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (κ → ℝ)).measurableEmbedding (g := 𝓕 f)
    exact h.1 hPi
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hf.continuous hfi hEi) (toLp 2 Ω)
  rw [Real.fourierInv_eq] at hinv
  show f (toLp 2 Ω) = ∫ s, 𝓕 f (toLp 2 s) * ∏ i, (𝐞 (s i * Ω i) : ℂ)
  rw [← hinv, ← (PiLp.volume_preserving_toLp κ).integral_comp
    (MeasurableEquiv.toLp 2 (κ → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [← fourierChar_finset_sum]
  congr 2
  rw [PiLp.inner_apply]
  refine sum_congr rfl fun i _ => ?_
  simp [mul_comm]

end WaveTurbulence.ApproxNT
