/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI6

/-!
# DH21 Lemma 5.7: the kernel of `I_{εα₁} ℛ I_{μ₁-εα₁}`

`kcomp_iker_sp_eq` is the first splitting (DH21 L1047–L1050) for an arbitrary superposition
`∫ g(z) J_{L; u(z), v(z)} dz`; a basic class `R` kernel is such a superposition with
`g(γ) = m(α', γ) χ_∞(ℓ₁+ε₂α₂+γ₃)/(ℓ₁+ε₂α₂+γ₃)` and `L = ℓ₂ + ε₂α₂` (`RSym.kernel_eq_sp`).
`kcomp_IRI_eq` is the analogue of `kcomp_IJI_eq`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

section Step1

variable {Z : Type*} [MeasureSpace Z] [SFinite (volume : Measure Z)]

/-- **The first splitting for a general superposition.** -/
theorem kcomp_iker_sp_eq {g : Z → ℂ} (hg : Integrable g) (L e : ℝ) {u v : Z → ℝ}
    (hu : Measurable u) (hv : Measurable v) {t w : ℝ} (h0 : 0 ≤ t - w) (h1 : t - w ≤ 1) :
    kcomp (iker e) (sp g L u v) t w =
      sp (fun p : Z × (ℝ × ℝ) => g p.1 * kerM (L + u p.1 + e) p.2) 0 (fun p => p.2.1)
          (fun p => u p.1 + v p.1 + e - p.2.1) t w +
        sp (fun z => g z * phiR (L + u z + e)) L (fun z => e + u z) v t w -
        sp (fun z => g z * phiR (L + u z + e)) 0 (fun _ => 0) (fun z => u z + v z + e) t w := by
  rw [iker_eq_jker, kcomp_jker_sp hg _ _ _ _ hu hv (by linarith)]
  have key : ∀ z, g z * kcomp (jker 0 0 e) (jker L (u z) (v z)) t w =
      (g z * ∫ q, kerM (L + u z + e) q * jker 0 q.1 (u z + v z + e - q.1) t w) +
        g z * phiR (L + u z + e) * jker L (e + u z) (v z) t w -
        g z * phiR (L + u z + e) * jker 0 0 (u z + v z + e) t w := fun z => by
    rw [kcomp_jker_split _ _ _ _ _ _ h0 h1]
    have e1 : L - 0 + e + u z = L + u z + e := by ring
    have e2 : e + u z + v z = u z + v z + e := by ring
    simp only [e1, e2, zero_add]
    ring
  simp_rw [key]
  have hX : Measurable fun z => L + u z + e := (measurable_const.add hu).add measurable_const
  have hJa : AEStronglyMeasurable fun p : Z × (ℝ × ℝ) =>
      jker 0 p.2.1 (u p.1 + v p.1 + e - p.2.1) t w :=
    ((continuous_jker_coeff 0 t w).measurable.comp ((measurable_fst.comp measurable_snd).prodMk
      ((((hu.comp measurable_fst).add (hv.comp measurable_fst)).add measurable_const).sub
        (measurable_fst.comp measurable_snd)))).aestronglyMeasurable
  have hia := integrable_mul_kerM hg hX hJa (fun p => (norm_jker _ _ _ _ _).le)
  have hT1 : Integrable fun z =>
      g z * ∫ q, kerM (L + u z + e) q * jker 0 q.1 (u z + v z + e - q.1) t w := by
    have := (by rw [Measure.volume_eq_prod] at hia; exact hia.integral_prod_left :
      Integrable fun z => ∫ q, g z * kerM (L + u z + e) q *
        jker 0 q.1 (u z + v z + e - q.1) t w)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun q => by simp only; ring)
  have hJb : AEStronglyMeasurable fun z => jker L (e + u z) (v z) t w :=
    ((continuous_jker_coeff L t w).measurable.comp ((measurable_const.add hu).prodMk
      hv)).aestronglyMeasurable
  have hJc : AEStronglyMeasurable fun z => jker 0 0 (u z + v z + e) t w :=
    ((continuous_jker_coeff 0 t w).measurable.comp (measurable_const.prodMk
      ((hu.add hv).add measurable_const))).aestronglyMeasurable
  have hT2 := integrable_mul_phiR_gen hg hX hJb (fun z => (norm_jker _ _ _ _ _).le)
  have hT3 := integrable_mul_phiR_gen hg hX hJc (fun z => (norm_jker _ _ _ _ _).le)
  have hT12 : Integrable fun z =>
      (g z * ∫ q, kerM (L + u z + e) q * jker 0 q.1 (u z + v z + e - q.1) t w) +
        g z * phiR (L + u z + e) * jker L (e + u z) (v z) t w := hT1.add hT2
  rw [integral_sub hT12 hT3, integral_add hT1 hT2,
    integral_mul_integral_kerM hg hX hJa (fun p => (norm_jker _ _ _ _ _).le)]
  rfl

end Step1

section RKernel

variable {ι : Type*} [Fintype ι]

/-- The coefficient `m(α', γ) χ_∞(ℓ₁+ε₂α₂+γ₃)/(ℓ₁+ε₂α₂+γ₃)` of a basic class `R` operator as a
superposition of `J_{ℓ₂+ε₂α₂; γ₁, γ₂}`. -/
@[expose] noncomputable def rcoef (R : RSym ι) (α : Option ι → ℝ) (γ : ℝ × ℝ × ℝ) : ℂ :=
  R.m (nsp α) γ * (chiInvR (bundle R.y₁ (nsp α) + R.ε * α none + γ.2.2) : ℂ)

theorem RSym.kernel_eq_sp (R : RSym ι) (α : Option ι → ℝ) :
    R.kernel α = sp (rcoef R α) (bundle R.y₂ (nsp α) + R.ε * α none) (fun γ => γ.1)
      (fun γ => γ.2.1) := by
  funext t s
  simp only [RSym.kernel, sp, rcoef, rker]
  refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
  simp only
  ring

theorem integrable_rcoef {θ A N : ℝ} {R : RSym ι} (hR : R.Bound θ A N) (α : Option ι → ℝ) :
    Integrable (rcoef R α) := by
  have hm := hR.reg.integrable (nsp α)
  have hc : Continuous fun γ : ℝ × ℝ × ℝ =>
      (chiInvR (bundle R.y₁ (nsp α) + R.ε * α none + γ.2.2) : ℂ) :=
    contDiff_chiInvRc.continuous.comp (continuous_const.add (continuous_snd.comp continuous_snd))
  refine (hm.norm.mul_const CPhi).mono' (hm.aestronglyMeasurable.mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun γ => ?_)
  rw [rcoef, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_chiInvR_le _) (norm_nonneg _)

/-- **The kernel of `I_e ℛ I_b`** as three compositions of superpositions with `J_{0;0,b}`. -/
theorem kcomp_IRI_eq {θ A N : ℝ} (R : RSym ι) (hR : R.Bound θ A N) (e b : ℝ)
    (α : Option ι → ℝ) {t s : ℝ} (h0 : 0 ≤ t - s) (h1 : t - s ≤ 1) :
    kcomp (kcomp (iker e) (R.kernel α)) (iker b) t s =
      kcomp (sp (fun p : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => rcoef R α p.1 *
          kerM (bundle R.y₂ (nsp α) + R.ε * α none + p.1.1 + e) p.2) 0 (fun p => p.2.1)
          (fun p => p.1.1 + p.1.2.1 + e - p.2.1)) (jker 0 0 b) t s +
        kcomp (sp (fun γ => rcoef R α γ * phiR (bundle R.y₂ (nsp α) + R.ε * α none + γ.1 + e))
          (bundle R.y₂ (nsp α) + R.ε * α none) (fun γ => e + γ.1) (fun γ => γ.2.1))
          (jker 0 0 b) t s -
        kcomp (sp (fun γ => rcoef R α γ * phiR (bundle R.y₂ (nsp α) + R.ε * α none + γ.1 + e))
          0 (fun _ => 0) (fun γ => γ.1 + γ.2.1 + e)) (jker 0 0 b) t s := by
  set L := bundle R.y₂ (nsp α) + R.ε * α none
  have hg := integrable_rcoef hR α
  have hu : Measurable fun γ : ℝ × ℝ × ℝ => γ.1 := measurable_fst
  have hv : Measurable fun γ : ℝ × ℝ × ℝ => γ.2.1 := measurable_fst.comp measurable_snd
  have hK : kcomp (kcomp (iker e) (R.kernel α)) (iker b) t s =
      kcomp (fun t z =>
        sp (fun p : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => rcoef R α p.1 * kerM (L + p.1.1 + e) p.2) 0
            (fun p => p.2.1) (fun p => p.1.1 + p.1.2.1 + e - p.2.1) t z +
          sp (fun γ => rcoef R α γ * phiR (L + γ.1 + e)) L (fun γ => e + γ.1)
            (fun γ => γ.2.1) t z -
          sp (fun γ => rcoef R α γ * phiR (L + γ.1 + e)) 0 (fun _ => 0)
            (fun γ => γ.1 + γ.2.1 + e) t z) (jker 0 0 b) t s := by
    show (∫ z in s..t, kcomp (iker e) (R.kernel α) t z * iker b z s) = ∫ z in s..t, _
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [Set.uIcc_of_le (by linarith)] at hz
    simp only
    rw [RSym.kernel_eq_sp, kcomp_iker_sp_eq hg L e hu hv (by linarith [hz.2])
      (by linarith [hz.1]), iker_eq_jker]
  have hva : Measurable fun p : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => p.1.1 + p.1.2.1 + e - p.2.1 :=
    (((measurable_fst.comp measurable_fst).add
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).add measurable_const).sub
      (measurable_fst.comp measurable_snd)
  have hX : Measurable fun γ : ℝ × ℝ × ℝ => L + γ.1 + e :=
    (measurable_const.add measurable_fst).add measurable_const
  have hfa := integrable_mul_kerM hg hX (J := fun _ => (1 : ℂ)) aestronglyMeasurable_const
    (fun _ => by simp)
  have hfb := integrable_mul_phiR_gen hg hX (J := fun _ => (1 : ℂ)) aestronglyMeasurable_const
    (fun _ => by simp)
  simp only [mul_one] at hfa hfb
  rw [hK, kcomp_add_sub
    (continuous_sp hfa 0 (u := fun p => p.2.1) (measurable_fst.comp measurable_snd) hva)
    (continuous_sp hfb L (u := fun γ => e + γ.1) (v := fun γ => γ.2.1)
      (measurable_const.add measurable_fst) hv)
    (continuous_sp hfb 0 (u := fun _ => 0) (v := fun γ => γ.1 + γ.2.1 + e) measurable_const
      ((hu.add hv).add measurable_const))
    (continuous_jker 0 0 b)]

end RKernel

end WaveTurbulence.ClassJR
