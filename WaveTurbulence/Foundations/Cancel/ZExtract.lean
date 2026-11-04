/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.RegW

/-!
# Extracting a component of the expansion (DH21 (maincoef3), (defintcal))

DH21 Prop 5.1 expands `B̃_Q = Σ_{Z ⊆ S} ∏_{z∈Z} Φ(ζ_zα_z) · B̃_{Q,Z}`, where `Φ(ζx) = χ_∞(x)/(ζπix)`
and `B̃_{Q,Z} ∈ L¹(α[S∖Z])`. DH21 (defintcal) sets `𝒥B̃_{Q,Z} = ∫ B̃_{Q,Z} dα[S∖Z]`. The expansion is
not unique a priori. This file shows that `𝒥B̃_{Q,Z}` is nonetheless determined by `B̃_Q`
(`tendsto_mint_wgt_of_expansion`):
`∫ B̃_{Q,Z} dα[S∖Z] = lim_{θ→0} ∫ B̃_Q(α) ∏_{z∈Z} θζ_zπiα_z ∏_{w∈S} e^{-πθ²α_w²} dα[S]`.

For the term `Z'` of the expansion, Fubini splits the integral over `S = (S∖Z') ∪ Z'`.
* If some `z ∈ Z' ∖ Z`, the factor `∫ Φ(ζx) e^{-πθ²x²} dx` vanishes (odd integrand).
* For `z ∈ Z' ∩ Z`, `∫ Φ(ζx) θζπix e^{-πθ²x²} dx = θ∫ χ_∞(x) e^{-πθ²x²} dx → 1`.
* If `Z' ⊊ Z`, the remaining factor `θζ_wπiα_w e^{-πθ²α_w²}` (`w ∈ Z∖Z'`) is bounded by `1` and tends
  to `0`, so dominated convergence kills the term.
* For `Z' = Z` the term tends to `∫ B̃_{Q,Z}`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR WaveTurbulence.Fourier

/-! ### One variable -/

theorem pi_mul_exp_le_one (y : ℝ) : π * |y| * Real.exp (-π * y ^ 2) ≤ 1 := by
  have h1 : π * |y| ≤ Real.exp (π * y ^ 2) := by
    have h2 := Real.add_one_le_exp (π * y ^ 2)
    have h3 : π * |y| ≤ π * y ^ 2 + 1 := by
      have hp := Real.pi_le_four
      have hy : |y| ^ 2 = y ^ 2 := sq_abs y
      nlinarith [sq_nonneg (|y| - 1 / 2), Real.pi_pos, abs_nonneg y]
    linarith
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact h1

theorem norm_omg_le {θ : ℝ} (hθ : 0 < θ) {z : ℤ} (hz : z = 1 ∨ z = -1) (b : Bool) (x : ℝ) :
    ‖omg θ z b x‖ ≤ 1 := by
  unfold omg
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gw_nonneg θ x)]
  cases b
  · simp only [Bool.false_eq_true, ite_false, norm_one, mul_one]; exact gw_le_one θ x
  · simp only [ite_true]
    have hz' : ‖(z : ℂ)‖ = 1 := by rcases hz with rfl | rfl <;> simp
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hz', Complex.norm_real, Complex.norm_real,
      Complex.norm_real, norm_I, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hθ, abs_of_pos Real.pi_pos]
    have := pi_mul_exp_le_one (θ * x)
    rw [abs_mul, abs_of_pos hθ] at this
    unfold gw
    calc Real.exp (-π * θ ^ 2 * x ^ 2) * (θ * 1 * π * 1 * |x|) =
        π * (θ * |x|) * Real.exp (-π * (θ * x) ^ 2) := by ring_nf
      _ ≤ 1 := this

theorem tendsto_omg {z : ℤ} (b : Bool) (x : ℝ) :
    Tendsto (fun θ => omg θ z b x) (𝓝[>] 0) (𝓝 (if b then 0 else 1)) := by
  have hg := (continuous_ofReal.tendsto 1).comp (tendsto_gw x)
  unfold omg
  cases b
  · simp only [Bool.false_eq_true, ite_false, mul_one]
    simpa [Function.comp_def] using hg
  · simp only [ite_true]
    have h2 : Tendsto (fun θ : ℝ => ((θ : ℂ) * z * π * I * x)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun θ : ℝ => ((θ : ℂ) * z * π * I * x)) (𝓝 0) (𝓝 ((0 : ℝ) * z * π * I * x)) :=
        (by fun_prop : Continuous fun θ : ℝ => ((θ : ℂ) * z * π * I * x)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa [Function.comp_def] using hg.mul h2

/-- `∫ Φ(ζx) e^{-πθ²x²} dx = 0`. -/
theorem integral_phiZ_omg_false (θ : ℝ) (z : ℤ) :
    ∫ x : ℝ, phiR (z * x) * omg θ z false x = 0 := by
  have h := greg_odd (θ := θ) (F := fun x => phiR (z * x)) fun x => by
    rw [show (z : ℝ) * -x = -(z * x) by ring, phiR_neg]
  unfold greg at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [omg, mul_comm]

/-- `Φ(ζx) · θζπix e^{-πθ²x²} = θχ_∞(x) e^{-πθ²x²}`. -/
theorem phiZ_mul_omg_true (θ : ℝ) {z : ℤ} (hz : z = 1 ∨ z = -1) (x : ℝ) :
    phiR (z * x) * omg θ z true x = θ * chiInfinity x * gw θ x := by
  rw [phiR_sign hz, omg]
  simp only [ite_true]
  rcases eq_or_ne x 0 with rfl | hx
  · have : chiInfinity 0 = 0 := by simp [chiInfinity, chi0_eq_one (by norm_num : |(0 : ℝ)| ≤ 1 / 2)]
    simp [this]
  · have hz0 : (z : ℂ) ≠ 0 := by rcases hz with rfl | rfl <;> norm_num
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
    field_simp

theorem integral_gw_eq {θ : ℝ} (hθ : 0 < θ) : ∫ x : ℝ, gw θ x = θ⁻¹ := by
  unfold gw
  have h := integral_gaussian (π * θ ^ 2)
  have e : (fun x : ℝ => Real.exp (-π * θ ^ 2 * x ^ 2)) = fun x => Real.exp (-(π * θ ^ 2) * x ^ 2) := by
    funext x; ring_nf
  rw [e, h, show π / (π * θ ^ 2) = (θ⁻¹) ^ 2 by field_simp, Real.sqrt_sq (inv_nonneg.2 hθ.le)]

/-- `∫ Φ(ζx) θζπix e^{-πθ²x²} dx → 1`. -/
theorem tendsto_integral_phiZ_omg_true {z : ℤ} (hz : z = 1 ∨ z = -1) :
    Tendsto (fun θ => ∫ x : ℝ, phiR (z * x) * omg θ z true x) (𝓝[>] 0) (𝓝 1) := by
  have hχ := chi0_integrable
  have e : ∀ θ, 0 < θ → ∫ x : ℝ, phiR (z * x) * omg θ z true x =
      1 - θ * ∫ x : ℝ, (chi0 x * gw θ x : ℝ) := by
    intro θ hθ
    simp_rw [phiZ_mul_omg_true θ hz]
    have i1 : Integrable fun x => gw θ x := integrable_gw hθ
    have i2 : Integrable fun x => chi0 x * gw θ x :=
      hχ.mul_bdd (c := 1) (continuous_gw θ).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (gw_nonneg θ x)]; exact gw_le_one θ x)
    have e1 : (fun x : ℝ => (θ : ℂ) * chiInfinity x * gw θ x) =
        fun x => ((θ * (gw θ x - chi0 x * gw θ x) : ℝ) : ℂ) := by
      funext x; simp only [chiInfinity]; push_cast; ring
    rw [e1, integral_complex_ofReal, MeasureTheory.integral_const_mul, MeasureTheory.integral_sub i1 i2,
      integral_gw_eq hθ, mul_sub, mul_inv_cancel₀ hθ.ne']
    push_cast; ring
  have hb : ∀ θ, 0 < θ → |∫ x : ℝ, (chi0 x * gw θ x : ℝ)| ≤ ∫ x, chi0 x := by
    intro θ hθ
    refine (MeasureTheory.abs_integral_le_integral_abs).trans (MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun x => abs_nonneg _) hχ (Eventually.of_forall fun x => ?_))
    show |chi0 x * gw θ x| ≤ chi0 x
    rw [abs_mul, abs_of_nonneg (chi0_nonneg x), abs_of_nonneg (gw_nonneg θ x)]
    exact mul_le_of_le_one_right (chi0_nonneg x) (gw_le_one θ x)
  have h0 : Tendsto (fun θ : ℝ => θ * ∫ x : ℝ, (chi0 x * gw θ x : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlin : Tendsto (fun θ : ℝ => θ * ∫ x, chi0 x) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun θ : ℝ => θ * ∫ x, chi0 x := continuous_id.mul continuous_const
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun θ => norm_nonneg _) ?_ hlin
    filter_upwards [eventually_pos_nhdsGT] with θ hθ
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hθ]
    exact mul_le_mul_of_nonneg_left (hb θ hθ) hθ.le
  have h1 : Tendsto (fun θ : ℝ => ((1 - θ * ∫ x : ℝ, (chi0 x * gw θ x : ℝ) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((1 - 0 : ℝ) : ℂ)) := (continuous_ofReal.tendsto _).comp (h0.const_sub 1)
  rw [sub_zero, ofReal_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_pos_nhdsGT] with θ hθ
  rw [e θ hθ]; push_cast; ring

/-! ### Products over a finite set of variables -/

variable {V : Type} [DecidableEq V]

theorem prod_updateFinset (h : V → ℝ → ℂ) (A : Finset V) (α₀ : V → ℝ) (y : ↥A → ℝ) :
    ∏ w ∈ A, h w (updateFinset α₀ A y w) = ∏ i : ↥A, h i (y i) := by
  rw [← Finset.prod_coe_sort]
  exact Finset.prod_congr rfl fun i _ => by simp [updateFinset, i.2]

theorem mInt_prod {A : Finset V} {h : V → ℝ → ℂ} (hh : ∀ w, Integrable (h w)) (α₀ : V → ℝ) :
    MInt A (fun α => ∏ w ∈ A, h w (α w)) α₀ := by
  unfold MInt
  simp_rw [prod_updateFinset]
  rw [volume_pi]
  exact Integrable.fintype_prod fun i => hh _

theorem mint_prod (A : Finset V) (h : V → ℝ → ℂ) (α₀ : V → ℝ) :
    mint A (fun α => ∏ w ∈ A, h w (α w)) α₀ = ∏ w ∈ A, ∫ x : ℝ, h w x := by
  unfold mint
  simp_rw [prod_updateFinset]
  rw [volume_pi, integral_fintype_prod_eq_prod, ← Finset.prod_coe_sort A]

omit [DecidableEq V] in
theorem dependsOn_prod (A : Finset V) (h : V → ℝ → ℂ) :
    DependsOn (fun α : V → ℝ => ∏ w ∈ A, h w (α w)) ↑A := by
  intro α α' hα
  exact Finset.prod_congr rfl fun w hw => by rw [hα w hw]

theorem norm_wgt_le {θ : ℝ} (hθ : 0 < θ) {ζ : V → ℤ} (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1)
    (Z S : Finset V) (α : V → ℝ) : ‖wgt θ ζ Z S α‖ ≤ 1 := by
  unfold wgt
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun w _ => norm_omg_le hθ (hζ w) _ _

/-- The limit of the weight: `1` if no variable of `S` lies in `Z`, else `0`. -/
theorem tendsto_wgt (ζ : V → ℤ) (Z S : Finset V) (α : V → ℝ) :
    Tendsto (fun θ => wgt θ ζ Z S α) (𝓝[>] 0)
      (𝓝 (∏ w ∈ S, if w ∈ Z then (0 : ℂ) else 1)) := by
  unfold wgt
  refine tendsto_finsetProd _ fun w _ => ?_
  have := tendsto_omg (z := ζ w) (decide (w ∈ Z)) (α w)
  by_cases hw : w ∈ Z <;> simpa [hw] using this

/-! ### The extraction -/

/-- **`𝒥B̃_{Q,Z}` is determined by `B̃_Q`.** If
`F = Σ_{Z' ⊆ S} ∏_{z∈Z'} Φ(ζ_zα_z) G_{Z'}` with `G_{Z'}` a function of `α[S∖Z']`, integrable there,
then for `Z ⊆ S`:
`∫ F(α) ∏_{z∈Z} θζ_zπiα_z ∏_{w∈S} e^{-πθ²α_w²} dα[S] → ∫ G_Z dα[S∖Z]` as `θ → 0+`. -/
theorem tendsto_mint_wgt_of_expansion {S Z : Finset V} (hZ : Z ⊆ S) {ζ : V → ℤ}
    (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1) {F : (V → ℝ) → ℂ} {G : Finset V → (V → ℝ) → ℂ}
    {α₀ : V → ℝ} (hGd : ∀ Z' ⊆ S, DependsOn (G Z') ↑(S \ Z'))
    (hGi : ∀ Z' ⊆ S, MInt (S \ Z') (G Z') α₀)
    (hF : ∀ α, F α = ∑ Z' ∈ S.powerset, (∏ z ∈ Z', PhiZ ζ z (α z)) * G Z' α) :
    Tendsto (fun θ => mint S (fun α => F α * wgt θ ζ Z S α) α₀) (𝓝[>] 0)
      (𝓝 (mint (S \ Z) (G Z) α₀)) := by
  -- the one-variable factors
  set c : ℝ → V → ℂ := fun θ z => ∫ x : ℝ, phiR (ζ z * x) * omg θ (ζ z) (decide (z ∈ Z)) x with hc
  -- the reduced weight on `S ∖ Z'`
  set m : ℝ → Finset V → ℂ := fun θ Z' => mint (S \ Z') (fun α => G Z' α * wgt θ ζ Z (S \ Z') α) α₀
    with hm
  -- each term factorizes
  have hterm : ∀ θ, 0 < θ → ∀ Z' ∈ S.powerset,
      MInt S (fun α => (∏ z ∈ Z', PhiZ ζ z (α z)) * G Z' α * wgt θ ζ Z S α) α₀ ∧
      mint S (fun α => (∏ z ∈ Z', PhiZ ζ z (α z)) * G Z' α * wgt θ ζ Z S α) α₀ =
        m θ Z' * ∏ z ∈ Z', c θ z := by
    intro θ hθ Z' hZ'
    have hZ'S : Z' ⊆ S := Finset.mem_powerset.1 hZ'
    have hS : S = (S \ Z') ∪ Z' := (Finset.sdiff_union_of_subset hZ'S).symm
    have he : (fun α => (∏ z ∈ Z', PhiZ ζ z (α z)) * G Z' α * wgt θ ζ Z S α) =
        fun α => (G Z' α * wgt θ ζ Z (S \ Z') α) *
          ∏ z ∈ Z', phiR (ζ z * α z) * omg θ (ζ z) (decide (z ∈ Z)) (α z) := by
      funext α
      unfold wgt PhiZ
      rw [← Finset.prod_sdiff hZ'S, Finset.prod_mul_distrib]
      ring
    have hgi : MInt (S \ Z') (fun α => G Z' α * wgt θ ζ Z (S \ Z') α) α₀ := by
      have h := hGi Z' hZ'S
      unfold MInt at h ⊢
      exact h.mul_bdd (c := 1) ((continuous_wgt θ ζ Z _).comp
        (continuous_updateFinset α₀ _)).aestronglyMeasurable
        (Eventually.of_forall fun y => norm_wgt_le hθ hζ _ _ _)
    have hpi : ∀ z, Integrable fun x : ℝ => phiR (ζ z * x) * omg θ (ζ z) (decide (z ∈ Z)) x :=
      fun z => (integrable_omg hθ _ _).bdd_mul (c := CPhi)
        ((contDiff_phiR.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
        (Eventually.of_forall fun x => norm_phiR_le _)
    obtain ⟨h1, h2⟩ := mint_mul_of_dependsOn (Finset.sdiff_disjoint) (α₀ := α₀)
      (f := fun α => G Z' α * wgt θ ζ Z (S \ Z') α)
      (g := fun α => ∏ z ∈ Z', phiR (ζ z * α z) * omg θ (ζ z) (decide (z ∈ Z)) (α z))
      (by
        intro α α' h
        simp only
        rw [hGd Z' hZ'S h, dependsOn_wgt θ ζ Z _ h])
      (dependsOn_prod Z' fun z x => phiR (ζ z * x) * omg θ (ζ z) (decide (z ∈ Z)) x) hgi
      (mInt_prod hpi α₀)
    rw [he]
    rw [← hS] at h1 h2
    refine ⟨h1, ?_⟩
    rw [h2, mint_prod Z' (fun z x => phiR (ζ z * x) * omg θ (ζ z) (decide (z ∈ Z)) x)]
  -- the sum over the terms
  have hsum : ∀ θ, 0 < θ → mint S (fun α => F α * wgt θ ζ Z S α) α₀ =
      ∑ Z' ∈ S.powerset, m θ Z' * ∏ z ∈ Z', c θ z := by
    intro θ hθ
    have e : (fun α => F α * wgt θ ζ Z S α) = fun α => ∑ Z' ∈ S.powerset,
        (∏ z ∈ Z', PhiZ ζ z (α z)) * G Z' α * wgt θ ζ Z S α := by
      funext α; rw [hF, Finset.sum_mul]
    rw [e]
    unfold mint
    rw [integral_finsetSum _ fun Z' hZ' => (hterm θ hθ Z' hZ').1]
    exact Finset.sum_congr rfl fun Z' hZ' => (hterm θ hθ Z' hZ').2
  -- the limit of each term
  have hlimm : ∀ Z' ∈ S.powerset, Z' ⊆ Z → Tendsto (fun θ => m θ Z') (𝓝[>] 0)
      (𝓝 (if Z' = Z then mint (S \ Z) (G Z) α₀ else 0)) := by
    intro Z' hZ' hZ'Z
    have hZ'S : Z' ⊆ S := Finset.mem_powerset.1 hZ'
    have hlim1 : (∏ w ∈ S \ Z', if w ∈ Z then (0 : ℂ) else 1) = if Z' = Z then 1 else 0 := by
      split_ifs with h
      · subst h
        exact Finset.prod_eq_one fun w hw => by simp [(Finset.mem_sdiff.1 hw).2]
      · obtain ⟨w, hwZ, hwZ'⟩ := Finset.not_subset.1
          (fun h' : Z ⊆ Z' => h (Finset.Subset.antisymm hZ'Z h'))
        exact Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨hZ hwZ, hwZ'⟩) (by simp [hwZ])
    have hG := hGi Z' hZ'S
    unfold MInt at hG
    have hlim : Tendsto (fun θ => m θ Z') (𝓝[>] 0) (𝓝 (mint (S \ Z') (fun α =>
        G Z' α * if Z' = Z then 1 else 0) α₀)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖G Z' (updateFinset α₀ _ y)‖)
        ?_ ?_ hG.norm ?_
      · exact Eventually.of_forall fun θ => hG.aestronglyMeasurable.mul
          ((continuous_wgt θ ζ Z _).comp (continuous_updateFinset α₀ _)).aestronglyMeasurable
      · filter_upwards [eventually_pos_nhdsGT] with θ hθ
        refine Eventually.of_forall fun y => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_wgt_le hθ hζ _ _ _)
      · refine Eventually.of_forall fun y => ?_
        have := (tendsto_wgt ζ Z (S \ Z') (updateFinset α₀ _ y)).const_mul
          (G Z' (updateFinset α₀ _ y))
        rwa [hlim1] at this
    split_ifs at hlim ⊢ with h
    · subst h; simpa using hlim
    · simpa [mint] using hlim
  have hlimc : ∀ z ∈ Z, Tendsto (fun θ => c θ z) (𝓝[>] 0) (𝓝 1) := by
    intro z hz
    simp only [hc, decide_eq_true hz]
    exact tendsto_integral_phiZ_omg_true (hζ z)
  -- assemble
  have hlimT : ∀ Z' ∈ S.powerset, Tendsto (fun θ => m θ Z' * ∏ z ∈ Z', c θ z) (𝓝[>] 0)
      (𝓝 (if Z' = Z then mint (S \ Z) (G Z) α₀ else 0)) := by
    intro Z' hZ'
    by_cases hZ'Z : Z' ⊆ Z
    · have h1 := (hlimm Z' hZ' hZ'Z).mul (tendsto_finsetProd Z' fun z hz => hlimc z (hZ'Z hz))
      simpa using h1
    · obtain ⟨z, hzZ', hzZ⟩ := Finset.not_subset.1 hZ'Z
      have hne : Z' ≠ Z := fun h => hZ'Z (h ▸ subset_rfl)
      simp only [hne, ↓reduceIte]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun θ => ?_)
      have h0 : c θ z = 0 := by
        simp only [hc, decide_eq_false hzZ]
        exact integral_phiZ_omg_false θ (ζ z)
      show 0 = m θ Z' * ∏ z ∈ Z', c θ z
      rw [Finset.prod_eq_zero hzZ' h0, mul_zero]
  have := tendsto_finsetSum S.powerset hlimT
  rw [Finset.sum_ite_eq' S.powerset Z] at this
  simp only [Finset.mem_powerset.2 hZ, ↓reduceIte] at this
  refine this.congr' ?_
  filter_upwards [eventually_pos_nhdsGT] with θ hθ
  exact (hsum θ hθ).symm

end WaveTurbulence.Cancel
