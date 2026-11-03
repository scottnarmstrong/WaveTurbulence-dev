/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Existence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The WKE Taylor expansion over one step: (wketaylor), (wketaylor2), (taylorbound)

TARGET L749–L760 (FINDINGS F10). Let `φ` be a Schwartz solution of (WKE) on `[0, τ★]` whose low
norm is bounded: `(1 + |y|)^{2d+1} |φ(τ, y)| ≤ B` for `τ ∈ [0, τ★]` (`B` plays the role of `𝔆`,
since `2d + 1 ≤ 40d`). Put `ρ = taylorRate d (2d+1) B`. For `0 < δ ≤ taylorStep d B` and every
`p` with `(p+1)δ ≤ τ★`, with `𝒰ₙ(t) = (δ(t-p))ⁿ aₙ[φ(pδ)]` (`taylorU`):

* (wketaylor) `wketaylor`: `φ((p+1)δ, k) = Σₙ 𝒰ₙ(p+1, k)`;
* (wketaylor2) `wketaylor2_zero`, `wketaylor2_succ`: `𝒰₀(t) = φ(pδ)`,
  `𝒰ₘ₊₁(t,k) = δ Σ_{n₁+n₂+n₃=m} ∫_p^t 𝒦(𝒰_{n₁}(t'), 𝒰_{n₂}(t'), 𝒰_{n₃}(t'))(k) dt'`;
* (taylorbound) `taylorbound`: for all `Λ₁, Λ₂` there is `C₂` (depending on `Λ₁, Λ₂` and `φ`) with
  `(1 + |y|)^{Λ₂} ‖Dʳ 𝒰ₙ(t)(y)‖ ≤ C₂ (C₁ δ)ⁿ` for `r ≤ Λ₁`, `t ∈ [p, p+1]`, **with
  `C₁ = 2ρ` depending only on `d` and `B`**, not on `Λ₁, Λ₂`.

The norm used: `sup_y (1 + |y|)^{Λ₂} ‖Dʳ F(y)‖` for `r ≤ Λ₁` (`Dʳ = iteratedFDeriv`), which
dominates TARGET's `𝔖^{Λ₁,Λ₂}` norm (normX2, L590) since `⟨k⟩ ≤ 1 + |k|` and
`|∂^ρ F| ≤ ‖D^{|ρ|} F‖`.
-/

public section

open MeasureTheory Set Filter Topology Finset intervalIntegral
open scoped InnerProductSpace SchwartzMap

namespace WaveTurbulence.WKE

variable {d : ℕ}

/-- The admissible step `δ₀(B) = 1 / (4 (taylorRate d (2d+1) (B+1) + 1))`. -/
@[expose] noncomputable def taylorStep (d : ℕ) (B : ℝ) : ℝ :=
  1 / (4 * (taylorRate d (2 * d + 1) (B + 1) + 1))

theorem taylorStep_pos (d : ℕ) (B : ℝ) : 0 < taylorStep d B := by
  have := taylorRate_nonneg d (2 * d + 1) (B + 1); unfold taylorStep; positivity

theorem taylorRate_mono (d : ℕ) (s₀ : ℝ) {X X' : ℝ} (hX : 0 ≤ X) (h : X ≤ X') :
    taylorRate d s₀ X ≤ taylorRate d s₀ X' := by
  unfold taylorRate
  have := multConst_nonneg d s₀
  gcongr

theorem taylorStep_le_solTime (φ₀ : 𝓢(Mom d, ℝ)) {B : ℝ}
    (hB : ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ₀ y| ≤ B) : taylorStep d B ≤ solTime φ₀ := by
  have h1 := lowConst_le φ₀ hB
  have h2 : taylorRho φ₀ ≤ taylorRate d (2 * d + 1) (B + 1) :=
    taylorRate_mono d _ (lowConst_pos φ₀).le h1
  have h3 := taylorRho_nonneg φ₀
  unfold taylorStep solTime
  apply one_div_le_one_div_of_le (by positivity)
  linarith

/-! ### Time shifts and identification with the Taylor sum -/

theorem isWKESolution_shift {φin : 𝓢(Mom d, ℝ)} {T : ℝ} {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : IsWKESolution φin T φ) {a h : ℝ} (ha : 0 ≤ a) (hah : a + h ≤ T) :
    IsWKESolution (φ a) h (fun s => φ (a + s)) := by
  have hmaps : MapsTo (fun s => a + s) (Icc 0 h) (Icc 0 T) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨hφ.1.comp (continuousOn_const.add continuousOn_id) hmaps, by simp, fun τ hτ k => ?_⟩
  have h2 : HasDerivWithinAt (fun s : ℝ => a + s) 1 (Icc 0 h) τ := by
    simpa using ((hasDerivAt_id τ).const_add a).hasDerivWithinAt (s := Icc 0 h)
  have hd := (hφ.2.2 (a + τ) (hmaps hτ) k).scomp τ h2 hmaps
  simpa [Function.comp_def] using hd

/-- For `δ ≤ taylorStep d B`, the solution over one step is the Taylor sum of its data. -/
theorem eq_taylorSol (hd : 2 ≤ d) {φin : 𝓢(Mom d, ℝ)} {T : ℝ} {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : IsWKESolution φin T φ) {B : ℝ}
    (hB : ∀ τ ∈ Icc 0 T, ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ τ y| ≤ B) {a δ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδB : δ ≤ taylorStep d B) (haδ : a + δ ≤ T) :
    ∀ s ∈ Icc 0 δ, φ (a + s) = taylorSol hd (φ a) s := by
  have haT : a ∈ Icc 0 T := ⟨ha, by linarith⟩
  have h1 := isWKESolution_shift hφ ha haδ
  have h2 := isWKESolution_mono (isWKESolution_taylorSol hd (φ a))
    (hδB.trans (taylorStep_le_solTime (φ a) (hB a haT)))
  exact isWKESolution_unique hd h1 h2

/-! ### The Taylor terms `𝒰ₙ` -/

/-- `𝒰ₙ(t) = (δ(t - p))ⁿ aₙ[φ(pδ)]` (TARGET (wketaylor2), L755). -/
@[expose] noncomputable def taylorU (hd : 2 ≤ d) (φ : ℝ → 𝓢(Mom d, ℝ)) (δ : ℝ) (p n : ℕ)
    (t : ℝ) : 𝓢(Mom d, ℝ) :=
  (δ * (t - p)) ^ n • taylorCoeff hd (φ (p * δ)) n

/-- **(wketaylor)** (TARGET L753). -/
theorem wketaylor (hd : 2 ≤ d) {φin : 𝓢(Mom d, ℝ)} {T : ℝ} {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : IsWKESolution φin T φ) {B : ℝ}
    (hB : ∀ τ ∈ Icc 0 T, ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ τ y| ≤ B) {δ : ℝ}
    (hδ : 0 < δ) (hδB : δ ≤ taylorStep d B) {p : ℕ} (hp : ((p : ℝ) + 1) * δ ≤ T) (k : Mom d) :
    φ (((p : ℝ) + 1) * δ) k = ∑' n, taylorU hd φ δ p n ((p : ℝ) + 1) k := by
  have ha : 0 ≤ (p : ℝ) * δ := by positivity
  have h := eq_taylorSol hd hφ hB ha hδ.le hδB (by linarith) δ ⟨hδ.le, le_rfl⟩
  rw [show ((p : ℝ) + 1) * δ = p * δ + δ by ring, h, taylorSol_apply]
  have hcl : clampT (φ (p * δ)) δ = δ := clampT_of_mem _ ⟨hδ.le, hδB.trans
    (taylorStep_le_solTime _ (hB _ ⟨ha, by linarith⟩))⟩
  rw [hcl]
  refine tsum_congr fun n => ?_
  simp [taylorU, smul_apply, smul_eq_mul]

/-- **(wketaylor2)**, `n = 0`. -/
theorem wketaylor2_zero (hd : 2 ≤ d) (φ : ℝ → 𝓢(Mom d, ℝ)) (δ : ℝ) (p : ℕ) (t : ℝ) :
    taylorU hd φ δ p 0 t = φ (p * δ) := by
  simp [taylorU, taylorCoeff_zero]

theorem integral_mul_sub_pow (δ a t : ℝ) (m : ℕ) :
    ∫ t' in a..t, (δ * (t' - a)) ^ m = δ ^ m * ((t - a) ^ (m + 1) / ((m : ℝ) + 1)) := by
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x => x ^ m) a, integral_pow]
  simp

/-- **(wketaylor2)**, `n = m + 1` (TARGET L755):
`𝒰ₘ₊₁(t,k) = δ Σ_{n₁+n₂+n₃=m} ∫_p^t 𝒦(𝒰_{n₁}(t'), 𝒰_{n₂}(t'), 𝒰_{n₃}(t'))(k) dt'`. -/
theorem wketaylor2_succ (hd : 2 ≤ d) (φ : ℝ → 𝓢(Mom d, ℝ)) (δ : ℝ) (p m : ℕ) (t : ℝ)
    (k : Mom d) :
    taylorU hd φ δ p (m + 1) t k = δ * ∑ q ∈ antidiagonal m, ∑ r ∈ antidiagonal q.2,
      ∫ t' in (p : ℝ)..t, collisionOp (taylorU hd φ δ p q.1 t') (taylorU hd φ δ p r.1 t')
        (taylorU hd φ δ p r.2 t') k := by
  set a := taylorCoeff hd (φ (p * δ))
  have hint : ∀ q ∈ antidiagonal m, ∀ r ∈ antidiagonal q.2,
      ∫ t' in (p : ℝ)..t, collisionOp (taylorU hd φ δ p q.1 t') (taylorU hd φ δ p r.1 t')
        (taylorU hd φ δ p r.2 t') k =
      collisionOp (a q.1) (a r.1) (a r.2) k * (δ ^ m * ((t - p) ^ (m + 1) / ((m : ℝ) + 1))) := by
    intro q hq r hr
    have h1 := mem_antidiagonal.mp hq; have h2 := mem_antidiagonal.mp hr
    have e : ∀ t' : ℝ, collisionOp (taylorU hd φ δ p q.1 t') (taylorU hd φ δ p r.1 t')
        (taylorU hd φ δ p r.2 t') k =
        collisionOp (a q.1) (a r.1) (a r.2) k * (δ * (t' - p)) ^ m := by
      intro t'
      simp only [taylorU]
      rw [collisionOp_smul_left, collisionOp_smul_mid, collisionOp_smul_right, ← h1, ← h2,
        pow_add, pow_add]
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_mul_sub_pow]
  rw [Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun r hr => hint q hq r hr]
  simp_rw [← Finset.sum_mul]
  simp only [taylorU, smul_apply, smul_eq_mul]
  rw [taylorCoeff_succ, smul_apply, _root_.sum_apply, smul_eq_mul]
  simp_rw [_root_.sum_apply, coe_collisionOpSchwartz]
  generalize (∑ q ∈ antidiagonal m, ∑ r ∈ antidiagonal q.2,
    collisionOp (a q.1) (a r.1) (a r.2) k) = X
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [mul_pow, pow_succ δ]
  field_simp

/-! ### (taylorbound) -/

theorem exists_uniform_weighted_bound {φ : ℝ → 𝓢(Mom d, ℝ)} {T : ℝ}
    (hφ : ContinuousOn φ (Icc 0 T)) (r : ℕ) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ τ ∈ Icc 0 T, ∀ y, (1 + ‖y‖) ^ s * ‖iteratedFDeriv ℝ r (φ τ) y‖ ≤ C := by
  set k : ℕ := ⌈s⌉₊
  have hc : ContinuousOn (fun τ => ∑ m ∈ Finset.Iic (k, r),
      SchwartzMap.seminorm ℝ m.1 m.2 (φ τ)) (Icc 0 T) :=
    continuousOn_finsetSum _ fun m _ =>
      ((schwartz_withSeminorms ℝ (Mom d) ℝ).continuous_seminorm m).comp_continuousOn hφ
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨2 ^ k * max A 0, by positivity, fun τ hτ y => ?_⟩
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, r)) le_rfl le_rfl
    (φ τ) y
  have hsup := Seminorm.finset_sup_le_sum (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
    (Finset.Iic (k, r)) (φ τ)
  have hAτ : ∑ m ∈ Finset.Iic (k, r), SchwartzMap.seminorm ℝ m.1 m.2 (φ τ) ≤ max A 0 := by
    have := hA τ hτ
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hx : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hpow : (1 + ‖y‖) ^ s ≤ (1 + ‖y‖) ^ k := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil s)
  calc (1 + ‖y‖) ^ s * ‖iteratedFDeriv ℝ r (φ τ) y‖
      ≤ (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ r (φ τ) y‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ 2 ^ k * ((Finset.Iic (k, r)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) (φ τ) := hb
    _ ≤ 2 ^ k * max A 0 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (by simpa using hsup : _ ≤ _).trans hAτ

/-- Every Schwartz solution on `[0, T]` has a uniform low-norm bound `B > 0` (the hypothesis of
`wketaylor` and `taylorbound`). -/
theorem exists_lowNorm_bound {φin : 𝓢(Mom d, ℝ)} {T : ℝ} {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : IsWKESolution φin T φ) :
    ∃ B, 0 < B ∧ ∀ τ ∈ Icc 0 T, ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ τ y| ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_uniform_weighted_bound hφ.1 0 (2 * d + 1)
  refine ⟨C + 1, by linarith, fun τ hτ y => ?_⟩
  have := hC τ hτ y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  linarith

theorem exists_uniform_multBound_base {φ : ℝ → 𝓢(Mom d, ℝ)} {T : ℝ}
    (hφ : ContinuousOn φ (Icc 0 T)) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ τ ∈ Icc 0 T, ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ τ y| ≤ B) (R W : ℕ) :
    ∃ Y, 0 ≤ Y ∧ ∀ τ ∈ Icc 0 T, MultBound R W (2 * d + 1) 1 Y B (φ τ) := by
  choose C hC0 hC using fun (q : ℕ × ℕ) =>
    exists_uniform_weighted_bound hφ q.1 ((q.2 : ℝ) + (2 * d + 1))
  set Y : ℝ := 1 + ∑ r ∈ range (R + 1), ∑ w ∈ range (W + 1), C (r, w) / B
  have hY1 : 1 ≤ Y := by
    have : 0 ≤ ∑ r ∈ range (R + 1), ∑ w ∈ range (W + 1), C (r, w) / B :=
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun w _ => div_nonneg (hC0 _) hB0.le
    simp only [Y]; linarith
  refine ⟨Y, by linarith, fun τ hτ r hr w hw y => ?_⟩
  rw [one_mul]
  rcases Nat.eq_zero_or_pos (r + w) with h | h
  · obtain ⟨rfl, rfl⟩ : r = 0 ∧ w = 0 := by omega
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hB τ hτ y
  · have hCY : C (r, w) ≤ Y * B := by
      have hle : C (r, w) / B ≤ Y := by
        have h1 : C (r, w) / B ≤ ∑ r' ∈ range (R + 1), ∑ w' ∈ range (W + 1), C (r', w') / B := by
          have hr' : r ∈ range (R + 1) := mem_range.mpr (by omega)
          have hw' : w ∈ range (W + 1) := mem_range.mpr (by omega)
          refine (Finset.single_le_sum (f := fun w' => C (r, w') / B)
            (fun w' _ => div_nonneg (hC0 _) hB0.le) hw').trans ?_
          exact Finset.single_le_sum (f := fun r' => ∑ w' ∈ range (W + 1), C (r', w') / B)
            (fun r' _ => Finset.sum_nonneg fun w' _ => div_nonneg (hC0 _) hB0.le) hr'
        simp only [Y]; linarith
      rwa [div_le_iff₀ hB0] at hle
    have hYp : Y ≤ Y ^ (r + w) := by
      calc Y = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ (r + w) := pow_le_pow_right₀ hY1 h
    calc (1 + ‖y‖) ^ ((w : ℝ) + (2 * d + 1)) * ‖iteratedFDeriv ℝ r (φ τ) y‖
        ≤ C (r, w) := hC (r, w) τ hτ y
      _ ≤ Y * B := hCY
      _ ≤ Y ^ (r + w) * B := mul_le_mul_of_nonneg_right hYp hB0.le

/-- **(taylorbound)** (TARGET L756–L758, FINDINGS F10): for all `Λ₁, Λ₂` there is `C₂` with
`(1 + |y|)^{Λ₂} ‖Dʳ 𝒰ₙ(t)(y)‖ ≤ C₂ (C₁ δ)ⁿ`, `r ≤ Λ₁`, `t ∈ [p, p+1]`, uniformly in the step `p`,
where `C₁ = 2 taylorRate d (2d+1) B` depends only on `d` and the low-norm bound `B`. -/
theorem taylorbound (hd : 2 ≤ d) {φin : 𝓢(Mom d, ℝ)} {T : ℝ} {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : IsWKESolution φin T φ) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ τ ∈ Icc 0 T, ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ τ y| ≤ B) {δ : ℝ}
    (hδ : 0 < δ) (Λ₁ Λ₂ : ℕ) :
    ∃ C₂, ∀ p : ℕ, ((p : ℝ) + 1) * δ ≤ T → ∀ n : ℕ, ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ r ≤ Λ₁,
      ∀ y : Mom d, (1 + ‖y‖) ^ (Λ₂ : ℝ) * ‖iteratedFDeriv ℝ r (taylorU hd φ δ p n t) y‖ ≤
        C₂ * (2 * taylorRate d (2 * d + 1) B * δ) ^ n := by
  obtain ⟨Y, hY, hbase⟩ := exists_uniform_multBound_base hφ.1 hB0 hB Λ₁ Λ₂
  set q := Λ₁ + Λ₂
  set ρ := taylorRate d (2 * d + 1) B
  have hρ : 0 ≤ ρ := taylorRate_nonneg _ _ _
  have hgeo := summable_two_mul_add_one_pow_mul_geometric q (q := 1 / 2) (by norm_num)
    (by norm_num)
  set Mq := ∑' n : ℕ, ((2 * n + 1 : ℕ) : ℝ) ^ q * (1 / 2) ^ n
  have hMq : ∀ n : ℕ, ((2 * n + 1 : ℕ) : ℝ) ^ q ≤ Mq * 2 ^ n := by
    intro n
    have := hgeo.le_tsum n (fun m _ => by positivity)
    rw [← div_le_iff₀ (by positivity)]
    calc ((2 * n + 1 : ℕ) : ℝ) ^ q / 2 ^ n = ((2 * n + 1 : ℕ) : ℝ) ^ q * (1 / 2) ^ n := by
          rw [one_div_pow, div_eq_mul_one_div]
      _ ≤ Mq := this
  refine ⟨B * (Y + 1) ^ q * Mq, fun p hp n t ht r hr y => ?_⟩
  have hpδ : (p : ℝ) * δ ∈ Icc 0 T := ⟨by positivity, by nlinarith⟩
  have hcoef := multBound_taylorCoeff hd (by linarith) hY (hbase _ hpδ) n r hr Λ₂ le_rfl y
  have e : iteratedFDeriv ℝ r (⇑(taylorU hd φ δ p n t)) y =
      (δ * (t - p)) ^ n • iteratedFDeriv ℝ r (taylorCoeff hd (φ (p * δ)) n) y :=
    iteratedFDeriv_const_smul_apply ((taylorCoeff hd (φ (p * δ)) n).smooth r).contDiffAt
  rw [e, norm_smul, Real.norm_eq_abs, abs_pow]
  have htp : |δ * (t - p)| ≤ δ := by
    rw [abs_mul, abs_of_pos hδ, abs_of_nonneg (by linarith [ht.1])]
    nlinarith [ht.2]
  have hw : (1 + ‖y‖) ^ (Λ₂ : ℝ) ≤ (1 + ‖y‖) ^ ((Λ₂ : ℝ) + (2 * d + 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y])
      (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hD := norm_nonneg (iteratedFDeriv ℝ r (taylorCoeff hd (φ (p * δ)) n) y)
  have h1 : ((2 * (n : ℝ) + 1) * Y) ^ (r + Λ₂) ≤ ((2 * n + 1 : ℕ) : ℝ) ^ q * (Y + 1) ^ q := by
    rw [← mul_pow]
    calc ((2 * (n : ℝ) + 1) * Y) ^ (r + Λ₂) ≤ ((2 * (n : ℝ) + 1) * (Y + 1)) ^ (r + Λ₂) :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith)
            (by positivity)) _
      _ ≤ ((2 * (n : ℝ) + 1) * (Y + 1)) ^ q :=
          pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg n :
            (0 : ℝ) ≤ n)]) (by linarith)) (by omega)
      _ = (((2 * n + 1 : ℕ) : ℝ) * (Y + 1)) ^ q := by push_cast; ring
  have h2 : B * ρ ^ n / ((n : ℝ) + 1) ^ 2 ≤ B * ρ ^ n := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h0 : 0 ≤ B * ρ ^ n := by positivity
    nlinarith
  calc (1 + ‖y‖) ^ (Λ₂ : ℝ) * (|δ * (t - p)| ^ n *
        ‖iteratedFDeriv ℝ r (taylorCoeff hd (φ (p * δ)) n) y‖)
      ≤ δ ^ n * ((1 + ‖y‖) ^ ((Λ₂ : ℝ) + (2 * d + 1)) *
          ‖iteratedFDeriv ℝ r (taylorCoeff hd (φ (p * δ)) n) y‖) := by
        have := pow_le_pow_left₀ (abs_nonneg _) htp n
        calc (1 + ‖y‖) ^ (Λ₂ : ℝ) * (|δ * (t - p)| ^ n *
              ‖iteratedFDeriv ℝ r (taylorCoeff hd (φ (p * δ)) n) y‖)
            = |δ * (t - p)| ^ n * ((1 + ‖y‖) ^ (Λ₂ : ℝ) *
                ‖iteratedFDeriv ℝ r (taylorCoeff hd (φ (p * δ)) n) y‖) := by ring
          _ ≤ δ ^ n * ((1 + ‖y‖) ^ ((Λ₂ : ℝ) + (2 * d + 1)) *
                ‖iteratedFDeriv ℝ r (taylorCoeff hd (φ (p * δ)) n) y‖) := by gcongr
    _ ≤ δ ^ n * (((2 * (n : ℝ) + 1) * Y) ^ (r + Λ₂) * (B * ρ ^ n / ((n : ℝ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ ≤ δ ^ n * ((((2 * n + 1 : ℕ) : ℝ) ^ q * (Y + 1) ^ q) * (B * ρ ^ n)) := by gcongr
    _ ≤ δ ^ n * (((Mq * 2 ^ n) * (Y + 1) ^ q) * (B * ρ ^ n)) := by
        gcongr; exact hMq n
    _ = B * (Y + 1) ^ q * Mq * (2 * ρ * δ) ^ n := by rw [mul_pow, mul_pow]; ring

end WaveTurbulence.WKE
