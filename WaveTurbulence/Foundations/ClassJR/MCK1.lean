/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCProd
public import WaveTurbulence.Foundations.ClassJR.CouplingRR

/-!
# The coupling of the type 1 recursion

DH21 Proposition 5.1, Case 1 (L1100–L1110, (regcplexpl)–(regcplex2)) computes
`∫_0^t ∫_0^s e^{πiα_𝔯(t₁-s₁)} e^{πi(λ*t₁ + λ**s₁)} = E(α_𝔯 + λ*, t) E(-α_𝔯 + λ**, s)`, with
`E(x, t) = ∫_0^t e^{πixu} du`. By `integral_gE_mul_exp` this is
`∫ gE(α_𝔯 + λ*; q₁) gE(-α_𝔯 + λ**; q₂) e^{πi(q₁.1 t + q₂.1 s)} dq`. The coupling
`K1 c₁ c₂ (α_𝔯; q) = gE(α_𝔯 + c₁; q₁) gE(-α_𝔯 + c₂; q₂)` then satisfies DH21 (regcplex2) with the
DH23 weights (`lintegral_K1_le`): for `a₁ + a₂ + b₁ < 1`,
`∫∫ (1+|v₁|)^{a₁} (1+|v₂|)^{a₂} (1+|α_𝔯 + c₁|)^{b₁} |∂^j K1| ≤ gev (16 C_E² Ir(2)² Ir(2 - a₁ - a₂ - b₁)) A₁ j`,
uniformly in `(c₁, c₂)`. The weight falls on one denominator at a time (DH23 L966–L969: "bounded for
all `0 < p < 1`").
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section K1

/-- **The type 1 coupling** `gE(α + c₁; q₁) gE(-α + c₂; q₂)` in the root variable `α`. -/
@[expose] noncomputable def K1 (c₁ c₂ : ℝ) (α : Unit → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  gE (α () + c₁) q.1 * gE (-α () + c₂) q.2

theorem isBundle_one : IsBundle (fun _ : Unit => (1 : ℤ)) := fun _ => by norm_num

theorem isBundle_negOne : IsBundle (fun _ : Unit => (-1 : ℤ)) := fun _ => by norm_num

theorem bundle_one (α : Unit → ℝ) : bundle (fun _ : Unit => (1 : ℤ)) α = α () := by
  simp [bundle]

theorem bundle_negOne (α : Unit → ℝ) : bundle (fun _ : Unit => (-1 : ℤ)) α = -α () := by
  simp [bundle]

theorem contDiff_K1 (c₁ c₂ : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiff ℝ ∞ fun α : Unit → ℝ => K1 c₁ c₂ α q := by
  have hp : ContDiff ℝ ∞ fun α : Unit → ℝ => α () :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℝ) ()).contDiff
  unfold K1
  exact ((contDiff_gE q.1).comp (hp.add contDiff_const)).mul
    ((contDiff_gE q.2).comp (hp.neg.add contDiff_const))

theorem measurable_K1 :
    Measurable fun p : (ℝ × ℝ) × ((Unit → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) => K1 p.1.1 p.1.2 p.2.1 p.2.2 := by
  unfold K1
  exact (measurable_gE.comp (f := fun p : (ℝ × ℝ) × ((Unit → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) =>
      (p.2.1 () + p.1.1, p.2.2.1)) (by fun_prop)).mul
    (measurable_gE.comp (f := fun p : (ℝ × ℝ) × ((Unit → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) =>
      (-p.2.1 () + p.1.2, p.2.2.2)) (by fun_prop))

/-- **The Leibniz rule for the type 1 coupling.** -/
theorem dnorm_K1_le (c₁ c₂ : ℝ) (j : ℕ) (α : Unit → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    dnorm j (K1 c₁ c₂) α q ≤ ∑ p ∈ range (j + 1), (j.choose p : ℝ≥0∞) *
      ‖iteratedDeriv p (fun y => gE y q.1) (α () + c₁)‖ₑ *
      ‖iteratedDeriv (j - p) (fun y => gE y q.2) (-α () + c₂)‖ₑ := by
  have hl : lift1 (K1 c₁ c₂) q = fun β =>
      gE (bundleL (fun _ : Unit => (1 : ℤ)) β + c₁) q.1 *
        gE (bundleL (fun _ : Unit => (-1 : ℤ)) β + c₂) q.2 := by
    funext β
    simp only [lift1, K1, bundleL_apply, bundle_one, bundle_negOne]
  have h1 : ContDiff ℝ ∞ fun β : L1 Unit => gE (bundleL (fun _ : Unit => (1 : ℤ)) β + c₁) q.1 :=
    (contDiff_gE q.1).comp ((bundleL (fun _ : Unit => (1 : ℤ))).contDiff.add contDiff_const)
  have h2 : ContDiff ℝ ∞ fun β : L1 Unit => gE (bundleL (fun _ : Unit => (-1 : ℤ)) β + c₂) q.2 :=
    (contDiff_gE q.2).comp ((bundleL (fun _ : Unit => (-1 : ℤ))).contDiff.add contDiff_const)
  rw [dnorm, hl]
  refine (enorm_iteratedFDeriv_mul_le h1 h2 _ j).trans ?_
  refine Finset.sum_le_sum fun p _ => ?_
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
  · have h := enorm_iteratedFDeriv_scalar_le (contDiff_gE q.1)
      (bundleL (fun _ : Unit => (1 : ℤ))) (norm_bundleL_le isBundle_one) c₁ (WithLp.toLp 1 α) p
    rw [bundleL_apply, bundle_one] at h
    exact h
  · have h := enorm_iteratedFDeriv_scalar_le (contDiff_gE q.2)
      (bundleL (fun _ : Unit => (-1 : ℤ))) (norm_bundleL_le isBundle_negOne) c₂ (WithLp.toLp 1 α)
      (j - p)
    rw [bundleL_apply, bundle_negOne] at h
    exact h

end K1

section K1Bound

/-- The pair integral of the type 1 coupling: `∫ (1+|x+c₁|)^{-p₁} (1+|-x+c₂|)^{-p₂} dx ≤ Ir(p₁+p₂)`. -/
theorem lintegral_pair_shift_le {p₁ p₂ : ℝ} (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h : 1 < p₁ + p₂)
    (c₁ c₂ : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + |x + c₁|) ^ (-p₁) * (1 + |-x + c₂|) ^ (-p₂)) ≤
      ENNReal.ofReal (Ir (p₁ + p₂)) := by
  have e : ∀ x : ℝ, (1 + |x + c₁|) ^ (-p₁) * (1 + |-x + c₂|) ^ (-p₂) =
      (fun u : ℝ => (1 + |u|) ^ (-p₁) * (1 + |u + -(c₁ + c₂)|) ^ (-p₂)) (x + c₁) := fun x => by
    simp only
    congr 2
    rw [show x + c₁ + -(c₁ + c₂) = -(-x + c₂) by ring, abs_neg]
  simp_rw [e]
  rw [lintegral_add_right_eq_self (fun u : ℝ => ENNReal.ofReal ((1 + |u|) ^ (-p₁) *
    (1 + |u + -(c₁ + c₂)|) ^ (-p₂))) c₁]
  exact lintegral_pair_gen_le h₁ h₂ h _

/-- **DH21 (regcplex2) with the DH23 weights**: the type 1 coupling is integrable in the root
variable and the two frequencies, uniformly in `(c₁, c₂)`. -/
theorem lintegral_K1_le {a₁ a₂ b₁ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁)
    (hs : a₁ + a₂ + b₁ < 1) (c₁ c₂ : ℝ) (j : ℕ) :
    ∫⁻ α : Unit → ℝ, ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), ((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ *
        ((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * ((1 : ℝ≥0∞) + ‖α () + c₁‖ₑ) ^ b₁ *
        dnorm j (K1 c₁ c₂) α q ≤
      gev (4 * (2 * CE * Ir 2) ^ 2 * Ir (2 - a₁ - a₂ - b₁)) A1 j := by
  have ha₁1 : a₁ ≤ 1 := by linarith
  have ha₂1 : a₂ ≤ 1 := by linarith
  set D : ℝ := 2 * CE * Ir 2 with hD
  have hD0 : 0 ≤ D := by have := CE_nonneg; have := Ir2_nonneg; positivity
  set Ip : ℝ := Ir (2 - a₁ - a₂ - b₁) with hIp
  have hI0 : 0 ≤ Ip := ENNReal.toReal_nonneg
  have hA1 := A1_nonneg
  -- the coefficient of the `p`-th Leibniz term
  set cf : ℕ → ℝ := fun p => (j.choose p : ℝ) * (D * A1 ^ p * (Nat.factorial (2 * p) : ℝ)) *
    (D * A1 ^ (j - p) * (Nat.factorial (2 * (j - p)) : ℝ)) with hcf
  have hcf0 : ∀ p, 0 ≤ cf p := fun p => by simp only [hcf]; positivity
  -- the profile in the root variable
  set R : ℝ → ℝ := fun x => (1 + |x + c₁|) ^ (a₁ + b₁ - 1) * (1 + |-x + c₂|) ^ (a₂ - 1) with hR
  have hR0 : ∀ x, 0 ≤ R x := fun x => by simp only [hR]; positivity
  -- the bound for fixed `α`
  have hq : ∀ α : Unit → ℝ, ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), ((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ *
      ((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * ((1 : ℝ≥0∞) + ‖α () + c₁‖ₑ) ^ b₁ *
      dnorm j (K1 c₁ c₂) α q ≤ ∑ p ∈ range (j + 1), ENNReal.ofReal (cf p) *
        ENNReal.ofReal (R (α ())) := by
    intro α
    set x₁ := α () + c₁
    set x₂ := -α () + c₂
    have hm1 : ∀ p, Measurable fun q : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖q.1‖ₑ) ^ a₁ * gEbd p x₁ q :=
      fun p => (by fun_prop : Measurable fun q : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖q.1‖ₑ) ^ a₁).mul
        ((measurable_gEbd p).comp (f := fun q : ℝ × ℝ => (x₁, q)) (by fun_prop))
    have hm2 : ∀ p, Measurable fun q : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖q.1‖ₑ) ^ a₂ * gEbd p x₂ q :=
      fun p => (by fun_prop : Measurable fun q : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖q.1‖ₑ) ^ a₂).mul
        ((measurable_gEbd p).comp (f := fun q : ℝ × ℝ => (x₂, q)) (by fun_prop))
    have hpt : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), ((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ *
        ((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * ((1 : ℝ≥0∞) + ‖x₁‖ₑ) ^ b₁ * dnorm j (K1 c₁ c₂) α q ≤
        ∑ p ∈ range (j + 1), (j.choose p : ℝ≥0∞) * ((1 : ℝ≥0∞) + ‖x₁‖ₑ) ^ b₁ *
          ((((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ * gEbd p x₁ q.1) *
            (((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * gEbd (j - p) x₂ q.2)) := by
      intro q
      refine (mul_le_mul' le_rfl ((dnorm_K1_le c₁ c₂ j α q).trans (Finset.sum_le_sum
        fun p _ => mul_le_mul' (mul_le_mul' le_rfl (enorm_iteratedDeriv_gE_le_bd p _ _))
          (enorm_iteratedDeriv_gE_le_bd (j - p) _ _)))).trans_eq ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    calc _ ≤ ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), ∑ p ∈ range (j + 1), (j.choose p : ℝ≥0∞) *
          ((1 : ℝ≥0∞) + ‖x₁‖ₑ) ^ b₁ * ((((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ * gEbd p x₁ q.1) *
            (((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * gEbd (j - p) x₂ q.2)) := lintegral_mono hpt
      _ = ∑ p ∈ range (j + 1), (j.choose p : ℝ≥0∞) * ((1 : ℝ≥0∞) + ‖x₁‖ₑ) ^ b₁ *
          ((∫⁻ q₁ : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q₁.1‖ₑ) ^ a₁ * gEbd p x₁ q₁) *
            ∫⁻ q₂ : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q₂.1‖ₑ) ^ a₂ * gEbd (j - p) x₂ q₂) := by
        have hprod : ∀ p, Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
            ((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ * gEbd p x₁ q.1 *
              (((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * gEbd (j - p) x₂ q.2) := fun p =>
          ((hm1 p).comp measurable_fst).mul ((hm2 (j - p)).comp measurable_snd)
        have hterm : ∀ p ∈ range (j + 1), Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
            (j.choose p : ℝ≥0∞) * ((1 : ℝ≥0∞) + ‖x₁‖ₑ) ^ b₁ *
              (((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ * gEbd p x₁ q.1 *
                (((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * gEbd (j - p) x₂ q.2)) := fun p _ =>
          measurable_const.mul (hprod p)
        rw [lintegral_finsetSum _ hterm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lintegral_const_mul _ (hprod p), Measure.volume_eq_prod,
          lintegral_prod_mul (f := fun q₁ : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖q₁.1‖ₑ) ^ a₁ * gEbd p x₁ q₁)
            (g := fun q₂ : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖q₂.1‖ₑ) ^ a₂ * gEbd (j - p) x₂ q₂)
            (hm1 p).aemeasurable (hm2 (j - p)).aemeasurable]
      _ ≤ ∑ p ∈ range (j + 1), (j.choose p : ℝ≥0∞) * ((1 : ℝ≥0∞) + ‖x₁‖ₑ) ^ b₁ *
          (ENNReal.ofReal (D * A1 ^ p * (Nat.factorial (2 * p) : ℝ) * (1 + |x₁|) ^ (a₁ - 1)) *
            ENNReal.ofReal (D * A1 ^ (j - p) * (Nat.factorial (2 * (j - p)) : ℝ) *
              (1 + |x₂|) ^ (a₂ - 1))) := by
        gcongr with p hp
        · exact lintegral_gEbd_le ha₁ ha₁1 p x₁
        · exact lintegral_gEbd_le ha₂ ha₂1 (j - p) x₂
      _ = ∑ p ∈ range (j + 1), ENNReal.ofReal (cf p) * ENNReal.ofReal (R (α ())) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [one_add_enorm_rpow_eq, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hx1 : 0 < 1 + |x₁| := by positivity
        have e : (1 + |x₁|) ^ b₁ * (1 + |x₁|) ^ (a₁ - 1) = (1 + |x₁|) ^ (a₁ + b₁ - 1) := by
          rw [← Real.rpow_add hx1]; ring_nf
        simp only [hcf, hR]
        rw [← e]
        ring
  -- integrate in the root variable
  have hRm : Measurable fun x => ENNReal.ofReal (R x) := by simp only [hR]; fun_prop
  calc ∫⁻ α : Unit → ℝ, ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), ((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ *
        ((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * ((1 : ℝ≥0∞) + ‖α () + c₁‖ₑ) ^ b₁ *
        dnorm j (K1 c₁ c₂) α q
      ≤ ∫⁻ α : Unit → ℝ, ∑ p ∈ range (j + 1), ENNReal.ofReal (cf p) *
          ENNReal.ofReal (R (α ())) := lintegral_mono hq
    _ = ∑ p ∈ range (j + 1), ENNReal.ofReal (cf p) * ∫⁻ x : ℝ, ENNReal.ofReal (R x) := by
        rw [lintegral_unitFun (G := fun x => ∑ p ∈ range (j + 1), ENNReal.ofReal (cf p) *
          ENNReal.ofReal (R x)), lintegral_finsetSum _ fun p _ => hRm.const_mul _]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lintegral_const_mul _ hRm]
    _ ≤ ∑ p ∈ range (j + 1), ENNReal.ofReal (cf p) * ENNReal.ofReal Ip := by
        gcongr with p hp
        have h := lintegral_pair_shift_le (p₁ := 1 - a₁ - b₁) (p₂ := 1 - a₂) (by linarith)
          (by linarith) (by linarith) c₁ c₂
        have e : (1 - a₁ - b₁) + (1 - a₂) = 2 - a₁ - a₂ - b₁ := by ring
        rw [e] at h
        refine le_trans (le_of_eq ?_) h
        refine lintegral_congr fun x => ?_
        simp only [hR]
        congr 2 <;> ring_nf
    _ ≤ gev (4 * D ^ 2 * Ip) A1 j := by
        rw [gev]
        simp_rw [← ENNReal.ofReal_mul (hcf0 _)]
        rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg (hcf0 p) hI0]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsum := Combinatorics.sum_choose_factorial_le j
        calc ∑ p ∈ range (j + 1), cf p * Ip
            = D ^ 2 * A1 ^ j * Ip * ∑ p ∈ range (j + 1), (j.choose p : ℝ) *
                (Nat.factorial (2 * p) : ℝ) * (Nat.factorial (2 * (j - p)) : ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p hp => ?_
              have hpj : p ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
              have : A1 ^ j = A1 ^ p * A1 ^ (j - p) := by rw [← pow_add, Nat.add_sub_cancel' hpj]
              simp only [hcf]
              rw [this]
              ring
          _ ≤ D ^ 2 * A1 ^ j * Ip * (4 * (Nat.factorial (2 * j) : ℝ)) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = 4 * D ^ 2 * Ip * A1 ^ j * (Nat.factorial (2 * j) : ℝ) := by ring

end K1Bound

end WaveTurbulence.ClassJR
