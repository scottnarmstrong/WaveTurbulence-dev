/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCGR
public import WaveTurbulence.Foundations.ClassJR.MCType1

/-!
# Lemma G for masked parametric class `J` and class `R` operators

DH21 L1124–L1137 (Cases 2.1 and 2.2). The operator `Ĩ` of Lemma 5.10 is masked class `J` plus class
`R` (`MJR`) in the variables `α̃[W]`, with parameters `μ`. Applied to `e^{πiλ₀s}`, each basic operator
is a superposition of exponentials `e^{πiλt}` (Lemma G: `volterra_jsym_exp`, `volterra_rsym_exp`).
Summing the basic operators gives one symbol for the class `J` part and one for the class `R` part
(`LGPiece`), with
* `FRep`: regularity, (propertyH) `∫∫ (1+|λ|)^θ |∂^k H| ≤ gev N A k`, and the weighted bound of
  the proof of (maincoef2.5): `∫∫ (1+|λ|)^a (1+|α_i|)^b |H| ≤ N` for every variable `i`.

The parameters are `(μ, λ₀)`; all bounds are uniform in them.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section FRepDef

variable {ι Ξ : Type*} [Fintype ι] [MeasureSpace Ξ]

/-- **A one-time representation symbol** with frequency map `fr` on the auxiliary space. -/
structure FRep (θ a b A N : ℝ) (fr : Ξ → ℝ) (H : (ι → ℝ) → Ξ → ℂ) : Prop where
  nonneg : 0 ≤ N
  reg : SymReg H
  norm : ∀ k, ∫⁻ β, ∫⁻ ξ, (1 + ‖fr ξ‖ₑ) ^ θ * dnorm k H β ξ ≤ gev N A k
  wnorm : ∀ i, ∫⁻ β, ∫⁻ ξ, (1 + ‖fr ξ‖ₑ) ^ a * (1 + ‖β i‖ₑ) ^ b * ‖H β ξ‖ₑ ≤ ENNReal.ofReal N

theorem FRep.mono {θ a b A N N' : ℝ} {fr : Ξ → ℝ} {H : (ι → ℝ) → Ξ → ℂ}
    (h : FRep θ a b A N fr H) (hN : N ≤ N') (hA : 0 ≤ A) : FRep θ a b A N' fr H where
  nonneg := h.nonneg.trans hN
  reg := h.reg
  norm k := (h.norm k).trans (gev_mono hN hA le_rfl (h.nonneg.trans hN) k)
  wnorm i := (h.wnorm i).trans (ENNReal.ofReal_le_ofReal hN)

theorem FRep.zero {θ a b A N : ℝ} {fr : Ξ → ℝ} (hN : 0 ≤ N) :
    FRep θ a b A N fr (fun (_ : ι → ℝ) (_ : Ξ) => (0 : ℂ)) where
  nonneg := hN
  reg := symReg_zero
  norm k := by simp only [dnorm_zero_fun, mul_zero, lintegral_zero]; exact bot_le
  wnorm i := by simp only [enorm_zero, mul_zero, lintegral_zero]; exact bot_le

end FRepDef

section FinSum

theorem dnorm_finsum_le {ι Γ κ : Type*} [Fintype ι] {s : Finset κ}
    {f : κ → (ι → ℝ) → Γ → ℂ} (hf : ∀ j, ∀ γ, ContDiff ℝ ∞ fun β => f j β γ) (k : ℕ)
    (β : ι → ℝ) (γ : Γ) :
    dnorm k (fun β γ => ∑ j ∈ s, f j β γ) β γ ≤ ∑ j ∈ s, dnorm k (f j) β γ := by
  unfold dnorm
  have e : lift1 (fun β γ => ∑ j ∈ s, f j β γ) γ = fun x => ∑ j ∈ s, lift1 (f j) γ x := rfl
  rw [e, iteratedFDeriv_sum (fun j _ => (contDiff_lift1 (hf j γ)).of_le
    (by exact_mod_cast le_top))]
  simp only [Finset.sum_apply]
  exact enorm_sum_le _ _

theorem gev_finsum {κ : Type*} (s : Finset κ) {c : κ → ℝ} (hc : ∀ j, 0 ≤ c j) (A : ℝ)
    (hA : 0 ≤ A) (k : ℕ) : ∑ j ∈ s, gev (c j) A k = gev (∑ j ∈ s, c j) A k := by
  unfold gev
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => by have := hc j; positivity]
  congr 1
  rw [Finset.sum_mul, Finset.sum_mul]

end FinSum

section Weights

variable {ι : Type*} [Fintype ι]

/-- `1 + |ℓ + γ₁| ≤ 1 + Σ|α_j| + |γ₁|` for a bundle `ℓ`. -/
theorem one_add_bundle_le {y : ι → ℤ} (hy : IsBundle y) (α : ι → ℝ) (γ₁ : ℝ) :
    (1 : ℝ≥0∞) + ‖bundle y α + γ₁‖ₑ ≤ 1 + ∑ j, ‖α j‖ₑ + ‖γ₁‖ₑ := by
  rw [add_assoc]
  gcongr
  exact (enorm_add_le _ _).trans (add_le_add (abs_bundle_le hy α) le_rfl)

/-- `x^p y^q ≤ X^{p+q} ≤ X^θ` for `x, y ≤ X`, `X ≥ 1`, `p + q ≤ θ`. -/
theorem rpow_mul_rpow_le_of_le {x y X : ℝ≥0∞} {p q θ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q ≤ θ) (hX1 : 1 ≤ X) (hXt : X ≠ ⊤) (hx : x ≤ X) (hy : y ≤ X) :
    x ^ p * y ^ q ≤ X ^ θ := by
  have hX0 : X ≠ 0 := (zero_lt_one.trans_le hX1).ne'
  calc x ^ p * y ^ q ≤ X ^ p * X ^ q := mul_le_mul' (ENNReal.rpow_le_rpow hx hp)
        (ENNReal.rpow_le_rpow hy hq)
    _ = X ^ (p + q) := (ENNReal.rpow_add _ _ hX0 hXt).symm
    _ ≤ X ^ θ := ENNReal.rpow_le_rpow_of_exponent_le hX1 hpq

theorem wJ_ne_top_base (α : ι → ℝ) (γ₁ : ℝ) : (1 : ℝ≥0∞) + ∑ j, ‖α j‖ₑ + ‖γ₁‖ₑ ≠ ⊤ := by
  simp [ENNReal.add_eq_top, enorm_ne_top]

theorem one_le_wJ_base (α : ι → ℝ) (γ₁ : ℝ) : (1 : ℝ≥0∞) ≤ 1 + ∑ j, ‖α j‖ₑ + ‖γ₁‖ₑ := by
  rw [add_assoc]; exact le_self_add

end Weights

section JPiece

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]

/-- **The class `J` symbol of Lemma G** for a sum of parametric basic class `J` operators. -/
@[expose] noncomputable def aGs {n : ℕ} (R : Fin n → JSymP P ι) (p : P) (L0 : ℝ) (β : ι → ℝ)
    (ζ : ℝ × ((ℝ × ℝ) × ℝ)) : ℂ :=
  ∑ i, aG (R i).y ((R i).m p) L0 β ζ

theorem frep_aGs {θ a b A : ℝ} {n : ℕ} {R : Fin n → JSymP P ι} {c : Fin n → ℝ}
    (hR : ∀ i, (R i).Bound θ A (c i)) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ θ) (hA : A1 ≤ A) (p : P) (L0 : ℝ) :
    FRep θ a b A (12 * CE * Ir 2 * ∑ i, c i) (fun ζ => ζ.1 + ζ.2.1.1) (aGs R p L0) := by
  have hc : ∀ i, 0 ≤ c i := fun i => (hR i).nonneg
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  have hK : 0 ≤ 12 * CE * Ir 2 := by have := CE_nonneg; have := Ir2_nonneg; positivity
  have hs : ∀ i, ∀ ζ, ContDiff ℝ ∞ fun β => aG (R i).y ((R i).m p) L0 β ζ := fun i ζ =>
    contDiff_aG _ ((hR i).bound p).reg.smooth L0 ζ
  have hm : ∀ i, Measurable (Function.uncurry (aG (R i).y ((R i).m p) L0)) := fun i =>
    measurable_aG _ ((hR i).bound p).reg.meas L0
  -- the weighted bound for a weight `w ≥ 0` on the frequency and `ρ` on the variables
  have key : ∀ {a' : ℝ} (_ : 0 ≤ a') (_ : a' ≤ 1) {ρ : (ι → ℝ) → ℝ≥0∞} (_ : Measurable ρ)
      (_ : ∀ α γ₁, ρ α * ((1 : ℝ≥0∞) + ‖∑ j, ((0 : ℤ) : ℝ) * α j + γ₁‖ₑ) ^ (0 : ℝ) = ρ α)
      (_ : ∀ i α γ₁, ρ α * ((1 : ℝ≥0∞) + ‖bundle (R i).y α + γ₁‖ₑ) ^ a' ≤ wJ θ α γ₁) (k : ℕ),
      ∫⁻ β, ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ β * dnorm k (aGs R p L0) β ζ ≤
        gev (12 * CE * Ir 2 * ∑ i, c i) A k := by
    intro a' ha' ha'1 ρ hρm _ hρ k
    calc ∫⁻ β, ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ β * dnorm k (aGs R p L0) β ζ
        ≤ ∫⁻ β, ∫⁻ ζ, ∑ i, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ β *
            dnorm k (aG (R i).y ((R i).m p) L0) β ζ := by
          refine lintegral_mono fun β => lintegral_mono fun ζ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul' le_rfl (dnorm_finsum_le hs k β ζ)
      _ = ∑ i, ∫⁻ β, ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ β *
            dnorm k (aG (R i).y ((R i).m p) L0) β ζ := by
          have hmi : ∀ i, Measurable (Function.uncurry fun (β : ι → ℝ) (ζ : ℝ × ((ℝ × ℝ) × ℝ)) =>
              (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ β *
                dnorm k (aG (R i).y ((R i).m p) L0) β ζ) := fun i =>
            ((by fun_prop : Measurable fun x : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) =>
              (1 + ‖x.2.1 + x.2.2.1.1‖ₑ) ^ a').mul (hρm.comp measurable_fst)).mul
              (measurable_dnorm (hs i) (hm i).stronglyMeasurable k)
          have hmi' : ∀ i, Measurable fun β : ι → ℝ => ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ β *
              dnorm k (aG (R i).y ((R i).m p) L0) β ζ := fun i => (hmi i).lintegral_prod_right'
          rw [← lintegral_finsetSum _ fun i _ => hmi' i]
          refine lintegral_congr fun β => ?_
          exact lintegral_finsetSum _ fun i _ => (hmi i).of_uncurry_left
      _ ≤ ∑ i, gev (12 * CE * Ir 2 * c i) A k := by
          gcongr with i
          exact lintegral_weight_aG_le ha' ha'1 hA ((hR i).bound p) (hρ i) L0 k
      _ = gev (12 * CE * Ir 2 * ∑ i, c i) A k := by
          rw [gev_finsum _ (fun i => mul_nonneg hK (hc i)) A hA0, ← Finset.mul_sum]
  have hnorm : ∀ k, ∫⁻ β, ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ θ * dnorm k (aGs R p L0) β ζ ≤
      gev (12 * CE * Ir 2 * ∑ i, c i) A k := fun k => by
    have := key (a' := θ) hθ0 hθ1 (ρ := fun _ => 1) measurable_const (fun _ _ => by simp)
      (fun i α γ₁ => by
        rw [one_mul]
        exact ENNReal.rpow_le_rpow (one_add_bundle_le ((hR i).bundle) α γ₁) hθ0) k
    simpa only [mul_one] using this
  refine ⟨mul_nonneg hK (Finset.sum_nonneg fun i _ => hc i), ?_, hnorm, fun j => ?_⟩
  · have hmeas : Measurable (Function.uncurry (aGs R p L0)) := by
      change Measurable fun x : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) =>
        ∑ i, aG (R i).y ((R i).m p) L0 x.1 x.2
      exact Finset.measurable_sum _ fun i _ => hm i
    refine SymReg.of_lintegral (fun ζ => ContDiff.sum fun i _ => hs i ζ)
      hmeas.stronglyMeasurable fun k => ?_
    refine ne_top_of_le_ne_top (by simp [gev]) ((lintegral_mono fun β => lintegral_mono
      fun ζ => ?_).trans (hnorm k))
    exact le_mul_of_one_le_left bot_le (one_le_one_add_rpow hθ0 _)
  · have := key (a' := a) ha (by linarith) (ρ := fun β => (1 + ‖β j‖ₑ) ^ b) (by fun_prop)
      (fun _ _ => by simp) (fun i α γ₁ => rpow_mul_rpow_le_of_le hb ha (by linarith)
        (one_le_wJ_base α γ₁) (wJ_ne_top_base α γ₁)
        (by
          rw [add_assoc]
          gcongr
          exact (Finset.single_le_sum (f := fun j => ‖α j‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ j)).trans le_self_add)
        (one_add_bundle_le ((hR i).bundle) α γ₁)) 0
    simp only [dnorm_zero, gev_zero_eq] at this
    exact this


end JPiece

section RPiece

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]

/-- **The class `R` symbol of Lemma G** for a sum of parametric basic class `R` operators. -/
@[expose] noncomputable def aRs {n : ℕ} (R : Fin n → RSymP P ι) (p : P) (L0 : ℝ)
    (β : Option ι → ℝ) (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) : ℂ :=
  ∑ i, aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0 β ζ

/-- The constant of the class `R` symbol. -/
@[expose] noncomputable def KRs (θ a b : ℝ) : ℝ := KR θ 0 + KR a b + KR a 0

theorem KRs_nonneg (θ a b : ℝ) : 0 ≤ KRs θ a b := by
  have := KR_nonneg θ 0; have := KR_nonneg a b; have := KR_nonneg a 0
  unfold KRs; positivity

theorem wR_base_ne_top (β : ι → ℝ) (γ₁ γ₃ : ℝ) :
    (1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ₁‖ₑ + ‖γ₃‖ₑ ≠ ⊤ := by
  simp [ENNReal.add_eq_top, enorm_ne_top]

theorem one_le_wR_base (β : ι → ℝ) (γ₁ γ₃ : ℝ) :
    (1 : ℝ≥0∞) ≤ 1 + ∑ j, ‖β j‖ₑ + ‖γ₁‖ₑ + ‖γ₃‖ₑ := by
  rw [add_assoc, add_assoc]; exact le_self_add

theorem frep_aRs {θ a b A : ℝ} {n : ℕ} {R : Fin n → RSymP P ι} {c : Fin n → ℝ}
    (hR : ∀ i, (R i).Bound θ A (c i)) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (habθ : a + b ≤ θ) (hA : A1 ≤ A) (p : P) (L0 : ℝ) :
    FRep θ a b A (KRs θ a b * ∑ i, c i) (fun ζ => ζ.1 + ζ.2.1.1) (aRs R p L0) := by
  have hc : ∀ i, 0 ≤ c i := fun i => (hR i).nonneg
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  have hs : ∀ i, ∀ ζ, ContDiff ℝ ∞ fun β => aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0 β ζ :=
    fun i ζ => contDiff_aR _ _ _ ((hR i).bound p).reg.smooth L0 ζ
  have hm : ∀ i, Measurable (Function.uncurry (aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0)) :=
    fun i => measurable_aR _ _ _ ((hR i).bound p).reg.meas L0
  have hSc : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  -- the weighted bound
  have key : ∀ {a' b' : ℝ} (_ : 0 ≤ a') (_ : 0 ≤ b') (_ : a' + b' < 1)
      {ρ : (ι → ℝ) → ℝ≥0∞} (_ : Measurable ρ)
      (_ : ∀ β γ₁ γ₃, ρ β * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ (a' + b') ≤
        wR θ β γ₁ γ₃) (k : ℕ),
      ∫⁻ β, ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ (nsp β) * (1 + ‖β none‖ₑ) ^ b' *
        dnorm k (aRs R p L0) β ζ ≤ gev (KR a' b' * ∑ i, c i) A k := by
    intro a' b' ha' hb' hab' ρ hρm hρ k
    have hmi : ∀ i, Measurable (Function.uncurry fun (β : Option ι → ℝ)
        (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) => (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ (nsp β) *
          (1 + ‖β none‖ₑ) ^ b' * dnorm k (aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0) β ζ) :=
      fun i => (((by fun_prop : Measurable fun x : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
        (1 + ‖x.2.1 + x.2.2.1.1‖ₑ) ^ a').mul (hρm.comp (measurable_nsp.comp measurable_fst))).mul
        (by fun_prop)).mul (measurable_dnorm (hs i) (hm i).stronglyMeasurable k)
    have hmi' : ∀ i, Measurable fun β : Option ι → ℝ => ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' *
        ρ (nsp β) * (1 + ‖β none‖ₑ) ^ b' *
          dnorm k (aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0) β ζ :=
      fun i => (hmi i).lintegral_prod_right'
    calc ∫⁻ β, ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ (nsp β) * (1 + ‖β none‖ₑ) ^ b' *
          dnorm k (aRs R p L0) β ζ
        ≤ ∫⁻ β, ∫⁻ ζ, ∑ i, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ (nsp β) * (1 + ‖β none‖ₑ) ^ b' *
            dnorm k (aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0) β ζ := by
          refine lintegral_mono fun β => lintegral_mono fun ζ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul' le_rfl (dnorm_finsum_le hs k β ζ)
      _ = ∑ i, ∫⁻ β, ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a' * ρ (nsp β) * (1 + ‖β none‖ₑ) ^ b' *
            dnorm k (aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0) β ζ := by
          rw [← lintegral_finsetSum _ fun i _ => hmi' i]
          refine lintegral_congr fun β => ?_
          exact lintegral_finsetSum _ fun i _ => (hmi i).of_uncurry_left
      _ ≤ ∑ i, gev (KR a' b' * c i) A k := by
          gcongr with i
          exact lintegral_weight_aR_le ha' hb' hab' hA ((hR i).bound p) hρm hρ L0 k
      _ = gev (KR a' b' * ∑ i, c i) A k := by
          rw [gev_finsum _ (fun i => mul_nonneg (KR_nonneg a' b') (hc i)) A hA0, ← Finset.mul_sum]
  have hle : ∀ {x : ℝ}, x ≤ KRs θ a b → x * ∑ i, c i ≤ KRs θ a b * ∑ i, c i := fun hx =>
    mul_le_mul_of_nonneg_right hx hSc
  have h1 : KR θ 0 ≤ KRs θ a b := by
    have := KR_nonneg a b; have := KR_nonneg a 0; unfold KRs; linarith
  have h2 : KR a b ≤ KRs θ a b := by
    have := KR_nonneg θ 0; have := KR_nonneg a 0; unfold KRs; linarith
  have h3 : KR a 0 ≤ KRs θ a b := by
    have := KR_nonneg θ 0; have := KR_nonneg a b; unfold KRs; linarith
  have hnorm : ∀ k, ∫⁻ β, ∫⁻ ζ, (1 + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ θ * dnorm k (aRs R p L0) β ζ ≤
      gev (KRs θ a b * ∑ i, c i) A k := fun k => by
    have := key (a' := θ) (b' := 0) hθ0 le_rfl (by linarith) (ρ := fun _ => 1) measurable_const
      (fun β γ₁ γ₃ => by rw [one_mul, add_zero]; rfl) k
    simp only [mul_one, ENNReal.rpow_zero] at this
    exact this.trans (gev_mono (hle h1) hA0 le_rfl (mul_nonneg (KRs_nonneg θ a b) hSc) k)
  refine ⟨mul_nonneg (KRs_nonneg θ a b) hSc, ?_, hnorm, fun j => ?_⟩
  · have hmeas : Measurable (Function.uncurry (aRs R p L0)) := by
      change Measurable fun x : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
        ∑ i, aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0 x.1 x.2
      exact Finset.measurable_sum _ fun i _ => hm i
    refine SymReg.of_lintegral (fun ζ => ContDiff.sum fun i _ => hs i ζ)
      hmeas.stronglyMeasurable fun k => ?_
    refine ne_top_of_le_ne_top (by simp [gev]) ((lintegral_mono fun β => lintegral_mono
      fun ζ => ?_).trans (hnorm k))
    exact le_mul_of_one_le_left bot_le (one_le_one_add_rpow hθ0 _)
  · rcases j with _ | j
    · have := key (a' := a) (b' := b) ha hb hab (ρ := fun _ => 1) measurable_const
        (fun β γ₁ γ₃ => by
          rw [one_mul]
          exact ENNReal.rpow_le_rpow_of_exponent_le (one_le_wR_base β γ₁ γ₃) habθ) 0
      simp only [mul_one, dnorm_zero, gev_zero_eq] at this
      exact this.trans (ENNReal.ofReal_le_ofReal (hle h2))
    · have := key (a' := a) (b' := 0) ha le_rfl (by linarith)
        (ρ := fun β => (1 + ‖β j‖ₑ) ^ b) (by fun_prop)
        (fun β γ₁ γ₃ => by
          rw [add_zero, mul_comm]
          refine rpow_mul_rpow_le_of_le ha hb habθ (one_le_wR_base β γ₁ γ₃)
            (wR_base_ne_top β γ₁ γ₃) le_rfl ?_
          rw [add_assoc, add_assoc]
          gcongr
          exact (Finset.single_le_sum (f := fun j => ‖β j‖ₑ) (fun _ _ => zero_le)
            (Finset.mem_univ j)).trans le_self_add) 0
      simp only [ENNReal.rpow_zero, mul_one, dnorm_zero, gev_zero_eq] at this
      exact this.trans (ENNReal.ofReal_le_ofReal (hle h3))


end RPiece

section Volterra

theorem volterra_congr_kernel {K K' : ℝ → ℝ → ℂ} (h : KEqOn K K') (g : ℝ → ℂ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : volterra K g t = volterra K' g t := by
  unfold volterra
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  simp only [h t s hs.1 hs.2 ht.2]

theorem volterra_finsum {κ : Type*} (s : Finset κ) (K : κ → ℝ → ℝ → ℂ)
    (hK : ∀ i, Continuous fun p : ℝ × ℝ => K i p.1 p.2) {g : ℝ → ℂ} (hg : Continuous g) (t : ℝ) :
    volterra (fun t s' => ∑ i ∈ s, K i t s') g t = ∑ i ∈ s, volterra (K i) g t := by
  unfold volterra
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i _ =>
    (((hK i).comp (continuous_const.prodMk continuous_id)).mul hg).intervalIntegrable _ _

theorem volterra_add {K₁ K₂ : ℝ → ℝ → ℂ} (h₁ : Continuous fun p : ℝ × ℝ => K₁ p.1 p.2)
    (h₂ : Continuous fun p : ℝ × ℝ => K₂ p.1 p.2) {g : ℝ → ℂ} (hg : Continuous g) (t : ℝ) :
    volterra (fun t s => K₁ t s + K₂ t s) g t = volterra K₁ g t + volterra K₂ g t := by
  have := volterra_finsum Finset.univ ![K₁, K₂] (fun i => by fin_cases i <;> simpa) hg t
  simpa [Fin.sum_univ_two] using this

theorem continuous_cexp_L0 (L0 : ℝ) : Continuous fun s : ℝ => cexp (π * I * (L0 * s)) := by
  fun_prop

end Volterra

section Pieces

variable {P : Type*} [MeasurableSpace P] {V : Type}

/-- **One piece of Lemma G**: the function `G(p, λ₀, α, t)` is, for `t ∈ [0, 1]`,
`∫ H(p, λ₀; α ∘ f, ξ) e^{πi fr(ξ) t} dξ` for a symbol `H` on `ℝ × Ξ` with `FRep` bounds uniform in
`(p, λ₀)`, where the frequency is a shear `fr(u, η) = u + b(η)` (in Lemma G, `u = v` and `b(η) = γ₁`). -/
@[expose] def LGPiece (θ a b A N : ℝ) (S : Set V) (G : P → ℝ → (V → ℝ) → ℝ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : ι → V) (Ξ : Type) (_ : MeasureSpace Ξ)
    (_ : SFinite (volume : Measure Ξ)) (bfr : Ξ → ℝ) (H : P → ℝ → (ι → ℝ) → ℝ × Ξ → ℂ),
    Function.Injective f ∧ Set.range f = S ∧ Measurable bfr ∧
    (∀ p L0, FRep θ a b A N (fun ξ => ξ.1 + bfr ξ.2) (H p L0)) ∧
    Measurable (fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × Ξ)) => H x.1.1 x.1.2 x.2.1 x.2.2) ∧
    ∀ p L0 α, ∀ t ∈ Icc (0 : ℝ) 1,
      G p L0 α t = ∫ ξ, H p L0 (α ∘ f) ξ * cexp (π * I * ((ξ.1 + bfr ξ.2) * t))

variable {θ a b A N : ℝ} {S : Set V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ}

/-- **Lemma G for masked parametric class `J`** (DH21 Case 2.1, (expandH), (propertyH)). -/
theorem MJ.lgpiece (hT : MJ θ A N S T) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ θ) (hA : A1 ≤ A) :
    LGPiece θ a b A (12 * CE * Ir 2 * N) S
      (fun p L0 α t => volterra (T p α) (fun s => cexp (π * I * (L0 * s))) t) := by
  obtain ⟨ι, hι, f, hf, hr, T', hT', he⟩ := hT
  obtain ⟨n, R, c, hbd, hs, he'⟩ := hT'
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  have hK : 0 ≤ 12 * CE * Ir 2 := by have := CE_nonneg; have := Ir2_nonneg; positivity
  refine ⟨ι, hι, f, (ℝ × ℝ) × ℝ, inferInstance, inferInstance, fun η => η.1.1,
    fun p L0 => aGs R p L0, hf, hr, by fun_prop,
    fun p L0 => (frep_aGs hbd hθ0 hθ1 ha hb hab hA p L0).mono
      (mul_le_mul_of_nonneg_left hs hK) hA0, ?_, fun p L0 α t ht => ?_⟩
  · change Measurable fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ))) =>
      ∑ i, (R i).m x.1.1 x.2.1 x.2.2.2.1 * gE (x.2.2.2.1.2 + x.1.2 - bundle (R i).y x.2.1)
        (x.2.2.1 - bundle (R i).y x.2.1, x.2.2.2.2)
    refine Finset.measurable_sum _ fun i _ => ?_
    have h1 : Measurable fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ))) =>
        (R i).m x.1.1 x.2.1 x.2.2.2.1 := (hbd i).meas.measurable.comp
      (f := fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ))) => (x.1.1, (x.2.1, x.2.2.2.1)))
      (by fun_prop)
    have h2 : Measurable fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ))) =>
        gE (x.2.2.2.1.2 + x.1.2 - bundle (R i).y x.2.1)
          (x.2.2.1 - bundle (R i).y x.2.1, x.2.2.2.2) :=
      measurable_gE.comp (f := fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ))) =>
        (x.2.2.2.1.2 + x.1.2 - bundle (R i).y x.2.1,
          (x.2.2.1 - bundle (R i).y x.2.1, x.2.2.2.2))) (by fun_prop)
    exact h1.mul h2
  · beta_reduce
    rw [volterra_congr_kernel (he p α) _ ht, volterra_congr_kernel (he' p (α ∘ f)) _ ht,
      volterra_finsum _ _ (fun i => JSym.continuous_kernel _ ((hbd i).bound p).reg _)
        (continuous_cexp_L0 L0)]
    have e : ∀ i, volterra (((R i).get p).kernel (α ∘ f)) (fun s => cexp (π * I * (L0 * s))) t =
        ∫ ζ, aG (R i).y ((R i).m p) L0 (α ∘ f) ζ * cexp (π * I * ((ζ.1 + ζ.2.1.1) * t)) :=
      fun i => volterra_jsym_exp _ ((hbd i).bound p).reg _ L0 ht
    simp_rw [e]
    rw [← integral_finsetSum _ fun i _ => ?_]
    · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
      simp only [aGs, Finset.sum_mul]
    · refine (integrable_aG _ ((hbd i).bound p).reg L0 _).mul_bdd (c := 1) (by fun_prop)
        (Eventually.of_forall fun ζ => ?_)
      rw [Complex.norm_exp]; simp

/-- **Lemma G for masked parametric class `R`** (DH21 Case 2.2, (expandG1), (propertyG1)). -/
theorem MR0.lgpiece (hT : MR0 θ A N S T) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A) :
    LGPiece θ a b A (KRs θ a b * N) S
        (fun p L0 α t => volterra (T p α) (fun s => cexp (π * I * (L0 * s))) t) ∨
      ∀ (p : P) (L0 : ℝ) (α : V → ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
        volterra (T p α) (fun s => cexp (π * I * (L0 * s))) t = 0 := by
  rcases hT with ⟨v₀, ι, hι, f, hf, hr, -, T', hT', he⟩ | ⟨-, hz⟩
  · left
    obtain ⟨n, R, c, hbd, hs, he'⟩ := hT'
    have hA0 : 0 ≤ A := A1_nonneg.trans hA
    refine ⟨Option ι, inferInstance, f, (ℝ × ℝ × ℝ) × ℝ, inferInstance, inferInstance,
      fun η => η.1.1, fun p L0 => aRs R p L0, hf, hr, by fun_prop,
      fun p L0 => (frep_aRs hbd hθ0 hθ1 ha hb hab1 hab hA p L0).mono
        (mul_le_mul_of_nonneg_left hs (KRs_nonneg θ a b)) hA0, ?_, fun p L0 α t ht => ?_⟩
    · change Measurable fun x : (P × ℝ) × ((Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ))) =>
        ∑ i, (R i).m x.1.1 (nsp x.2.1) x.2.2.2.1 *
          (chiInvR (bundle (R i).y₁ (nsp x.2.1) + (R i).ε * x.2.1 none + x.2.2.2.1.2.2) : ℂ) *
          gE (x.2.2.2.1.2.1 + x.1.2 - (bundle (R i).y₂ (nsp x.2.1) + (R i).ε * x.2.1 none))
            (x.2.2.1 - (bundle (R i).y₂ (nsp x.2.1) + (R i).ε * x.2.1 none), x.2.2.2.2)
      refine Finset.measurable_sum _ fun i _ => ?_
      have h1 : Measurable fun x : (P × ℝ) × ((Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ))) =>
          (R i).m x.1.1 (nsp x.2.1) x.2.2.2.1 := (hbd i).meas.measurable.comp
        (f := fun x : (P × ℝ) × ((Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ))) =>
          (x.1.1, (nsp x.2.1, x.2.2.2.1))) (by fun_prop)
      have h2 : Measurable fun x : (P × ℝ) × ((Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ))) =>
          (chiInvR (bundle (R i).y₁ (nsp x.2.1) + (R i).ε * x.2.1 none + x.2.2.2.1.2.2) : ℂ) :=
        Complex.measurable_ofReal.comp (measurable_chiInvR.comp
          (f := fun x : (P × ℝ) × ((Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ))) =>
            bundle (R i).y₁ (nsp x.2.1) + (R i).ε * x.2.1 none + x.2.2.2.1.2.2) (by fun_prop))
      have h3 : Measurable fun x : (P × ℝ) × ((Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ))) =>
          gE (x.2.2.2.1.2.1 + x.1.2 - (bundle (R i).y₂ (nsp x.2.1) + (R i).ε * x.2.1 none))
            (x.2.2.1 - (bundle (R i).y₂ (nsp x.2.1) + (R i).ε * x.2.1 none), x.2.2.2.2) :=
        measurable_gE.comp
          (f := fun x : (P × ℝ) × ((Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ))) =>
            (x.2.2.2.1.2.1 + x.1.2 - (bundle (R i).y₂ (nsp x.2.1) + (R i).ε * x.2.1 none),
              (x.2.2.1 - (bundle (R i).y₂ (nsp x.2.1) + (R i).ε * x.2.1 none), x.2.2.2.2)))
          (by fun_prop)
      exact (h1.mul h2).mul h3
    · beta_reduce
      rw [volterra_congr_kernel (he p α) _ ht, volterra_congr_kernel (he' p (α ∘ f)) _ ht,
        volterra_finsum _ _ (fun i => RSym.continuous_kernel _ ((hbd i).bound p) _)
          (continuous_cexp_L0 L0)]
      have e : ∀ i, volterra (((R i).get p).kernel (α ∘ f)) (fun s => cexp (π * I * (L0 * s))) t =
          ∫ ζ, aR (R i).y₁ (R i).y₂ (R i).ε ((R i).m p) L0 (α ∘ f) ζ *
            cexp (π * I * ((ζ.1 + ζ.2.1.1) * t)) :=
        fun i => volterra_rsym_exp _ ((hbd i).bound p).reg _ L0 ht
      simp_rw [e]
      rw [← integral_finsetSum _ fun i _ => ?_]
      · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
        simp only [aRs, Finset.sum_mul]
      · have hreg := aR_symReg hθ0 hA ((hbd i).bound p) L0
        refine (hreg.integrable _).mul_bdd (c := 1) (by fun_prop)
          (Eventually.of_forall fun ζ => ?_)
        rw [Complex.norm_exp]; simp
  · right
    intro p L0 α t ht
    rw [volterra_congr_kernel (hz p α) _ ht]
    simp [volterra]


/-- **Lemma G for masked class `J` plus class `R`** (DH21 L1124–L1137): the operator applied to
`e^{πiλ₀s}` is the sum of a class `J` piece and a class `R` piece (or zero). -/
theorem MJR.lgpieces (hT : MJR θ A N S T) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A) :
    ∃ (GJ GR : P → ℝ → (V → ℝ) → ℝ → ℂ) (NJ NR : ℝ), 0 ≤ NJ ∧ 0 ≤ NR ∧ NJ + NR ≤ N ∧
      LGPiece θ a b A (12 * CE * Ir 2 * NJ) S GJ ∧
      (LGPiece θ a b A (KRs θ a b * NR) S GR ∨
        ∀ (p : P) (L0 : ℝ) (α : V → ℝ), ∀ t ∈ Icc (0 : ℝ) 1, GR p L0 α t = 0) ∧
      ∀ (p : P) (L0 : ℝ) (α : V → ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
        volterra (T p α) (fun s => cexp (π * I * (L0 * s))) t = GJ p L0 α t + GR p L0 α t := by
  obtain ⟨NJ, NR, TJ, TR, hJ, hR, hN, he⟩ := hT
  refine ⟨fun p L0 α t => volterra (TJ p α) (fun s => cexp (π * I * (L0 * s))) t,
    fun p L0 α t => volterra (TR p α) (fun s => cexp (π * I * (L0 * s))) t, NJ, NR,
    hJ.nonneg, hR.nonneg, hN, hJ.lgpiece hθ0 hθ1.le ha hb hab hA,
    hR.lgpiece hθ0 hθ1 ha hb hab1 hab hA, fun p L0 α t ht => ?_⟩
  obtain ⟨KJ, hKJc, hKJ⟩ := hJ.exists_rep p α
  obtain ⟨KR, hKRc, hKR⟩ := hR.exists_rep p α
  have hsum : KEqOn (T p α) fun t s => KJ t s + KR t s := fun t s h0 h1 h2 => by
    rw [he p α t s h0 h1 h2]
    beta_reduce
    rw [hKJ t s h0 h1 h2, hKR t s h0 h1 h2]
  rw [volterra_congr_kernel hsum _ ht, volterra_add hKJc hKRc (continuous_cexp_L0 L0),
    ← volterra_congr_kernel hKJ _ ht, ← volterra_congr_kernel hKR _ ht]

end Pieces

end WaveTurbulence.ClassJR
