/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainT
public import WaveTurbulence.Foundations.ClassJR.MCSum
public import WaveTurbulence.Foundations.ClassJR.CompJJ

/-!
# Rebasing a chain at the time `s` (DH21 Proposition 6.10)

For a regular tree, the coefficient of DH21 (varat) is a chain integral over
`t > t₁ > ⋯ > t_{2m} > s`: the lone leaf hangs from the last chain node, whose time exceeds `s`. In the
continuation-passing form `chainT`, this is a continuation vanishing below `s`. Since every pair `{a, b}`
of the chain has opposite phases `e^{±πiε_jα_jt}` (DH21 L930: `β_b = -β_a`), shifting all times by `s`
leaves the phases unchanged, and the chain integral is the chain integral over `(0, t - s)` with the
pair coefficients evaluated at the shifted times (`chainT_rebase`). This is DH21's "for `t > s`"
(L1705–L1708). The zero lemma `chainT_eq_zero_of_le` says the chain vanishes for `t ≤ s`.

A coefficient of the rebased chain is a function of `(t - s, s)`. `MCRep.sub_time` turns a
representation `∫ 𝒞(λ) e^{πi(λ₁τ + λ₂s)}` in `(τ, s)` into one in `(t, s)`, with the symbol
`𝒞(λ₁, λ₂ + λ₁)` and twice the constant: the DH23 weights `⟨max(λ₁,λ₂)⟩` are invariant under the shear
up to a factor `2` (DH21 L1707: the weights become `(⟨λ₁⟩ + ⟨λ₂⟩)`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Rebase

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

/-- An interval integral does not see a piece where the integrand vanishes. -/
theorem intervalIntegral_eq_of_eq_zero {f : ℝ → ℂ} {c : ℝ} (h0 : ∀ x ∈ uIcc 0 c, f x = 0)
    (u : ℝ) : ∫ x in c..u, f x = ∫ x in (0 : ℝ)..u, f x := by
  have hz : IntervalIntegrable f volume c 0 := by
    rw [intervalIntegrable_iff]
    refine (integrableOn_zero (ε' := ℂ)).congr_fun (fun x hx => (h0 x ?_).symm)
      measurableSet_uIoc
    rw [Set.uIcc_comm]
    exact Set.uIoc_subset_uIcc hx
  have hz0 : ∫ x in c..0, f x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun x hx =>
      h0 x (by rwa [Set.uIcc_comm] at hx)]
    simp
  by_cases hi : IntervalIntegrable f volume 0 u
  · rw [← intervalIntegral.integral_add_adjacent_intervals hz hi, hz0, zero_add]
  · rw [intervalIntegral.integral_undef hi, intervalIntegral.integral_undef]
    exact fun h => hi (hz.symm.trans h)

/-- **The chain vanishes below `s`** when its continuation does (`0 ≤ s`). -/
theorem chainT_eq_zero_of_le : ∀ (c : LegalCode) (q : ℕ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ)
    (α : V → ℝ) {s : ℝ} (_ : 0 ≤ s) {g : ℝ → ℂ} (_ : ∀ t' ≤ s, g t' = 0) {t : ℝ} (_ : t ≤ s),
    chainT σ ε c q F α t g = 0
  | .nil, _, _, _, _, _, _, hg, t, ht => hg t ht
  | .node i r, q, F, α, s, hs, g, hg, t, ht => by
    rw [chainT_node]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun ta hta => ?_]
    · simp
    have hta' : ta ≤ s := (Set.mem_uIcc.1 hta).elim (fun h => h.2.trans ht)
      (fun h => h.2.trans hs)
    have hk : ∀ t' ≤ s, (∫ tb in (0 : ℝ)..t', cexp (π * I * (-(ε q * α (σ q)) * tb)) *
        F q α ta tb * chainT σ ε r (q + i.size + 1) F α tb g) = 0 := fun t' ht' => by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun tb htb => ?_]
      · simp
      have htb' : tb ≤ s := (Set.mem_uIcc.1 htb).elim (fun h => h.2.trans ht')
        (fun h => h.2.trans hs)
      simp only
      rw [chainT_eq_zero_of_le r _ F α hs hg htb', mul_zero]
    simp only
    rw [chainT_eq_zero_of_le i (q + 1) F α hs hk hta', mul_zero]

/-- **Rebasing the chain at `s`** (DH21 Proposition 6.10, "for `t > s`"): for a continuation vanishing
below `s ≥ 0` and `t ≥ s`, the chain integral is the chain integral over `(0, t - s)` with the pair
coefficients at the shifted times. The phases of each pair cancel under the shift. -/
theorem chainT_rebase : ∀ (c : LegalCode) (q : ℕ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (α : V → ℝ)
    {s : ℝ} (_ : 0 ≤ s) {g : ℝ → ℂ} (_ : ∀ t' ≤ s, g t' = 0) {t : ℝ} (_ : s ≤ t),
    chainT σ ε c q F α t g =
      chainT σ ε c q (fun j β u v => F j β (u + s) (v + s)) α (t - s) (fun u => g (u + s))
  | .nil, _, _, _, s, _, g, _, t, _ => by
    simp only [chainT_nil, sub_add_cancel]
  | .node i r, q, F, α, s, hs, g, hg, t, hst => by
    set β : ℝ := ε q * α (σ q) with hβ
    set Y : ℝ → ℝ → ℂ := fun ta tb =>
      cexp (π * I * (-(ε q * α (σ q)) * tb)) * F q α ta tb * chainT σ ε r (q + i.size + 1) F α tb g
      with hY
    set Fs : ℕ → (V → ℝ) → ℝ → ℝ → ℂ := fun j β u v => F j β (u + s) (v + s) with hFs
    -- the continuations vanish below `s`
    have hY0 : ∀ ta tb, tb ≤ s → Y ta tb = 0 := fun ta tb htb => by
      simp only [hY]
      rw [chainT_eq_zero_of_le r _ F α hs hg htb, mul_zero]
    have hk0 : ∀ ta, ∀ t' ≤ s, (∫ tb in (0 : ℝ)..t', Y ta tb) = 0 := fun ta t' ht' => by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun tb htb =>
        hY0 ta tb ((Set.mem_uIcc.1 htb).elim (fun h => h.2.trans ht') (fun h => h.2.trans hs))]
      simp
    -- the rest of the chain, rebased
    have hrest : ∀ v, chainT σ ε r (q + i.size + 1) F α (v + s) g =
        chainT σ ε r (q + i.size + 1) Fs α v (fun u => g (u + s)) := fun v => by
      by_cases hv : 0 ≤ v
      · have h := chainT_rebase r (q + i.size + 1) F α hs hg (t := v + s) (by linarith)
        simpa only [add_sub_cancel_right] using h
      · push Not at hv
        rw [chainT_eq_zero_of_le r _ F α hs hg (by linarith),
          chainT_eq_zero_of_le r _ Fs α le_rfl (fun u hu => hg _ (by linarith)) hv.le]
    -- the continuation of the inner block, rebased
    have hcont : ∀ ta, (fun u' => ∫ tb in (0 : ℝ)..(u' + s), Y ta tb) = fun u' =>
        cexp (π * I * (-β * s)) * ∫ v in (0 : ℝ)..u', cexp (π * I * (-(ε q * α (σ q)) * v)) *
          F q α ta (v + s) * chainT σ ε r (q + i.size + 1) Fs α v (fun u => g (u + s)) := by
      intro ta
      funext u'
      have e1 : ∫ tb in (0 : ℝ)..(u' + s), Y ta tb = ∫ v in (-s)..u', Y ta (v + s) := by
        rw [intervalIntegral.integral_comp_add_right (fun tb => Y ta tb) s, neg_add_cancel]
      rw [e1, intervalIntegral_eq_of_eq_zero (fun v hv => hY0 ta _ (by
        rcases Set.mem_uIcc.1 hv with h | h <;> linarith [h.1, h.2])) u',
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v _ => ?_
      simp only [hY, hrest v]
      have e2 : cexp (π * I * (-(ε q * α (σ q)) * (v + s : ℝ))) =
          cexp (π * I * (-β * s)) * cexp (π * I * (-(ε q * α (σ q)) * v)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; rw [hβ]; push_cast; ring
      rw [e2]
      ring
    -- the outer integral
    rw [chainT_node, chainT_node]
    set X : ℝ → ℂ := fun ta => cexp (π * I * (ε q * α (σ q) * ta)) *
        chainT σ ε i (q + 1) F α ta (fun t' => ∫ tb in (0 : ℝ)..t', Y ta tb) with hX
    have hX0 : ∀ ta ∈ uIcc 0 s, X ta = 0 := fun ta hta => by
      simp only [hX]
      rw [chainT_eq_zero_of_le i (q + 1) F α hs (hk0 ta)
        ((Set.mem_uIcc.1 hta).elim (fun h => h.2) (fun h => h.2.trans hs)), mul_zero]
    have hsub : ∫ ta in s..t, X ta = ∫ u in (0 : ℝ)..(t - s), X (u + s) := by
      rw [intervalIntegral.integral_comp_add_right X s, zero_add, sub_add_cancel]
    rw [← intervalIntegral_eq_of_eq_zero hX0 t, hsub]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by
      rcases Set.mem_uIcc.1 hu with h | h
      · exact h.1
      · linarith [h.1, h.2]
    simp only [hX]
    have hinner := chainT_rebase i (q + 1) F α hs (hk0 (u + s)) (t := u + s) (by linarith)
    rw [add_sub_cancel_right] at hinner
    rw [hinner, hcont (u + s), chainT_const_mul]
    have e3 : cexp (π * I * (ε q * α (σ q) * (u + s : ℝ))) * cexp (π * I * (-β * s)) =
        cexp (π * I * (ε q * α (σ q) * u)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; rw [hβ]; push_cast; ring
    rw [← mul_assoc, e3]

end Rebase


section Shear

variable {V : Type} {θ a b A N : ℝ}

theorem shearAddRight_apply (lam : ℝ × ℝ) :
    MeasurableEquiv.shearAddRight ℝ lam = (lam.1, lam.1 + lam.2) := rfl

theorem measurePreserving_shearAddRight :
    MeasurePreserving (MeasurableEquiv.shearAddRight ℝ) (volume : Measure (ℝ × ℝ)) volume := by
  rw [Measure.volume_eq_prod]
  exact measurePreserving_prod_add volume volume

/-- The DH23 weights under the shear `(λ₁, λ₂) ↦ (λ₁, λ₁ + λ₂)`. -/
theorem wL_le_two_mul_wL_shear {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (lam : ℝ × ℝ) :
    wL c lam ≤ 2 * wL c (MeasurableEquiv.shearAddRight ℝ lam) := by
  rw [shearAddRight_apply]
  unfold wL
  have h2 : (2 : ℝ≥0∞) = 2 ^ (1 : ℝ) := by simp
  have hle : (1 : ℝ≥0∞) + ‖lam.1‖ₑ + ‖lam.2‖ₑ ≤ 2 * (1 + ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ) := by
    have ht : ‖lam.2‖ₑ ≤ ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ := by
      calc ‖lam.2‖ₑ = ‖-lam.1 + (lam.1 + lam.2)‖ₑ := by ring_nf
        _ ≤ ‖-lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ := enorm_add_le _ _
        _ = ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ := by rw [enorm_neg]
    calc (1 : ℝ≥0∞) + ‖lam.1‖ₑ + ‖lam.2‖ₑ ≤ 1 + ‖lam.1‖ₑ + (‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ) := by
          gcongr
      _ = (1 + ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ) + ‖lam.1‖ₑ := by ring
      _ ≤ (1 + ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ) + (1 + ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ) := by
          gcongr; exact le_add_right le_add_self
      _ = 2 * (1 + ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ) := (two_mul _).symm
  calc ((1 : ℝ≥0∞) + ‖lam.1‖ₑ + ‖lam.2‖ₑ) ^ c ≤ (2 * (1 + ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ)) ^ c :=
        ENNReal.rpow_le_rpow hle hc
    _ = 2 ^ c * (1 + ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ) ^ c := ENNReal.mul_rpow_of_nonneg _ _ hc
    _ ≤ 2 * (1 + ‖lam.1‖ₑ + ‖lam.1 + lam.2‖ₑ) ^ c := by
        gcongr
        calc (2 : ℝ≥0∞) ^ c ≤ 2 ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hc1
          _ = 2 := by simp

/-- **Rebasing a representation**: if `F(α, τ, s) = ∫ 𝒞(λ) e^{πi(λ₁τ + λ₂s)}`, then
`(t, s) ↦ F(α, t - s, s)` is, for `0 ≤ s ≤ t ≤ 1`, the representation with the sheared symbol
`𝒞(λ₁, λ₁ + λ₂)`, with twice the constant. -/
theorem MCRep.sub_time {S : Set V} {F : (V → ℝ) → ℝ → ℝ → ℂ} (h : MCRep θ a b A N S F)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ F' : (V → ℝ) → ℝ → ℝ → ℂ, MCRep θ a b A (2 * N) S F' ∧
      ∀ α t s, 0 ≤ s → s ≤ t → t ≤ 1 → F' α t s = F α (t - s) s := by
  obtain ⟨ι, hι, f, C, hf, hr, hN, hreg, hn, hw, he⟩ := h
  set E := MeasurableEquiv.shearAddRight ℝ with hE
  have hmp := measurePreserving_shearAddRight
  have hd : ∀ k β lam, dnorm k (fun β lam => C β (E lam)) β lam = dnorm k C β (E lam) :=
    fun _ _ _ => rfl
  refine ⟨fun α t s => ∫ lam, C (α ∘ f) (E lam) * e2 lam t s,
    ⟨ι, hι, f, fun β lam => C β (E lam), hf, hr, by positivity, hreg.comp_equiv E hmp,
      fun k => ?_, fun i => ?_, fun α t s _ _ => rfl⟩, fun α t s hs hst ht1 => ?_⟩
  · calc ∫⁻ β, ∫⁻ lam, wL θ lam * dnorm k (fun β lam => C β (E lam)) β lam
        ≤ ∫⁻ β, ∫⁻ lam, 2 * (wL θ (E lam) * dnorm k C β (E lam)) :=
          lintegral_mono fun β => lintegral_mono fun lam => by
            rw [hd, ← mul_assoc]
            exact mul_le_mul' (wL_le_two_mul_wL_shear hθ hθ1 lam) le_rfl
      _ = 2 * ∫⁻ β, ∫⁻ mu, wL θ mu * dnorm k C β mu := by
          rw [← lintegral_const_mul' _ _ (by simp)]
          refine lintegral_congr fun β => ?_
          rw [lintegral_const_mul' _ _ (by simp),
            hmp.lintegral_comp_emb E.measurableEmbedding (fun mu => wL θ mu * dnorm k C β mu)]
      _ ≤ 2 * gev N A k := by gcongr; exact hn k
      _ = gev (2 * N) A k := gev_two_mul N A k
  · calc ∫⁻ β, ∫⁻ lam, wL a lam * (1 + ‖β i‖ₑ) ^ b * ‖C β (E lam)‖ₑ
        ≤ ∫⁻ β, ∫⁻ lam, 2 * (wL a (E lam) * (1 + ‖β i‖ₑ) ^ b * ‖C β (E lam)‖ₑ) :=
          lintegral_mono fun β => lintegral_mono fun lam => by
            rw [← mul_assoc, ← mul_assoc]
            exact mul_le_mul' (mul_le_mul' (wL_le_two_mul_wL_shear ha ha1 lam) le_rfl) le_rfl
      _ = 2 * ∫⁻ β, ∫⁻ mu, wL a mu * (1 + ‖β i‖ₑ) ^ b * ‖C β mu‖ₑ := by
          rw [← lintegral_const_mul' _ _ (by simp)]
          refine lintegral_congr fun β => ?_
          rw [lintegral_const_mul' _ _ (by simp), hmp.lintegral_comp_emb E.measurableEmbedding
            (fun mu => wL a mu * (1 + ‖β i‖ₑ) ^ b * ‖C β mu‖ₑ)]
      _ ≤ 2 * ENNReal.ofReal N := by gcongr; exact hw i
      _ = ENNReal.ofReal (2 * N) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
  · have hte : ∀ lam, e2 lam t s = e2 (E lam) (t - s) s := fun lam => by
      rw [hE, shearAddRight_apply]
      unfold e2
      congr 1
      push_cast
      ring
    simp_rw [hte]
    rw [hmp.integral_comp E.measurableEmbedding (fun mu => C (α ∘ f) mu * e2 mu (t - s) s)]
    exact (he α (t - s) s ⟨by linarith, by linarith⟩ ⟨hs, by linarith⟩).symm

end Shear

end WaveTurbulence.ClassJR
