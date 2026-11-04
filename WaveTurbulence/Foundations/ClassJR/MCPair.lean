/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCType1

/-!
# Products of coefficient representations (the pairs of a chain)

In DH21 (newexp2) each pair `{a, b}` of a regular chain carries the product
`ℬ̃_{𝒬_{j,ε,1}}(t_a, t_b) ℬ̃_{𝒬_{j,ε,2}}(t_a, t_b)` of the coefficients of its two subcouples
(possibly with `(t_a, t_b)` swapped). Its frequencies are `λ_a = λ_{a,1} + λ_{a,2}`,
`λ_b = λ_{b,1} + λ_{b,2}` (DH21 L1117). The product of two representations is a representation with
the convolution symbol `convC` (`MCRep.mul`). Since `wL` is submultiplicative, `(1 + |λ¹ + λ²|) ≤
(1 + |λ¹|)(1 + |λ²|)`, the bounds multiply. `MCExp.mul` is the expansion step with
`Z = Z₁ ∪ Z₂`, and `MCExp.swapTimes` swaps the times.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

attribute [local instance] isAddRightInvariant_volume_prod

section Conv

theorem wL_add_le {a : ℝ} (ha : 0 ≤ a) (u η : ℝ × ℝ) : wL a (u + η) ≤ wL a u * wL a η := by
  unfold wL
  rw [← ENNReal.mul_rpow_of_nonneg _ _ ha]
  refine ENNReal.rpow_le_rpow ?_ ha
  simp only [Prod.fst_add, Prod.snd_add]
  calc 1 + ‖u.1 + η.1‖ₑ + ‖u.2 + η.2‖ₑ ≤ 1 + (‖u.1‖ₑ + ‖η.1‖ₑ) + (‖u.2‖ₑ + ‖η.2‖ₑ) :=
        add_le_add (add_le_add le_rfl (enorm_add_le _ _)) (enorm_add_le _ _)
    _ ≤ 1 + (‖u.1‖ₑ + ‖η.1‖ₑ) + (‖u.2‖ₑ + ‖η.2‖ₑ) +
          (‖u.1‖ₑ * ‖η.1‖ₑ + ‖u.1‖ₑ * ‖η.2‖ₑ + ‖u.2‖ₑ * ‖η.1‖ₑ + ‖u.2‖ₑ * ‖η.2‖ₑ) := le_self_add
    _ = (1 + ‖u.1‖ₑ + ‖u.2‖ₑ) * (1 + ‖η.1‖ₑ + ‖η.2‖ₑ) := by ring

theorem e2_add (u η : ℝ × ℝ) (t s : ℝ) : e2 (u + η) t s = e2 u t s * e2 η t s := by
  simp only [e2, Prod.fst_add, Prod.snd_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- **The convolution symbol** `𝒞(α, λ) = ∫ 𝒞₁(α₁, λ - η) 𝒞₂(α₂, η) dη`. -/
@[expose] noncomputable def convC (C₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ) (C₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ) :
    (ι₁ ⊕ ι₂ → ℝ) → ℝ × ℝ → ℂ :=
  pushSym (pprod C₁ C₂) id

theorem pprod_symReg {θ a b A N₁ N₂ : ℝ} {C₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ}
    {C₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ} (h₁ : SRep θ a b A N₁ C₁) (h₂ : SRep θ a b A N₂ C₂)
    (hθ : 0 ≤ θ) (hA : 0 ≤ A) : SymReg (pprod C₁ C₂) := by
  refine SymReg.of_lintegral (contDiff_pprod h₁.reg.smooth h₂.reg.smooth)
    (measurable_pprod h₁.reg.meas h₂.reg.meas) fun k => ?_
  have := lintegral_pprod_gev_le h₁.reg.smooth h₁.reg.meas h₂.reg.smooth h₂.reg.meas
    (wM := fun _ _ => 1) measurable_const (wC := fun _ _ => 1) measurable_const h₁.nonneg h₂.nonneg
    hA (fun j => by simpa only [one_mul] using h₁.norm_unweighted hθ j)
    (fun j => by simpa only [one_mul] using h₂.norm_unweighted hθ j) k
  simp only [one_mul] at this
  exact ne_top_of_le_ne_top (by simp [gev]) this

theorem SRep.lintegral_wL_a_le {ιx : Type*} [Fintype ιx] {θ a b A N : ℝ}
    {C : (ιx → ℝ) → ℝ × ℝ → ℂ} (h : SRep θ a b A N C) (haθ : a ≤ θ) :
    ∫⁻ α, ∫⁻ lam, wL a lam * dnorm 0 C α lam ≤ ENNReal.ofReal N := by
  refine le_trans (lintegral_mono fun α => lintegral_mono fun lam => ?_)
    ((h.norm 0).trans_eq (gev_zero_eq N A))
  refine mul_le_mul' ?_ le_rfl
  unfold wL
  exact ENNReal.rpow_le_rpow_of_exponent_le (le_self_add.trans le_self_add) haθ

/-- **The bounds of the convolution symbol.** -/
theorem SRep.conv {θ a b A N₁ N₂ : ℝ} {C₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ}
    {C₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ} (h₁ : SRep θ a b A N₁ C₁) (h₂ : SRep θ a b A N₂ C₂)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haθ : a ≤ θ) (hA : 0 ≤ A) :
    SRep θ a b A (4 * N₁ * N₂) (convC C₁ C₂) := by
  have hreg := pprod_symReg h₁ h₂ hθ hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hwθ : Measurable fun u : ℝ × ℝ => wL θ u := measurable_wL θ
  have hwa : Measurable fun u : ℝ × ℝ => wL a u := measurable_wL a
  have hsw1 := h₁.lintegral_wL_a_le haθ
  have hsw2 := h₂.lintegral_wL_a_le haθ
  refine ⟨by positivity, pushSym_symReg hreg measurable_id, fun k => ?_, fun i => ?_⟩
  · refine (lintegral_weight_pushSym_le hreg measurable_id (w := fun _ γ => wL θ γ)
      (hwθ.comp measurable_snd) k).trans ?_
    refine le_trans (lintegral_mono fun α => lintegral_mono fun ζ =>
      mul_le_mul' (wL_add_le hθ ζ.1 ζ.2) le_rfl) ?_
    exact lintegral_pprod_gev_le h₁.reg.smooth h₁.reg.meas h₂.reg.smooth h₂.reg.meas
      (wM := fun _ u => wL θ u) (hwθ.comp measurable_snd) (wC := fun _ u => wL θ u)
      (hwθ.comp measurable_snd) hN₁ hN₂ hA h₁.norm h₂.norm k
  · have e : ∀ α lam, ‖convC C₁ C₂ α lam‖ₑ = dnorm 0 (convC C₁ C₂) α lam := fun α lam =>
      (dnorm_zero _ _ _).symm
    simp_rw [e]
    have hw : Measurable (Function.uncurry fun (α : ι₁ ⊕ ι₂ → ℝ) (lam : ℝ × ℝ) =>
        wL a lam * (1 + ‖α i‖ₑ) ^ b) := by
      change Measurable fun x : (ι₁ ⊕ ι₂ → ℝ) × (ℝ × ℝ) => wL a x.2 * (1 + ‖x.1 i‖ₑ) ^ b
      exact (hwa.comp measurable_snd).mul (by fun_prop)
    refine (lintegral_weight_pushSym_le hreg measurable_id hw 0).trans ?_
    rcases i with i | i
    · have hwM : Measurable (Function.uncurry fun (β : ι₁ → ℝ) (u : ℝ × ℝ) =>
          wL a u * (1 + ‖β i‖ₑ) ^ b) := by
        change Measurable fun x : (ι₁ → ℝ) × (ℝ × ℝ) => wL a x.2 * (1 + ‖x.1 i‖ₑ) ^ b
        exact (hwa.comp measurable_snd).mul (by fun_prop)
      have h := lintegral_pprod_le h₁.reg.smooth h₁.reg.meas h₂.reg.smooth h₂.reg.meas hwM
        (wC := fun _ u => wL a u) (hwa.comp measurable_snd) 0
      simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self] at h
      refine le_trans (lintegral_mono fun α => lintegral_mono fun ζ => ?_) (h.trans ?_)
      · calc wL a (ζ.1 + ζ.2) * (1 + ‖α (Sum.inl i)‖ₑ) ^ b * dnorm 0 (pprod C₁ C₂) α ζ
            ≤ wL a ζ.1 * wL a ζ.2 * (1 + ‖α (Sum.inl i)‖ₑ) ^ b * dnorm 0 (pprod C₁ C₂) α ζ := by
              gcongr; exact wL_add_le ha ζ.1 ζ.2
          _ = _ := by ring
      · rw [show 4 * N₁ * N₂ = 4 * (N₁ * N₂) by ring, ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul hN₁]
        have hw1 : ∫⁻ α₁, ∫⁻ z, wL a z * (1 + ‖α₁ i‖ₑ) ^ b * dnorm 0 C₁ α₁ z ≤
            ENNReal.ofReal N₁ := by
          simpa only [dnorm_zero] using h₁.wnorm i
        calc (∫⁻ α₁, ∫⁻ z, wL a z * (1 + ‖α₁ i‖ₑ) ^ b * dnorm 0 C₁ α₁ z) *
              (∫⁻ α₂, ∫⁻ q, wL a q * dnorm 0 C₂ α₂ q)
            ≤ ENNReal.ofReal N₁ * ENNReal.ofReal N₂ := mul_le_mul' hw1 hsw2
          _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal N₁ * ENNReal.ofReal N₂) := by
            refine le_mul_of_one_le_left bot_le ?_
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
    · have hwC : Measurable (Function.uncurry fun (β : ι₂ → ℝ) (u : ℝ × ℝ) =>
          wL a u * (1 + ‖β i‖ₑ) ^ b) := by
        change Measurable fun x : (ι₂ → ℝ) × (ℝ × ℝ) => wL a x.2 * (1 + ‖x.1 i‖ₑ) ^ b
        exact (hwa.comp measurable_snd).mul (by fun_prop)
      have h := lintegral_pprod_le h₁.reg.smooth h₁.reg.meas h₂.reg.smooth h₂.reg.meas
        (wM := fun _ u => wL a u) (hwa.comp measurable_snd) hwC 0
      simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self] at h
      refine le_trans (lintegral_mono fun α => lintegral_mono fun ζ => ?_) (h.trans ?_)
      · calc wL a (ζ.1 + ζ.2) * (1 + ‖α (Sum.inr i)‖ₑ) ^ b * dnorm 0 (pprod C₁ C₂) α ζ
            ≤ wL a ζ.1 * wL a ζ.2 * (1 + ‖α (Sum.inr i)‖ₑ) ^ b * dnorm 0 (pprod C₁ C₂) α ζ := by
              gcongr; exact wL_add_le ha ζ.1 ζ.2
          _ = _ := by ring
      · rw [show 4 * N₁ * N₂ = 4 * (N₁ * N₂) by ring, ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul hN₁]
        have hw2 : ∫⁻ α₂, ∫⁻ z, wL a z * (1 + ‖α₂ i‖ₑ) ^ b * dnorm 0 C₂ α₂ z ≤
            ENNReal.ofReal N₂ := by
          simpa only [dnorm_zero] using h₂.wnorm i
        calc (∫⁻ α₁, ∫⁻ z, wL a z * dnorm 0 C₁ α₁ z) *
              (∫⁻ α₂, ∫⁻ q, wL a q * (1 + ‖α₂ i‖ₑ) ^ b * dnorm 0 C₂ α₂ q)
            ≤ ENNReal.ofReal N₁ * ENNReal.ofReal N₂ := mul_le_mul' hsw1 hw2
          _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal N₁ * ENNReal.ofReal N₂) := by
            refine le_mul_of_one_le_left bot_le ?_
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The product of two representations** is represented by the convolution symbol. -/
theorem integral_convC_e2 {C₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ} {C₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ}
    (hreg : SymReg (pprod C₁ C₂)) (α : ι₁ ⊕ ι₂ → ℝ) (t s : ℝ) :
    ∫ lam, convC C₁ C₂ α lam * e2 lam t s =
      (∫ lam, C₁ (fun i => α (Sum.inl i)) lam * e2 lam t s) *
        ∫ lam, C₂ (fun i => α (Sum.inr i)) lam * e2 lam t s := by
  have hφ : Continuous fun lam : ℝ × ℝ => e2 lam t s := by unfold e2; fun_prop
  rw [convC, integral_pushSym_mul hreg measurable_id α hφ.aestronglyMeasurable
    (fun γ => (norm_e2 γ t s).le)]
  rw [← integral_prod_mul (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure (ℝ × ℝ)))]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [pprod, kprod, id, e2_add]
  ring

end Conv

section RepProduct

variable {V : Type} {θ a b A : ℝ}

/-- **The product of two coefficient representations** in disjoint variables. -/
theorem MCRep.mul {N₁ N₂ : ℝ} {S₁ S₂ : Set V} {F₁ F₂ : (V → ℝ) → ℝ → ℝ → ℂ}
    (h₁ : MCRep θ a b A N₁ S₁ F₁) (h₂ : MCRep θ a b A N₂ S₂ F₂) (hd : Disjoint S₁ S₂)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haθ : a ≤ θ) (hA : 0 ≤ A) :
    MCRep θ a b A (4 * N₁ * N₂) (S₁ ∪ S₂) (fun α t s => F₁ α t s * F₂ α t s) := by
  obtain ⟨ι₁, _, f₁, C₁, hf₁, hr₁, hS₁, he₁⟩ := h₁.exists_srep
  obtain ⟨ι₂, _, f₂, C₂, hf₂, hr₂, hS₂, he₂⟩ := h₂.exists_srep
  have hS := hS₁.conv hS₂ hθ ha haθ hA
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim f₁ f₂, convC C₁ C₂, ?_, ?_, hS.nonneg, hS.reg, hS.norm,
    hS.wnorm, fun α t s ht hs => ?_⟩
  · refine hf₁.sumElim hf₂ fun x y h => ?_
    exact Set.disjoint_left.1 hd (hr₁ ▸ Set.mem_range_self x) (h ▸ hr₂ ▸ Set.mem_range_self y)
  · rw [Set.Sum.elim_range, hr₁, hr₂]
  · beta_reduce
    rw [integral_convC_e2 (pprod_symReg hS₁ hS₂ hθ hA), he₁ α t s ht hs, he₂ α t s ht hs]
    rfl

theorem union2_inter_left [DecidableEq V] {S₁ S₂ Z₁ Z₂ : Finset V} (h12 : Disjoint S₁ S₂)
    (hZ₁ : Z₁ ⊆ S₁) (hZ₂ : Z₂ ⊆ S₂) : (Z₁ ∪ Z₂) ∩ S₁ = Z₁ := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hx⟩
    · exact h
    · exact absurd (hZ₂ h) (Finset.disjoint_left.1 h12 hx)
  · intro h; exact ⟨Or.inl h, hZ₁ h⟩

theorem union2_inter_right [DecidableEq V] {S₁ S₂ Z₁ Z₂ : Finset V} (h12 : Disjoint S₁ S₂)
    (hZ₁ : Z₁ ⊆ S₁) (hZ₂ : Z₂ ⊆ S₂) : (Z₁ ∪ Z₂) ∩ S₂ = Z₂ := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hx⟩
    · exact absurd hx (Finset.disjoint_left.1 h12 (hZ₁ h))
    · exact h
  · intro h; exact ⟨Or.inr h, hZ₂ h⟩

/-- **The product of two expansions** (maincoef3), with `Z = Z₁ ∪ Z₂`. -/
theorem MCExp.mul [DecidableEq V] {N₁ N₂ : ℝ} {ζ : V → ℤ} {S₁ S₂ : Finset V}
    {F₁ F₂ : (V → ℝ) → ℝ → ℝ → ℂ} (h₁ : MCExp θ a b A N₁ ζ S₁ F₁)
    (h₂ : MCExp θ a b A N₂ ζ S₂ F₂) (hd : Disjoint S₁ S₂) (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (haθ : a ≤ θ) (hA : 0 ≤ A) :
    MCExp θ a b A (4 * N₁ * N₂) ζ (S₁ ∪ S₂) (fun α t s => F₁ α t s * F₂ α t s) := by
  obtain ⟨G₁, hG₁, hF₁⟩ := h₁
  obtain ⟨G₂, hG₂, hF₂⟩ := h₂
  refine ⟨fun Z α t s => G₁ (Z ∩ S₁) α t s * G₂ (Z ∩ S₂) α t s, fun Z hZ => ?_,
    fun α t s ht hs => ?_⟩
  · have key := MCRep.mul (hG₁ (Z ∩ S₁) Finset.inter_subset_right)
      (hG₂ (Z ∩ S₂) Finset.inter_subset_right)
      (Finset.disjoint_coe.2 (Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hd))) hθ ha haθ hA
    have hset : (↑((S₁ ∪ S₂) \ Z) : Set V) = ↑(S₁ \ (Z ∩ S₁)) ∪ ↑(S₂ \ (Z ∩ S₂)) := by
      ext x
      simp only [Finset.coe_sdiff, Finset.coe_union, Finset.coe_inter, Set.mem_union,
        Set.mem_sdiff, Finset.mem_coe, Set.mem_inter_iff]
      tauto
    rw [hset]
    exact key
  · beta_reduce
    rw [hF₁ α t s ht hs, hF₂ α t s ht hs, Finset.sum_mul_sum,
      sum_powerset_union_of_disjoint hd]
    refine Finset.sum_congr rfl fun Z₁ hZ₁ => Finset.sum_congr rfl fun Z₂ hZ₂ => ?_
    rw [Finset.mem_powerset] at hZ₁ hZ₂
    rw [union2_inter_left hd hZ₁ hZ₂, union2_inter_right hd hZ₁ hZ₂,
      Finset.prod_union (Finset.disjoint_of_subset_left hZ₁ (Finset.disjoint_of_subset_right hZ₂ hd))]
    ring

/-- **Swapping the times** in an expansion. -/
theorem MCExp.swapTimes [DecidableEq V] {N : ℝ} {ζ : V → ℤ} {S : Finset V} {F : (V → ℝ) → ℝ → ℝ → ℂ}
    (h : MCExp θ a b A N ζ S F) (sw : Bool) : MCExp θ a b A N ζ S (swapT sw F) := by
  obtain ⟨G, hG, hF⟩ := h
  refine ⟨fun Z => swapT sw (G Z), fun Z hZ => ?_, fun α t s ht hs => ?_⟩
  · obtain ⟨ι, hι, f, C, hf, hr, hS, he⟩ := (hG Z hZ).exists_srep
    have hS' := hS.swap sw
    exact ⟨ι, hι, f, swapC sw C, hf, hr, hS'.nonneg, hS'.reg, hS'.norm, hS'.wnorm,
      fun α t s ht hs => swapT_rep he sw α ht hs⟩
  · cases sw
    · simp only [swapT, Bool.false_eq_true, ↓reduceIte]
      exact hF α t s ht hs
    · simp only [swapT, ↓reduceIte]
      exact hF α s t hs ht

end RepProduct

end WaveTurbulence.ClassJR
