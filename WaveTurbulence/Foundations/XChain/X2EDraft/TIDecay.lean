/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerTop

/-!
# X2E-5, step 1: the time integral decays in `Ω`

**Statements.**
- `norm_integral_indicator_exp_le`: for an order-connected bounded `S ⊆ ℝ` and `θ ≠ 0`,
  `‖∫_S e^{iθu} du‖ ≤ 2/|θ|`;
- `integral_eq_integral_glueAt_inner`: Fubini at one coordinate, with the inner integral over that coordinate;
- **`norm_TIpat_plain_le`**: for `p < s < t ≤ p + 1` and a node `c ≠ 𝔣^pr` outside `off`,
  `‖TIpat_plain(t, s)‖ ≤ 2/(πδL^{2γ}|Ω_c|)` (X3's time integral, plain pattern, per decoration).
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Set Induct SysAPI Fixedpt

/-! ## One variable -/

theorem norm_integral_indicator_exp_le {S : Set ℝ} (hS : S.OrdConnected) (hb : BddBelow S) (ha : BddAbove S)
    {θ : ℝ} (hθ : θ ≠ 0) :
    ‖∫ u, S.indicator (fun u : ℝ => Complex.exp (((θ * u : ℝ) : ℂ) * Complex.I)) u‖ ≤ 2 / |θ| := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Set.indicator_empty, integral_zero, norm_zero]
    positivity
  set a := sInf S
  set b := sSup S
  have hsub : S ⊆ Icc a b := fun x hx => ⟨csInf_le hb hx, le_csSup ha hx⟩
  have hsup : Ioo a b ⊆ S := fun x hx => by
    obtain ⟨y, hy, hya⟩ := exists_lt_of_csInf_lt hne hx.1
    obtain ⟨z, hz, hzb⟩ := exists_lt_of_lt_csSup hne hx.2
    exact hS.out hy hz ⟨hya.le, hzb.le⟩
  have hab : a ≤ b := (csInf_le hb hne.some_mem).trans (le_csSup ha hne.some_mem)
  have h1 : S \ Ioc a b ⊆ {a} := by
    intro x ⟨hx, hx'⟩
    have := hsub hx
    by_contra hxa
    exact hx' ⟨lt_of_le_of_ne this.1 (Ne.symm hxa), this.2⟩
  have h2 : Ioc a b \ S ⊆ {b} := by
    intro x ⟨hx, hx'⟩
    by_contra hxb
    exact hx' (hsup ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩)
  have hae : S =ᵐ[volume] Ioc a b :=
    ae_eq_set.mpr ⟨measure_mono_null h1 (measure_singleton a), measure_mono_null h2 (measure_singleton b)⟩
  set c : ℂ := (θ : ℂ) * Complex.I
  have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hθ) Complex.I_ne_zero
  have hf : (fun u : ℝ => Complex.exp (((θ * u : ℝ) : ℂ) * Complex.I)) = fun u : ℝ => Complex.exp (c * u) := by
    funext u
    congr 1
    push_cast
    ring
  rw [integral_indicator hS.measurableSet, setIntegral_congr_set hae, ← intervalIntegral.integral_of_le hab, hf,
    integral_exp_mul_complex hc]
  have hb' : ‖Complex.exp (c * b)‖ = 1 := by
    rw [show c * (b : ℂ) = ((θ * b : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have ha' : ‖Complex.exp (c * a)‖ = 1 := by
    rw [show c * (a : ℂ) = ((θ * a : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hcn : ‖c‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_div, hcn]
  gcongr
  calc ‖Complex.exp (c * b) - Complex.exp (c * a)‖ ≤ ‖Complex.exp (c * b)‖ + ‖Complex.exp (c * a)‖ :=
        norm_sub_le _ _
    _ = 2 := by rw [hb', ha']; norm_num

/-! ## Fubini with the inner integral at one coordinate -/

theorem integral_eq_integral_glueAt_inner {J : Type*} [Fintype J] [DecidableEq J] (c₀ : J)
    {H : (J → ℝ) → ℂ} (hH : Integrable H) :
    ∫ τ, H τ = ∫ τ', ∫ u, H (glueAt c₀ u τ') := by
  have hE := MeasurePreserving.symm (splitAt' c₀) (measurePreserving_splitAt' c₀)
  have hint : Integrable (fun z : ℝ × ({c : J // c ≠ c₀} → ℝ) => H (glueAt c₀ z.1 z.2))
      ((volume : Measure ℝ).prod volume) :=
    (hE.integrable_comp_emb (splitAt' c₀).symm.measurableEmbedding).2 hH
  rw [← hE.integral_comp' H]
  exact integral_prod_symm _ hint

/-! ## The time integral -/

section Decay

variable (L γ δ : ℝ) {d : ℕ} {F : FTree} (hF : F ≠ FTree.flower) (p : ℕ)
  (off : Finset (GBranch (single F.toTree))) (κ : GNode (single F.toTree) → (Fin d → ℤ))

/-- The full time vector with `t_{𝔣^pr} = s`, `t_c = u` and the other times from `σ'`. -/
noncomputable def glue2 (c : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF}) (s u : ℝ)
    (σ' : {c' : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} // c' ≠ c} → ℝ) :
    GBranch (single F.toTree) → ℝ :=
  glueAt (F.flowerParent hF) s (glueAt c u σ')

theorem glue2_c (c : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF}) (s u : ℝ) σ' :
    glue2 hF c s u σ' c.1 = u := by
  unfold glue2
  rw [glueAt_ne _ _ _ c.2]
  exact glueAt_self _ _ _

theorem glue2_ne (c : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF}) (s u v : ℝ) σ'
    {b : GBranch (single F.toTree)} (hb : b ≠ c.1) : glue2 hF c s u σ' b = glue2 hF c s v σ' b := by
  unfold glue2
  by_cases hbf : b = F.flowerParent hF
  · subst hbf
    rw [glueAt_self, glueAt_self]
  · rw [glueAt_ne _ _ _ hbf, glueAt_ne _ _ _ hbf]
    have hb' : (⟨b, hbf⟩ : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF}) ≠ c :=
      fun h => hb (congrArg Subtype.val h)
    rw [glueAt_ne _ _ _ hb', glueAt_ne _ _ _ hb']

theorem ordConnected_slice (c : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF}) (s t : ℝ) σ' :
    {u : ℝ | glue2 hF c s u σ' ∈ treeTimeDomain F.toTree p t}.OrdConnected := by
  refine ⟨fun u₁ hu₁ u₂ hu₂ u hu b => ?_⟩
  have h1 := hu₁ b
  have h2 := hu₂ b
  by_cases hb : b = c.1
  · subst hb
    rw [glue2_c] at h1 h2 ⊢
    refine ⟨h1.1.trans_le hu.1, hu.2.trans_lt h2.2.1, fun b' hb' => ?_⟩
    have hne : b' ≠ c.1 := fun h => by
      subst h
      obtain ⟨-, i, hi⟩ := hb'
      have := congrArg List.length hi
      simp at this
    have := h1.2.2 b' hb'
    rw [glue2_ne hF c s u₁ u σ' hne] at this
    exact this.trans_le hu.1
  · rw [glue2_ne hF c s u u₁ σ' hb]
    refine ⟨h1.1, h1.2.1, fun b' hb' => ?_⟩
    by_cases hb'c : b' = c.1
    · subst hb'c
      have := h2.2.2 _ hb'
      rw [glue2_c, glue2_ne hF c s u₂ u₁ σ' hb] at this
      rw [glue2_c]
      exact hu.2.trans_lt this
    · rw [glue2_ne hF c s u u₁ σ' hb'c]
      exact h1.2.2 b' hb'

/-- The phase at `c` splits off the phase product. -/
theorem phaseOffT_glue2 (c : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF}) (hoff : c.1 ∉ off)
    (s u : ℝ) σ' :
    phaseOffT L γ δ F.toTree off κ (glue2 hF c s u σ') =
      Complex.exp (((Real.pi * ((treeSign F.toTree c.1.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaT L F.toTree κ c.1 * u : ℝ) : ℂ) * Complex.I) *
      ∏ b ∈ univ.erase c.1, (if b ∈ off then 1 else Complex.exp (((Real.pi * ((treeSign F.toTree b.toNode : ℤˣ) : ℤ) *
        δ * L ^ (2 * γ) * omegaT L F.toTree κ b * glue2 hF c s 0 σ' b : ℝ) : ℂ) * Complex.I)) := by
  unfold phaseOffT
  rw [← mul_prod_erase univ _ (mem_univ c.1), ite_eq_right hoff, glue2_c]
  congr 1
  refine prod_congr rfl fun b hb => ?_
  rw [glue2_ne hF c s u 0 σ' (ne_of_mem_erase hb)]

theorem treeSign_ne_zero_real (c : GBranch (single F.toTree)) : (((treeSign F.toTree c.toNode : ℤˣ) : ℤ) : ℝ) ≠ 0 := by
  rcases Int.units_eq_one_or (treeSign F.toTree c.toNode) with h | h <;> rw [h] <;> norm_num

/-- **The `Ω`-decay of the plain time integral.** -/
theorem norm_TIpat_plain_le {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (ht : t ≤ p + 1)
    (c : GBranch (single F.toTree)) (hc : c ≠ F.flowerParent hF) (hoff : c ∉ off) (hδ : 0 < δ) (hL : 0 < L)
    (hΩ : omegaT L F.toTree κ c ≠ 0) :
    ‖TIpat L γ δ hF p off κ .plain t s‖ ≤ 2 / (Real.pi * δ * L ^ (2 * γ) * |omegaT L F.toTree κ c|) := by
  classical
  set c' : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} := ⟨c, hc⟩
  set θ : ℝ := Real.pi * ((treeSign F.toTree c.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaT L F.toTree κ c
  have hLγ : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL _
  have hθ : θ ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero Real.pi_ne_zero
    (treeSign_ne_zero_real c)) hδ.ne') hLγ.ne') hΩ
  have hθabs : |θ| = Real.pi * δ * L ^ (2 * γ) * |omegaT L F.toTree κ c| := by
    have hs : |(((treeSign F.toTree c.toNode : ℤˣ) : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (treeSign F.toTree c.toNode) with h | h <;> rw [h] <;> norm_num
    simp only [θ, abs_mul, hs, abs_of_pos Real.pi_pos, abs_of_pos hδ, abs_of_pos hLγ, mul_one]
  set K : ℝ := 2 / |θ|
  have hK0 : 0 ≤ K := by positivity
  unfold TIpat
  rw [timeInt_plain_eq L γ δ hF p off κ hps hst ht]
  rw [integral_eq_integral_glueAt_inner c' (integrable_HT_glue L γ δ p F.toTree off κ t (F.flowerParent hF) s)]
  set Box : Set ({c'' : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} // c'' ≠ c'} → ℝ) :=
    Set.pi univ fun _ => Icc (p : ℝ) (p + 1)
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hvol : volume Box = 1 := by
    rw [volume_pi_pi]
    simp [Real.volume_Icc]
  have hint : Integrable (Box.indicator fun _ => K) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top))
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun σ' => ?_)).trans (le_of_eq ?_)
  · have hslice : (fun u => HT L γ δ p F.toTree off κ t (glueAt (F.flowerParent hF) s (glueAt c' u σ'))) =
        fun u => (∏ b ∈ univ.erase c, (if b ∈ off then 1 else Complex.exp (((Real.pi *
          ((treeSign F.toTree b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaT L F.toTree κ b *
            glue2 hF c' s 0 σ' b : ℝ) : ℂ) * Complex.I))) *
          {u : ℝ | glue2 hF c' s u σ' ∈ treeTimeDomain F.toTree p t}.indicator
            (fun u : ℝ => Complex.exp (((θ * u : ℝ) : ℂ) * Complex.I)) u := by
      funext u
      change (treeTimeDomain F.toTree p t).indicator (phaseOffT L γ δ F.toTree off κ) (glue2 hF c' s u σ') = _
      by_cases hm : glue2 hF c' s u σ' ∈ treeTimeDomain F.toTree p t
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show u ∈ {u : ℝ | glue2 hF c' s u σ' ∈
          treeTimeDomain F.toTree p t} from hm), phaseOffT_glue2 L γ δ hF off κ c' hoff, mul_comm]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show u ∉ {u : ℝ | glue2 hF c' s u σ' ∈
          treeTimeDomain F.toTree p t} from hm), mul_zero]
    rw [hslice, integral_const_mul, norm_mul]
    have hR : ‖∏ b ∈ univ.erase c, (if b ∈ off then (1 : ℂ) else Complex.exp (((Real.pi *
        ((treeSign F.toTree b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaT L F.toTree κ b *
          glue2 hF c' s 0 σ' b : ℝ) : ℂ) * Complex.I))‖ ≤ 1 := by
      rw [norm_prod]
      refine prod_le_one₀ (fun _ _ => norm_nonneg _) fun b _ => ?_
      split_ifs
      · rw [norm_one]
      · rw [Complex.norm_exp_ofReal_mul_I]
    by_cases hσ : σ' ∈ Box
    · rw [Set.indicator_of_mem hσ]
      have hbd : {u : ℝ | glue2 hF c' s u σ' ∈ treeTimeDomain F.toTree p t} ⊆ Ioo (p : ℝ) t := by
        intro u hu
        have h := hu c
        rw [show c = c'.1 from rfl, glue2_c] at h
        exact ⟨h.1, h.2.1⟩
      have h1 := norm_integral_indicator_exp_le (ordConnected_slice hF p c' s t σ')
        ⟨p, fun u hu => (hbd hu).1.le⟩ ⟨t, fun u hu => (hbd hu).2.le⟩ hθ
      calc _ ≤ 1 * (2 / |θ|) := mul_le_mul hR h1 (norm_nonneg _) zero_le_one
        _ = K := one_mul _
    · rw [Set.indicator_of_notMem hσ]
      have hempty : {u : ℝ | glue2 hF c' s u σ' ∈ treeTimeDomain F.toTree p t} = ∅ := by
        ext u
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hu
        apply hσ
        intro c'' _
        have h := hu c''.1.1
        have hne : c''.1.1 ≠ c'.1 := fun e => c''.2 (Subtype.ext e)
        have hv : glue2 hF c' s u σ' c''.1.1 = σ' c'' := by
          unfold glue2
          rw [glueAt_ne _ _ _ c''.1.2]
          exact glueAt_ne _ _ _ c''.2
        rw [hv] at h
        exact ⟨h.1.le, h.2.1.le.trans ht⟩
      rw [hempty, Set.indicator_empty, integral_zero, norm_zero, mul_zero]
  · rw [integral_indicator hBm, setIntegral_const, smul_eq_mul, measureReal_def, hvol]
    simp [K, hθabs]

end Decay

end WaveTurbulence.X2E
