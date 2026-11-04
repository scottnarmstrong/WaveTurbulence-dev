/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCTBound
public import WaveTurbulence.Foundations.ClassJR.MCChainTerm

/-!
# One term of a rebased tree chain (DH21 Proposition 6.10)

For the rebased chain of a regular tree, the pair coefficients are twisted by `e^{πi(λ₁+λ₂)s}`
(`tsym`). In a term of `chainT_bottom_expand`, the product of the twists is `e^{πiΛ(z)s}` (`Mz_tsym`),
which joins the phase `e^{πiλ₂s}` of the bottom coefficient. The measure-preserving shear
`(z, (λ₁, λ₂)) ↦ (z, (λ₁, λ₂ - Λ(z)))` (`shearZ`) moves it into the bottom symbol, so the term is the
time integral of `Cassem` built from `M' = (∏_j 𝒞_j ⊗ 𝒞_b) ∘ shearZ` (`treeTerm`). Its DH23 bounds
(`shearM_bounds`): the weight `⟨λ₂⟩` of `M'` is `⟨λ₂ + Λ(z)⟩ ≤ ⟨λ₂⟩⟨Λ(z)⟩` for `M = ∏_j 𝒞_j ⊗ 𝒞_b`; the
factor `⟨Λ(z)⟩` is paid by the pair weights `∏_j ⟨λ_j⟩` (`MzSW`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

attribute [local instance] isAddRightInvariant_volume_prod

section Shear

/-- **The shear of the bottom frequency** `(z, (λ₁, λ₂)) ↦ (z, (λ₁, λ₂ - Λ(z)))`. -/
@[expose] noncomputable def shearZ (c : LegalCode) : ZT c × (ℝ × ℝ) ≃ᵐ ZT c × (ℝ × ℝ) where
  toFun w := (w.1, (w.2.1, w.2.2 - Λsum c w.1))
  invFun w := (w.1, (w.2.1, w.2.2 + Λsum c w.1))
  left_inv w := by simp
  right_inv w := by simp
  measurable_toFun := by
    have := (continuous_Λsum c).measurable
    show Measurable fun w : ZT c × (ℝ × ℝ) => (w.1, (w.2.1, w.2.2 - Λsum c w.1))
    fun_prop
  measurable_invFun := by
    have := (continuous_Λsum c).measurable
    show Measurable fun w : ZT c × (ℝ × ℝ) => (w.1, (w.2.1, w.2.2 + Λsum c w.1))
    fun_prop

theorem shearZ_apply (c : LegalCode) (w : ZT c × (ℝ × ℝ)) :
    shearZ c w = (w.1, (w.2.1, w.2.2 - Λsum c w.1)) := rfl

theorem shearZ_symm_apply (c : LegalCode) (w : ZT c × (ℝ × ℝ)) :
    (shearZ c).symm w = (w.1, (w.2.1, w.2.2 + Λsum c w.1)) := rfl

theorem measurePreserving_shearZ (c : LegalCode) : MeasurePreserving (shearZ c) := by
  have hg : ∀ z : ZT c, Measure.map (fun lam : ℝ × ℝ => (lam.1, lam.2 - Λsum c z)) volume =
      (volume : Measure (ℝ × ℝ)) := fun z => by
    have h := (measurePreserving_sub_right (volume : Measure (ℝ × ℝ)) ((0 : ℝ), Λsum c z)).map_eq
    convert h using 2
    funext lam
    simp [Prod.ext_iff]
  have hm : Measurable (Function.uncurry fun (z : ZT c) (lam : ℝ × ℝ) => (lam.1, lam.2 - Λsum c z)) := by
    have := (continuous_Λsum c).measurable
    change Measurable fun p : ZT c × (ℝ × ℝ) => (p.2.1, p.2.2 - Λsum c p.1)
    fun_prop
  have h := (MeasurePreserving.id (volume : Measure (ZT c))).skew_product hm
    (Filter.Eventually.of_forall hg)
  exact h

theorem one_add_enorm_add_rpow_le {θ : ℝ} (hθ : 0 ≤ θ) (x y : ℝ) :
    (1 + ‖x + y‖ₑ) ^ θ ≤ (1 + ‖x‖ₑ) ^ θ * (1 + ‖y‖ₑ) ^ θ := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hθ]
  refine ENNReal.rpow_le_rpow ?_ hθ
  calc (1 : ℝ≥0∞) + ‖x + y‖ₑ ≤ 1 + (‖x‖ₑ + ‖y‖ₑ) := by gcongr; exact enorm_add_le x y
    _ ≤ 1 + ‖x‖ₑ + ‖y‖ₑ + ‖x‖ₑ * ‖y‖ₑ := by rw [← add_assoc]; exact le_self_add
    _ = (1 + ‖x‖ₑ) * (1 + ‖y‖ₑ) := by ring

end Shear

section ShearM

variable {c : LegalCode} {ι ιb : Type} [Fintype ι] [Fintype ιb]

/-- **The sheared product** `M'(β; z, λ) = (∏_j 𝒞_j ⊗ 𝒞_b)(β; z, λ₁, λ₂ - Λ(z))`. -/
@[expose] noncomputable def shearM (MS : (ι → ℝ) → ZT c → ℂ) (Cb : (ιb → ℝ) → ℝ × ℝ → ℂ) :
    (ι ⊕ ιb → ℝ) → ZT c × (ℝ × ℝ) → ℂ :=
  fun β w => pprod MS Cb β (shearZ c w)

theorem dnorm_shearM (MS : (ι → ℝ) → ZT c → ℂ) (Cb : (ιb → ℝ) → ℝ × ℝ → ℂ) (k : ℕ)
    (β : ι ⊕ ιb → ℝ) (w : ZT c × (ℝ × ℝ)) :
    dnorm k (shearM MS Cb) β w = dnorm k (pprod MS Cb) β (shearZ c w) := rfl

/-- Integrals against `M'` are integrals against `M` with the weight of `λ₂` shifted by `Λ(z)`. -/
theorem lintegral_shearM (MS : (ι → ℝ) → ZT c → ℂ) (Cb : (ιb → ℝ) → ℝ × ℝ → ℂ)
    (u : (ι ⊕ ιb → ℝ) → ZT c × (ℝ × ℝ) → ℝ≥0∞) (k : ℕ) (β : ι ⊕ ιb → ℝ) :
    ∫⁻ w, u β w * dnorm k (shearM MS Cb) β w =
      ∫⁻ w, u β ((shearZ c).symm w) * dnorm k (pprod MS Cb) β w := by
  have h := (measurePreserving_shearZ c).lintegral_comp_emb (shearZ c).measurableEmbedding
    (fun w => u β ((shearZ c).symm w) * dnorm k (pprod MS Cb) β w)
  simp only [MeasurableEquiv.symm_apply_apply] at h
  rw [← h]
  rfl

/-- **The bounds of the sheared product** in the form used by `srep_assemble`. The weight `⟨λ₂⟩` of
`M'` is `⟨λ₂ + Λ(z)⟩ ≤ ⟨λ₂⟩⟨Λ(z)⟩`; `⟨λ₂⟩` falls on the bottom symbol, `⟨Λ(z)⟩` on the pair weights. -/
theorem shearM_bounds {θ a b A NT Nb : ℝ} {MS : (ι → ℝ) → ZT c → ℂ}
    {Cb : (ιb → ℝ) → ℝ × ℝ → ℂ} (hs : ∀ z, ContDiff ℝ ∞ fun β => MS β z)
    (hm : StronglyMeasurable (Function.uncurry MS)) (hNT : 0 ≤ NT)
    (hTθ : ∀ k, ∫⁻ β, ∫⁻ z, ENNReal.ofReal (Wprod θ c z) * dnorm k MS β z ≤ gev NT A k)
    (hT0 : ∫⁻ β, ∫⁻ z, ENNReal.ofReal (Wprod a c z) * dnorm 0 MS β z ≤ ENNReal.ofReal NT)
    (hTv : ∀ i, ∫⁻ β, ∫⁻ z, ENNReal.ofReal (Wprod a c z) * (1 + ‖β i‖ₑ) ^ b * dnorm 0 MS β z ≤
      ENNReal.ofReal NT)
    (hTf : ∀ j, ∫⁻ β, ∫⁻ z, ENNReal.ofReal (Wprod a c z) * (1 + ‖(Λz c 0 z j).1‖ₑ) ^ b *
      dnorm 0 MS β z ≤ ENNReal.ofReal NT)
    (hC : SRep θ a b A Nb Cb) (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haθ : a ≤ θ) (hA : 0 ≤ A) :
    (∀ k, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ θ * dnorm k (shearM MS Cb) β w ≤ gev (4 * NT * Nb) A k) ∧
    (∀ i, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖β i‖ₑ) ^ b * dnorm 0 (shearM MS Cb) β w ≤
      ENNReal.ofReal (4 * NT * Nb)) ∧
    (∀ j, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖(Λz c 0 w.1 j).1‖ₑ) ^ b *
      dnorm 0 (shearM MS Cb) β w ≤ ENNReal.ofReal (4 * NT * Nb)) := by
  have hNb := hC.nonneg
  have hc : ENNReal.ofReal NT * ENNReal.ofReal Nb ≤ ENNReal.ofReal (4 * NT * Nb) := by
    rw [← ENNReal.ofReal_mul hNT]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hNT hNb])
  have hwC : ∀ c' : ℝ, Measurable (Function.uncurry fun (_ : ιb → ℝ) (lam : ℝ × ℝ) =>
      ((1 : ℝ≥0∞) + ‖lam.2‖ₑ) ^ c') := fun c' => by
    change Measurable fun y : (ιb → ℝ) × (ℝ × ℝ) => ((1 : ℝ≥0∞) + ‖y.2.2‖ₑ) ^ c'
    fun_prop
  have hwW : ∀ e : ℝ, Measurable (Function.uncurry fun (_ : ι → ℝ) (z : ZT c) =>
      ENNReal.ofReal (Wprod e c z)) := fun e => by
    have := (continuous_Wprod e c).measurable
    change Measurable fun y : (ι → ℝ) × ZT c => ENNReal.ofReal (Wprod e c y.2)
    fun_prop
  have hCa : ∫⁻ β, ∫⁻ lam, (1 + ‖lam.2‖ₑ) ^ a * dnorm 0 Cb β lam ≤ ENNReal.ofReal Nb :=
    le_trans (lintegral_mono fun β => lintegral_mono fun lam =>
      mul_le_mul' (one_add_snd_rpow_le_wL ha haθ lam) le_rfl) ((hC.norm 0).trans_eq (gev_zero_eq _ _))
  -- the weight of `λ₂` after the shear
  have hsplit : ∀ {e : ℝ}, 0 ≤ e → ∀ w : ZT c × (ℝ × ℝ),
      (1 + ‖((shearZ c).symm w).2.2‖ₑ) ^ e ≤ ENNReal.ofReal (Wprod e c w.1) * (1 + ‖w.2.2‖ₑ) ^ e :=
    fun he w => by
      rw [shearZ_symm_apply, mul_comm]
      exact (one_add_enorm_add_rpow_le he _ _).trans
        (mul_le_mul' le_rfl (one_add_enorm_Λsum_rpow_le he c w.1))
  refine ⟨fun k => ?_, ?_, fun j => ?_⟩
  · have h := lintegral_pprod_gev_le hs hm hC.reg.smooth hC.reg.meas (hwW θ) (hwC θ)
      (N₁ := NT) (N₂ := Nb) hNT hNb hA hTθ (fun j => le_trans (lintegral_mono fun β =>
        lintegral_mono fun lam => mul_le_mul' (one_add_snd_rpow_le_wL hθ le_rfl lam) le_rfl)
          (hC.norm j)) k
    refine le_trans (lintegral_mono fun β => ?_) h
    rw [lintegral_shearM MS Cb (fun _ w => (1 + ‖w.2.2‖ₑ) ^ θ)]
    exact lintegral_mono fun w => mul_le_mul' (hsplit hθ w) le_rfl
  · rintro (i | i)
    · have hw : Measurable (Function.uncurry fun (β : ι → ℝ) (z : ZT c) =>
          ENNReal.ofReal (Wprod a c z) * ((1 : ℝ≥0∞) + ‖β i‖ₑ) ^ b) := by
        have := (continuous_Wprod a c).measurable
        change Measurable fun y : (ι → ℝ) × ZT c => ENNReal.ofReal (Wprod a c y.2) *
          ((1 : ℝ≥0∞) + ‖y.1 i‖ₑ) ^ b
        fun_prop
      have h := lintegral_pprod_zero_le hs hm hC.reg.smooth hC.reg.meas hw (hwC a)
      refine le_trans (lintegral_mono fun β => ?_) (h.trans ((mul_le_mul' (hTv i) hCa).trans hc))
      rw [lintegral_shearM MS Cb (fun β w => (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖β (Sum.inl i)‖ₑ) ^ b)]
      refine lintegral_mono fun w => ?_
      calc (1 + ‖((shearZ c).symm w).2.2‖ₑ) ^ a * (1 + ‖β (Sum.inl i)‖ₑ) ^ b *
            dnorm 0 (pprod MS Cb) β w
          ≤ ENNReal.ofReal (Wprod a c w.1) * (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖β (Sum.inl i)‖ₑ) ^ b *
            dnorm 0 (pprod MS Cb) β w := by gcongr; exact hsplit ha w
        _ = ENNReal.ofReal (Wprod a c w.1) * (1 + ‖β (Sum.inl i)‖ₑ) ^ b * (1 + ‖w.2.2‖ₑ) ^ a *
            dnorm 0 (pprod MS Cb) β w := by ring
    · have hw : Measurable (Function.uncurry fun (β : ιb → ℝ) (lam : ℝ × ℝ) =>
          wL a lam * ((1 : ℝ≥0∞) + ‖β i‖ₑ) ^ b) := by
        change Measurable fun y : (ιb → ℝ) × (ℝ × ℝ) => wL a y.2 * ((1 : ℝ≥0∞) + ‖y.1 i‖ₑ) ^ b
        have := measurable_wL a
        fun_prop
      have h := lintegral_pprod_zero_le hs hm hC.reg.smooth hC.reg.meas (hwW a) hw
      have hCw : ∫⁻ β, ∫⁻ lam, wL a lam * (1 + ‖β i‖ₑ) ^ b * dnorm 0 Cb β lam ≤
          ENNReal.ofReal Nb := by
        simpa only [dnorm_zero] using hC.wnorm i
      refine le_trans (lintegral_mono fun β => ?_) (h.trans ((mul_le_mul' hT0 hCw).trans hc))
      rw [lintegral_shearM MS Cb (fun β w => (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖β (Sum.inr i)‖ₑ) ^ b)]
      refine lintegral_mono fun w => ?_
      calc (1 + ‖((shearZ c).symm w).2.2‖ₑ) ^ a * (1 + ‖β (Sum.inr i)‖ₑ) ^ b *
            dnorm 0 (pprod MS Cb) β w
          ≤ ENNReal.ofReal (Wprod a c w.1) * (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖β (Sum.inr i)‖ₑ) ^ b *
            dnorm 0 (pprod MS Cb) β w := by gcongr; exact hsplit ha w
        _ ≤ ENNReal.ofReal (Wprod a c w.1) * (wL a w.2 * (1 + ‖β (Sum.inr i)‖ₑ) ^ b) *
            dnorm 0 (pprod MS Cb) β w := by
          rw [mul_assoc (ENNReal.ofReal _)]
          gcongr
          exact one_add_snd_rpow_le_wL ha le_rfl w.2
  · have hw : Measurable (Function.uncurry fun (_ : ι → ℝ) (z : ZT c) =>
        ENNReal.ofReal (Wprod a c z) * ((1 : ℝ≥0∞) + ‖(Λz c 0 z j).1‖ₑ) ^ b) := by
      have h1 := (continuous_Wprod a c).measurable
      have h2 := measurable_weight_Λz (X := ι → ℝ) c 0 j b (pr := fun z => z) measurable_id
      change Measurable fun y : (ι → ℝ) × ZT c => ENNReal.ofReal (Wprod a c y.2) *
        ((1 : ℝ≥0∞) + ‖(Λz c 0 y.2 j).1‖ₑ) ^ b
      exact (ENNReal.measurable_ofReal.comp (h1.comp measurable_snd)).mul h2
    have h := lintegral_pprod_zero_le hs hm hC.reg.smooth hC.reg.meas hw (hwC a)
    refine le_trans (lintegral_mono fun β => ?_) (h.trans ((mul_le_mul' (hTf j) hCa).trans hc))
    rw [lintegral_shearM MS Cb (fun _ w => (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖(Λz c 0 w.1 j).1‖ₑ) ^ b)]
    refine lintegral_mono fun w => ?_
    rw [shearZ_symm_apply]
    calc (1 + ‖(w.1, (w.2.1, w.2.2 + Λsum c w.1)).2.2‖ₑ) ^ a *
          (1 + ‖(Λz c 0 (w.1, (w.2.1, w.2.2 + Λsum c w.1)).1 j).1‖ₑ) ^ b * dnorm 0 (pprod MS Cb) β w
        ≤ ENNReal.ofReal (Wprod a c w.1) * (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖(Λz c 0 w.1 j).1‖ₑ) ^ b *
          dnorm 0 (pprod MS Cb) β w := by
          gcongr
          have := hsplit ha w
          rwa [shearZ_symm_apply] at this
      _ = ENNReal.ofReal (Wprod a c w.1) * (1 + ‖(Λz c 0 w.1 j).1‖ₑ) ^ b * (1 + ‖w.2.2‖ₑ) ^ a *
          dnorm 0 (pprod MS Cb) β w := by ring

end ShearM

section Term

variable {V : Type} [DecidableEq V] {σ : ℕ → V} {ε : ℕ → ℤ}

/-- **The twisted pair symbols** `e^{πi(λ₁+λ₂)s} 𝒞_j(λ)`, the symbols of the rebased pairs. -/
@[expose] noncomputable def twistP (P : ℕ → PSym V) (s : ℝ) : ℕ → PSym V :=
  fun j => ⟨(P j).ι, (P j).f, tsym s (P j).C⟩

/-- **One term of a rebased tree chain** (DH21 Proposition 6.10, L1705–L1708): the term of
`chainT_bottom_expand` with the twisted pairs, at the bottom time `s`, is the time integral of the
coefficient `Cassem` of the sheared product `M'`, which has the DH23 bounds. The weights of `⟨λ₂⟩` are
paid by the bottom symbol and by the pair weights (`MzSW`): `hTθ` (Gevrey bounds, weight `θ`) and `hTa`
(per-variable and frequency bounds, weight `a`). -/
theorem treeTerm {θ a b A NT Nb NH : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haθ : a ≤ θ) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1) {c : LegalCode}
    (hinj : Set.InjOn σ (Set.Ico 0 c.size)) {P : ℕ → PSym V} {Y Y' : Finset ℕ}
    (hD : Y \ Y' ⊆ Finset.Ico 0 (0 + c.size))
    (hT : TBound A NT b c 0 (MzS (chainP P σ ε (Y \ Y')) c 0))
    (hTθ : TBound A NT 0 c 0 (MzSW (chainP P σ ε (Y \ Y')) θ c 0))
    (hTa : TBound A NT b c 0 (MzSW (chainP P σ ε (Y \ Y')) a c 0))
    {ιb : Type} [Fintype ιb] {fb : ιb → V} {Cb : (ιb → ℝ) → ℝ × ℝ → ℂ}
    (hCb : SRep θ a b A Nb Cb)
    {ιH : Type} [Fintype ιH] {fH : ιH → V} {Ξ : Type} [MeasureSpace Ξ]
    [SFinite (volume : Measure Ξ)] {bfr : Ξ → ℝ} (hbfr : Measurable bfr)
    {H : ZT c → ℝ → (ιH → ℝ) → ℝ × Ξ → ℂ} (hNH : 0 ≤ NH)
    (hH : ∀ p L0, FRep θ a b A NH (fun ξ => ξ.1 + bfr ξ.2) (H p L0))
    (hHm : Measurable fun x : (ZT c × ℝ) × ((ιH → ℝ) × (ℝ × Ξ)) => H x.1.1 x.1.2 x.2.1 x.2.2)
    {jH : ιH → ℕ} (hjH : ∀ i, jH i ∈ Set.Ico 0 c.size ∧ fH i = σ (jH i))
    {Gp : ZT c → ℝ → (V → ℝ) → ℝ → ℂ}
    (hGp : ∀ p L0 α, ∀ t ∈ Icc (0 : ℝ) 1,
      Gp p L0 α t = ∫ ξ, H p L0 (α ∘ fH) ξ * cexp (π * I * ((ξ.1 + bfr ξ.2) * t))) :
    SRep θ a b A (4 * (4 * NT * Nb) * NH)
        (Cassem (shearM (MzS (chainP P σ ε (Y \ Y')) c 0) Cb) H bfr (sV σ ε c fH)) ∧
      ∀ s : ℝ, ∀ α : V → ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
        Integrable (gTerm σ ε (twistP P s) fb Cb c Gp Y Y' α t s) ∧
          ∫ w, gTerm σ ε (twistP P s) fb Cb c Gp Y Y' α t s w =
            ∫ lam, Cassem (shearM (MzS (chainP P σ ε (Y \ Y')) c 0) Cb) H bfr (sV σ ε c fH)
              (α ∘ fTerm (σ := σ) (ε := ε) P c (Y \ Y') fb fH) lam * e2 lam t s := by
  classical
  set D := Y \ Y' with hD_def
  set P' := chainP P σ ε D with hP'
  set MS := MzS P' c 0 with hMS
  have hNT := hT.nonneg
  -- the weighted bounds of the product of the pair symbols
  have hTθ' : ∀ k, ∫⁻ β, ∫⁻ z, ENNReal.ofReal (Wprod θ c z) * dnorm k MS β z ≤ gev NT A k :=
    fun k => le_trans (le_of_eq (lintegral_congr fun β => lintegral_congr fun z =>
      (dnorm_MzSW P' hT.smooth k β z).symm)) (hTθ.norm k)
  have hW : ∀ (u : (ιT P' c 0 → ℝ) → ZT c → ℝ≥0∞) β z, ENNReal.ofReal (Wprod a c z) * u β z *
      dnorm 0 MS β z = u β z * dnorm 0 (MzSW P' a c 0) β z := fun u β z => by
    rw [dnorm_MzSW P' hT.smooth]; ring
  have hT0 : ∫⁻ β, ∫⁻ z, ENNReal.ofReal (Wprod a c z) * dnorm 0 MS β z ≤ ENNReal.ofReal NT :=
    le_trans (le_of_eq (lintegral_congr fun β => lintegral_congr fun z =>
      (dnorm_MzSW P' hT.smooth 0 β z).symm)) ((hTa.norm 0).trans_eq (gev_zero_eq _ _))
  have hTv : ∀ i, ∫⁻ β, ∫⁻ z, ENNReal.ofReal (Wprod a c z) * (1 + ‖β i‖ₑ) ^ b * dnorm 0 MS β z ≤
      ENNReal.ofReal NT := fun i => le_trans (le_of_eq (lintegral_congr fun β =>
        lintegral_congr fun z => hW (fun β _ => (1 + ‖β i‖ₑ) ^ b) β z)) (hTa.wvar i)
  have hTf : ∀ j, ∫⁻ β, ∫⁻ z, ENNReal.ofReal (Wprod a c z) * (1 + ‖(Λz c 0 z j).1‖ₑ) ^ b *
      dnorm 0 MS β z ≤ ENNReal.ofReal NT := fun j => le_trans (le_of_eq (lintegral_congr fun β =>
        lintegral_congr fun z => hW (fun _ z => (1 + ‖(Λz c 0 z j).1‖ₑ) ^ b) β z)) (hTa.wfreq j)
  obtain ⟨hMn, hMv, hMf⟩ := shearM_bounds hT.smooth hT.meas hNT hTθ' hT0 hTv hTf hCb hθ ha haθ hA
  have hvH : ∀ i, Measurable fun w' : ZT c => ((1 : ℝ≥0∞) + ‖(Λz c 0 w' (jH i)).1‖ₑ) ^ b :=
    fun i => ((measurable_fst.comp (continuous_Λz c 0 (jH i)).measurable).enorm.const_add
      1).pow_const b
  have hMs : ∀ w, ContDiff ℝ ∞ fun β => shearM MS Cb β w := fun w =>
    contDiff_pprod hT.smooth hCb.reg.smooth (shearZ c w)
  have hMm : StronglyMeasurable (Function.uncurry (shearM MS Cb)) := by
    have h := (measurable_pprod hT.meas hCb.reg.meas).measurable
    have e : Function.uncurry (shearM MS Cb) =
        Function.uncurry (pprod MS Cb) ∘ fun y : (ιT P' c 0 ⊕ ιb → ℝ) × (ZT c × (ℝ × ℝ)) =>
          (y.1, shearZ c y.2) := rfl
    rw [e]
    exact (h.comp (measurable_fst.prodMk ((shearZ c).measurable.comp measurable_snd))).stronglyMeasurable
  obtain ⟨hS, hreg, hid⟩ := srep_assemble (M := shearM MS Cb) (H := H) (bfr := bfr)
    (sH := sV σ ε c fH) hθ ha haθ hb hA hMs hMm (by have := hCb.nonneg; positivity)
    hMn hMv (vH := fun i w' => ((1 : ℝ≥0∞) + ‖(Λz c 0 w' (jH i)).1‖ₑ) ^ b) hvH
    (fun i => hMf (jH i)) hbfr hNH hH hHm (measurable_sV fH)
    (fun w' i => one_add_sV_le hε hinj (hjH i).1 (hjH i).2 w')
  refine ⟨hS, fun s α t ht => ?_⟩
  set Ĉ : ℕ → ℝ × ℝ → ℂ := fun j => (P j).C (α ∘ (P j).f) with hĈ
  set β := α ∘ fTerm (σ := σ) (ε := ε) P c D fb fH with hβ
  set F : (ZT c × (ℝ × ℝ)) × (ℝ × Ξ) → ℂ := fun x =>
    kprod (shearM MS Cb) (Kc H (sV σ ε c fH)) β x * e2 (FrA bfr x) t s with hF
  have hFi : Integrable F := by
    refine (hreg.integrable β).mul_bdd (c := 1) ?_ (Eventually.of_forall fun x => (norm_e2 _ t s).le)
    have h1 : Measurable fun x : (ZT c × (ℝ × ℝ)) × (ℝ × Ξ) => FrA bfr x := by
      unfold FrA; fun_prop
    have h2 : Continuous fun p : ℝ × ℝ => e2 p t s := by unfold e2; fun_prop
    exact (h2.measurable.comp h1).aestronglyMeasurable
  -- the product of the pair symbols
  have hM : ∀ z : ZT c, MzS P' c 0 (α ∘ fT P' c 0) z =
      Mz Ĉ c 0 z * ∏ j ∈ D, Dfun (ε j) (Λz c 0 z j).1 (α (σ j)) := by
    intro z
    rw [← Mz_eq_MzS]
    have e : (fun j => (P' j).C (α ∘ (P' j).f)) =
        fun j lam => Ĉ j lam * (if j ∈ D then Dfun (ε j) lam.1 (α (σ j)) else 1) := by
      funext j lam
      exact chainP_C α j lam
    rw [e, Mz_mul, Finset.prod_ite_mem, Finset.inter_eq_right.2 hD]
  -- the sheared term
  set gT : ZT c × (ℝ × ℝ) → ℂ := fun w =>
    (Mz Ĉ c 0 w.1 * (∏ j ∈ D, Dfun (ε j) (Λz c 0 w.1 j).1 (α (σ j))) *
      (Cb (α ∘ fb) (w.2.1, w.2.2 - Λsum c w.1) * cexp (π * I * (w.2.2 * s)))) *
    Gp w.1 w.2.1 (shiftV σ ε (Λz c 0 w.1) 0 c.size α) t with hgT
  -- the integral over the Lemma G variables
  have hpt : ∀ w : ZT c × (ℝ × ℝ), ∫ ξ, F (w, ξ) = gT w := by
    intro w
    have e1 : ∀ ξ : ℝ × Ξ, F (w, ξ) =
        (Mz Ĉ c 0 w.1 * (∏ j ∈ D, Dfun (ε j) (Λz c 0 w.1 j).1 (α (σ j))) *
          (Cb (α ∘ fb) (w.2.1, w.2.2 - Λsum c w.1) * cexp (π * I * (w.2.2 * s)))) *
        (H w.1 w.2.1 (shiftV σ ε (Λz c 0 w.1) 0 c.size α ∘ fH) ξ *
          cexp (π * I * ((ξ.1 + bfr ξ.2) * t))) := by
      intro ξ
      have e2' : F (w, ξ) = (MzS P' c 0 (α ∘ fT P' c 0) w.1 *
          Cb (α ∘ fb) (w.2.1, w.2.2 - Λsum c w.1)) *
          H w.1 w.2.1 (α ∘ fH + sV σ ε c fH w.1) ξ * e2 (ξ.1 + bfr ξ.2, w.2.2) t s := rfl
      rw [e2', hM, ← shiftV_comp, e2_split]
      dsimp only
      push_cast
      ring
    simp_rw [e1]
    rw [integral_const_mul, ← hGp w.1 w.2.1 _ t ht]
  -- the twisted term is the sheared term after the shear
  have htw : ∀ w, gTerm σ ε (twistP P s) fb Cb c Gp Y Y' α t s w = gT ((shearZ c).symm w) := by
    intro w
    have hMt : Mz (fun j => (twistP P s j).C (α ∘ (twistP P s j).f)) c 0 w.1 =
        cexp (π * I * (Λsum c w.1 * s)) * Mz Ĉ c 0 w.1 := by
      exact Mz_tsym s Ĉ c 0 w.1
    simp only [gTerm, hMt, hgT, shearZ_symm_apply, add_sub_cancel_right]
    have e : cexp (π * I * (((w.2.2 + Λsum c w.1 : ℝ) : ℂ) * s)) =
        cexp (π * I * (Λsum c w.1 * s)) * cexp (π * I * (w.2.2 * s)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e, hD_def]
    ring
  have hmp := (measurePreserving_shearZ c).symm
  have hgTi : Integrable gT := (hFi.integral_prod_left).congr (Eventually.of_forall hpt)
  refine ⟨?_, ?_⟩
  · have h := (hmp.integrable_comp_emb (shearZ c).symm.measurableEmbedding).2 hgTi
    exact h.congr (Eventually.of_forall fun w => (htw w).symm)
  · rw [hid β t s]
    have e3 : ∫ x, F x = ∫ w, ∫ ξ, F (w, ξ) := integral_prod _ hFi
    rw [show (∫ x, kprod (shearM MS Cb) (Kc H (sV σ ε c fH)) β x * e2 (FrA bfr x) t s) =
      ∫ x, F x from rfl, e3]
    simp_rw [hpt, htw]
    exact hmp.integral_comp (shearZ c).symm.measurableEmbedding gT

end Term

end WaveTurbulence.ClassJR
