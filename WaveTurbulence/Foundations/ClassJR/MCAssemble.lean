/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainM
public import WaveTurbulence.Foundations.ClassJR.MCGP

/-!
# Assembling the coefficient of a chain term

In Case 2 of DH21 Proposition 5.1 (L1137–L1150), after fixing the frequencies and applying Lemma G,
each term of the chain integral is
`∫ M(β_M; w) H(w; β_H + s(w), ξ) e^{πi(fr(ξ) t + λ₂ s)} dw dξ`, where
* `w = (w', (λ₁, λ₂))` collects the frequencies of the pairs (`w'`) and of the bottom coefficient;
* `M` is the product of the pair symbols and of the bottom symbol;
* `H` is a Lemma G symbol with bounds uniform in its parameters `(w', λ₁)`, evaluated at variables
  shifted by `s(w')` (the shift `α̃_j = α_j + ε_jλ_{j,1}` of DH21 (kusingI)).

This file shows that the pushforward of `M ⊗ H` to the frequencies `(fr(ξ), λ₂)` (`pushF`, along a
shear `fr(u, η) = u + b(η)`) is a coefficient symbol with the DH23 weights (`srep_assemble`), and
computes its time integral (`integral_assemble`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

attribute [local instance] isAddRightInvariant_volume_prod

section PushF

variable {ι : Type*} [Fintype ι] {X Q : Type*} [MeasureSpace X] [MeasureSpace Q]
  [SFinite (volume : Measure Q)] {a : (ι → ℝ) → X → ℂ}

/-- **The pushforward along a shear**: if `Fr (ψ (γ, q)) = γ + b q` for a measure-preserving `ψ`,
then `pushF ψ b a` is the symbol of `∫ a(α, x) φ(Fr x) dx`. -/
@[expose] noncomputable def pushF (ψ : (ℝ × ℝ) × Q ≃ᵐ X) (b : Q → ℝ × ℝ)
    (a : (ι → ℝ) → X → ℂ) : (ι → ℝ) → ℝ × ℝ → ℂ :=
  pushSym (fun α ζ => a α (ψ ζ)) b

variable {ψ : (ℝ × ℝ) × Q ≃ᵐ X} {b : Q → ℝ × ℝ}

theorem pushF_symReg (ha : SymReg a) (hψ : MeasurePreserving ψ) (hb : Measurable b) :
    SymReg (pushF ψ b a) :=
  pushSym_symReg (ha.comp_equiv ψ hψ) hb

theorem lintegral_weight_pushF_le (ha : SymReg a) (hψ : MeasurePreserving ψ) (hb : Measurable b)
    {Fr : X → ℝ × ℝ} (hFr : ∀ ζ, Fr (ψ ζ) = ζ.1 + b ζ.2) {w : (ι → ℝ) → ℝ × ℝ → ℝ≥0∞}
    (hw : Measurable (Function.uncurry w)) (k : ℕ) :
    ∫⁻ α, ∫⁻ γ, w α γ * dnorm k (pushF ψ b a) α γ ≤ ∫⁻ α, ∫⁻ x, w α (Fr x) * dnorm k a α x := by
  refine (lintegral_weight_pushSym_le (ha.comp_equiv ψ hψ) hb hw k).trans_eq ?_
  refine lintegral_congr fun α => ?_
  rw [← hψ.lintegral_comp_emb ψ.measurableEmbedding]
  refine lintegral_congr fun ζ => ?_
  rw [hFr]
  rfl

theorem integral_pushF_mul (ha : SymReg a) (hψ : MeasurePreserving ψ) (hb : Measurable b)
    {Fr : X → ℝ × ℝ} (hFr : ∀ ζ, Fr (ψ ζ) = ζ.1 + b ζ.2) (α : ι → ℝ) {φ : ℝ × ℝ → ℂ}
    (hφ : AEStronglyMeasurable φ) {C : ℝ} (hφC : ∀ γ, ‖φ γ‖ ≤ C) :
    ∫ γ, pushF ψ b a α γ * φ γ = ∫ x, a α x * φ (Fr x) := by
  rw [pushF, integral_pushSym_mul (ha.comp_equiv ψ hψ) hb α hφ hφC,
    ← hψ.integral_comp ψ.measurableEmbedding]
  simp_rw [hFr]

end PushF

section Shift

variable {ι : Type*} [Fintype ι] {Γ : Type*}

/-- Derivatives commute with translations of the variables. -/
theorem dnorm_add_shift (H : (ι → ℝ) → Γ → ℂ) (s : ι → ℝ) (k : ℕ) (β : ι → ℝ) (γ : Γ) :
    dnorm k (fun β γ => H (β + s) γ) β γ = dnorm k H (β + s) γ := by
  simp only [dnorm]
  have e : lift1 (fun β γ => H (β + s) γ) γ = fun x => lift1 H γ (x + WithLp.toLp 1 s) := by
    funext x
    simp only [lift1, WithLp.ofLp_add]
  rw [e, iteratedFDeriv_comp_add_right]
  rfl

end Shift

section Weights

theorem wL_le_mul {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    wL c (u, v) ≤ (1 + ‖u‖ₑ) ^ c * (1 + ‖v‖ₑ) ^ c := by
  unfold wL
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hc]
  refine ENNReal.rpow_le_rpow ?_ hc
  calc (1 : ℝ≥0∞) + ‖u‖ₑ + ‖v‖ₑ ≤ 1 + ‖u‖ₑ + ‖v‖ₑ + ‖u‖ₑ * ‖v‖ₑ := le_self_add
    _ = (1 + ‖u‖ₑ) * (1 + ‖v‖ₑ) := by ring

end Weights

section Equiv

variable (W Ξ : Type*) [MeasureSpace W] [MeasureSpace Ξ]

/-- The reordering `((u₁, u₂), ((w, λ₁), η)) ↦ ((w, (λ₁, u₂)), (u₁, η))`. -/
@[expose] noncomputable def psiA : (ℝ × ℝ) × ((W × ℝ) × Ξ) ≃ᵐ (W × (ℝ × ℝ)) × (ℝ × Ξ) :=
  (mswap.trans ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl (ℝ × Ξ))).trans
    (mswap.trans (MeasurableEquiv.prodAssoc.prodCongr (MeasurableEquiv.refl (ℝ × Ξ))))))

theorem psiA_apply (ζ : (ℝ × ℝ) × ((W × ℝ) × Ξ)) :
    psiA W Ξ ζ = ((ζ.2.1.1, (ζ.2.1.2, ζ.1.2)), (ζ.1.1, ζ.2.2)) := rfl

theorem measurePreserving_psiA [SFinite (volume : Measure W)] [SFinite (volume : Measure Ξ)] :
    MeasurePreserving (psiA W Ξ) := by
  have h1 : MeasurePreserving (mswap : (ℝ × ℝ) × ((W × ℝ) × Ξ) ≃ᵐ (ℝ × (W × ℝ)) × (ℝ × Ξ)) :=
    measurePreserving_mswap
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl (ℝ × Ξ)) :
      (ℝ × (W × ℝ)) × (ℝ × Ξ) ≃ᵐ ((W × ℝ) × ℝ) × (ℝ × Ξ)) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (W × ℝ)))).prod
      (MeasurePreserving.id (volume : Measure (ℝ × Ξ)))
  have h3 : MeasurePreserving (mswap : ((W × ℝ) × ℝ) × (ℝ × Ξ) ≃ᵐ ((W × ℝ) × ℝ) × (ℝ × Ξ)) :=
    measurePreserving_mswap
  have h4 : MeasurePreserving (MeasurableEquiv.prodAssoc.prodCongr (MeasurableEquiv.refl (ℝ × Ξ)) :
      ((W × ℝ) × ℝ) × (ℝ × Ξ) ≃ᵐ (W × (ℝ × ℝ)) × (ℝ × Ξ)) :=
    volume_preserving_prodAssoc.prod (MeasurePreserving.id (volume : Measure (ℝ × Ξ)))
  exact h4.comp (h3.comp (h2.comp h1))

end Equiv

section Assemble

variable {W : Type} [MeasureSpace W] [SFinite (volume : Measure W)]
  {ιM ιH : Type} [Fintype ιM] [Fintype ιH] {Ξ : Type} [MeasureSpace Ξ] [SFinite (volume : Measure Ξ)]

/-- The Lemma G factor `H(w', λ₁; β + s(w'), ξ)` of a chain term, as a coupled symbol. -/
@[expose] def Kc (H : W → ℝ → (ιH → ℝ) → ℝ × Ξ → ℂ) (sH : W → ιH → ℝ) :
    (ιH → ℝ) → (W × (ℝ × ℝ)) × (ℝ × Ξ) → ℂ :=
  fun β x => H x.1.1 x.1.2.1 (β + sH x.1.1) x.2

/-- The frequencies `(fr(ξ), λ₂)` of a chain term. -/
@[expose] def FrA (bfr : Ξ → ℝ) (x : (W × (ℝ × ℝ)) × (ℝ × Ξ)) : ℝ × ℝ :=
  (x.2.1 + bfr x.2.2, x.1.2.2)

/-- The shift of the shear. -/
@[expose] def bA (bfr : Ξ → ℝ) (q : (W × ℝ) × Ξ) : ℝ × ℝ := (bfr q.2, 0)

omit [SFinite (volume : Measure W)] [SFinite (volume : Measure Ξ)] in
theorem FrA_psiA (bfr : Ξ → ℝ) (ζ : (ℝ × ℝ) × ((W × ℝ) × Ξ)) :
    FrA bfr (psiA W Ξ ζ) = ζ.1 + bA bfr ζ.2 := by
  simp [FrA, bA, psiA_apply, Prod.ext_iff]

omit [SFinite (volume : Measure W)] [SFinite (volume : Measure Ξ)] in
theorem measurable_bA {bfr : Ξ → ℝ} (hbfr : Measurable bfr) : Measurable (bA (W := W) bfr) :=
  (hbfr.comp measurable_snd).prodMk measurable_const

/-- **The coefficient of a chain term** (DH21 L1137–L1150): the pushforward of `M ⊗ H` to the
frequencies `(fr(ξ), λ₂)`. -/
@[expose] noncomputable def Cassem (M : (ιM → ℝ) → W × (ℝ × ℝ) → ℂ)
    (H : W → ℝ → (ιH → ℝ) → ℝ × Ξ → ℂ) (bfr : Ξ → ℝ) (sH : W → ιH → ℝ) :
    (ιM ⊕ ιH → ℝ) → ℝ × ℝ → ℂ :=
  pushF (psiA W Ξ) (bA bfr) (kprod M (Kc H sH))

variable {M : (ιM → ℝ) → W × (ℝ × ℝ) → ℂ} {H : W → ℝ → (ιH → ℝ) → ℝ × Ξ → ℂ} {bfr : Ξ → ℝ}
  {sH : W → ιH → ℝ}

omit [MeasureSpace W] [SFinite (volume : Measure W)] [SFinite (volume : Measure Ξ)] in
theorem contDiff_Kc (hH : ∀ p L0, SymReg (H p L0)) (x : (W × (ℝ × ℝ)) × (ℝ × Ξ)) :
    ContDiff ℝ ∞ fun β => Kc H sH β x :=
  ((hH x.1.1 x.1.2.1).smooth x.2).comp (contDiff_id.add contDiff_const)

omit [Fintype ιH] [SFinite (volume : Measure W)] [SFinite (volume : Measure Ξ)] in
theorem measurable_Kc
    (hHm : Measurable fun x : (W × ℝ) × ((ιH → ℝ) × (ℝ × Ξ)) => H x.1.1 x.1.2 x.2.1 x.2.2)
    (hsH : Measurable sH) : StronglyMeasurable (Function.uncurry (Kc H sH)) := by
  have e : Function.uncurry (Kc H sH) =
      (fun x : (W × ℝ) × ((ιH → ℝ) × (ℝ × Ξ)) => H x.1.1 x.1.2 x.2.1 x.2.2) ∘
        (fun y : (ιH → ℝ) × ((W × (ℝ × ℝ)) × (ℝ × Ξ)) =>
          ((y.2.1.1, y.2.1.2.1), (y.1 + sH y.2.1.1, y.2.2))) := rfl
  rw [e]
  exact (hHm.comp (by fun_prop)).stronglyMeasurable

omit [MeasureSpace W] [SFinite (volume : Measure W)] [SFinite (volume : Measure Ξ)] in
/-- The coupling integrals of `Kc` are those of `H`, by translation invariance. -/
theorem lintegral_Kc_eq (w : W × (ℝ × ℝ)) (wH : (ιH → ℝ) → ℝ × Ξ → ℝ≥0∞) (j : ℕ) :
    ∫⁻ β, ∫⁻ ξ, wH (β + sH w.1) ξ * dnorm j (Kc H sH) β (w, ξ) =
      ∫⁻ β, ∫⁻ ξ, wH β ξ * dnorm j (H w.1 w.2.1) β ξ := by
  have e : ∀ β ξ, dnorm j (Kc H sH) β (w, ξ) = dnorm j (H w.1 w.2.1) (β + sH w.1) ξ :=
    fun β ξ => dnorm_add_shift (H w.1 w.2.1) (sH w.1) j β ξ
  simp_rw [e]
  exact lintegral_add_right_eq_self (fun β => ∫⁻ ξ, wH β ξ * dnorm j (H w.1 w.2.1) β ξ) (sH w.1)

/-- **The bounds of the coefficient of a chain term** (DH21 L1137–L1150 with the DH23 weights).
The weights split as `wL c (fr, λ₂) ≤ ⟨fr⟩^c ⟨λ₂⟩^c`; `⟨fr⟩^c` is paid by the Lemma G symbol, `⟨λ₂⟩^c`
by `M`. For a variable of `H`, the shift `s(w')` costs `⟨s⟩^b ≤ v(w')`, also paid by `M`. -/
theorem srep_assemble {θ a b A NM NH : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haθ : a ≤ θ) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hMs : ∀ w, ContDiff ℝ ∞ fun β => M β w)
    (hMm : StronglyMeasurable (Function.uncurry M)) (hNM : 0 ≤ NM)
    (hMn : ∀ k, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ θ * dnorm k M β w ≤ gev NM A k)
    (hMv : ∀ i, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖β i‖ₑ) ^ b * dnorm 0 M β w ≤
      ENNReal.ofReal NM)
    {vH : ιH → W → ℝ≥0∞} (hvH : ∀ i, Measurable (vH i))
    (hMf : ∀ i, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ a * vH i w.1 * dnorm 0 M β w ≤ ENNReal.ofReal NM)
    (hbfr : Measurable bfr) (hNH : 0 ≤ NH)
    (hH : ∀ p L0, FRep θ a b A NH (fun ξ => ξ.1 + bfr ξ.2) (H p L0))
    (hHm : Measurable fun x : (W × ℝ) × ((ιH → ℝ) × (ℝ × Ξ)) => H x.1.1 x.1.2 x.2.1 x.2.2)
    (hsH : Measurable sH) (hsv : ∀ w i, (1 + ‖sH w i‖ₑ) ^ b ≤ vH i w) :
    SRep θ a b A (4 * NM * NH) (Cassem M H bfr sH) ∧ SymReg (kprod M (Kc H sH)) ∧
      ∀ β t s, ∫ lam, Cassem M H bfr sH β lam * e2 lam t s =
        ∫ x, kprod M (Kc H sH) β x * e2 (FrA bfr x) t s := by
  have hKs := contDiff_Kc (sH := sH) fun p L0 => (hH p L0).reg
  have hKm := measurable_Kc hHm hsH
  have hfr : Measurable fun ξ : ℝ × Ξ => ξ.1 + bfr ξ.2 := by fun_prop
  -- the coupling bounds
  have hgθ : ∀ (c : ℝ), 0 ≤ c → c ≤ θ → ∀ j (w : W × (ℝ × ℝ)),
      ∫⁻ β, ∫⁻ ξ, (1 + ‖ξ.1 + bfr ξ.2‖ₑ) ^ c * dnorm j (Kc H sH) β (w, ξ) ≤ gev NH A j * 1 := by
    intro c hc hcθ j w
    rw [mul_one]
    have h := lintegral_Kc_eq (H := H) (sH := sH) w
      (fun (_ : ιH → ℝ) (ξ : ℝ × Ξ) => (1 + ‖ξ.1 + bfr ξ.2‖ₑ) ^ c) j
    rw [h]
    refine le_trans (lintegral_mono fun β => lintegral_mono fun ξ => ?_) ((hH w.1 w.2.1).norm j)
    exact mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_le le_self_add hcθ) le_rfl
  have hwfr : ∀ c : ℝ, Measurable (Function.uncurry fun (_ : ιH → ℝ)
      (x : (W × (ℝ × ℝ)) × (ℝ × Ξ)) => ((1 : ℝ≥0∞) + ‖x.2.1 + bfr x.2.2‖ₑ) ^ c) := fun c => by
    change Measurable fun y : (ιH → ℝ) × ((W × (ℝ × ℝ)) × (ℝ × Ξ)) =>
      ((1 : ℝ≥0∞) + ‖y.2.2.1 + bfr y.2.2.2‖ₑ) ^ c
    fun_prop
  have hwl2 : ∀ c : ℝ, Measurable (Function.uncurry fun (_ : ιM → ℝ) (w : W × (ℝ × ℝ)) =>
      ((1 : ℝ≥0∞) + ‖w.2.2‖ₑ) ^ c) := fun c => by
    change Measurable fun y : (ιM → ℝ) × (W × (ℝ × ℝ)) => ((1 : ℝ≥0∞) + ‖y.2.2.2‖ₑ) ^ c
    fun_prop
  -- the Gevrey bounds of the symbol
  have hkn : ∀ k, ∫⁻ β, ∫⁻ x, wL θ (FrA bfr x) * dnorm k (kprod M (Kc H sH)) β x ≤
      gev (4 * NM * NH) A k := by
    intro k
    have h := lintegral_kprod_le hMs hMm hKs hKm (hwl2 θ) (hwfr θ) measurable_const
      (g := gev NH A) (hgθ θ hθ le_rfl) k
    simp only [mul_one] at h
    refine le_trans (lintegral_mono fun β => lintegral_mono fun x => ?_)
      (h.trans (gev_conv_le hNM hNH hA hMn (fun j => le_rfl) k))
    refine mul_le_mul' ?_ le_rfl
    rw [mul_comm]
    exact wL_le_mul hθ _ _
  -- the per-variable bounds of the symbol
  have hkv : ∀ i, ∫⁻ β, ∫⁻ x, wL a (FrA bfr x) * (1 + ‖β i‖ₑ) ^ b *
      dnorm 0 (kprod M (Kc H sH)) β x ≤ ENNReal.ofReal (4 * NM * NH) := by
    have hc : ENNReal.ofReal NM * ENNReal.ofReal NH ≤ ENNReal.ofReal (4 * NM * NH) := by
      rw [← ENNReal.ofReal_mul hNM]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hNM hNH])
    rintro (i | i)
    · have hw : Measurable (Function.uncurry fun (β : ιM → ℝ) (w : W × (ℝ × ℝ)) =>
          ((1 : ℝ≥0∞) + ‖w.2.2‖ₑ) ^ a * (1 + ‖β i‖ₑ) ^ b) := by
        change Measurable fun y : (ιM → ℝ) × (W × (ℝ × ℝ)) =>
          ((1 : ℝ≥0∞) + ‖y.2.2.2‖ₑ) ^ a * (1 + ‖y.1 i‖ₑ) ^ b
        fun_prop
      have h := lintegral_kprod_le hMs hMm hKs hKm hw (hwfr a) measurable_const
        (g := gev NH A) (hgθ a ha haθ) 0
      simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self, mul_one, gev_zero_eq] at h
      refine le_trans (lintegral_mono fun β => lintegral_mono fun x => ?_)
        (h.trans ((mul_le_mul' (hMv i) le_rfl).trans hc))
      refine mul_le_mul' ?_ le_rfl
      calc wL a (FrA bfr x) * (1 + ‖β (Sum.inl i)‖ₑ) ^ b
          ≤ ((1 + ‖x.2.1 + bfr x.2.2‖ₑ) ^ a * (1 + ‖x.1.2.2‖ₑ) ^ a) *
              (1 + ‖β (Sum.inl i)‖ₑ) ^ b := mul_le_mul' (wL_le_mul ha _ _) le_rfl
        _ = (1 + ‖x.1.2.2‖ₑ) ^ a * (1 + ‖β (Sum.inl i)‖ₑ) ^ b *
              (1 + ‖x.2.1 + bfr x.2.2‖ₑ) ^ a := by ring
    · have hw : Measurable (Function.uncurry fun (_ : ιM → ℝ) (w : W × (ℝ × ℝ)) =>
          ((1 : ℝ≥0∞) + ‖w.2.2‖ₑ) ^ a * vH i w.1) := by
        change Measurable fun y : (ιM → ℝ) × (W × (ℝ × ℝ)) =>
          ((1 : ℝ≥0∞) + ‖y.2.2.2‖ₑ) ^ a * vH i y.2.1
        have := hvH i
        fun_prop
      have hwK : Measurable (Function.uncurry fun (β : ιH → ℝ) (x : (W × (ℝ × ℝ)) × (ℝ × Ξ)) =>
          ((1 : ℝ≥0∞) + ‖x.2.1 + bfr x.2.2‖ₑ) ^ a * (1 + ‖β i + sH x.1.1 i‖ₑ) ^ b) := by
        change Measurable fun y : (ιH → ℝ) × ((W × (ℝ × ℝ)) × (ℝ × Ξ)) =>
          ((1 : ℝ≥0∞) + ‖y.2.2.1 + bfr y.2.2.2‖ₑ) ^ a * (1 + ‖y.1 i + sH y.2.1.1 i‖ₑ) ^ b
        have hs : Measurable fun y : (ιH → ℝ) × ((W × (ℝ × ℝ)) × (ℝ × Ξ)) => sH y.2.1.1 i :=
          (measurable_pi_apply i).comp (hsH.comp (by fun_prop))
        fun_prop
      have hKb : ∀ j (w : W × (ℝ × ℝ)), ∫⁻ β, ∫⁻ ξ,
          ((1 : ℝ≥0∞) + ‖ξ.1 + bfr ξ.2‖ₑ) ^ a * (1 + ‖β i + sH w.1 i‖ₑ) ^ b *
            dnorm j (Kc H sH) β (w, ξ) ≤ (if j = 0 then ENNReal.ofReal NH else ⊤) * 1 := by
        intro j w
        rw [mul_one]
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp only [↓reduceIte]
          have h := lintegral_Kc_eq (H := H) (sH := sH) w
            (fun (β : ιH → ℝ) (ξ : ℝ × Ξ) => (1 + ‖ξ.1 + bfr ξ.2‖ₑ) ^ a * (1 + ‖β i‖ₑ) ^ b) 0
          simp only [Pi.add_apply] at h
          rw [h]
          refine le_trans (le_of_eq ?_) ((hH w.1 w.2.1).wnorm i)
          refine lintegral_congr fun β => lintegral_congr fun ξ => ?_
          rw [dnorm_zero]
        · simp only [hj.ne', ↓reduceIte]
          exact le_top
      have h := lintegral_kprod_le hMs hMm hKs hKm hw hwK measurable_const hKb 0
      simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self, mul_one, ↓reduceIte] at h
      refine le_trans (lintegral_mono fun β => lintegral_mono fun x => ?_)
        (h.trans ((mul_le_mul' (hMf i) le_rfl).trans hc))
      refine mul_le_mul' ?_ le_rfl
      calc wL a (FrA bfr x) * (1 + ‖β (Sum.inr i)‖ₑ) ^ b
          ≤ ((1 + ‖x.2.1 + bfr x.2.2‖ₑ) ^ a * (1 + ‖x.1.2.2‖ₑ) ^ a) *
              ((1 + ‖β (Sum.inr i) + sH x.1.1 i‖ₑ) ^ b * vH i x.1.1) :=
            mul_le_mul' (wL_le_mul ha _ _) ((one_add_enorm_rpow_shift_le hb _ _).trans
              (mul_le_mul' le_rfl (hsv x.1.1 i)))
        _ = (1 + ‖x.1.2.2‖ₑ) ^ a * vH i x.1.1 *
              ((1 + ‖x.2.1 + bfr x.2.2‖ₑ) ^ a * (1 + ‖β (Sum.inr i) + sH x.1.1 i‖ₑ) ^ b) := by
            ring
  -- regularity and the pushforward
  have hreg : SymReg (kprod M (Kc H sH)) := SymReg.of_lintegral (contDiff_kprod hMs hKs)
    (measurable_kprod hMm hKm) fun k => ne_top_of_le_ne_top (gev_ne_top _ _ _)
      ((lintegral_mono fun β => lintegral_mono fun x =>
        le_mul_of_one_le_left bot_le (one_le_wL hθ _)).trans (hkn k))
  have hψ := measurePreserving_psiA W Ξ
  have hbA := measurable_bA (W := W) hbfr
  refine ⟨⟨by positivity, pushF_symReg hreg hψ hbA, fun k => ?_, fun i => ?_⟩, hreg,
    fun β t s => ?_⟩
  · exact (lintegral_weight_pushF_le hreg hψ hbA (FrA_psiA bfr) (w := fun _ lam => wL θ lam)
      ((measurable_wL θ).comp measurable_snd) k).trans (hkn k)
  · have hw : Measurable (Function.uncurry fun (β : ιM ⊕ ιH → ℝ) (lam : ℝ × ℝ) =>
        wL a lam * (1 + ‖β i‖ₑ) ^ b) := by
      change Measurable fun y : (ιM ⊕ ιH → ℝ) × (ℝ × ℝ) => wL a y.2 * (1 + ‖y.1 i‖ₑ) ^ b
      have := measurable_wL a
      fun_prop
    have h := lintegral_weight_pushF_le hreg hψ hbA (FrA_psiA bfr) hw 0
    simp only [dnorm_zero] at h
    exact h.trans (by simpa only [dnorm_zero] using hkv i)
  · have hφ : Continuous fun lam : ℝ × ℝ => e2 lam t s := by unfold e2; fun_prop
    exact integral_pushF_mul hreg hψ hbA (FrA_psiA bfr) β (φ := fun lam => e2 lam t s)
      hφ.aestronglyMeasurable (C := 1) fun lam => (norm_e2 lam t s).le

end Assemble

end WaveTurbulence.ClassJR
