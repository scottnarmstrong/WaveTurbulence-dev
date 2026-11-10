/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCSRep
public import WaveTurbulence.Foundations.ClassJR.MCK1

/-!
# DH21 Proposition 5.1, Case 1: the type 1 recursion

DH21 L1100–L1112 (Case 1). Given coefficient symbols `D₁, D₂, D₃` of the three subcouples (with their
frequencies swapped as in (newexp1)), the new coefficient is
`𝒞(α, v) = ∫ D₁(α₁, λ₁) D₂(α₂, λ₂) D₃(α₃, λ₃) gE(α_𝔯 + λ*; v₁, τ₁) gE(-α_𝔯 + λ**; v₂, τ₂) dλ dτ`,
where `λ* = Σ_j λ_{j,1}` and `λ** = Σ_j λ_{j,2}` (DH21 (newexp3), (regcplexpl), (regcplex1)).

As a symbol it is the pushforward (`pushR`) to the frequencies `v = (v₁, v₂)` of the coupled product
`a1 = kprod (D₁ ⊗ D₂ ⊗ D₃) K1`.
* (maincoef2): `wL θ v ≤ (1 + |v₁|)^θ + (1 + |v₂|)^θ`, and each term is absorbed by one `gE` factor
  (`lintegral_K1_le`). No frequency weight of the subcouples is used, so the `λ₂` weight of DH23
  comes from the structure, as audit W4 asks.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

attribute [local instance] isAddRightInvariant_volume_prod

section PushR

variable {ι : Type*} [Fintype ι] {X Q : Type*} [MeasureSpace X] [MeasureSpace Q]
  [SFinite (volume : Measure Q)]

/-- **The pushforward to the frequencies through a reordering** `ρ : (ℝ × ℝ) × Q ≃ X`:
`𝒞(α, v) = ∫ a(α, ρ(v, q)) dq`. -/
@[expose] noncomputable def pushR (ρ : (ℝ × ℝ) × Q ≃ᵐ X) (a : (ι → ℝ) → X → ℂ) :
    (ι → ℝ) → ℝ × ℝ → ℂ :=
  pushSym (fun α ζ => a α (ρ ζ)) (fun _ => (0 : ℝ × ℝ))

variable {ρ : (ℝ × ℝ) × Q ≃ᵐ X} {a : (ι → ℝ) → X → ℂ}

theorem pushR_symReg (ha : SymReg a) (hρ : MeasurePreserving ρ) : SymReg (pushR ρ a) :=
  pushSym_symReg (ha.comp_equiv ρ hρ) measurable_const

theorem lintegral_weight_pushR_le (ha : SymReg a) (hρ : MeasurePreserving ρ)
    {w : (ι → ℝ) → ℝ × ℝ → ℝ≥0∞} (hw : Measurable (Function.uncurry w)) (k : ℕ) :
    ∫⁻ α, ∫⁻ γ, w α γ * dnorm k (pushR ρ a) α γ ≤
      ∫⁻ α, ∫⁻ x, w α (ρ.symm x).1 * dnorm k a α x := by
  refine (lintegral_weight_pushSym_le (ha.comp_equiv ρ hρ) measurable_const hw k).trans_eq ?_
  refine lintegral_congr fun α => ?_
  simp only [add_zero]
  have := hρ.symm.lintegral_comp_emb ρ.symm.measurableEmbedding
    (fun ζ : (ℝ × ℝ) × Q => w α ζ.1 * dnorm k (fun α y => a α (ρ y)) α ζ)
  rw [← this]
  refine lintegral_congr fun x => ?_
  have key : lift1 (fun α y => a α (ρ y)) (ρ.symm x) = lift1 a x := by
    funext β
    simp [lift1]
  simp only [dnorm, key]

theorem integral_pushR_mul (ha : SymReg a) (hρ : MeasurePreserving ρ) (α : ι → ℝ)
    {φ : ℝ × ℝ → ℂ} (hφ : AEStronglyMeasurable φ) {C : ℝ} (hφC : ∀ γ, ‖φ γ‖ ≤ C) :
    ∫ γ, pushR ρ a α γ * φ γ = ∫ x, a α x * φ (ρ.symm x).1 := by
  rw [pushR, integral_pushSym_mul (ha.comp_equiv ρ hρ) measurable_const α hφ hφC]
  simp only [add_zero]
  have := hρ.symm.integral_comp ρ.symm.measurableEmbedding
    (fun ζ : (ℝ × ℝ) × Q => a α (ρ ζ) * φ ζ.1)
  rw [← this]
  simp only [MeasurableEquiv.apply_symm_apply]

end PushR

section Helpers

theorem lintegral_lintegral_add {A B : Type*} [MeasureSpace A] [MeasureSpace B]
    [SFinite (volume : Measure B)] {F G : A → B → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    ∫⁻ a, ∫⁻ b, (F a b + G a b) = (∫⁻ a, ∫⁻ b, F a b) + ∫⁻ a, ∫⁻ b, G a b := by
  calc ∫⁻ a, ∫⁻ b, (F a b + G a b) = ∫⁻ a, ((∫⁻ b, F a b) + ∫⁻ b, G a b) :=
        lintegral_congr fun a => lintegral_add_left hF.of_uncurry_left _
    _ = _ := lintegral_add_left hF.lintegral_prod_right' _

/-- Splitting a double integral along a pointwise bound by a sum. -/
theorem lintegral_two_le {A B : Type*} [MeasureSpace A] [MeasureSpace B]
    [SFinite (volume : Measure B)] {F G H : A → B → ℝ≥0∞} {X Y : ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) (hpt : ∀ a b, H a b ≤ F a b + G a b)
    (hX : ∫⁻ a, ∫⁻ b, F a b ≤ X) (hY : ∫⁻ a, ∫⁻ b, G a b ≤ Y) :
    ∫⁻ a, ∫⁻ b, H a b ≤ X + Y := by
  calc ∫⁻ a, ∫⁻ b, H a b ≤ ∫⁻ a, ∫⁻ b, (F a b + G a b) :=
        lintegral_mono fun a => lintegral_mono fun b => hpt a b
    _ = _ := lintegral_lintegral_add hF
    _ ≤ X + Y := add_le_add hX hY

theorem one_add_enorm_add_le (x y : ℝ) : 1 + ‖x + y‖ₑ ≤ (1 + ‖x‖ₑ) * (1 + ‖y‖ₑ) :=
  calc 1 + ‖x + y‖ₑ ≤ 1 + (‖x‖ₑ + ‖y‖ₑ) := add_le_add le_rfl (enorm_add_le x y)
    _ ≤ 1 + (‖x‖ₑ + ‖y‖ₑ) + ‖x‖ₑ * ‖y‖ₑ := le_self_add
    _ = (1 + ‖x‖ₑ) * (1 + ‖y‖ₑ) := by ring

/-- `(1 + |x|)^b ≤ (1 + |x + c|)^b (1 + |c|)^b`. -/
theorem one_add_enorm_rpow_shift_le {b : ℝ} (hb : 0 ≤ b) (x c : ℝ) :
    (1 + ‖x‖ₑ) ^ b ≤ (1 + ‖x + c‖ₑ) ^ b * (1 + ‖c‖ₑ) ^ b := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hb]
  refine ENNReal.rpow_le_rpow ?_ hb
  have h := one_add_enorm_add_le (x + c) (-c)
  rwa [add_neg_cancel_right, enorm_neg] at h

/-- `wL a (v₁, v₂) ≤ (1 + |v₁|)^a + (1 + |v₂|)^a` for `0 ≤ a ≤ 1`. -/
theorem wL_le_add {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (v₁ v₂ : ℝ) :
    wL a (v₁, v₂) ≤ (1 + ‖v₁‖ₑ) ^ a + (1 + ‖v₂‖ₑ) ^ a := by
  unfold wL
  refine (ENNReal.rpow_add_le_add_rpow _ _ h0 h1).trans (add_le_add le_rfl ?_)
  exact ENNReal.rpow_le_rpow le_add_self h0

/-- `(1 + |λ₁|)^b ≤ wL θ λ` for `0 ≤ b ≤ θ`. -/
theorem one_add_rpow_le_wL {b θ : ℝ} (hb : 0 ≤ b) (hbθ : b ≤ θ) (lam : ℝ × ℝ) :
    (1 + ‖lam.1‖ₑ) ^ b ≤ wL θ lam := by
  unfold wL
  calc (1 + ‖lam.1‖ₑ) ^ b ≤ (1 + ‖lam.1‖ₑ) ^ θ :=
        ENNReal.rpow_le_rpow_of_exponent_le le_self_add hbθ
    _ ≤ (1 + ‖lam.1‖ₑ + ‖lam.2‖ₑ) ^ θ := ENNReal.rpow_le_rpow le_self_add (hb.trans hbθ)

theorem gev_add {N N' A : ℝ} (hN : 0 ≤ N) (hN' : 0 ≤ N') (hA : 0 ≤ A) (k : ℕ) :
    gev N A k + gev N' A k = gev (N + N') A k := by
  unfold gev
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  ring_nf

end Helpers

section Case1Defs

/-- The frequencies `((λ₁, λ₂), λ₃)` of the three subcouples. -/
abbrev ZC1 : Type := ((ℝ × ℝ) × (ℝ × ℝ)) × (ℝ × ℝ)

/-- The variables `((v₁, τ₁), (v₂, τ₂))` of the two `gE` factors. -/
abbrev QC1 : Type := (ℝ × ℝ) × (ℝ × ℝ)

/-- `λ* = λ_{1,1} + λ_{2,1} + λ_{3,1}` (DH21 L1104). -/
@[expose] def lst (z : ZC1) : ℝ := z.1.1.1 + z.1.2.1 + z.2.1

/-- `λ** = λ_{1,2} + λ_{2,2} + λ_{3,2}` (DH21 L1104). -/
@[expose] def lss (z : ZC1) : ℝ := z.1.1.2 + z.1.2.2 + z.2.2

@[fun_prop] theorem continuous_lst : Continuous lst := by unfold lst; fun_prop

@[fun_prop] theorem continuous_lss : Continuous lss := by unfold lss; fun_prop

@[fun_prop] theorem measurable_lst : Measurable lst := continuous_lst.measurable

@[fun_prop] theorem measurable_lss : Measurable lss := continuous_lss.measurable

/-- **The type 1 coupling with the shifts of the subcouples**:
`gE(α_𝔯 + λ*; v₁, τ₁) gE(-α_𝔯 + λ**; v₂, τ₂)`. -/
@[expose] noncomputable def K1z (α : Unit → ℝ) (p : ZC1 × QC1) : ℂ := K1 (lst p.1) (lss p.1) α p.2

theorem contDiff_K1z (p : ZC1 × QC1) : ContDiff ℝ ∞ fun α => K1z α p := contDiff_K1 _ _ p.2

theorem measurable_K1z : StronglyMeasurable (Function.uncurry K1z) := by
  have h : Function.uncurry K1z = (fun p : (ℝ × ℝ) × ((Unit → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) =>
      K1 p.1.1 p.1.2 p.2.1 p.2.2) ∘
      (fun x : (Unit → ℝ) × (ZC1 × QC1) => ((lst x.2.1, lss x.2.1), (x.1, x.2.2))) := rfl
  rw [h]
  exact (measurable_K1.comp (by fun_prop)).stronglyMeasurable

/-- The weight of the type 1 coupling: `(1 + |v₁|)^{a₁} (1 + |v₂|)^{a₂} (1 + |α_𝔯 + λ*|)^{b₁}`. -/
@[expose] noncomputable def wK1 (a₁ a₂ b₁ : ℝ) (α : Unit → ℝ) (p : ZC1 × QC1) : ℝ≥0∞ :=
  (1 + ‖p.2.1.1‖ₑ) ^ a₁ * (1 + ‖p.2.2.1‖ₑ) ^ a₂ * (1 + ‖α () + lst p.1‖ₑ) ^ b₁

theorem measurable_wK1 (a₁ a₂ b₁ : ℝ) : Measurable (Function.uncurry (wK1 a₁ a₂ b₁)) := by
  change Measurable fun x : (Unit → ℝ) × (ZC1 × QC1) => (1 + ‖x.2.2.1.1‖ₑ) ^ a₁ *
    (1 + ‖x.2.2.2.1‖ₑ) ^ a₂ * (1 + ‖x.1 () + lst x.2.1‖ₑ) ^ b₁
  fun_prop

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]

/-- **The product of the three subcouple coefficients** (DH21 L1104). -/
@[expose] def M3 (D₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ) (D₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ)
    (D₃ : (ι₃ → ℝ) → ℝ × ℝ → ℂ) : ((ι₁ ⊕ ι₂) ⊕ ι₃ → ℝ) → ZC1 → ℂ :=
  pprod (pprod D₁ D₂) D₃

/-- **The integrand of the Case 1 coefficient** (DH21 (regcplexpl)). -/
@[expose] noncomputable def a1 (D₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ) (D₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ)
    (D₃ : (ι₃ → ℝ) → ℝ × ℝ → ℂ) : (((ι₁ ⊕ ι₂) ⊕ ι₃) ⊕ Unit → ℝ) → ZC1 × QC1 → ℂ :=
  kprod (M3 D₁ D₂ D₃) K1z

/-- The reordering `((v₁, v₂), (z, (τ₁, τ₂))) ↦ (z, ((v₁, τ₁), (v₂, τ₂)))`. -/
@[expose] noncomputable def rho1 : (ℝ × ℝ) × (ZC1 × (ℝ × ℝ)) ≃ᵐ ZC1 × QC1 :=
  frontSwap.trans ((MeasurableEquiv.refl ZC1).prodCongr mswap)

theorem rho1_symm_fst (x : ZC1 × QC1) : (rho1.symm x).1 = (x.2.1.1, x.2.2.1) := by
  have : rho1.symm x = ((x.2.1.1, x.2.2.1), (x.1, (x.2.1.2, x.2.2.2))) := by
    rw [MeasurableEquiv.symm_apply_eq]
    rfl
  rw [this]

theorem measurePreserving_rho1 : MeasurePreserving rho1 :=
  ((MeasurePreserving.id (volume : Measure ZC1)).prod measurePreserving_mswap).comp
    measurePreserving_frontSwap

/-- **The Case 1 coefficient** (DH21 (newexp3), (regcplexpl)):
`𝒞(α, v) = ∫ D₁ D₂ D₃ gE(α_𝔯 + λ*; v₁, τ₁) gE(-α_𝔯 + λ**; v₂, τ₂) dλ dτ`. -/
@[expose] noncomputable def C1 (D₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ) (D₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ)
    (D₃ : (ι₃ → ℝ) → ℝ × ℝ → ℂ) : (((ι₁ ⊕ ι₂) ⊕ ι₃) ⊕ Unit → ℝ) → ℝ × ℝ → ℂ :=
  pushR rho1 (a1 D₁ D₂ D₃)

end Case1Defs

section CouplingBound

variable {ι : Type*} [Fintype ι] {M : (ι → ℝ) → ZC1 → ℂ}

/-- The constant of the type 1 coupling bound. -/
@[expose] noncomputable def NK1 (p : ℝ) : ℝ := 4 * (2 * CE * Ir 2) ^ 2 * Ir (2 - p)

theorem NK1_nonneg (p : ℝ) : 0 ≤ NK1 p := by
  have h1 : 0 ≤ Ir (2 - p) := ENNReal.toReal_nonneg
  unfold NK1; positivity

omit [Fintype ι] in
theorem measurable_kw {ι₂ : Type*} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {wM : (ι → ℝ) → X → ℝ≥0∞} (hwM : Measurable (Function.uncurry wM))
    {wK : (ι₂ → ℝ) → X × Y → ℝ≥0∞} (hwK : Measurable (Function.uncurry wK))
    {d : (ι ⊕ ι₂ → ℝ) → X × Y → ℝ≥0∞} (hd : Measurable (Function.uncurry d)) :
    Measurable (Function.uncurry fun (α : ι ⊕ ι₂ → ℝ) (p : X × Y) =>
      wM (fun i => α (Sum.inl i)) p.1 * wK (fun i => α (Sum.inr i)) p * d α p) := by
  have h1 : Measurable fun x : (ι ⊕ ι₂ → ℝ) × (X × Y) => wM (fun i => x.1 (Sum.inl i)) x.2.1 :=
    hwM.comp ((measurable_restrL.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun x : (ι ⊕ ι₂ → ℝ) × (X × Y) => wK (fun i => x.1 (Sum.inr i)) x.2 :=
    hwK.comp ((measurable_restrR.comp measurable_fst).prodMk measurable_snd)
  exact (h1.mul h2).mul hd

omit [Fintype ι] in
theorem measurable_wd {ι₂ : Type*} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {wK : (ι₂ → ℝ) → X × Y → ℝ≥0∞} (hwK : Measurable (Function.uncurry wK))
    {d : (ι ⊕ ι₂ → ℝ) → X × Y → ℝ≥0∞} (hd : Measurable (Function.uncurry d)) :
    Measurable (Function.uncurry fun (α : ι ⊕ ι₂ → ℝ) (p : X × Y) =>
      wK (fun i => α (Sum.inr i)) p * d α p) := by
  have h2 : Measurable fun x : (ι ⊕ ι₂ → ℝ) × (X × Y) => wK (fun i => x.1 (Sum.inr i)) x.2 :=
    hwK.comp ((measurable_restrR.comp measurable_fst).prodMk measurable_snd)
  exact h2.mul hd

/-- **Weighted norms of the Case 1 integrand** (DH21 L1110–L1112 with (regcplex2)). -/
theorem lintegral_a1_le (hMs : ∀ z, ContDiff ℝ ∞ fun α => M α z)
    (hMm : StronglyMeasurable (Function.uncurry M)) {wM : (ι → ℝ) → ZC1 → ℝ≥0∞}
    (hwM : Measurable (Function.uncurry wM)) {a₁ a₂ b₁ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hs : a₁ + a₂ + b₁ < 1) (k : ℕ) :
    ∫⁻ α : ι ⊕ Unit → ℝ, ∫⁻ p : ZC1 × QC1, wM (fun i => α (Sum.inl i)) p.1 *
        wK1 a₁ a₂ b₁ (fun i => α (Sum.inr i)) p * dnorm k (kprod M K1z) α p ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
        (∫⁻ α₁, ∫⁻ z, wM α₁ z * dnorm j M α₁ z) * gev (NK1 (a₁ + a₂ + b₁)) A1 (k - j) := by
  have hKb : ∀ j z, ∫⁻ α₂, ∫⁻ q, wK1 a₁ a₂ b₁ α₂ (z, q) * dnorm j K1z α₂ (z, q) ≤
      gev (NK1 (a₁ + a₂ + b₁)) A1 j * (fun _ => (1 : ℝ≥0∞)) z := fun j z => by
    rw [mul_one]
    calc ∫⁻ α₂, ∫⁻ q, wK1 a₁ a₂ b₁ α₂ (z, q) * dnorm j K1z α₂ (z, q) =
          ∫⁻ α₂ : Unit → ℝ, ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), ((1 : ℝ≥0∞) + ‖q.1.1‖ₑ) ^ a₁ *
            ((1 : ℝ≥0∞) + ‖q.2.1‖ₑ) ^ a₂ * ((1 : ℝ≥0∞) + ‖α₂ () + lst z‖ₑ) ^ b₁ *
            dnorm j (K1 (lst z) (lss z)) α₂ q := rfl
      _ ≤ gev (4 * (2 * CE * Ir 2) ^ 2 * Ir (2 - a₁ - a₂ - b₁)) A1 j :=
          lintegral_K1_le ha₁ ha₂ hb₁ hs (lst z) (lss z) j
      _ = gev (NK1 (a₁ + a₂ + b₁)) A1 j := by
          unfold NK1
          congr 3
          ring
  have h := lintegral_kprod_le hMs hMm contDiff_K1z measurable_K1z hwM (measurable_wK1 a₁ a₂ b₁)
    measurable_const hKb k
  simp only [mul_one] at h
  exact h

/-- The case `k = 0`. -/
theorem lintegral_a1_zero_le (hMs : ∀ z, ContDiff ℝ ∞ fun α => M α z)
    (hMm : StronglyMeasurable (Function.uncurry M)) {wM : (ι → ℝ) → ZC1 → ℝ≥0∞}
    (hwM : Measurable (Function.uncurry wM)) {a₁ a₂ b₁ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hs : a₁ + a₂ + b₁ < 1) :
    ∫⁻ α : ι ⊕ Unit → ℝ, ∫⁻ p : ZC1 × QC1, wM (fun i => α (Sum.inl i)) p.1 *
        wK1 a₁ a₂ b₁ (fun i => α (Sum.inr i)) p * dnorm 0 (kprod M K1z) α p ≤
      (∫⁻ α₁, ∫⁻ z, wM α₁ z * dnorm 0 M α₁ z) * ENNReal.ofReal (NK1 (a₁ + a₂ + b₁)) := by
  have h := lintegral_a1_le hMs hMm hwM ha₁ ha₂ hb₁ hs 0
  simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.sub_self, gev_zero_eq] at h
  exact h

/-- **Gevrey bounds of the Case 1 integrand** (unweighted subcouple factor). -/
theorem lintegral_a1_gev_le (hMs : ∀ z, ContDiff ℝ ∞ fun α => M α z)
    (hMm : StronglyMeasurable (Function.uncurry M)) {a₁ a₂ b₁ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hs : a₁ + a₂ + b₁ < 1) {A NM : ℝ} (hA : A1 ≤ A) (hNM : 0 ≤ NM)
    (hM : ∀ j, ∫⁻ α, ∫⁻ z, dnorm j M α z ≤ gev NM A j) (k : ℕ) :
    ∫⁻ α : ι ⊕ Unit → ℝ, ∫⁻ p : ZC1 × QC1,
        wK1 a₁ a₂ b₁ (fun i => α (Sum.inr i)) p * dnorm k (kprod M K1z) α p ≤
      gev (4 * NM * NK1 (a₁ + a₂ + b₁)) A k := by
  have h := lintegral_a1_le hMs hMm (wM := fun _ _ => 1) measurable_const ha₁ ha₂ hb₁ hs k
  simp only [one_mul] at h
  refine h.trans (gev_conv_le hNM (NK1_nonneg _) (A1_nonneg.trans hA) hM
    (S₂ := fun j => gev (NK1 (a₁ + a₂ + b₁)) A1 j)
    (fun j => gev_mono le_rfl A1_nonneg hA (NK1_nonneg _) j) k)

end CouplingBound

section PProdBound

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {Z Q : Type*} [MeasureSpace Z] [MeasureSpace Q]
  [SFinite (volume : Measure Z)] [SFinite (volume : Measure Q)]
  {M : (ι₁ → ℝ) → Z → ℂ} {C : (ι₂ → ℝ) → Q → ℂ}

/-- **Gevrey bounds of pure products.** -/
theorem lintegral_pprod_gev_le (hMs : ∀ z, ContDiff ℝ ∞ fun α => M α z)
    (hMm : StronglyMeasurable (Function.uncurry M)) (hCs : ∀ q, ContDiff ℝ ∞ fun α => C α q)
    (hCm : StronglyMeasurable (Function.uncurry C))
    {wM : (ι₁ → ℝ) → Z → ℝ≥0∞} (hwM : Measurable (Function.uncurry wM))
    {wC : (ι₂ → ℝ) → Q → ℝ≥0∞} (hwC : Measurable (Function.uncurry wC))
    {N₁ N₂ A : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂) (hA : 0 ≤ A)
    (h₁ : ∀ j, ∫⁻ α, ∫⁻ z, wM α z * dnorm j M α z ≤ gev N₁ A j)
    (h₂ : ∀ j, ∫⁻ α, ∫⁻ q, wC α q * dnorm j C α q ≤ gev N₂ A j) (k : ℕ) :
    ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ p : Z × Q, wM (fun i => α (Sum.inl i)) p.1 *
        wC (fun i => α (Sum.inr i)) p.2 * dnorm k (pprod M C) α p ≤ gev (4 * N₁ * N₂) A k :=
  (lintegral_pprod_le hMs hMm hCs hCm hwM hwC k).trans (gev_conv_le hN₁ hN₂ hA h₁ h₂ k)

/-- **Per-variable bounds of pure products** (DH21 (maincoef2.5) for a product). -/
theorem lintegral_pprod_var_le (hMs : ∀ z, ContDiff ℝ ∞ fun α => M α z)
    (hMm : StronglyMeasurable (Function.uncurry M)) (hCs : ∀ q, ContDiff ℝ ∞ fun α => C α q)
    (hCm : StronglyMeasurable (Function.uncurry C)) {b : ℝ} {NM NC : ℝ≥0∞}
    (hM0 : ∫⁻ α, ∫⁻ z, dnorm 0 M α z ≤ NM)
    (hMv : ∀ i, ∫⁻ α, ∫⁻ z, (1 + ‖α i‖ₑ) ^ b * dnorm 0 M α z ≤ NM)
    (hC0 : ∫⁻ α, ∫⁻ q, dnorm 0 C α q ≤ NC)
    (hCv : ∀ i, ∫⁻ α, ∫⁻ q, (1 + ‖α i‖ₑ) ^ b * dnorm 0 C α q ≤ NC) :
    (∫⁻ α, ∫⁻ p, dnorm 0 (pprod M C) α p ≤ NM * NC) ∧
      ∀ i, ∫⁻ α, ∫⁻ p, (1 + ‖α i‖ₑ) ^ b * dnorm 0 (pprod M C) α p ≤ NM * NC := by
  have key : ∀ {wM : (ι₁ → ℝ) → Z → ℝ≥0∞} (_ : Measurable (Function.uncurry wM))
      {wC : (ι₂ → ℝ) → Q → ℝ≥0∞} (_ : Measurable (Function.uncurry wC)),
      ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ p : Z × Q, wM (fun i => α (Sum.inl i)) p.1 *
        wC (fun i => α (Sum.inr i)) p.2 * dnorm 0 (pprod M C) α p ≤
      (∫⁻ α₁, ∫⁻ z, wM α₁ z * dnorm 0 M α₁ z) * ∫⁻ α₂, ∫⁻ q, wC α₂ q * dnorm 0 C α₂ q := by
    intro wM hwM wC hwC
    have h := lintegral_pprod_le hMs hMm hCs hCm hwM hwC 0
    simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul,
      Nat.sub_self] at h
    exact h
  refine ⟨?_, ?_⟩
  · have h := key (wM := fun _ _ => 1) measurable_const (wC := fun _ _ => 1) measurable_const
    simp only [one_mul] at h
    exact h.trans (mul_le_mul' hM0 hC0)
  · rintro (i | i)
    · have hw : Measurable (Function.uncurry fun (α : ι₁ → ℝ) (_ : Z) => (1 + ‖α i‖ₑ) ^ b) := by
        change Measurable fun x : (ι₁ → ℝ) × Z => (1 + ‖x.1 i‖ₑ) ^ b
        fun_prop
      have h := key hw (wC := fun _ _ => 1) measurable_const
      simp only [mul_one, one_mul] at h
      exact h.trans (mul_le_mul' (hMv i) hC0)
    · have hw : Measurable (Function.uncurry fun (α : ι₂ → ℝ) (_ : Q) => (1 + ‖α i‖ₑ) ^ b) := by
        change Measurable fun x : (ι₂ → ℝ) × Q => (1 + ‖x.1 i‖ₑ) ^ b
        fun_prop
      have h := key (wM := fun _ _ => 1) measurable_const hw
      simp only [one_mul] at h
      exact h.trans (mul_le_mul' hM0 (hCv i))

end PProdBound

section SRepUnweighted

variable {ι : Type*} [Fintype ι] {θ a b A N : ℝ} {C : (ι → ℝ) → ℝ × ℝ → ℂ}

theorem SRep.dnorm0_le (h : SRep θ a b A N C) (hθ : 0 ≤ θ) :
    ∫⁻ α, ∫⁻ lam, dnorm 0 C α lam ≤ ENNReal.ofReal N :=
  (h.norm_unweighted hθ 0).trans_eq (gev_zero_eq N A)

theorem SRep.var_le (h : SRep θ a b A N C) (ha : 0 ≤ a) (i : ι) :
    ∫⁻ α, ∫⁻ lam, (1 + ‖α i‖ₑ) ^ b * dnorm 0 C α lam ≤ ENNReal.ofReal N := by
  refine le_trans (lintegral_mono fun α => lintegral_mono fun lam => ?_) (h.wnorm i)
  rw [dnorm_zero, mul_assoc]
  exact le_mul_of_one_le_left bot_le (one_le_wL ha lam)

end SRepUnweighted

section M3Bound

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
  {D₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ} {D₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ} {D₃ : (ι₃ → ℝ) → ℝ × ℝ → ℂ}

theorem M3_smooth (h₁ : SymReg D₁) (h₂ : SymReg D₂) (h₃ : SymReg D₃) (z : ZC1) :
    ContDiff ℝ ∞ fun α => M3 D₁ D₂ D₃ α z :=
  contDiff_pprod (contDiff_pprod h₁.smooth h₂.smooth) h₃.smooth z

theorem M3_meas (h₁ : SymReg D₁) (h₂ : SymReg D₂) (h₃ : SymReg D₃) :
    StronglyMeasurable (Function.uncurry (M3 D₁ D₂ D₃)) :=
  measurable_pprod (measurable_pprod h₁.meas h₂.meas) h₃.meas

/-- **Gevrey bounds of the product of three subcouple coefficients.** -/
theorem lintegral_M3_le (h₁ : SymReg D₁) (h₂ : SymReg D₂) (h₃ : SymReg D₃)
    {w : ℝ × ℝ → ℝ≥0∞} (hw : Measurable w) {N₁ N₂ N₃ A : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hN₃ : 0 ≤ N₃) (hA : 0 ≤ A)
    (b₁ : ∀ j, ∫⁻ α, ∫⁻ lam, w lam * dnorm j D₁ α lam ≤ gev N₁ A j)
    (b₂ : ∀ j, ∫⁻ α, ∫⁻ lam, w lam * dnorm j D₂ α lam ≤ gev N₂ A j)
    (b₃ : ∀ j, ∫⁻ α, ∫⁻ lam, w lam * dnorm j D₃ α lam ≤ gev N₃ A j) (k : ℕ) :
    ∫⁻ α, ∫⁻ z : ZC1, w z.1.1 * w z.1.2 * w z.2 * dnorm k (M3 D₁ D₂ D₃) α z ≤
      gev (16 * (N₁ * N₂ * N₃)) A k := by
  have hw2 : Measurable (Function.uncurry fun (_ : ι₁ ⊕ ι₂ → ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) =>
      w p.1 * w p.2) := by
    change Measurable fun x : (ι₁ ⊕ ι₂ → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) => w x.2.1 * w x.2.2
    fun_prop
  have h12 : ∀ j, ∫⁻ α, ∫⁻ p : (ℝ × ℝ) × (ℝ × ℝ), w p.1 * w p.2 * dnorm j (pprod D₁ D₂) α p ≤
      gev (4 * N₁ * N₂) A j := fun j =>
    lintegral_pprod_gev_le h₁.smooth h₁.meas h₂.smooth h₂.meas (wM := fun _ lam => w lam)
      (hw.comp measurable_snd) (wC := fun _ lam => w lam) (hw.comp measurable_snd) hN₁ hN₂ hA
      b₁ b₂ j
  have h := lintegral_pprod_gev_le (contDiff_pprod h₁.smooth h₂.smooth)
    (measurable_pprod h₁.meas h₂.meas) h₃.smooth h₃.meas hw2 (wC := fun _ lam => w lam)
    (hw.comp measurable_snd) (by positivity) hN₃ hA h12 b₃ k
  refine h.trans_eq ?_
  congr 1
  ring

/-- **Per-variable bounds of the product of three subcouple coefficients.** -/
theorem lintegral_M3_var_le {θ a b A N₁ N₂ N₃ : ℝ} (h₁ : SRep θ a b A N₁ D₁)
    (h₂ : SRep θ a b A N₂ D₂) (h₃ : SRep θ a b A N₃ D₃) (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (i : (ι₁ ⊕ ι₂) ⊕ ι₃) :
    ∫⁻ α, ∫⁻ z, (1 + ‖α i‖ₑ) ^ b * dnorm 0 (M3 D₁ D₂ D₃) α z ≤
      ENNReal.ofReal (N₁ * N₂ * N₃) := by
  have h12 := lintegral_pprod_var_le h₁.reg.smooth h₁.reg.meas h₂.reg.smooth h₂.reg.meas
    (h₁.dnorm0_le hθ) (h₁.var_le ha) (h₂.dnorm0_le hθ) (h₂.var_le ha)
  have h := lintegral_pprod_var_le (contDiff_pprod h₁.reg.smooth h₂.reg.smooth)
    (measurable_pprod h₁.reg.meas h₂.reg.meas) h₃.reg.smooth h₃.reg.meas h12.1 h12.2
    (h₃.dnorm0_le hθ) (h₃.var_le ha)
  rw [ENNReal.ofReal_mul (mul_nonneg h₁.nonneg h₂.nonneg), ENNReal.ofReal_mul h₁.nonneg]
  exact h.2 i

/-- `(1 + |λ*|)^b ≤ wL θ λ₁ wL θ λ₂ wL θ λ₃` for `0 ≤ b ≤ θ`. -/
theorem one_add_lst_rpow_le {b θ : ℝ} (hb : 0 ≤ b) (hbθ : b ≤ θ) (z : ZC1) :
    (1 + ‖lst z‖ₑ) ^ b ≤ wL θ z.1.1 * wL θ z.1.2 * wL θ z.2 := by
  unfold lst
  calc (1 + ‖z.1.1.1 + z.1.2.1 + z.2.1‖ₑ) ^ b ≤
        ((1 + ‖z.1.1.1‖ₑ) * (1 + ‖z.1.2.1‖ₑ) * (1 + ‖z.2.1‖ₑ)) ^ b :=
        ENNReal.rpow_le_rpow ((one_add_enorm_add_le _ _).trans
          (mul_le_mul' (one_add_enorm_add_le _ _) le_rfl)) hb
    _ = (1 + ‖z.1.1.1‖ₑ) ^ b * (1 + ‖z.1.2.1‖ₑ) ^ b * (1 + ‖z.2.1‖ₑ) ^ b := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hb, ENNReal.mul_rpow_of_nonneg _ _ hb]
    _ ≤ wL θ z.1.1 * wL θ z.1.2 * wL θ z.2 :=
        mul_le_mul' (mul_le_mul' (one_add_rpow_le_wL hb hbθ _) (one_add_rpow_le_wL hb hbθ _))
          (one_add_rpow_le_wL hb hbθ _)

end M3Bound

section Case1Bound

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
  {D₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ} {D₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ} {D₃ : (ι₃ → ℝ) → ℝ × ℝ → ℂ}
  {θ a b A N₁ N₂ N₃ : ℝ}

/-- The constant of the Case 1 step. -/
@[expose] noncomputable def KC1 (θ a b : ℝ) : ℝ := 128 * (NK1 θ + NK1 a + NK1 (a + b))

theorem KC1_nonneg (θ a b : ℝ) : 0 ≤ KC1 θ a b := by
  have := NK1_nonneg θ; have := NK1_nonneg a; have := NK1_nonneg (a + b)
  unfold KC1; positivity

/-- **Regularity of the Case 1 integrand.** -/
theorem a1_symReg (h₁ : SRep θ a b A N₁ D₁) (h₂ : SRep θ a b A N₂ D₂) (h₃ : SRep θ a b A N₃ D₃)
    (hθ : 0 ≤ θ) (hA : A1 ≤ A) : SymReg (a1 D₁ D₂ D₃) := by
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  have hN : 0 ≤ N₁ * N₂ * N₃ := mul_nonneg (mul_nonneg h₁.nonneg h₂.nonneg) h₃.nonneg
  have hMs := M3_smooth h₁.reg h₂.reg h₃.reg
  have hMm := M3_meas h₁.reg h₂.reg h₃.reg
  have hM0 : ∀ j, ∫⁻ α, ∫⁻ z, dnorm j (M3 D₁ D₂ D₃) α z ≤ gev (16 * (N₁ * N₂ * N₃)) A j :=
    fun j => by
      have := lintegral_M3_le h₁.reg h₂.reg h₃.reg (w := fun _ => 1) measurable_const h₁.nonneg
        h₂.nonneg h₃.nonneg hA0 (fun j => by simpa only [one_mul] using h₁.norm_unweighted hθ j)
        (fun j => by simpa only [one_mul] using h₂.norm_unweighted hθ j)
        (fun j => by simpa only [one_mul] using h₃.norm_unweighted hθ j) j
      simpa only [one_mul] using this
  refine SymReg.of_lintegral (fun p => contDiff_kprod hMs contDiff_K1z p)
    (measurable_kprod hMm measurable_K1z) fun k => ?_
  have e : ∀ (β : Unit → ℝ) (p : ZC1 × QC1), wK1 0 0 0 β p = 1 := fun β p => by simp [wK1]
  have hb0 := lintegral_a1_gev_le hMs hMm le_rfl le_rfl le_rfl (by norm_num) hA (by positivity)
    hM0 k
  simp only [e, one_mul] at hb0
  exact ne_top_of_le_ne_top (by unfold gev; exact ENNReal.ofReal_ne_top) hb0

/-- **DH21 Proposition 5.1, Case 1: the bounds** (DH21 L1100–L1112 with the DH23 weights). The
coefficient of a type 1 couple built from three subcouples with coefficients `D₁, D₂, D₃`
satisfies (maincoef2) and (maincoef2.5) with the constant `KC1 θ a b N₁ N₂ N₃`. The weight `wL θ`
of the new frequencies is split as `(1 + |v₁|)^θ + (1 + |v₂|)^θ`, and each term is absorbed by one
`gE` factor; this needs `θ < 1` (DH23: `θ = 1 - η/8`). The weight `(1 + |α_𝔯|)^b` of the root
variable is moved to `(1 + |α_𝔯 + λ*|)^b (1 + |λ*|)^b`, and `(1 + |λ*|)^b` is absorbed by the
frequency weights `wL θ` of the subcouples (`b ≤ θ`). -/
theorem SRep.case1 (h₁ : SRep θ a b A N₁ D₁) (h₂ : SRep θ a b A N₂ D₂) (h₃ : SRep θ a b A N₃ D₃)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) (hbθ : b ≤ θ)
    (hA : A1 ≤ A) : SRep θ a b A (KC1 θ a b * (N₁ * N₂ * N₃)) (C1 D₁ D₂ D₃) := by
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  have hN : 0 ≤ N₁ * N₂ * N₃ := mul_nonneg (mul_nonneg h₁.nonneg h₂.nonneg) h₃.nonneg
  have hNM : 0 ≤ 16 * (N₁ * N₂ * N₃) := by positivity
  have hMs := M3_smooth h₁.reg h₂.reg h₃.reg
  have hMm := M3_meas h₁.reg h₂.reg h₃.reg
  have hM0 : ∀ j, ∫⁻ α, ∫⁻ z, dnorm j (M3 D₁ D₂ D₃) α z ≤ gev (16 * (N₁ * N₂ * N₃)) A j :=
    fun j => by
      have := lintegral_M3_le h₁.reg h₂.reg h₃.reg (w := fun _ => 1) measurable_const h₁.nonneg
        h₂.nonneg h₃.nonneg hA0 (fun j => by simpa only [one_mul] using h₁.norm_unweighted hθ0 j)
        (fun j => by simpa only [one_mul] using h₂.norm_unweighted hθ0 j)
        (fun j => by simpa only [one_mul] using h₃.norm_unweighted hθ0 j) j
      simpa only [one_mul] using this
  have hreg := a1_symReg h₁ h₂ h₃ hθ0 hA
  have hd : ∀ k, Measurable (Function.uncurry (dnorm k (kprod (M3 D₁ D₂ D₃) K1z))) := fun k =>
    measurable_dnorm (fun p => contDiff_kprod hMs contDiff_K1z p)
      (measurable_kprod hMm measurable_K1z) k
  have hKa := NK1_nonneg a
  have hKab := NK1_nonneg (a + b)
  have hKθ := NK1_nonneg θ
  refine ⟨mul_nonneg (KC1_nonneg θ a b) hN, pushR_symReg hreg measurePreserving_rho1,
    fun k => ?_, fun i => ?_⟩
  · -- (maincoef2)
    refine (lintegral_weight_pushR_le hreg measurePreserving_rho1 (w := fun _ lam => wL θ lam)
      ((measurable_wL θ).comp measurable_snd) k).trans ?_
    simp only [rho1_symm_fst]
    rw [show a1 D₁ D₂ D₃ = kprod (M3 D₁ D₂ D₃) K1z from rfl]
    refine (lintegral_two_le (measurable_wd (measurable_wK1 θ 0 0) (hd k)) ?_
      (lintegral_a1_gev_le hMs hMm hθ0 le_rfl le_rfl (by linarith) hA hNM hM0 k)
      (lintegral_a1_gev_le hMs hMm le_rfl hθ0 le_rfl (by linarith) hA hNM hM0 k)).trans ?_
    · intro α x
      simp only [wK1, ENNReal.rpow_zero, mul_one, one_mul]
      rw [← add_mul]
      exact mul_le_mul' (wL_le_add hθ0 hθ1.le _ _) le_rfl
    · simp only [add_zero, zero_add]
      rw [gev_add (by positivity) (by positivity) hA0]
      refine gev_mono ?_ hA0 le_rfl (mul_nonneg (KC1_nonneg θ a b) hN) k
      unfold KC1
      nlinarith [mul_nonneg hN hKa, mul_nonneg hN hKab, mul_nonneg hN hKθ]
  · -- (maincoef2.5)
    have e : ∀ α lam, ‖C1 D₁ D₂ D₃ α lam‖ₑ = dnorm 0 (C1 D₁ D₂ D₃) α lam := fun α lam =>
      (dnorm_zero _ _ _).symm
    simp_rw [e]
    have hw : Measurable (Function.uncurry fun (α : ((ι₁ ⊕ ι₂) ⊕ ι₃) ⊕ Unit → ℝ) (lam : ℝ × ℝ) =>
        wL a lam * (1 + ‖α i‖ₑ) ^ b) := by
      change Measurable fun x : (((ι₁ ⊕ ι₂) ⊕ ι₃) ⊕ Unit → ℝ) × (ℝ × ℝ) =>
        wL a x.2 * (1 + ‖x.1 i‖ₑ) ^ b
      exact ((measurable_wL a).comp measurable_snd).mul (by fun_prop)
    refine (lintegral_weight_pushR_le hreg measurePreserving_rho1 hw 0).trans ?_
    simp only [rho1_symm_fst]
    rw [show a1 D₁ D₂ D₃ = kprod (M3 D₁ D₂ D₃) K1z from rfl]
    rcases i with i | ⟨⟩
    · -- a variable of a subcouple
      have hwM : Measurable (Function.uncurry fun (β : (ι₁ ⊕ ι₂) ⊕ ι₃ → ℝ) (_ : ZC1) =>
          (1 + ‖β i‖ₑ) ^ b) := by
        change Measurable fun x : ((ι₁ ⊕ ι₂) ⊕ ι₃ → ℝ) × ZC1 => (1 + ‖x.1 i‖ₑ) ^ b
        fun_prop
      refine (lintegral_two_le (measurable_kw hwM (measurable_wK1 a 0 0) (hd 0)) ?_
        (lintegral_a1_zero_le hMs hMm hwM ha le_rfl le_rfl (by linarith))
        (lintegral_a1_zero_le hMs hMm hwM le_rfl ha le_rfl (by linarith))).trans ?_
      · intro α x
        simp only [wK1, ENNReal.rpow_zero, mul_one, one_mul]
        calc wL a (x.2.1.1, x.2.2.1) * (1 + ‖α (Sum.inl i)‖ₑ) ^ b *
              dnorm 0 (kprod (M3 D₁ D₂ D₃) K1z) α x ≤
            ((1 + ‖x.2.1.1‖ₑ) ^ a + (1 + ‖x.2.2.1‖ₑ) ^ a) * (1 + ‖α (Sum.inl i)‖ₑ) ^ b *
              dnorm 0 (kprod (M3 D₁ D₂ D₃) K1z) α x :=
            mul_le_mul' (mul_le_mul' (wL_le_add ha (by linarith) _ _) le_rfl) le_rfl
          _ = _ := by ring
      · have hv := lintegral_M3_var_le h₁ h₂ h₃ hθ0 ha i
        simp only [add_zero, zero_add]
        calc _ ≤ ENNReal.ofReal (N₁ * N₂ * N₃) * ENNReal.ofReal (NK1 a) +
              ENNReal.ofReal (N₁ * N₂ * N₃) * ENNReal.ofReal (NK1 a) := by gcongr
          _ ≤ _ := by
            rw [← ENNReal.ofReal_mul hN, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            unfold KC1
            nlinarith [mul_nonneg hN hKa, mul_nonneg hN hKab, mul_nonneg hN hKθ]
    · -- the root variable
      have hwM : Measurable (Function.uncurry fun (_ : (ι₁ ⊕ ι₂) ⊕ ι₃ → ℝ) (z : ZC1) =>
          (1 + ‖lst z‖ₑ) ^ b) := by
        change Measurable fun x : ((ι₁ ⊕ ι₂) ⊕ ι₃ → ℝ) × ZC1 => (1 + ‖lst x.2‖ₑ) ^ b
        fun_prop
      refine (lintegral_two_le (measurable_kw hwM (measurable_wK1 a 0 b) (hd 0)) ?_
        (lintegral_a1_zero_le hMs hMm hwM ha le_rfl hb (by linarith))
        (lintegral_a1_zero_le hMs hMm hwM le_rfl ha hb (by linarith))).trans ?_
      · intro α x
        simp only [wK1, ENNReal.rpow_zero, mul_one, one_mul]
        calc wL a (x.2.1.1, x.2.2.1) * (1 + ‖α (Sum.inr ())‖ₑ) ^ b *
              dnorm 0 (kprod (M3 D₁ D₂ D₃) K1z) α x ≤
            ((1 + ‖x.2.1.1‖ₑ) ^ a + (1 + ‖x.2.2.1‖ₑ) ^ a) *
              ((1 + ‖α (Sum.inr ()) + lst x.1‖ₑ) ^ b * (1 + ‖lst x.1‖ₑ) ^ b) *
              dnorm 0 (kprod (M3 D₁ D₂ D₃) K1z) α x :=
            mul_le_mul' (mul_le_mul' (wL_le_add ha (by linarith) _ _)
              (one_add_enorm_rpow_shift_le hb _ _)) le_rfl
          _ = _ := by ring
      · have hl : ∫⁻ α₁, ∫⁻ z, (1 + ‖lst z‖ₑ) ^ b * dnorm 0 (M3 D₁ D₂ D₃) α₁ z ≤
            ENNReal.ofReal (16 * (N₁ * N₂ * N₃)) := by
          refine (lintegral_mono fun α => lintegral_mono fun z =>
            mul_le_mul' (one_add_lst_rpow_le hb hbθ z) le_rfl).trans ?_
          exact (lintegral_M3_le h₁.reg h₂.reg h₃.reg (measurable_wL θ) h₁.nonneg h₂.nonneg
            h₃.nonneg hA0 h₁.norm h₂.norm h₃.norm 0).trans_eq (gev_zero_eq _ _)
        simp only [add_zero, zero_add]
        calc _ ≤ ENNReal.ofReal (16 * (N₁ * N₂ * N₃)) * ENNReal.ofReal (NK1 (a + b)) +
              ENNReal.ofReal (16 * (N₁ * N₂ * N₃)) * ENNReal.ofReal (NK1 (a + b)) := by gcongr
          _ ≤ _ := by
            rw [← ENNReal.ofReal_mul hNM, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            unfold KC1
            nlinarith [mul_nonneg hN hKa, mul_nonneg hN hKab, mul_nonneg hN hKθ]

end Case1Bound

section Case1Rep

theorem norm_e2 (lam : ℝ × ℝ) (t s : ℝ) : ‖e2 lam t s‖ = 1 := by
  rw [e2, Complex.norm_exp]
  simp

theorem norm_cexp_pi_I_mul (x : ℝ) : ‖cexp (π * I * x)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem e2_split (lam : ℝ × ℝ) (t s : ℝ) :
    e2 lam t s = cexp (π * I * (lam.1 * t)) * cexp (π * I * (lam.2 * s)) := by
  rw [e2, ← Complex.exp_add]
  congr 1
  ring

theorem e2_lst (z : ZC1) (t s : ℝ) :
    e2 (lst z, lss z) t s = e2 z.1.1 t s * e2 z.1.2 t s * e2 z.2 t s := by
  simp only [e2, lst, lss, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[fun_prop] theorem continuous_e2 : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => e2 p.1 p.2.1 p.2.2 := by
  unfold e2
  fun_prop

/-- Exchanging an interval integral with an integral against an integrable function. -/
theorem intervalIntegral_integral_mul_swap {Z : Type*} [MeasureSpace Z]
    [SFinite (volume : Measure Z)] {f : Z → ℂ} (hf : Integrable f) {g : ℝ → Z → ℂ}
    (hg : StronglyMeasurable (Function.uncurry g)) {C : ℝ} (hgC : ∀ u z, ‖g u z‖ ≤ C) (a b : ℝ) :
    ∫ u in a..b, ∫ z, f z * g u z = ∫ z, f z * ∫ u in a..b, g u z := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := Real.isFiniteMeasure_restrict_Ioc _ _
  have hint : Integrable (Function.uncurry fun u z => f z * g u z)
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
    refine Integrable.mono' ((integrable_const C).mul_prod hf.norm) ?_ ?_
    · exact hf.1.comp_snd.mul hg.aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      change ‖f p.2 * g p.1 p.2‖ ≤ C * ‖f p.2‖
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hgC _ _) (norm_nonneg _)
  rw [intervalIntegral_integral_swap hint]
  congr 1
  funext z
  exact intervalIntegral.integral_const_mul _ _

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
  {D₁ : (ι₁ → ℝ) → ℝ × ℝ → ℂ} {D₂ : (ι₂ → ℝ) → ℝ × ℝ → ℂ} {D₃ : (ι₃ → ℝ) → ℝ × ℝ → ℂ}

omit [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
/-- The product of the three subcouple representations (DH21 L1104). -/
theorem prod_integral_e2 (α : (ι₁ ⊕ ι₂) ⊕ ι₃ → ℝ) (t₁ s₁ : ℝ) :
    (∫ lam, D₁ (fun i => α (Sum.inl (Sum.inl i))) lam * e2 lam t₁ s₁) *
        (∫ lam, D₂ (fun i => α (Sum.inl (Sum.inr i))) lam * e2 lam t₁ s₁) *
        (∫ lam, D₃ (fun i => α (Sum.inr i)) lam * e2 lam t₁ s₁) =
      ∫ z : ZC1, M3 D₁ D₂ D₃ α z * e2 (lst z, lss z) t₁ s₁ := by
  rw [← integral_prod_mul (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure (ℝ × ℝ))),
    ← integral_prod_mul (μ := (volume : Measure (ℝ × ℝ)).prod volume)
      (ν := (volume : Measure (ℝ × ℝ)))]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [M3, pprod, kprod, e2_lst]
  ring

/-- **DH21 Proposition 5.1, Case 1: the representation** (DH21 (newexp1), (newexp3),
(regcplexpl)). For `t, s ∈ [0, 1]`, the time integral of the type 1 recursion with the three
subcouple representations is represented by the Case 1 coefficient `C1`. -/
theorem integral_C1_e2 (h₁ : SymReg D₁) (h₂ : SymReg D₂) (h₃ : SymReg D₃)
    (hreg : SymReg (a1 D₁ D₂ D₃)) (α : ((ι₁ ⊕ ι₂) ⊕ ι₃) ⊕ Unit → ℝ) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ lam, C1 D₁ D₂ D₃ α lam * e2 lam t s =
      ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) *
        ((∫ lam, D₁ (fun i => α (Sum.inl (Sum.inl (Sum.inl i)))) lam * e2 lam t₁ s₁) *
          (∫ lam, D₂ (fun i => α (Sum.inl (Sum.inl (Sum.inr i)))) lam * e2 lam t₁ s₁) *
          ∫ lam, D₃ (fun i => α (Sum.inl (Sum.inr i))) lam * e2 lam t₁ s₁) := by
  have hMint : Integrable (M3 D₁ D₂ D₃ fun i => α (Sum.inl i)) :=
    ((h₁.integrable _).mul_prod (h₂.integrable _)).mul_prod (h₃.integrable _)
  -- the inner time integrand
  have hg : ∀ t₁ : ℝ, StronglyMeasurable (Function.uncurry fun (s₁ : ℝ) (z : ZC1) =>
      cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) * e2 (lst z, lss z) t₁ s₁) := fun t₁ => by
    have : Continuous fun p : ℝ × ZC1 =>
        cexp (π * I * (α (Sum.inr ()) * (t₁ - p.1))) * e2 (lst p.2, lss p.2) t₁ p.1 := by
      unfold e2
      fun_prop
    exact this.stronglyMeasurable
  have hgC : ∀ (t₁ s₁ : ℝ) (z : ZC1),
      ‖cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) * e2 (lst z, lss z) t₁ s₁‖ ≤ 1 := by
    intro t₁ s₁ z
    rw [norm_mul, norm_e2, mul_one]
    have := norm_cexp_pi_I_mul (α (Sum.inr ()) * (t₁ - s₁))
    push_cast at this
    exact this.le
  -- the outer time integrand
  have hg' : StronglyMeasurable (Function.uncurry fun (t₁ : ℝ) (z : ZC1) =>
      ∫ s₁ in (0 : ℝ)..s,
        cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) * e2 (lst z, lss z) t₁ s₁) := by
    have : Continuous fun x : ℝ × ZC1 => ∫ s₁ in (0 : ℝ)..s,
        cexp (π * I * (α (Sum.inr ()) * (x.1 - s₁))) * e2 (lst x.2, lss x.2) x.1 s₁ := by
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 s
      unfold e2
      fun_prop
    exact this.stronglyMeasurable
  have hg'C : ∀ (t₁ : ℝ) (z : ZC1), ‖∫ s₁ in (0 : ℝ)..s,
      cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) * e2 (lst z, lss z) t₁ s₁‖ ≤ 1 * |s - 0| :=
    fun t₁ z => intervalIntegral.norm_integral_le_of_norm_le_const fun s₁ _ => hgC t₁ s₁ z
  -- the time integrals of the exponentials
  have hT : ∀ z : ZC1, ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s,
      cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) * e2 (lst z, lss z) t₁ s₁ =
        eInt (α (Sum.inr ()) + lst z) t * eInt (-α (Sum.inr ()) + lss z) s := by
    intro z
    have hpt : ∀ t₁ s₁ : ℝ, cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) *
        e2 (lst z, lss z) t₁ s₁ = cexp (π * I * (((α (Sum.inr ()) + lst z : ℝ) : ℂ) * t₁)) *
          cexp (π * I * (((-α (Sum.inr ()) + lss z : ℝ) : ℂ) * s₁)) := by
      intro t₁ s₁
      simp only [e2, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hpt, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_mul_const]
    rfl
  -- the `gE` representation of the time integrals
  have hC : ∀ z : ZC1, eInt (α (Sum.inr ()) + lst z) t * eInt (-α (Sum.inr ()) + lss z) s =
      ∫ q : QC1, K1z (fun i => α (Sum.inr i)) (z, q) * e2 (q.1.1, q.2.1) t s := by
    intro z
    rw [← integral_gE_mul_exp (α (Sum.inr ()) + lst z) ht,
      ← integral_gE_mul_exp (-α (Sum.inr ()) + lss z) hs,
      ← integral_prod_mul (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure (ℝ × ℝ)))]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [K1z, K1, e2_split]
    ring
  have hint : Integrable (fun p : ZC1 × QC1 => a1 D₁ D₂ D₃ α p * e2 (p.2.1.1, p.2.2.1) t s)
      ((volume : Measure ZC1).prod (volume : Measure QC1)) := by
    refine (hreg.integrable α).norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous fun p : ZC1 × QC1 => e2 (p.2.1.1, p.2.2.1) t s := by
        unfold e2
        fun_prop
      exact (hreg.integrable α).1.mul hc.aestronglyMeasurable
    · rw [norm_mul, norm_e2, mul_one]
  have hφ : Continuous fun lam : ℝ × ℝ => e2 lam t s := by
    unfold e2
    fun_prop
  symm
  calc ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) *
        ((∫ lam, D₁ (fun i => α (Sum.inl (Sum.inl (Sum.inl i)))) lam * e2 lam t₁ s₁) *
          (∫ lam, D₂ (fun i => α (Sum.inl (Sum.inl (Sum.inr i)))) lam * e2 lam t₁ s₁) *
          ∫ lam, D₃ (fun i => α (Sum.inl (Sum.inr i))) lam * e2 lam t₁ s₁) =
      ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, ∫ z, M3 D₁ D₂ D₃ (fun i => α (Sum.inl i)) z *
        (cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) * e2 (lst z, lss z) t₁ s₁) := by
        refine intervalIntegral.integral_congr fun t₁ _ => ?_
        refine intervalIntegral.integral_congr fun s₁ _ => ?_
        rw [prod_integral_e2 (fun i => α (Sum.inl i)) t₁ s₁, ← integral_const_mul]
        congr 1
        funext z
        ring
    _ = ∫ t₁ in (0 : ℝ)..t, ∫ z, M3 D₁ D₂ D₃ (fun i => α (Sum.inl i)) z *
        ∫ s₁ in (0 : ℝ)..s,
          cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) * e2 (lst z, lss z) t₁ s₁ :=
        intervalIntegral.integral_congr fun t₁ _ =>
          intervalIntegral_integral_mul_swap hMint (hg t₁) (hgC t₁) 0 s
    _ = ∫ z, M3 D₁ D₂ D₃ (fun i => α (Sum.inl i)) z * ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s,
          cexp (π * I * (α (Sum.inr ()) * (t₁ - s₁))) * e2 (lst z, lss z) t₁ s₁ :=
        intervalIntegral_integral_mul_swap hMint hg' hg'C 0 t
    _ = ∫ z, ∫ q, a1 D₁ D₂ D₃ α (z, q) * e2 (q.1.1, q.2.1) t s := by
        congr 1
        funext z
        rw [hT z, hC z, ← integral_const_mul]
        congr 1
        funext q
        simp only [a1, kprod]
        ring
    _ = ∫ p : ZC1 × QC1, a1 D₁ D₂ D₃ α p * e2 (p.2.1.1, p.2.2.1) t s :=
        (integral_prod _ hint).symm
    _ = ∫ lam, C1 D₁ D₂ D₃ α lam * e2 lam t s := by
        rw [C1, integral_pushR_mul hreg measurePreserving_rho1 α (φ := fun lam => e2 lam t s)
          hφ.aestronglyMeasurable (fun γ => (norm_e2 γ t s).le)]
        simp only [rho1_symm_fst]

end Case1Rep

end WaveTurbulence.ClassJR
