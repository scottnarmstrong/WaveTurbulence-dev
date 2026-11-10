/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.OfAny

/-!
# Class `J` and `R` operators depending on parameters `μ[E]`

DH21 Definition 5.2 (L955–L963) lets the operators and their symbols depend on parameters
`μ[E]`, with the bounds (typeJ2), (typeR2) uniform in `μ`. In the proof of Proposition 5.1
(L1112–L1140) these parameters are sums `μ_j = λ_a + λ_b` of integration variables, and the
coefficient produced by Lemma 5.10 is integrated over the `λ`'s; hence the symbol must be jointly
measurable in `(μ, α, γ)`. `JSymP P ι` is a family of basic class `J` data indexed by `p : P` with a
common bundle, and `JSymP.Bound` requires the bounds for every `p` together with joint strong
measurability of the symbol; `ClassJP`, `ClassRP` are the corresponding classes. No regularity in
`μ` beyond measurability is required (DH21 never differentiates in `μ`).

`stronglyMeasurable_pushSym_param` shows that the pushforward of generalized representations is
jointly measurable in the parameters, so the conversion lemmas `JSym.ofGen`, `JSym.ofGenE`,
`JSym.ofAny`, `RSym.ofAny` have parametric versions.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

attribute [local instance] isAddRightInvariant_volume_prod

section Defs

variable (P ι : Type*)

/-- A parametric family of basic class `J` data with a common bundle. -/
structure JSymP where
  /-- The common bundle. -/
  y : ι → ℤ
  /-- The symbol `m(μ, α, γ)`. -/
  m : P → (ι → ℝ) → ℝ × ℝ → ℂ

/-- A parametric family of basic class `R` data with common sign and bundles. -/
structure RSymP where
  /-- The sign of the special variable. -/
  ε : ℤ
  /-- The denominator bundle. -/
  y₁ : ι → ℤ
  /-- The phase bundle. -/
  y₂ : ι → ℤ
  /-- The symbol `m(μ, α[A \ {1}], γ)`. -/
  m : P → (ι → ℝ) → ℝ × ℝ × ℝ → ℂ

variable {P ι} [MeasurableSpace P] [Fintype ι]

/-- The member at parameter `p`. -/
@[expose] def JSymP.get (R : JSymP P ι) (p : P) : JSym ι := ⟨R.y, R.m p⟩

/-- The member at parameter `p`. -/
@[expose] def RSymP.get (R : RSymP P ι) (p : P) : RSym ι := ⟨R.ε, R.y₁, R.y₂, R.m p⟩

/-- Bounds uniform in the parameter, and joint measurability of the symbol. -/
structure JSymP.Bound (R : JSymP P ι) (θ A N : ℝ) : Prop where
  bound : ∀ p, (R.get p).Bound θ A N
  meas : StronglyMeasurable fun x : P × ((ι → ℝ) × (ℝ × ℝ)) => R.m x.1 x.2.1 x.2.2
  nonneg : 0 ≤ N
  bundle : IsBundle R.y

/-- Bounds uniform in the parameter, and joint measurability of the symbol. -/
structure RSymP.Bound (R : RSymP P ι) (θ A N : ℝ) : Prop where
  bound : ∀ p, (R.get p).Bound θ A N
  meas : StronglyMeasurable fun x : P × ((ι → ℝ) × (ℝ × ℝ × ℝ)) => R.m x.1 x.2.1 x.2.2
  nonneg : 0 ≤ N
  sign : R.ε = 1 ∨ R.ε = -1
  bundle₁ : IsBundle R.y₁
  bundle₂ : IsBundle R.y₂

/-- **Parametric class `J`** (DH21 Definition 5.2 with the parameters `μ[E]`). -/
@[expose] def ClassJP (θ A N : ℝ) (T : P → (ι → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (n : ℕ) (R : Fin n → JSymP P ι) (c : Fin n → ℝ), (∀ i, (R i).Bound θ A (c i)) ∧
    ∑ i, c i ≤ N ∧ ∀ p α, KEqOn (T p α) fun t s => ∑ i, ((R i).get p).kernel α t s

/-- **Parametric class `R`** (special variable `α none`). -/
@[expose] def ClassRP (θ A N : ℝ) (T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (n : ℕ) (R : Fin n → RSymP P ι) (c : Fin n → ℝ), (∀ i, (R i).Bound θ A (c i)) ∧
    ∑ i, c i ≤ N ∧ ∀ p α, KEqOn (T p α) fun t s => ∑ i, ((R i).get p).kernel α t s

end Defs

section PushParam

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]
variable {Γ : Type*} [MeasureSpace Γ] [AddGroup Γ] [MeasurableAdd₂ Γ] [MeasurableSub₂ Γ]
  [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

omit [MeasurableAdd₂ Γ] [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)] in
/-- **The pushforward is jointly measurable in the parameters.** -/
theorem stronglyMeasurable_pushSym_param {a : P → (ι → ℝ) → Γ × Q → ℂ}
    (hreg : ∀ p, SymReg (a p))
    (ha : StronglyMeasurable fun x : P × ((ι → ℝ) × (Γ × Q)) => a x.1 x.2.1 x.2.2)
    {b : P → Q → Γ} (hb : Measurable (Function.uncurry b)) :
    StronglyMeasurable fun x : P × ((ι → ℝ) × Γ) => pushSym (a x.1) (b x.1) x.2.1 x.2.2 := by
  set ã : (ι → ℝ) → P × (Γ × Q) → ℂ := fun α w => a w.1 α w.2 with hãd
  have hãs : ∀ w, ContDiff ℝ ∞ fun α => ã α w := fun w => (hreg w.1).smooth w.2
  have hãm : StronglyMeasurable (Function.uncurry ã) :=
    ha.comp_measurable ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.prodMk
      (measurable_snd.comp measurable_snd)))
  have hsup : ∀ k, Measurable (supD k ã) := fun k => measurable_supD hãs hãm k
  have hsup' : ∀ k p ζ, supD k (a p) ζ = supD k ã (p, ζ) := fun k p ζ => rfl
  set S : Set (P × Γ) := ⋂ k, (fun x : P × Γ =>
    ∫⁻ η, supD k ã (x.1, (x.2 - b x.1 η, η))) ⁻¹' {⊤}ᶜ with hSd
  have hS : MeasurableSet S := by
    refine MeasurableSet.iInter fun k => ?_
    have hm : Measurable fun q : (P × Γ) × Q => supD k ã (q.1.1, (q.1.2 - b q.1.1 q.2, q.2)) :=
      (hsup k).comp ((measurable_fst.comp measurable_fst).prodMk
        (((measurable_snd.comp measurable_fst).sub (hb.comp ((measurable_fst.comp
          measurable_fst).prodMk measurable_snd))).prodMk measurable_snd))
    exact hm.lintegral_prod_right' (measurableSet_singleton ⊤).compl
  have hmem : ∀ p γ, γ ∈ goodSet (a p) (b p) ↔ (p, γ) ∈ S := fun p γ => by
    simp [goodSet, hSd, hsup']
  have hint : StronglyMeasurable fun x : P × ((ι → ℝ) × Γ) =>
      ∫ η, a x.1 x.2.1 (x.2.2 - b x.1 η, η) := by
    refine StronglyMeasurable.integral_prod_right'
      (f := fun q : (P × ((ι → ℝ) × Γ)) × Q => a q.1.1 q.1.2.1 (q.1.2.2 - b q.1.1 q.2, q.2)) ?_
    exact ha.comp_measurable ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (((measurable_snd.comp (measurable_snd.comp measurable_fst)).sub
          (hb.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).prodMk
            measurable_snd)))
  have hS' : MeasurableSet {x : P × ((ι → ℝ) × Γ) | (x.1, x.2.2) ∈ S} :=
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) hS
  have heq : (fun x : P × ((ι → ℝ) × Γ) => pushSym (a x.1) (b x.1) x.2.1 x.2.2) =
      {x : P × ((ι → ℝ) × Γ) | (x.1, x.2.2) ∈ S}.indicator
        fun x => ∫ η, a x.1 x.2.1 (x.2.2 - b x.1 η, η) := by
    funext x
    by_cases hx : (x.1, x.2.2) ∈ S
    · rw [Set.indicator_of_mem (show x ∈ {x : P × ((ι → ℝ) × Γ) | (x.1, x.2.2) ∈ S} from hx)]
      simp [pushSym, Set.indicator_of_mem ((hmem _ _).2 hx)]
    · rw [Set.indicator_of_notMem (show x ∉ {x : P × ((ι → ℝ) × Γ) | (x.1, x.2.2) ∈ S}
        from hx)]
      simp [pushSym, Set.indicator_of_notMem (fun h => hx ((hmem _ _).1 h))]
  rw [heq]
  exact hint.indicator hS'

end PushParam


section Conv

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]
variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- **Parametric generalized class `J` representations.** -/
theorem JSymP.ofGen {y : ι → ℤ} (hy : IsBundle y) {a : P → (ι → ℝ) → (ℝ × ℝ) × Q → ℂ}
    (hreg : ∀ p, SymReg (a p))
    (ha : StronglyMeasurable fun x : P × ((ι → ℝ) × ((ℝ × ℝ) × Q)) => a x.1 x.2.1 x.2.2)
    {b : P → Q → ℝ × ℝ} (hb : Measurable (Function.uncurry b)) {θ A N : ℝ} (hN : 0 ≤ N)
    (hnorm : ∀ p k, ∫⁻ α, ∫⁻ ζ, wJ θ α (ζ.1.1 + (b p ζ.2).1) * dnorm k (a p) α ζ ≤
      gev N A k) :
    ∃ R : JSymP P ι, R.y = y ∧ R.Bound θ A N ∧ ∀ p α t s, (R.get p).kernel α t s =
      ∫ ζ, a p α ζ * jker (bundle y α) (ζ.1.1 + (b p ζ.2).1) (ζ.1.2 + (b p ζ.2).2) t s := by
  have hbp : ∀ p, Measurable (b p) := fun p => hb.comp (measurable_const.prodMk measurable_id)
  refine ⟨⟨y, fun p => pushSym (a p) (b p)⟩, rfl, ⟨fun p => ⟨hN, hy,
    pushSym_symReg (hreg p) (hbp p), fun k => ?_⟩, stronglyMeasurable_pushSym_param hreg ha hb,
    hN, hy⟩, fun p α t s => ?_⟩
  · refine le_trans ?_ (hnorm p k)
    have := lintegral_weight_pushSym_le (hreg p) (hbp p) (measurable_wJ (ι := ι) θ) k
    simpa only [jNorm, JSymP.get, Prod.fst_add] using this
  · have hcont : Continuous fun γ : ℝ × ℝ => jker (bundle y α) γ.1 γ.2 t s := by
      unfold jker; fun_prop
    have := integral_pushSym_mul (hreg p) (hbp p) α hcont.aestronglyMeasurable (C := 1)
      (fun γ => (norm_jker _ _ _ _ _).le)
    simpa only [JSymP.get, JSym.kernel, Prod.fst_add, Prod.snd_add] using this

/-- **Parametric generalized class `R` representations.** -/
theorem RSymP.ofGen {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁)
    (hy₂ : IsBundle y₂) {a : P → (ι → ℝ) → (ℝ × ℝ × ℝ) × Q → ℂ} (hreg : ∀ p, SymReg (a p))
    (ha : StronglyMeasurable fun x : P × ((ι → ℝ) × ((ℝ × ℝ × ℝ) × Q)) => a x.1 x.2.1 x.2.2)
    {b : P → Q → ℝ × ℝ × ℝ} (hb : Measurable (Function.uncurry b)) {θ A N : ℝ} (hN : 0 ≤ N)
    (hnorm : ∀ p k, ∫⁻ α, ∫⁻ ζ, wR θ α (ζ.1.1 + (b p ζ.2).1) (ζ.1.2.2 + (b p ζ.2).2.2) *
      dnorm k (a p) α ζ ≤ gev N A k) :
    ∃ R : RSymP P ι, R.ε = ε ∧ R.y₁ = y₁ ∧ R.y₂ = y₂ ∧ R.Bound θ A N ∧ ∀ p α t s,
      (R.get p).kernel α t s = ∫ ζ, a p (nsp α) ζ * rker (bundle y₁ (nsp α) + ε * α none)
        (bundle y₂ (nsp α) + ε * α none) (ζ.1.1 + (b p ζ.2).1) (ζ.1.2.1 + (b p ζ.2).2.1)
        (ζ.1.2.2 + (b p ζ.2).2.2) t s := by
  have hbp : ∀ p, Measurable (b p) := fun p => hb.comp (measurable_const.prodMk measurable_id)
  refine ⟨⟨ε, y₁, y₂, fun p => pushSym (a p) (b p)⟩, rfl, rfl, rfl, ⟨fun p => ⟨hN, hε, hy₁, hy₂,
    pushSym_symReg (hreg p) (hbp p), fun k => ?_⟩, stronglyMeasurable_pushSym_param hreg ha hb,
    hN, hε, hy₁, hy₂⟩, fun p α t s => ?_⟩
  · refine le_trans ?_ (hnorm p k)
    have := lintegral_weight_pushSym_le (hreg p) (hbp p) (measurable_wR (ι := ι) θ) k
    simpa only [rNorm, RSymP.get, Prod.fst_add, Prod.snd_add] using this
  · have := integral_pushSym_mul (hreg p) (hbp p) (nsp α)
      (continuous_rker_coeff (bundle y₁ (nsp α) + ε * α none) (bundle y₂ (nsp α) + ε * α none)
        t s).aestronglyMeasurable (C := CPhi) (fun γ => norm_rker_le _ _ _ _ _ _ _)
    simpa only [RSymP.get, RSym.kernel, Prod.fst_add, Prod.snd_add] using this

variable {Z : Type*} [MeasureSpace Z]

/-- **Parametric generalized class `J` representations through an equivalence.** -/
theorem JSymP.ofGenE {y : ι → ℤ} (hy : IsBundle y) {a : P → (ι → ℝ) → Z → ℂ}
    (hreg : ∀ p, SymReg (a p))
    (ha : StronglyMeasurable fun x : P × ((ι → ℝ) × Z) => a x.1 x.2.1 x.2.2)
    (E : Z ≃ᵐ (ℝ × ℝ) × Q) (hE : MeasurePreserving E) {b : Q → ℝ × ℝ} (hb : Measurable b)
    {θ A N : ℝ} (hN : 0 ≤ N)
    (hnorm : ∀ p k, ∫⁻ α, ∫⁻ z, wJ θ α ((E z).1.1 + (b (E z).2).1) * dnorm k (a p) α z ≤
      gev N A k) :
    ∃ R : JSymP P ι, R.y = y ∧ R.Bound θ A N ∧ ∀ p α t s, (R.get p).kernel α t s =
      ∫ z, a p α z * jker (bundle y α) ((E z).1.1 + (b (E z).2).1) ((E z).1.2 + (b (E z).2).2)
        t s := by
  have hreg' : ∀ p, SymReg fun α ζ => a p α (E.symm ζ) := fun p =>
    (hreg p).comp_equiv E.symm (hE.symm E)
  have ha' : StronglyMeasurable fun x : P × ((ι → ℝ) × ((ℝ × ℝ) × Q)) =>
      a x.1 x.2.1 (E.symm x.2.2) :=
    ha.comp_measurable (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (E.symm.measurable.comp (measurable_snd.comp measurable_snd))))
  obtain ⟨R, hRy, hRb, hRk⟩ := JSymP.ofGen (θ := θ) (A := A) hy hreg' ha'
    (b := fun _ => b) (hb.comp measurable_snd) hN (fun p k => by
      refine le_trans (le_of_eq ?_) (hnorm p k)
      refine lintegral_congr fun α => ?_
      rw [← hE.lintegral_comp_emb E.measurableEmbedding]
      refine lintegral_congr fun z => ?_
      have key : lift1 (fun α ζ => a p α (E.symm ζ)) (E z) = lift1 (a p) z := by
        funext β
        simp [lift1]
      simp only [dnorm, key])
  refine ⟨R, hRy, hRb, fun p α t s => ?_⟩
  rw [hRk, ← hE.integral_comp' (g := fun ζ => a p α (E.symm ζ) *
    jker (bundle y α) (ζ.1.1 + (b ζ.2).1) (ζ.1.2 + (b ζ.2).2) t s)]
  simp only [MeasurableEquiv.symm_apply_apply]

end Conv

section ConvAny

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]
variable {Z : Type*} [MeasureSpace Z] [SFinite (volume : Measure Z)]

/-- The weighted norm of the smoothed generalized symbol. -/
theorem lintegral_smoothed_le {a : (ι → ℝ) → Z → ℂ} (ha : SymReg a) {c : Z → ℝ × ℝ}
    (hc : Measurable c) {θ A N : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hnorm : ∀ k, ∫⁻ α, ∫⁻ z, wJ θ α (c z).1 * dnorm k a α z ≤ gev N A k) (k : ℕ) :
    ∫⁻ α, ∫⁻ ζ : (ℝ × ℝ) × Z, wJ θ α (ζ.1.1 + (c ζ.2).1) *
      dnorm k (fun α (p : (ℝ × ℝ) × Z) => M00 p.1 * a α p.2) α ζ ≤ gev (CM0 * N) A k := by
  have hmw : ∀ α, Measurable fun z => wJ θ α (c z).1 * dnorm k a α z := fun α =>
    (measurable_wJ_comp (measurable_fst.comp hc) α).mul
      (measurable_dnorm ha.smooth ha.meas k).of_uncurry_left
  calc ∫⁻ α, ∫⁻ ζ : (ℝ × ℝ) × Z, wJ θ α (ζ.1.1 + (c ζ.2).1) *
        dnorm k (fun α (p : (ℝ × ℝ) × Z) => M00 p.1 * a α p.2) α ζ
      ≤ ∫⁻ α, ∫⁻ ζ : (ℝ × ℝ) × Z, ((1 + ‖ζ.1.1‖ₑ) * ‖M00 ζ.1‖ₑ) *
          (wJ θ α (c ζ.2).1 * dnorm k a α ζ.2) := by
        refine lintegral_mono fun α => lintegral_mono fun ζ => ?_
        rw [dnorm_mul_fixed k M00 a ha.smooth]
        calc wJ θ α (ζ.1.1 + (c ζ.2).1) * (‖M00 ζ.1‖ₑ * dnorm k a α ζ.2)
            ≤ ((1 + ‖ζ.1.1‖ₑ) * wJ θ α (c ζ.2).1) * (‖M00 ζ.1‖ₑ * dnorm k a α ζ.2) := by
              gcongr; exact wJ_shift_le h0 h1 α _ _
          _ = _ := by ring
    _ = ∫⁻ α, ENNReal.ofReal CM0 * ∫⁻ z, wJ θ α (c z).1 * dnorm k a α z := by
        refine lintegral_congr fun α => ?_
        rw [Measure.volume_eq_prod, lintegral_prod_mul
          (f := fun u : ℝ × ℝ => (1 + ‖u.1‖ₑ) * ‖M00 u‖ₑ)
          (g := fun z => wJ θ α (c z).1 * dnorm k a α z)
          ((measurable_const.add measurable_fst.enorm).mul
            continuous_M00.measurable.enorm).aemeasurable (hmw α).aemeasurable,
          lintegral_M00_weight]
    _ = ENNReal.ofReal CM0 * ∫⁻ α, ∫⁻ z, wJ θ α (c z).1 * dnorm k a α z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal CM0 * gev N A k := mul_le_mul' le_rfl (hnorm k)
    _ = gev (CM0 * N) A k := gev_mul_const _ CM0_nonneg k

/-- **Parametric class `J` from superpositions with arbitrary coefficient maps.** -/
theorem JSymP.ofAny {y : ι → ℤ} (hy : IsBundle y) {a : P → (ι → ℝ) → Z → ℂ}
    (hreg : ∀ p, SymReg (a p))
    (ha : StronglyMeasurable fun x : P × ((ι → ℝ) × Z) => a x.1 x.2.1 x.2.2)
    {c : P → Z → ℝ × ℝ} (hc : Measurable (Function.uncurry c)) {θ A N : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) (hN : 0 ≤ N)
    (hnorm : ∀ p k, ∫⁻ α, ∫⁻ z, wJ θ α (c p z).1 * dnorm k (a p) α z ≤ gev N A k) :
    ∃ R : JSymP P ι, R.y = y ∧ R.Bound θ A (CM0 * N) ∧ ∀ p α t s, t ∈ Icc (0 : ℝ) 1 →
      s ∈ Icc (0 : ℝ) 1 → (R.get p).kernel α t s =
        ∫ z, a p α z * jker (bundle y α) (c p z).1 (c p z).2 t s := by
  have hcp : ∀ p, Measurable (c p) := fun p => hc.comp (measurable_const.prodMk measurable_id)
  have ha' : StronglyMeasurable fun x : P × ((ι → ℝ) × ((ℝ × ℝ) × Z)) =>
      M00 x.2.2.1 * a x.1 x.2.1 x.2.2.2 :=
    (continuous_M00.stronglyMeasurable.comp_measurable
      (measurable_fst.comp (measurable_snd.comp measurable_snd))).mul
      (ha.comp_measurable (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  obtain ⟨R, hRy, hRb, hRk⟩ := JSymP.ofGen (θ := θ) (A := A) hy (fun p => (hreg p).smoothed) ha'
    (b := c) hc (mul_nonneg CM0_nonneg hN)
    (fun p k => lintegral_smoothed_le (hreg p) (hcp p) h0 h1 (hnorm p) k)
  refine ⟨R, hRy, hRb, fun p α t s ht hs => ?_⟩
  rw [hRk]
  have := integral_smoothed ((hreg p).integrable α) (bundle y α) (hcp p) ht hs (fun _ => 1)
    aestronglyMeasurable_const (C := 1) (fun _ => by simp)
  simp only [one_mul] at this
  rw [← this]

end ConvAny

section ConvAnyR

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]
variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- **Parametric class `R` from superpositions with arbitrary coefficient maps.** -/
theorem RSymP.ofAny {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁)
    (hy₂ : IsBundle y₂) {a : P → (ι → ℝ) → ℝ × Q → ℂ} (hreg : ∀ p, SymReg (a p))
    (ha : StronglyMeasurable fun x : P × ((ι → ℝ) × (ℝ × Q)) => a x.1 x.2.1 x.2.2)
    {c : P → ℝ × Q → ℝ × ℝ} (hc : Measurable (Function.uncurry c)) {θ A N : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) (hN : 0 ≤ N)
    (hnorm : ∀ p k, ∫⁻ α, ∫⁻ z, wR θ α (c p z).1 z.1 * dnorm k (a p) α z ≤ gev N A k) :
    ∃ R : RSymP P ι, R.ε = ε ∧ R.y₁ = y₁ ∧ R.y₂ = y₂ ∧ R.Bound θ A (CM0 * N) ∧ ∀ p α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      (R.get p).kernel α t s = ∫ z, a p (nsp α) z * rker (bundle y₁ (nsp α) + ε * α none)
        (bundle y₂ (nsp α) + ε * α none) (c p z).1 (c p z).2 z.1 t s := by
  have hcp : ∀ p, Measurable (c p) := fun p => hc.comp (measurable_const.prodMk measurable_id)
  set E : P → (ℝ × ℝ) × (ℝ × Q) ≃ᵐ (ℝ × ℝ × ℝ) × Q := fun p =>
    (shiftEquiv (c p) (hcp p)).trans reassocR with hEd
  have hE : ∀ p, MeasurePreserving (E p) := fun p =>
    measurePreserving_reassocR.comp (measurePreserving_shiftEquiv (c p) (hcp p))
  have hEa : ∀ p ζ, E p ζ = ((ζ.1.1 + (c p ζ.2).1, (ζ.1.2 + (c p ζ.2).2, ζ.2.1)), ζ.2.2) :=
    fun p ζ => rfl
  have hEs : ∀ p ζ, (E p).symm ζ =
      ((ζ.1.1 - (c p (ζ.1.2.2, ζ.2)).1, ζ.1.2.1 - (c p (ζ.1.2.2, ζ.2)).2), (ζ.1.2.2, ζ.2)) :=
    fun p ζ => rfl
  set a' : P → (ι → ℝ) → (ℝ × ℝ × ℝ) × Q → ℂ := fun p α ζ =>
    M00 ((E p).symm ζ).1 * a p α ((E p).symm ζ).2 with ha'd
  have hreg' : ∀ p, SymReg (a' p) := fun p =>
    ((hreg p).smoothed).comp_equiv (E p).symm ((hE p).symm _)
  have hcm : Measurable fun x : P × ((ι → ℝ) × ((ℝ × ℝ × ℝ) × Q)) =>
      c x.1 (x.2.2.1.2.2, x.2.2.2) :=
    hc.comp (measurable_fst.prodMk ((measurable_snd.comp (measurable_snd.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have ha' : StronglyMeasurable fun x : P × ((ι → ℝ) × ((ℝ × ℝ × ℝ) × Q)) =>
      a' x.1 x.2.1 x.2.2 := by
    have hA : StronglyMeasurable fun x : P × ((ι → ℝ) × ((ℝ × ℝ × ℝ) × Q)) =>
        a x.1 x.2.1 (x.2.2.1.2.2, x.2.2.2) :=
      ha.comp_measurable (g := fun x : P × ((ι → ℝ) × ((ℝ × ℝ × ℝ) × Q)) =>
        (x.1, (x.2.1, (x.2.2.1.2.2, x.2.2.2)))) (measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk ((measurable_snd.comp (measurable_snd.comp
            (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
              (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
    have hu : Measurable fun x : P × ((ι → ℝ) × ((ℝ × ℝ × ℝ) × Q)) =>
        ((x.2.2.1.1 - (c x.1 (x.2.2.1.2.2, x.2.2.2)).1,
          x.2.2.1.2.1 - (c x.1 (x.2.2.1.2.2, x.2.2.2)).2) : ℝ × ℝ) :=
      ((measurable_fst.comp (measurable_fst.comp (measurable_snd.comp
        measurable_snd))).sub (measurable_fst.comp hcm)).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp
          measurable_snd)))).sub (measurable_snd.comp hcm))
    have hM := continuous_M00.stronglyMeasurable.comp_measurable hu
    exact hM.mul hA
  obtain ⟨R, e1, e2, e3, hRb, hRk⟩ := RSymP.ofGen (θ := θ) (A := A) hε hy₁ hy₂ hreg' ha'
    (b := fun _ _ => 0) measurable_const (mul_nonneg CM0_nonneg hN) (fun p k => by
      have hmw : ∀ α, Measurable fun z => wR θ α (c p z).1 z.1 * dnorm k (a p) α z := fun α =>
        (measurable_wR_comp (measurable_fst.comp (hcp p)) measurable_fst α).mul
          (measurable_dnorm (hreg p).smooth (hreg p).meas k).of_uncurry_left
      have hmov : ∀ α, ∫⁻ ζ : (ℝ × ℝ × ℝ) × Q, wR θ α (ζ.1.1 + (0 : ℝ × ℝ × ℝ).1)
          (ζ.1.2.2 + (0 : ℝ × ℝ × ℝ).2.2) * dnorm k (a' p) α ζ =
          ∫⁻ ζ : (ℝ × ℝ) × (ℝ × Q), wR θ α ((E p) ζ).1.1 ((E p) ζ).1.2.2 *
            dnorm k (fun α (q : (ℝ × ℝ) × (ℝ × Q)) => M00 q.1 * a p α q.2) α ζ := fun α => by
        rw [← (hE p).lintegral_comp_emb (E p).measurableEmbedding]
        refine lintegral_congr fun ζ => ?_
        have key : lift1 (a' p) (E p ζ) =
            lift1 (fun α (q : (ℝ × ℝ) × (ℝ × Q)) => M00 q.1 * a p α q.2) ζ := by
          funext β; simp [lift1, ha'd]
        simp only [dnorm, key, Prod.fst_zero, Prod.snd_zero, add_zero]
      simp_rw [hmov]
      calc ∫⁻ α, ∫⁻ ζ : (ℝ × ℝ) × (ℝ × Q), wR θ α ((E p) ζ).1.1 ((E p) ζ).1.2.2 *
            dnorm k (fun α (q : (ℝ × ℝ) × (ℝ × Q)) => M00 q.1 * a p α q.2) α ζ
          ≤ ∫⁻ α, ∫⁻ ζ : (ℝ × ℝ) × (ℝ × Q), ((1 + ‖ζ.1.1‖ₑ) * ‖M00 ζ.1‖ₑ) *
              (wR θ α (c p ζ.2).1 ζ.2.1 * dnorm k (a p) α ζ.2) := by
            refine lintegral_mono fun α => lintegral_mono fun ζ => ?_
            rw [dnorm_mul_fixed k M00 (a p) (hreg p).smooth, hEa]
            calc wR θ α (ζ.1.1 + (c p ζ.2).1) ζ.2.1 * (‖M00 ζ.1‖ₑ * dnorm k (a p) α ζ.2)
                ≤ ((1 + ‖ζ.1.1‖ₑ) * wR θ α (c p ζ.2).1 ζ.2.1) *
                    (‖M00 ζ.1‖ₑ * dnorm k (a p) α ζ.2) := by
                  gcongr; exact wR_shift_le h0 h1 α _ _ _
              _ = _ := by ring
        _ = ∫⁻ α, ENNReal.ofReal CM0 * ∫⁻ z, wR θ α (c p z).1 z.1 * dnorm k (a p) α z := by
            refine lintegral_congr fun α => ?_
            rw [Measure.volume_eq_prod, lintegral_prod_mul
              (f := fun u : ℝ × ℝ => (1 + ‖u.1‖ₑ) * ‖M00 u‖ₑ)
              (g := fun z => wR θ α (c p z).1 z.1 * dnorm k (a p) α z)
              ((measurable_const.add measurable_fst.enorm).mul
                continuous_M00.measurable.enorm).aemeasurable (hmw α).aemeasurable,
              lintegral_M00_weight]
        _ = ENNReal.ofReal CM0 * ∫⁻ α, ∫⁻ z, wR θ α (c p z).1 z.1 * dnorm k (a p) α z :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal CM0 * gev N A k := mul_le_mul' le_rfl (hnorm p k)
        _ = gev (CM0 * N) A k := gev_mul_const _ CM0_nonneg k)
  refine ⟨R, e1, e2, e3, hRb, fun p α t s ht hs => ?_⟩
  rw [hRk, ← (hE p).integral_comp' (g := fun ζ => a' p (nsp α) ζ *
    rker (bundle y₁ (nsp α) + ε * α none) (bundle y₂ (nsp α) + ε * α none)
      (ζ.1.1 + (0 : ℝ × ℝ × ℝ).1) (ζ.1.2.1 + (0 : ℝ × ℝ × ℝ).2.1)
      (ζ.1.2.2 + (0 : ℝ × ℝ × ℝ).2.2) t s)]
  have hφ : Measurable fun z : ℝ × Q => (chiInvR (bundle y₁ (nsp α) + ε * α none + z.1) : ℂ) :=
    contDiff_chiInvRc.continuous.measurable.comp (measurable_const.add measurable_fst)
  have := integral_smoothed ((hreg p).integrable (nsp α)) (bundle y₂ (nsp α) + ε * α none)
    (hcp p) ht hs (fun z => (chiInvR (bundle y₁ (nsp α) + ε * α none + z.1) : ℂ))
    hφ.aestronglyMeasurable (C := CPhi) (fun z => norm_chiInvR_le _)
  simp only [ha'd, MeasurableEquiv.symm_apply_apply]
  simp only [hEa, Prod.fst_zero, Prod.snd_zero, add_zero, rker]
  rw [← this]

end ConvAnyR

end WaveTurbulence.ClassJR
