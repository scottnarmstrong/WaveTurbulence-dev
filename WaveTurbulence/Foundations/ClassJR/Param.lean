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

/-- Bounds uniform in the parameter, and joint measurability of the symbol. -/
structure RSymP.Bound (R : RSymP P ι) (θ A N : ℝ) : Prop where
  bound : ∀ p, (R.get p).Bound θ A N
  meas : StronglyMeasurable fun x : P × ((ι → ℝ) × (ℝ × ℝ × ℝ)) => R.m x.1 x.2.1 x.2.2

/-- **Parametric class `J`** (DH21 Definition 5.2 with the parameters `μ[E]`). -/
@[expose] def ClassJP (θ A N : ℝ) (T : P → (ι → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (n : ℕ) (R : Fin n → JSymP P ι) (c : Fin n → ℝ), (∀ i, (R i).Bound θ A (c i)) ∧
    ∑ i, c i ≤ N ∧ ∀ p α, KEqOn (T p α) fun t s => ∑ i, ((R i).get p).kernel α t s

/-- **Parametric class `R`** (special variable `α none`). -/
@[expose] def ClassRP (θ A N : ℝ) (T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (n : ℕ) (R : Fin n → RSymP P ι) (c : Fin n → ℝ), (∀ i, (R i).Bound θ A (c i)) ∧
    ∑ i, c i ≤ N ∧ ∀ p α, KEqOn (T p α) fun t s => ∑ i, ((R i).get p).kernel α t s

theorem ClassJP.classJ {θ A N : ℝ} {T : P → (ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassJP θ A N T)
    (p : P) : ClassJ θ A N (T p) := by
  obtain ⟨n, R, c, hb, hs, he⟩ := h
  exact ⟨n, fun i => (R i).get p, c, fun i => (hb i).bound p, hs, fun α => he p α⟩

theorem ClassRP.classR {θ A N : ℝ} {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassRP θ A N T)
    (p : P) : ClassR θ A N (T p) := by
  obtain ⟨n, R, c, hb, hs, he⟩ := h
  exact ⟨n, fun i => (R i).get p, c, fun i => (hb i).bound p, hs, fun α => he p α⟩

end Defs

section PushParam

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]
variable {Γ : Type*} [MeasureSpace Γ] [AddGroup Γ] [MeasurableAdd₂ Γ] [MeasurableSub₂ Γ]
  [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

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
    pushSym_symReg (hreg p) (hbp p), fun k => ?_⟩, stronglyMeasurable_pushSym_param hreg ha hb⟩,
    fun p α t s => ?_⟩
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
    pushSym_symReg (hreg p) (hbp p), fun k => ?_⟩, stronglyMeasurable_pushSym_param hreg ha hb⟩,
    fun p α t s => ?_⟩
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

end WaveTurbulence.ClassJR
