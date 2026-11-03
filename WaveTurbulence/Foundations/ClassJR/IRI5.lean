/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI4

/-!
# DH21 Lemma 5.7: tools for the class `R` pieces

The terms V–VI of `I_{εα₁} ℛ I_{μ₁-εα₁}` are class `R` operators with special variable `α₁`
whose symbols `m(α', γ) χ_∞(x₁)/x₁ F(x₀, q)` depend on `α₂` through `x₀ = γ₂ - ℓ₂ - ε₂α₂` and the
input denominator `x₁ = ℓ₁ + γ₃ + ε₂α₂` (DH21 L1070–L1071). Here: `RSymP.ofAnyE` (conversion
through a measure-preserving relabelling of the coefficient variables), `RSymP.reindex`, the two
forms `LsIRIR`, and the couplings `KRV = (πi)⁻¹ kerM(x₀) χ_∞(x₁)/x₁`,
`KRVI = (πi)⁻¹ Φ(x₀) χ_∞(x₁)/x₁` with their `Γ` bounds (from `gamma_KMR_le`, `gamma_KPR_le`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

section OfAnyE

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]
variable {Z : Type*} [MeasureSpace Z] {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- **Parametric class `R` from superpositions, through a relabelling `E` of the coefficient
variables** (`(E z).1` is the third coefficient). -/
theorem RSymP.ofAnyE {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁)
    (hy₂ : IsBundle y₂) {a : P → (ι → ℝ) → Z → ℂ} (hreg : ∀ p, SymReg (a p))
    (ha : StronglyMeasurable fun x : P × ((ι → ℝ) × Z) => a x.1 x.2.1 x.2.2)
    (E : Z ≃ᵐ ℝ × Q) (hE : MeasurePreserving E)
    {c : P → Z → ℝ × ℝ} (hc : Measurable (Function.uncurry c)) {θ A N : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) (hN : 0 ≤ N)
    (hnorm : ∀ p k, ∫⁻ α, ∫⁻ z, wR θ α (c p z).1 (E z).1 * dnorm k (a p) α z ≤ gev N A k) :
    ∃ R : RSymP P ι, R.ε = ε ∧ R.y₁ = y₁ ∧ R.y₂ = y₂ ∧ R.Bound θ A (CM0 * N) ∧ ∀ p α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      (R.get p).kernel α t s = ∫ z, a p (nsp α) z * rker (bundle y₁ (nsp α) + ε * α none)
        (bundle y₂ (nsp α) + ε * α none) (c p z).1 (c p z).2 (E z).1 t s := by
  have hreg' : ∀ p, SymReg fun α ζ => a p α (E.symm ζ) := fun p =>
    (hreg p).comp_equiv E.symm (hE.symm E)
  have ha' : StronglyMeasurable fun x : P × ((ι → ℝ) × (ℝ × Q)) =>
      a x.1 x.2.1 (E.symm x.2.2) :=
    ha.comp_measurable (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (E.symm.measurable.comp (measurable_snd.comp measurable_snd))))
  have hc' : Measurable (Function.uncurry fun p (ζ : ℝ × Q) => c p (E.symm ζ)) :=
    hc.comp (measurable_fst.prodMk (E.symm.measurable.comp measurable_snd))
  obtain ⟨R, e1, e2, e3, hRb, hRk⟩ := RSymP.ofAny (θ := θ) (A := A) hε hy₁ hy₂ hreg' ha'
    hc' h0 h1 hN (fun p k => by
      refine le_trans (le_of_eq ?_) (hnorm p k)
      refine lintegral_congr fun α => ?_
      rw [← hE.lintegral_comp_emb E.measurableEmbedding]
      refine lintegral_congr fun z => ?_
      have key : lift1 (fun α ζ => a p α (E.symm ζ)) (E z) = lift1 (a p) z := by
        funext β
        simp [lift1]
      simp only [dnorm, key, MeasurableEquiv.symm_apply_apply])
  refine ⟨R, e1, e2, e3, hRb, fun p α t s ht hs => ?_⟩
  rw [hRk p α t s ht hs, ← hE.integral_comp' (g := fun ζ => a p (nsp α) (E.symm ζ) *
    rker (bundle y₁ (nsp α) + ε * α none) (bundle y₂ (nsp α) + ε * α none)
      (c p (E.symm ζ)).1 (c p (E.symm ζ)).2 ζ.1 t s)]
  simp only [MeasurableEquiv.symm_apply_apply]

end OfAnyE

section ReindexR

variable {P : Type*} [MeasurableSpace P] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The relabelled parametric basic class `R` datum. -/
@[expose] def RSymP.reindex (e : ι ≃ ι') (R : RSymP P ι) : RSymP P ι' where
  ε := R.ε
  y₁ := fun j => R.y₁ (e.symm j)
  y₂ := fun j => R.y₂ (e.symm j)
  m := fun p α' γ => R.m p (fun i => α' (e i)) γ

theorem RSymP.Bound.reindex (e : ι ≃ ι') {R : RSymP P ι} {θ A N : ℝ} (h : R.Bound θ A N) :
    (R.reindex e).Bound θ A N where
  bound p :=
    { nonneg := h.nonneg
      sign := h.sign
      bundle₁ := fun j => h.bundle₁ (e.symm j)
      bundle₂ := fun j => h.bundle₂ (e.symm j)
      reg := (h.bound p).reg.reindex e
      norm := fun k => by
        refine le_of_eq_of_le ?_ ((h.bound p).norm k)
        show rNorm θ k (fun α' γ => (R.get p).m (fun i => α' (e i)) γ) = _
        unfold rNorm
        simp only [dnorm_reindex]
        have hw : ∀ (α' : ι' → ℝ) (γ₁ γ₃ : ℝ), wR θ α' γ₁ γ₃ = wR θ (fun i => α' (e i)) γ₁ γ₃ := by
          intro α' γ₁ γ₃; unfold wR; rw [sum_enorm_reindex e]
        simp_rw [hw]
        exact lintegral_reindex e (F := fun α => ∫⁻ γ : ℝ × ℝ × ℝ,
          wR θ α γ.1 γ.2.2 * dnorm k (R.get p).m α γ) }
  meas := by
    have hmap : Measurable fun x : P × ((ι' → ℝ) × (ℝ × ℝ × ℝ)) =>
        ((x.1, ((fun i => x.2.1 (e i)), x.2.2)) : P × ((ι → ℝ) × (ℝ × ℝ × ℝ))) :=
      measurable_fst.prodMk ((Measurable.of_eval fun i => (measurable_pi_apply (e i)).comp
        (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
    exact h.meas.comp_measurable hmap
  nonneg := h.nonneg
  sign := h.sign
  bundle₁ j := h.bundle₁ (e.symm j)
  bundle₂ j := h.bundle₂ (e.symm j)

omit [MeasurableSpace P] in
theorem RSymP.reindex_kernel (e : ι ≃ ι') (R : RSymP P ι) (p : P) (α : Option ι' → ℝ)
    (t s : ℝ) : ((R.reindex e).get p).kernel α t s =
      (R.get p).kernel (fun o => α (Option.map e o)) t s := by
  simp only [RSym.kernel, RSymP.reindex, RSymP.get, nsp, bundle_reindex, Option.map_none]
  rfl

end ReindexR

section FormsR

variable {ι : Type*} [Fintype ι]

/-- The forms `x₀ = γ₂ - ℓ₂ - ε₂α₂` and `x₁ = ℓ₁ + γ₃ + ε₂α₂` of the class `R` pieces, on the
variables `(ι ⊕ Empty) ⊕ Unit` (`α₂ = α (inr ())`). -/
@[expose] def LsIRIR (R : RSym ι) : Fin 2 → (ι ⊕ Empty) ⊕ Unit → ℤ :=
  ![y3 (fun i => -R.y₂ i) 0 (-R.ε), y3 R.y₁ 0 R.ε]

/-- The constant parts `γ₂` and `γ₃`. -/
@[expose] def csIRIR (Q : Type*) : Fin 2 → (ℝ × ℝ × ℝ) × (Unit × Q) → ℝ :=
  ![fun z => z.1.2.1, fun z => z.1.2.2]

theorem isBundle_LsIRIR {R : RSym ι} {θ A N : ℝ} (h : R.Bound θ A N) :
    ∀ r, IsBundle (LsIRIR R r) := by
  intro r; fin_cases r
  · refine isBundle_y3 (fun i => ?_) isBundle_zero (abs_sign_le (sign_neg h.sign))
    simpa using h.bundle₂ i
  · exact isBundle_y3 h.bundle₁ isBundle_zero (abs_sign_le h.sign)

theorem measurable_csIRIR (Q : Type*) [MeasurableSpace Q] : ∀ r, Measurable (csIRIR Q r) := by
  intro r; fin_cases r
  · simp only [csIRIR]; exact measurable_fst.comp (measurable_snd.comp measurable_fst)
  · simp only [csIRIR]; exact measurable_snd.comp (measurable_snd.comp measurable_fst)

variable {R : RSym ι} {Q : Type*}

theorem formsV_IRIR_zero (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (z : (ℝ × ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIRIR R) (csIRIR Q) α z 0 =
      z.1.2.1 - bundle R.y₂ (vA α) - R.ε * α (Sum.inr ()) := by
  simp only [formsV, LsIRIR, csIRIR, Matrix.cons_val, bundle_y3, bundle_zero_fun]
  have : bundle (fun i => -R.y₂ i) (vA α) = -bundle R.y₂ (vA α) := by
    simp [bundle, Finset.sum_neg_distrib]
  rw [this]; push_cast; ring

theorem formsV_IRIR_one (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (z : (ℝ × ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIRIR R) (csIRIR Q) α z 1 = bundle R.y₁ (vA α) + z.1.2.2 + R.ε * α (Sum.inr ()) := by
  simp only [formsV, LsIRIR, csIRIR, Matrix.cons_val, bundle_y3, bundle_zero_fun]
  ring

end FormsR

end WaveTurbulence.ClassJR
