/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCReorder

/-!
# Coefficient symbols with the DH23 bounds, swaps and pure products

`SRep θ a b A N C` collects the properties of a coefficient symbol `𝒞 : (ι → ℝ) → ℝ × ℝ → ℂ` in DH21
Proposition 5.1 with the DH23 weights:
* regularity (`SymReg`, audit W3);
* (maincoef2) `∫∫ wL θ |∂^k 𝒞| ≤ gev N A k`;
* (maincoef2.5) per variable, `∫∫ wL a (1 + |α_i|)^b |𝒞| ≤ N`.

`swapC` exchanges the two frequencies (DH21 L924, L936: "the variables `(t₁, s₁)` may be replaced by
`(s₁, t₁)`"). `pprod` is the product of two symbols in disjoint variables, a coupled product
(`kprod`) with trivial coupling.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section SRepDef

variable {ι : Type*} [Fintype ι]

/-- **The bounds of a coefficient symbol** (DH21 (maincoef2), (maincoef2.5) with DH23 weights). -/
structure SRep (θ a b A N : ℝ) (C : (ι → ℝ) → ℝ × ℝ → ℂ) : Prop where
  nonneg : 0 ≤ N
  reg : SymReg C
  norm : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam * dnorm k C α lam ≤ gev N A k
  wnorm : ∀ i : ι, ∫⁻ α, ∫⁻ lam, wL a lam * (1 + ‖α i‖ₑ) ^ b * ‖C α lam‖ₑ ≤ ENNReal.ofReal N

theorem one_le_wL {a : ℝ} (h0 : 0 ≤ a) (lam : ℝ × ℝ) : 1 ≤ wL a lam := by
  unfold wL
  rcases eq_or_lt_of_le h0 with h' | h'
  · rw [← h', ENNReal.rpow_zero]
  · exact ENNReal.one_le_rpow (le_self_add.trans le_self_add) h'

theorem measurable_wL (a : ℝ) : Measurable (wL a) := by unfold wL; fun_prop

theorem wL_swap (a : ℝ) (lam : ℝ × ℝ) : wL a lam.swap = wL a lam := by
  simp only [wL, Prod.fst_swap, Prod.snd_swap, add_assoc, add_comm ‖lam.2‖ₑ]

/-- The unweighted norms are dominated by the `wL θ` norms. -/
theorem SRep.norm_unweighted {θ a b A N : ℝ} {C : (ι → ℝ) → ℝ × ℝ → ℂ} (h : SRep θ a b A N C)
    (hθ : 0 ≤ θ) (k : ℕ) : ∫⁻ α, ∫⁻ lam, dnorm k C α lam ≤ gev N A k :=
  (lintegral_mono fun _ => lintegral_mono fun lam =>
    le_mul_of_one_le_left bot_le (one_le_wL hθ lam)).trans (h.norm k)

end SRepDef

section Swap

variable {ι : Type*} [Fintype ι]

/-- **Exchanging the two frequencies** of a coefficient symbol. -/
@[expose] def swapC (sw : Bool) (C : (ι → ℝ) → ℝ × ℝ → ℂ) : (ι → ℝ) → ℝ × ℝ → ℂ :=
  if sw then fun α lam => C α lam.swap else C

theorem dnorm_swap (k : ℕ) (C : (ι → ℝ) → ℝ × ℝ → ℂ) (α : ι → ℝ) (lam : ℝ × ℝ) :
    dnorm k (fun α lam => C α lam.swap) α lam = dnorm k C α lam.swap := rfl

theorem lintegral_swap_eq (F : ℝ × ℝ → ℝ≥0∞) : ∫⁻ lam : ℝ × ℝ, F lam.swap = ∫⁻ lam, F lam := by
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).lintegral_comp_emb MeasurableEquiv.prodComm.measurableEmbedding F
  rw [← Measure.volume_eq_prod] at h
  exact h

theorem integral_swap_eq (F : ℝ × ℝ → ℂ) : ∫ lam : ℝ × ℝ, F lam.swap = ∫ lam, F lam := by
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).integral_comp MeasurableEquiv.prodComm.measurableEmbedding F
  rw [← Measure.volume_eq_prod] at h
  exact h

theorem SRep.swap {θ a b A N : ℝ} {C : (ι → ℝ) → ℝ × ℝ → ℂ} (h : SRep θ a b A N C) (sw : Bool) :
    SRep θ a b A N (swapC sw C) := by
  cases sw
  · simpa [swapC] using h
  · simp only [swapC, ↓reduceIte]
    refine ⟨h.nonneg, ?_, fun k => ?_, fun i => ?_⟩
    · refine ⟨fun lam => h.reg.smooth lam.swap, ?_, fun k => ?_⟩
      · exact h.reg.meas.comp_measurable (measurable_fst.prodMk (measurable_swap.comp measurable_snd))
      · have := h.reg.dom k
        simp only [supD, dnorm_swap]
        rw [lintegral_swap_eq (fun lam => ⨆ α, dnorm k C α lam)]
        exact this
    · refine le_trans (le_of_eq ?_) (h.norm k)
      refine lintegral_congr fun α => ?_
      rw [← lintegral_swap_eq (fun lam => wL θ lam * dnorm k C α lam)]
      simp only [dnorm_swap, wL_swap]
    · refine le_trans (le_of_eq ?_) (h.wnorm i)
      refine lintegral_congr fun α => ?_
      rw [← lintegral_swap_eq (fun lam => wL a lam * (1 + ‖α i‖ₑ) ^ b * ‖C α lam‖ₑ)]
      simp only [wL_swap]

omit [Fintype ι] in
/-- `∫ swapC sw C(α, λ) e^{πi(λ₁t + λ₂s)} = ∫ C(α, λ) e^{πi(λ₁t' + λ₂s')}` with `(t', s')` the
swapped times. -/
theorem integral_swapC_e2 (sw : Bool) (C : (ι → ℝ) → ℝ × ℝ → ℂ) (α : ι → ℝ) (t s : ℝ) :
    ∫ lam, swapC sw C α lam * e2 lam t s =
      if sw then ∫ lam, C α lam * e2 lam s t else ∫ lam, C α lam * e2 lam t s := by
  cases sw
  · simp [swapC]
  · simp only [swapC, ↓reduceIte]
    rw [← integral_swap_eq (fun lam => C α lam * e2 lam s t)]
    refine integral_congr_ae (Eventually.of_forall fun lam => ?_)
    simp only [e2, Prod.fst_swap, Prod.snd_swap]
    congr 2
    ring

end Swap

section PureProduct

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {Z Q : Type*} [MeasureSpace Z] [MeasureSpace Q]
  [SFinite (volume : Measure Z)] [SFinite (volume : Measure Q)]

/-- **The product of two symbols in disjoint variables** (trivial coupling). -/
@[expose] def pprod (M : (ι₁ → ℝ) → Z → ℂ) (C : (ι₂ → ℝ) → Q → ℂ) :
    (ι₁ ⊕ ι₂ → ℝ) → Z × Q → ℂ :=
  kprod M fun α p => C α p.2

/-- **Weighted norms of pure products.** -/
theorem lintegral_pprod_le {M : (ι₁ → ℝ) → Z → ℂ} {C : (ι₂ → ℝ) → Q → ℂ}
    (hMs : ∀ z, ContDiff ℝ ∞ fun α => M α z) (hMm : StronglyMeasurable (Function.uncurry M))
    (hCs : ∀ q, ContDiff ℝ ∞ fun α => C α q) (hCm : StronglyMeasurable (Function.uncurry C))
    {wM : (ι₁ → ℝ) → Z → ℝ≥0∞} (hwM : Measurable (Function.uncurry wM))
    {wC : (ι₂ → ℝ) → Q → ℝ≥0∞} (hwC : Measurable (Function.uncurry wC)) (k : ℕ) :
    ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ p : Z × Q, wM (fun i => α (Sum.inl i)) p.1 *
        wC (fun i => α (Sum.inr i)) p.2 * dnorm k (pprod M C) α p ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
        (∫⁻ α₁, ∫⁻ z, wM α₁ z * dnorm j M α₁ z) *
          ∫⁻ α₂, ∫⁻ q, wC α₂ q * dnorm (k - j) C α₂ q := by
  have hKm : StronglyMeasurable (Function.uncurry fun (α : ι₂ → ℝ) (p : Z × Q) => C α p.2) :=
    (hCm.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).stronglyMeasurable
  have h := lintegral_kprod_le (M := M) (K := fun α p => C α p.2) hMs hMm (fun p => hCs p.2) hKm
    hwM (wK := fun α p => wC α p.2)
    (hwC.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    (v := fun _ => 1) measurable_const
    (g := fun j => ∫⁻ α₂, ∫⁻ q, wC α₂ q * dnorm j C α₂ q)
    (fun j z => by
      simp only [mul_one]
      exact le_rfl) k
  simp only [mul_one] at h
  exact h

omit [MeasureSpace Z] [MeasureSpace Q] [SFinite (volume : Measure Z)]
  [SFinite (volume : Measure Q)] in
theorem contDiff_pprod {M : (ι₁ → ℝ) → Z → ℂ} {C : (ι₂ → ℝ) → Q → ℂ}
    (hMs : ∀ z, ContDiff ℝ ∞ fun α => M α z) (hCs : ∀ q, ContDiff ℝ ∞ fun α => C α q)
    (p : Z × Q) : ContDiff ℝ ∞ fun α => pprod M C α p :=
  contDiff_kprod hMs (fun p => hCs p.2) p

omit [Fintype ι₁] [Fintype ι₂] [MeasureSpace Z] [MeasureSpace Q] [SFinite (volume : Measure Z)]
  [SFinite (volume : Measure Q)] in
theorem measurable_pprod [MeasurableSpace Z] [MeasurableSpace Q] {M : (ι₁ → ℝ) → Z → ℂ}
    {C : (ι₂ → ℝ) → Q → ℂ} (hMm : StronglyMeasurable (Function.uncurry M))
    (hCm : StronglyMeasurable (Function.uncurry C)) :
    StronglyMeasurable (Function.uncurry (pprod M C)) :=
  measurable_kprod hMm
    (hCm.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).stronglyMeasurable

end PureProduct

end WaveTurbulence.ClassJR
