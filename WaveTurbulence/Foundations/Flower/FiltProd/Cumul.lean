/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Dens
public import WaveTurbulence.Foundations.Incoh.RootCumulativeLocal
public import WaveTurbulence.Foundations.Incoh.TreeCausalGlobalSource

/-! # D5b-2 FILT-PROD: cumulative and causal kernels (twins of `RootCumulative`, `RootCumulativeLocal`, `RootCausalSource`, `TreeCausalExtension` (def), `TreeCausalGlobalSource`)

For trees the multiplier may depend on the momentum: `φ : Mom d → Fin n → ℝ → ℂ` (link `i` at momentum `k` carries `φ k i`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc
/-- The localized source kernel with its literal external root-time constraints. -/
def RootCoordinates.cumulativeKernelFilt {d n : ℕ} (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ)) (t : Fin 2 → ℝ) : ℂ :=
  normalizedLinkIntegralFilt L γ δ Q φ (I ∩ R.rootCut t)

/-- TARGET (incohproof17): the literal constrained kernel is the cumulative actual root density. -/
theorem RootCoordinates.cumulativeKernel_eq_setIntegralFilt {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (t : Fin 2 → ℝ) :
    RootCoordinates.cumulativeKernelFilt R L γ δ Q φ I t = ∫ u in Iic t, RootCoordinates.linkDensityFilt R L γ δ Q φ I u := by
  have hcut := R.measurableSet_rootCut t
  have hF := integrable_normalizedLinkIntegrandFilt hL γ δ Q φ hI hbox
  have heq : normalizedLinkIntegrandFilt L γ δ Q φ (I ∩ R.rootCut t) =
      (R.rootCut t).indicator (normalizedLinkIntegrandFilt L γ δ Q φ I) := by
    funext u
    by_cases hi : u ∈ I <;> by_cases hc : u ∈ R.rootCut t <;>
      simp [normalizedLinkIntegrandFilt, hi, hc]
  rw [cumulativeKernelFilt, ← integral_normalizedLinkIntegrandFilt L γ δ Q φ (hI.inter hcut), heq,
    integral_indicator hcut]
  exact (R.setIntegral_density hF (Iic t)).symm



/-- The literal cumulative kernel is exactly the root-box integral in local clocks. -/
theorem RootCoordinates.cumulativeKernel_eq_localBoxIntegralFilt {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (t : Fin 2 → ℝ) :
    RootCoordinates.cumulativeKernelFilt R L γ δ Q φ I t =
      ∫ u in Icc (0 : Fin 2 → ℝ) (t - R.baseRootTimes Q), RootCoordinates.localLinkDensityFilt R L γ δ Q φ I u := by
  classical
  let q := R.baseRootTimes Q
  let F := RootCoordinates.linkDensityFilt R L γ δ Q φ I
  have hind : (Iic t).indicator F = (Icc q t).indicator F := by
    funext u
    by_cases hup : u ≤ t
    · by_cases hlo : q ≤ u
      · simp [hup, hlo]
      · have hz : F u = 0 := RootCoordinates.linkDensityFilt_eq_zero_of_notMem_rootBox R L γ δ Q φ hbox (fun h => hlo h.1)
        simp [hup, hlo, hz]
    · simp [hup]
  have hpre : (fun u : Fin 2 → ℝ => u + q) ⁻¹' Icc q t = Icc (0 : Fin 2 → ℝ) (t - q) := by
    ext u
    simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    constructor
    · intro h
      constructor
      · intro a; have ha := h.1 a; linarith
      · intro a; have ha := h.2 a; linarith
    · intro h
      constructor
      · intro a; have ha := h.1 a; linarith
      · intro a; have ha := h.2 a; linarith
  have hmp : MeasurePreserving (fun u : Fin 2 → ℝ => u + q) := measurePreserving_add_right volume q
  have htrans := hmp.setIntegral_preimage_emb (MeasurableEquiv.addRight q).measurableEmbedding F (Icc q t)
  rw [hpre] at htrans
  calc
    _ = ∫ u in Iic t, F u := RootCoordinates.cumulativeKernel_eq_setIntegralFilt R hL γ δ Q φ hI hbox t
    _ = ∫ u in Icc q t, F u := by
      rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Icc, hind]
    _ = _ := htrans.symm

/-- The literal normalized source product with its external causal constraints. -/
def RootCoordinates.causalKernelFilt {d n : ℕ} (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ)) (t : Fin 2 → ℝ) : ℂ :=
  normalizedLinkIntegralFilt L γ δ Q φ (I ∩ R.causalRootCut t)

/-- The actual constrained source integral is the causal root-marginal integral. -/
theorem RootCoordinates.causalKernel_eq_setIntegralFilt {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (t : Fin 2 → ℝ) :
    RootCoordinates.causalKernelFilt R L γ δ Q φ I t = ∫ u in causalTriangle (t 0) (t 1), RootCoordinates.linkDensityFilt R L γ δ Q φ I u := by
  have hcut := R.measurableSet_causalRootCut t
  have hF := integrable_normalizedLinkIntegrandFilt hL γ δ Q φ hI hbox
  have heq : normalizedLinkIntegrandFilt L γ δ Q φ (I ∩ R.causalRootCut t) =
      (R.causalRootCut t).indicator (normalizedLinkIntegrandFilt L γ δ Q φ I) := by
    funext u
    by_cases hi : u ∈ I <;> by_cases hc : u ∈ R.causalRootCut t <;>
      simp [normalizedLinkIntegrandFilt, hi, hc]
  rw [causalKernelFilt, ← integral_normalizedLinkIntegrandFilt L γ δ Q φ (hI.inter hcut), heq,
    integral_indicator hcut]
  exact (R.setIntegral_density hF (causalTriangle (t 0) (t 1))).symm

/-- Interior clock cutoffs equal to one on the source box leave the literal marginal unchanged. -/
theorem RootCoordinates.cutoff_linkDensity_eq_selfFilt {d n : ℕ} (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {χ : ℝ → ℝ}
    (hχ : ∀ u ∈ R.rootBox Q, ∀ j, χ (u j) = 1) (u : Fin 2 → ℝ) :
    (χ (u 0) : ℂ) * (χ (u 1) : ℂ) * RootCoordinates.linkDensityFilt R L γ δ Q φ I u = RootCoordinates.linkDensityFilt R L γ δ Q φ I u := by
  by_cases hu : u ∈ R.rootBox Q
  · rw [hχ u hu 0, hχ u hu 1]
    simp only [Complex.ofReal_one, one_mul]
  · rw [RootCoordinates.linkDensityFilt_eq_zero_of_notMem_rootBox R L γ δ Q φ hbox hu, mul_zero]

/-- The causal cutoff extension of the actual root/lone-parent marginal. -/
def RootCoordinates.treeCausalExtensionFilt {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Mom d → Fin n → LayerLink d) (φ : Mom d → Fin n → ℝ → ℂ)
    (I : Mom d → Set (Fin n → Fin 2 → ℝ)) : (Fin 2 → ℝ) → Mom d → ℂ :=
  Fourier.cutoffJ χ (fun t k => RootCoordinates.linkDensityFilt R L γ δ (Q k) (φ k) (I k) t)

/-- The estimated causal extension agrees pointwise with the literal source kernel. -/
theorem RootCoordinates.treeCausalExtension_agreesFilt {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Mom d → Fin n → LayerLink d) (φ : Mom d → Fin n → ℝ → ℂ)
    (I : Mom d → Set (Fin n → Fin 2 → ℝ)) (k : Mom d) (hI : MeasurableSet (I k))
    (hbox : I k ⊆ univ.pi (fun i => linkBox (Q k i))) {χ : ℝ → ℝ}
    (hχ : ∀ u ∈ R.rootBox (Q k), ∀ j, χ (u j) = 1)
    {t : Fin 2 → ℝ} (ht : t 1 ≤ t 0) (htχ : ∀ j, χ (t j) = 1) :
    RootCoordinates.treeCausalExtensionFilt R χ L γ δ Q φ I t k = RootCoordinates.causalKernelFilt R L γ δ (Q k) (φ k) (I k) t := by
  have he (x y : ℝ) : (χ x : ℂ) * (χ y : ℂ) * RootCoordinates.linkDensityFilt R L γ δ (Q k) (φ k) (I k) ![x, y] =
      RootCoordinates.linkDensityFilt R L γ δ (Q k) (φ k) (I k) ![x, y] :=
    RootCoordinates.cutoff_linkDensity_eq_selfFilt R L γ δ (Q k) (φ k) hbox hχ ![x, y]
  change (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    (∫ x in t 1..t 0, ∫ y in t 1..x,
      (χ x : ℂ) * (χ y : ℂ) * RootCoordinates.linkDensityFilt R L γ δ (Q k) (φ k) (I k) ![x, y]) = _
  rw [htχ 0, htχ 1]
  simp only [Complex.ofReal_one, one_mul]
  simp_rw [he]
  rw [integral_triangle_eq_setIntegral (RootCoordinates.integrable_linkDensityFilt R hL γ δ (Q k) (φ k) hI hbox) ht]
  exact (RootCoordinates.causalKernel_eq_setIntegralFilt R hL γ δ (Q k) (φ k) hI hbox t).symm




/-- The canonical extension equals the cutoff-weighted source at forward clocks. -/
theorem RootCoordinates.treeCausalExtension_eq_weighted_sourceFilt {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Mom d → Fin n → LayerLink d) (φ : Mom d → Fin n → ℝ → ℂ)
    (I : Mom d → Set (Fin n → Fin 2 → ℝ)) (k : Mom d) (hI : MeasurableSet (I k))
    (hbox : I k ⊆ univ.pi (fun i => linkBox (Q k i))) {χ : ℝ → ℝ}
    (hχ : ∀ u ∈ R.rootBox (Q k), ∀ j, χ (u j) = 1)
    {t : Fin 2 → ℝ} (ht : t 1 ≤ t 0) :
    RootCoordinates.treeCausalExtensionFilt R χ L γ δ Q φ I t k =
      (χ (t 0) : ℂ) * (χ (t 1) : ℂ) * RootCoordinates.causalKernelFilt R L γ δ (Q k) (φ k) (I k) t := by
  have he (x y : ℝ) : (χ x : ℂ) * (χ y : ℂ) * RootCoordinates.linkDensityFilt R L γ δ (Q k) (φ k) (I k) ![x, y] =
      RootCoordinates.linkDensityFilt R L γ δ (Q k) (φ k) (I k) ![x, y] :=
    RootCoordinates.cutoff_linkDensity_eq_selfFilt R L γ δ (Q k) (φ k) hbox hχ ![x, y]
  change (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    (∫ x in t 1..t 0, ∫ y in t 1..x,
      (χ x : ℂ) * (χ y : ℂ) * RootCoordinates.linkDensityFilt R L γ δ (Q k) (φ k) (I k) ![x, y]) = _
  simp_rw [he]
  rw [integral_triangle_eq_setIntegral (RootCoordinates.integrable_linkDensityFilt R hL γ δ (Q k) (φ k) hI hbox) ht,
    RootCoordinates.causalKernel_eq_setIntegralFilt R hL γ δ (Q k) (φ k) hI hbox t]

/-- Causal support of the literal source gives causal support of its actual root marginal. -/
theorem RootCoordinates.linkDensity_eq_zero_of_reverseFilt {d n : ℕ} (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (hord : ∀ w ∈ I, (R.equiv w).1 1 < (R.equiv w).1 0)
    {v : Fin 2 → ℝ} (hv : v 0 ≤ v 1) : RootCoordinates.linkDensityFilt R L γ δ Q φ I v = 0 := by
  unfold RootCoordinates.linkDensityFilt RootCoordinates.density
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  have hi : R.equiv.symm (v, u) ∉ I := by
    intro h
    have hh := hord _ h
    rw [MeasurableEquiv.apply_symm_apply] at hh
    exact (not_lt_of_ge hv) hh
  simp only [normalizedLinkIntegrandFilt, indicator_of_notMem hi, mul_zero, Pi.zero_apply]

/-- Reversed external clock pairs give zero for every causally supported source. -/
theorem RootCoordinates.treeCausalExtension_eq_zero_of_reverseFilt {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Mom d → Fin n → LayerLink d) (φ : Mom d → Fin n → ℝ → ℂ)
    (I : Mom d → Set (Fin n → Fin 2 → ℝ)) (k : Mom d)
    (hord : ∀ w ∈ I k, (R.equiv w).1 1 < (R.equiv w).1 0)
    {t : Fin 2 → ℝ} (ht : t 0 ≤ t 1) : RootCoordinates.treeCausalExtensionFilt R χ L γ δ Q φ I t k = 0 := by
  change (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    Fourier.orderedIntegral 2 (fun v => (χ (v 0) : ℂ) * (χ (v 1) : ℂ) *
      RootCoordinates.linkDensityFilt R L γ δ (Q k) (φ k) (I k) v) (t 0) (t 1) = 0
  rw [orderedIntegral_eq_zero_of_reverse_support 0 _ (fun v hv => by
    rw [RootCoordinates.linkDensity_eq_zero_of_reverseFilt R L γ δ (Q k) (φ k) (I k) hord hv, mul_zero]) ht, mul_zero]


end WaveTurbulence.Flower.FiltProd
