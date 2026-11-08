/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.EngInt

/-! # B3s-HELPER3 B3 (1): the assembled expansion on a general time domain

Domain-generic twin of `MkSlots/EngInt.lean` (B3s's pinned engine, step 2). Main's `AsmCtxH` is reused unchanged
(built with the unpinned hinge hypothesis `hHk`); only what reads the time domain is twinned:
* `gIHD A D`: main's summand `gIH` (RepH8) with the indicator of an arbitrary set `D` of time vectors;
* `hasSum_gIHD`: copy of main's `hasSum_gIH`, using main's pointwise `hasSum_assembledH` with the hinge HasSum and the
  slot boxes assumed ON `D` (`hboxD`, `hHkD`), so it holds at every `τ`;
* the integral lemmas of `EngInt` with `μ D ≤ 1` in place of `μ (splicedTimeDomain) ≤ 1`.
Against `fixMeasure fix` the engine integrates over `D := Dom ∩ pinSet fix` (`pinSet fix`: the pinned coordinates
equal the pins); `fixMeasure fix` only sees `pinSet fix` (`integral_fixMeasure_inter_pinSet`), so the outer form on
`Dom` and the kernel's relaxed domain agree under `hsliceD` (`integral_fixMeasure_indicatorD`, `value_eqHMD`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsB

/-! ## The pinned slice -/

/-- The pinned slice: time vectors whose pinned coordinates are the pins. -/
def pinSet {ι : Type*} (fix : ι → Option ℝ) : Set (ι → ℝ) := {τ | ∀ i v, fix i = some v → τ i = v}

theorem measurableSet_pinSet {ι : Type*} [Countable ι] (fix : ι → Option ℝ) : MeasurableSet (pinSet fix) := by
  have h : pinSet fix = ⋂ i, {τ : ι → ℝ | ∀ v, fix i = some v → τ i = v} := by
    ext τ; simp [pinSet]
  rw [h]
  refine MeasurableSet.iInter fun i => ?_
  rcases hi : fix i with _ | v
  · simp
  · have : {τ : ι → ℝ | ∀ v', some v = some v' → τ i = v'} = {τ | τ i = v} := by
      ext τ; simp
    rw [this]
    exact measurableSet_eq_fun (measurable_pi_apply i) measurable_const

theorem extendFixI_mem_pinSet {ι : Type*} (fix : ι → Option ℝ) (τ : {i // fix i = none} → ℝ) :
    extendFixI fix τ ∈ pinSet fix := fun _ _ h => extendFixI_some fix τ h

/-- `fixMeasure fix` only sees the pinned slice. -/
theorem integral_fixMeasure_inter_pinSet {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (fix : ι → Option ℝ) (Dom : Set (ι → ℝ)) (f : (ι → ℝ) → E) :
    ∫ τ, (Dom ∩ pinSet fix).indicator f τ ∂(fixMeasure fix) = ∫ τ, Dom.indicator f τ ∂(fixMeasure fix) := by
  rw [integral_fixMeasure, integral_fixMeasure]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  by_cases h : extendFixI fix τ ∈ Dom
  · have h' : extendFixI fix τ ∈ Dom ∩ pinSet fix := ⟨h, extendFixI_mem_pinSet fix τ⟩
    rw [indicator_of_mem h', indicator_of_mem h]
  · have h' : extendFixI fix τ ∉ Dom ∩ pinSet fix := fun h' => h h'.1
    rw [indicator_of_notMem h', indicator_of_notMem h]

variable {w d : ℕ}

/-- **The time integral against the pinned measure on `Dom ∩ pinSet` is the pinned time integral**, when `Dom` and
the relaxed pinned domain agree on the pinned slice (domain-generic `integral_fixMeasure_indicator`). -/
theorem integral_fixMeasure_indicatorD (G : Garden w) (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (Dom : Set (GBranch G.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch G.tree // D.fix b = none} → ℝ,
      G.extendFix D.fix τ ∈ Dom ↔ G.extendFix D.fix τ ∈ splicedTimeDomainFix G D.layer D.rootTime D.fix ∩ splicedLBDomain D.lb) :
    ∫ τ, (Dom ∩ pinSet D.fix).indicator (fun t =>
        phaseProd L γ δ G (cosetDecoration G L base z) t *
          ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I)) τ
        ∂(fixMeasure D.fix) =
      splicedTimeIntegralMK G D L γ δ base z := by
  rw [integral_fixMeasure_inter_pinSet, integral_fixMeasure]
  unfold splicedTimeIntegralMK
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  rw [← extendFix_eq_extendFixI_fun G D.fix]
  by_cases h : G.extendFix D.fix τ ∈ Dom
  · rw [indicator_of_mem h, indicator_of_mem ((hsliceD τ).1 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hsliceD τ).2 h'))]

/-! ## The summand on a general domain -/

variable {S : Garden w} (A : AsmCtxH S d)

open scoped Classical in
/-- Main's summand `gIH` (RepH8) with the indicator of the set `D` of time vectors. -/
def gIHD (D : Set (GBranch S.tree → ℝ)) (ξh : A.Xi) (κ : GenDecoration S d A.roots 0)
    (τ : GBranch S.tree → ℝ) : ℂ :=
  (if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
    (A.constWH ξh * A.E ξh.1 κ * A.hingeAmp ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1))) *
    D.indicator (fun τ =>
      phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.timeFacH ξh τ) τ

/-- The summand on `D` with the atom weight of the decoration. -/
def gIHMD (D : Set (GBranch S.tree → ℝ)) (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode S.tree → Mom d) → ℝ) (ξh : A.Xi) (κ : GenDecoration S d A.roots 0)
    (τ : GBranch S.tree → ℝ) : ℂ :=
  atomWF filt ind (cosetDecoration S A.L A.base κ.1) * gIHD A D ξh κ τ

section Generic

variable (D : Set (GBranch S.tree → ℝ))

open scoped Classical in
/-- Main's `hasSum_gIH` on the domain `D`, with the slot boxes and the hinge HasSum assumed on `D`. -/
theorem hasSum_gIHD (hboxD : ∀ τ ∈ D, ∀ s, slotTs A.hS A.tt τ s ∈ A.Box s)
    (hHkD : ∀ κ : GenDecoration S d A.roots 0, A.selSk κ → ∀ τ ∈ D, ∀ j c,
      (∀ i, ‖(A.base + latticePoint A.L (κ.1 (A.hmom j i))) - latPt d (c i)‖ ≤ 1) →
      HasSum (fun l => (A.H.w j c l : ℂ) * A.H.a j c l (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i))) *
        fsPhase (A.H.m j c l) (fun i => clockOf S A.tt τ (A.hclk j i)))
        (A.Hk j (fun i => clockOf S A.tt τ (A.hclk j i))
          (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i)))))
    (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    HasSum (fun ξh => gIHD A D ξh κ τ) ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
      D.indicator (fun τ =>
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ) := by
  by_cases hτ : τ ∈ D
  · by_cases hsel : A.selSk κ
    · simp only [Set.indicator_of_mem hτ, hsel, ↓reduceIte]
      have hs := hasSum_assembledH A.fam A.hS A.hd A.Cχ A.hC A.hCpos A.L A.base A.roots A.tt A.Fn κ τ
        (fun s => A.hFn s _ (hboxD τ hτ s) _) A.H A.hmom A.hclk A.Hk A.Mh A.hMh
        (fun j c hc => hHkD κ hsel τ hτ j c hc)
      have h2 := hs.mul_left (((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) *
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ)
      convert h2 using 1
      · funext ξh
        simp only [gIHD, hsel, ↓reduceIte, Set.indicator_of_mem hτ]
        rw [mul_assoc (((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ)) (phaseProd _ _ _ _ _ _),
          A.slotTerm_mul_hingeTerm ξh κ τ]
        ring
      · unfold AsmCtx.skel AsmCtxH.hk; ring
    · simp only [gIHD, hsel, ↓reduceIte, zero_mul]
      exact hasSum_zero
  · simp only [gIHD, Set.indicator_of_notMem hτ, mul_zero]
    exact hasSum_zero

/-- Main's `norm_gIH_le` (RepH9) on the domain `D`. -/
theorem norm_gIHD_le (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    ‖gIHD A D ξh κ τ‖ ≤ D.indicator (fun _ => ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) τ := by
  classical
  unfold gIHD
  by_cases hτ : τ ∈ D
  · simp only [Set.indicator_of_mem hτ]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_phaseProd_le, one_mul, A.norm_timeFacH, mul_one]
    have h1 : ‖(if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0)‖ ≤ 1 := by
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs]; exact AsmCtxH.norm_splicedEpsilon_le S A.hinges κ.1
      · simp
    have h2 := A.norm_hingeAmp_le ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1))
    calc _ ≤ 1 * (‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖ * 1) := by gcongr
      _ = _ := by ring
  · simp [Set.indicator_of_notMem hτ]

theorem meas_gIHD (hD : MeasurableSet D) (μ : Measure (GBranch S.tree → ℝ)) (ξh : A.Xi)
    (κ : GenDecoration S d A.roots 0) : AEStronglyMeasurable (gIHD A D ξh κ) μ := by
  classical
  unfold gIHD
  refine aestronglyMeasurable_const.mul ?_
  refine (Continuous.aestronglyMeasurable ?_).indicator hD
  exact (Represents.continuous_phaseProd _ _ _ _).mul (A.continuous_timeFacH ξh)

variable (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ)) (ind : (GNode S.tree → Mom d) → ℝ)

open scoped Classical in
theorem hasSum_gIHMD (hboxD : ∀ τ ∈ D, ∀ s, slotTs A.hS A.tt τ s ∈ A.Box s)
    (hHkD : ∀ κ : GenDecoration S d A.roots 0, A.selSk κ → ∀ τ ∈ D, ∀ j c,
      (∀ i, ‖(A.base + latticePoint A.L (κ.1 (A.hmom j i))) - latPt d (c i)‖ ≤ 1) →
      HasSum (fun l => (A.H.w j c l : ℂ) * A.H.a j c l (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i))) *
        fsPhase (A.H.m j c l) (fun i => clockOf S A.tt τ (A.hclk j i)))
        (A.Hk j (fun i => clockOf S A.tt τ (A.hclk j i))
          (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i)))))
    (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    HasSum (fun ξh => gIHMD A D filt ind ξh κ τ) (atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
      ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        D.indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ)) :=
  (hasSum_gIHD A D hboxD hHkD κ τ).mul_left _

theorem meas_gIHMD (hD : MeasurableSet D) (μ : Measure (GBranch S.tree → ℝ)) (ξh : A.Xi)
    (κ : GenDecoration S d A.roots 0) : AEStronglyMeasurable (gIHMD A D filt ind ξh κ) μ :=
  aestronglyMeasurable_const.mul (meas_gIHD A D hD μ ξh κ)

variable {filt ind} (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1)
include hfilt hind

theorem norm_gIHMD_le (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    ‖gIHMD A D filt ind ξh κ τ‖ ≤ D.indicator (fun _ => ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) τ := by
  unfold gIHMD
  rw [norm_mul]
  calc _ ≤ 1 * ‖gIHD A D ξh κ τ‖ :=
        mul_le_mul_of_nonneg_right (norm_atomWF_le filt ind hfilt hind _) (norm_nonneg _)
    _ = ‖gIHD A D ξh κ τ‖ := one_mul _
    _ ≤ _ := norm_gIHD_le A D ξh κ τ

/-- `EngInt.lintegral_gIHM_le` on the domain `D`, against a time measure with `μ D ≤ 1`. -/
theorem lintegral_gIHMD_le (hD : MeasurableSet D) (μ : Measure (GBranch S.tree → ℝ)) (hμ : μ D ≤ 1)
    (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) :
    ∫⁻ τ, ‖gIHMD A D filt ind ξh κ τ‖ₑ ∂μ ≤ ENNReal.ofReal (‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) := by
  classical
  set c : ℝ := ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖ with hc
  calc ∫⁻ τ, ‖gIHMD A D filt ind ξh κ τ‖ₑ ∂μ
      ≤ ∫⁻ τ, D.indicator (fun _ => ENNReal.ofReal c) τ ∂μ := by
        refine lintegral_mono fun τ => ?_
        have := norm_gIHMD_le A D hfilt hind ξh κ τ
        by_cases hτ : τ ∈ D
        · simp only [Set.indicator_of_mem hτ] at this ⊢
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal this
        · simp only [Set.indicator_of_notMem hτ] at this ⊢
          have h0 : gIHMD A D filt ind ξh κ τ = 0 := norm_le_zero_iff.1 this
          rw [h0]; simp
    _ = ENNReal.ofReal c * μ D := lintegral_indicator_const hD _
    _ ≤ ENNReal.ofReal c * 1 := by gcongr
    _ = _ := mul_one _

open scoped Classical in
/-- `EngInt.sum_lintegral_gIHM_ne_top` on the domain `D`. -/
theorem sum_lintegral_gIHMD_ne_top (hD : MeasurableSet D) (μ : Measure (GBranch S.tree → ℝ)) (hμ : μ D ≤ 1) :
    ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHMD A D filt ind ξh κ τ‖ₑ ∂μ ≠ ⊤ := by
  set N : ℝ≥0∞ := ((((⌊2 * A.L⌋₊ + 2) ^ d) ^ Fintype.card (Reg.Skeleton.SourcePair S) : ℕ) : ℝ≥0∞) with hN
  have h1 : ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHMD A D filt ind ξh κ τ‖ₑ ∂μ ≤
      ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ * N := by
    refine ENNReal.tsum_le_tsum fun ξh => ?_
    calc ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHMD A D filt ind ξh κ τ‖ₑ ∂μ
        ≤ ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.constWH ξh‖ * ENNReal.ofReal ‖A.E ξh.1 κ‖ := by
          refine ENNReal.tsum_le_tsum fun κ => ?_
          refine (lintegral_gIHMD_le A D hfilt hind hD μ hμ ξh κ).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
      _ = ENNReal.ofReal ‖A.constWH ξh‖ * ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.E ξh.1 κ‖ :=
          ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact A.toAsmCtx.tsum_bondProd_le ξh.1
  refine ne_top_of_le_ne_top ?_ h1
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ?_ A.tsum_constWH_le) (by simp [hN])
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ?_ A.toAsmCtx.tsum_constW_le)
    (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top A.toAsmCtx.mass_ne_top (by simp))

end Generic

/-! ## One assembled mode on `Dom ∩ pinSet fix` is a pinned spliced kernel -/

section Pinned

variable (fix : GBranch S.tree → Option ℝ) (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ))
  (ind : (GNode S.tree → Mom d) → ℝ) (lb : GBranch S.tree → Option ℝ) (Dom : Set (GBranch S.tree → ℝ))
  (hsliceD : ∀ τ : {b : GBranch S.tree // fix b = none} → ℝ,
    S.extendFix fix τ ∈ Dom ↔ S.extendFix fix τ ∈ splicedTimeDomainFix S A.layer0 A.tt fix ∩ splicedLBDomain lb)

include hsliceD in
open scoped Classical in
/-- `EngInt.tsum_int_gIHM` on `Dom ∩ pinSet fix`: summed over the decorations and integrated against
`fixMeasure fix`, the summand of one assembled mode is `constWH ξh · K^{MK}_{G_sb}(DHMK ξh)`. -/
theorem tsum_int_gIHMD (ξh : A.Xi) :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order *
        ∑' κ : GenDecoration S d A.roots 0, ∫ τ, gIHMD A (Dom ∩ pinSet fix) filt ind ξh κ τ ∂(fixMeasure fix) =
      A.constWH ξh * splicedKernelMK S (DHMK A fix filt ind ξh lb) A.L A.γ A.η A.δ A.base A.roots := by
  have key : ∀ κ : GenDecoration S d A.roots 0,
      ∫ τ, gIHMD A (Dom ∩ pinSet fix) filt ind ξh κ τ ∂(fixMeasure fix) =
      A.constWH ξh *
        ((DHMK A fix filt ind ξh lb).atomW (cosetDecoration S A.L A.base κ.1) *
          (splicedEpsilon S (DHMK A fix filt ind ξh lb).hinges κ.1 : ℂ) *
          (splicedGapIndicator S (DHMK A fix filt ind ξh lb).toSplicedKernelData A.L A.γ A.η A.base κ.1 : ℂ) *
          (∏ x ∈ S.molecule.bonds, (DHMK A fix filt ind ξh lb).edgeAmplitude x
            (A.base + latticePoint A.L (bondIndex S κ.1 x))) *
          (DHMK A fix filt ind ξh lb).hingeAmplitude (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) *
          splicedTimeIntegralMK S (DHMK A fix filt ind ξh lb) A.L A.γ A.δ A.base κ.1) := by
    intro κ
    unfold gIHMD gIHD
    rw [integral_const_mul, integral_const_mul]
    have hgap : splicedGapIndicator S (DHMK A fix filt ind ξh lb).toSplicedKernelData A.L A.γ A.η A.base κ.1 =
        if A.selSk κ then 1 else 0 := A.hgs (A.DH ξh) rfl κ
    rw [hgap]
    have hI : ∫ a, (Dom ∩ pinSet fix).indicator (fun τ =>
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.timeFacH ξh τ) a ∂(fixMeasure fix) =
        splicedTimeIntegralMK S (DHMK A fix filt ind ξh lb) A.L A.γ A.δ A.base κ.1 :=
      integral_fixMeasure_indicatorD S (DHMK A fix filt ind ξh lb) A.L A.γ A.δ A.base κ.1 Dom hsliceD
    have hE : A.E ξh.1 κ = ∏ x ∈ S.molecule.bonds, (DHMK A fix filt ind ξh lb).edgeAmplitude x
        (A.base + latticePoint A.L (bondIndex S κ.1 x)) := rfl
    have hh : (DHMK A fix filt ind ξh lb).hingeAmplitude (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) =
        A.hingeAmp ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) := rfl
    have hhin : (DHMK A fix filt ind ξh lb).hinges = A.hinges := rfl
    have haw : (DHMK A fix filt ind ξh lb).atomW (cosetDecoration S A.L A.base κ.1) =
        atomWF filt ind (cosetDecoration S A.L A.base κ.1) := rfl
    rw [hI, hE, hh, hhin, haw]
    by_cases hsel : A.selSk κ
    · simp only [hsel, ite_true, Complex.ofReal_one]
      ring
    · simp only [hsel, ite_false, Complex.ofReal_zero]
      simp
  unfold splicedKernelMK
  simp_rw [key]
  rw [tsum_mul_left]
  ring

variable {filt ind}

include hsliceD in
open scoped Classical in
/-- `EngInt.value_eqHM` on a general time domain `Dom`: the outer form on `Dom` against `fixMeasure fix` with the atom
weight is `Σ_{ξh} (ζ(G_sb) · constWH ξh) · K^{MK}_{G_sb}(DHMK ξh)`, given the slot boxes and the hinge HasSum on
`Dom ∩ pinSet fix`. -/
theorem value_eqHMD (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1)
    (hD : MeasurableSet Dom) (hμ : fixMeasure fix Dom ≤ 1)
    (hboxD : ∀ τ ∈ Dom ∩ pinSet fix, ∀ s, slotTs A.hS A.tt τ s ∈ A.Box s)
    (hHkD : ∀ κ : GenDecoration S d A.roots 0, A.selSk κ → ∀ τ ∈ Dom ∩ pinSet fix, ∀ j c,
      (∀ i, ‖(A.base + latticePoint A.L (κ.1 (A.hmom j i))) - latPt d (c i)‖ ≤ 1) →
      HasSum (fun l => (A.H.w j c l : ℂ) * A.H.a j c l (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i))) *
        fsPhase (A.H.m j c l) (fun i => clockOf S A.tt τ (A.hclk j i)))
        (A.Hk j (fun i => clockOf S A.tt τ (A.hclk j i))
          (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i))))) :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
      ∑' κ : GenDecoration S d A.roots 0, atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
          ∫ τ, Dom.indicator (fun τ =>
            phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure fix)) =
      ∑' ξh : A.Xi, (S.zeta * A.constWH ξh) *
        splicedKernelMK S (DHMK A fix filt ind ξh lb) A.L A.γ A.η A.δ A.base A.roots := by
  have hDP : MeasurableSet (Dom ∩ pinSet fix) := hD.inter (measurableSet_pinSet fix)
  have hμP : fixMeasure fix (Dom ∩ pinSet fix) ≤ 1 := (measure_mono inter_subset_left).trans hμ
  have h1 : ∀ κ : GenDecoration S d A.roots 0, atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
      ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        ∫ τ, Dom.indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
          ∂(fixMeasure fix)) =
      ∫ τ, ∑' ξh, gIHMD A (Dom ∩ pinSet fix) filt ind ξh κ τ ∂(fixMeasure fix) := by
    intro κ
    rw [← integral_fixMeasure_inter_pinSet fix Dom, ← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ =>
      ((hasSum_gIHMD A (Dom ∩ pinSet fix) filt ind hboxD hHkD κ τ).tsum_eq).symm)
  simp_rw [h1]
  have hswap := (sum_integral_sum_swap (fixMeasure fix) (gIHMD A (Dom ∩ pinSet fix) filt ind)
    (meas_gIHMD A (Dom ∩ pinSet fix) filt ind hDP (fixMeasure fix))
    (sum_lintegral_gIHMD_ne_top A (Dom ∩ pinSet fix) hfilt hind hDP (fixMeasure fix) hμP)).1
  rw [hswap]
  calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
        ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0,
          ∫ τ, gIHMD A (Dom ∩ pinSet fix) filt ind ξh κ τ ∂(fixMeasure fix)
      = ∑' ξh : A.Xi, (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
          ∑' κ : GenDecoration S d A.roots 0,
            ∫ τ, gIHMD A (Dom ∩ pinSet fix) filt ind ξh κ τ ∂(fixMeasure fix) := by
        rw [tsum_mul_left]
    _ = _ := by
      refine tsum_congr fun ξh => ?_
      have := tsum_int_gIHMD A fix filt ind lb Dom hsliceD ξh
      calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
            ∑' κ : GenDecoration S d A.roots 0,
              ∫ τ, gIHMD A (Dom ∩ pinSet fix) filt ind ξh κ τ ∂(fixMeasure fix)
          = S.zeta * ((coupling d A.L A.γ A.δ : ℂ) ^ S.order *
            ∑' κ : GenDecoration S d A.roots 0,
              ∫ τ, gIHMD A (Dom ∩ pinSet fix) filt ind ξh κ τ ∂(fixMeasure fix)) := by ring
        _ = _ := by rw [this]; ring

end Pinned

end WaveTurbulence.Flower.MkSlotsB
