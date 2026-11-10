/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelRep
public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFixD

/-! # B3s-HELPER4 (δ) S1 (2): the assembled expansion on a general time domain

B3s's pinned engine (`MkSlots/EngInt.lean`) integrates main's assembled summand `AsmCtxH.gIH` against `fixMeasure fix`;
`gIH`, the hinge hypothesis `AsmCtxH.hHk` and the box hypothesis `AsmCtx.hbox` all carry main's UNPINNED spliced
domain. On pieces with adjacent pins (milestone β) that domain is empty on the pinned slice, so here the summand is
taken over an arbitrary domain `Dom` (`gIHD`), with the box and hinge hypotheses on `Dom` as explicit arguments.

The domain-free parts of an `AsmCtxH` (`constWH`, `E`, `hingeAmp`, `freqH`, `timeFacH`, `skel`, `hk`,
`slotTerm_mul_hingeTerm`, the mass lemmas) are reused unchanged; the integration domain is
`domFix G layer rt fix lb := (splicedTimeDomainFix G layer rt fix ∩ splicedLBDomain lb) ∩ pinSlice fix` (the kernel
domain `fixLB` of `splicedTimeIntegralMK` with the lower bounds of ruling R187, on the pinned slice; measurable,
`fixMeasure`-mass `≤ 1`).
A context with the layer `dummyLayer` has an empty unpinned domain (if `G_sb` has a branch), so its own `hHk` field
is vacuous (`splicedTimeDomain_dummyLayer_sub`).

* slice: `pinSlice`, `fixLB`, `domFix`, `measurableSet_domFix`, `splicedKernelMK_congr_dataL`, `fixMeasure_domFix_le`, `integral_indicator_congr_slice`,
  `extendFix_mem_domFix_iff`, `mem_of_mem_domFix`, `dummyLayer`, `splicedTimeDomain_dummyLayer_sub`;
* `gIHD`, `hasSum_gIHD`, `norm_gIHD_le` (copies of main RepH8 `hasSum_gIH`, RepH9 `norm_gIH_le` with `Dom`);
* `gIHMD` (with the atom weight), `meas_gIHMD`, `lintegral_gIHMD_le`, `sum_lintegral_gIHMD_ne_top` (copies of B3s's
  EngInt lemmas with `Dom`);
* `DHMKD` (the kernel data at the real layer `lay`), `tsum_int_gIHMD`, `value_eqHMD` (copies of B3s's
  `tsum_int_gIHM`, `value_eqHM` at `Dom = domFix S lay A.tt fix lb`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsS

variable {w d : ℕ}

/-! ## The pinned slice and the integration domain -/

/-- The pinned slice: time vectors agreeing with the pins. -/
def pinSlice {ι : Type*} (fix : ι → Option ℝ) : Set (ι → ℝ) := {τ | ∀ i x, fix i = some x → τ i = x}

theorem extendFixI_mem_pinSlice {ι : Type*} (fix : ι → Option ℝ) (τ : {i // fix i = none} → ℝ) :
    extendFixI fix τ ∈ pinSlice fix := fun _ _ h => extendFixI_some fix τ h

theorem extendFixI_restrict {ι : Type*} (fix : ι → Option ℝ) (τ : ι → ℝ) (h : τ ∈ pinSlice fix) :
    extendFixI fix (fun i => τ i.1) = τ := by
  funext i
  rcases hfi : fix i with _ | x
  · rw [extendFixI_none fix _ hfi]
  · rw [extendFixI_some fix _ hfi, h i x hfi]

theorem measurableSet_pinSlice {ι : Type*} [Fintype ι] (fix : ι → Option ℝ) : MeasurableSet (pinSlice fix) := by
  have h : pinSlice fix = ⋂ i, {τ : ι → ℝ | ∀ x, fix i = some x → τ i = x} := by
    ext τ; simp [pinSlice]
  rw [h]
  refine MeasurableSet.iInter fun i => ?_
  rcases hfi : fix i with _ | x
  · simp
  · have : {τ : ι → ℝ | ∀ y, some x = some y → τ i = y} = {τ : ι → ℝ | τ i = x} := by
      ext τ
      simp only [mem_setOf_eq, Option.some.injEq]
      exact ⟨fun h => h x rfl, fun h y hy => hy ▸ h⟩
    rw [this]
    exact measurableSet_eq_fun (measurable_pi_apply i) measurable_const

/-- The time domain of `splicedTimeIntegralMK` (ruling R187): the pinned spliced domain with the constant lower bounds
`lb`. -/
def fixLB (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (lb : GBranch G.tree → Option ℝ) : Set (GBranch G.tree → ℝ) :=
  splicedTimeDomainFix G layer rt fix ∩ splicedLBDomain lb

/-- The integration domain: the domain of the kernel (`fixLB`) on the pinned slice. -/
def domFix (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (lb : GBranch G.tree → Option ℝ) : Set (GBranch G.tree → ℝ) :=
  fixLB G layer rt fix lb ∩ pinSlice fix

theorem measurableSet_splicedLBDomain {G : Garden w} (lb : GBranch G.tree → Option ℝ) :
    MeasurableSet (splicedLBDomain lb) := by
  have h : splicedLBDomain lb = ⋂ v, {τ : GBranch G.tree → ℝ | ∀ x, lb v = some x → x < τ v} := by
    ext τ; simp [splicedLBDomain]
  rw [h]
  refine MeasurableSet.iInter fun v => ?_
  rcases hv : lb v with _ | x
  · simp
  · have : {τ : GBranch G.tree → ℝ | ∀ y, some x = some y → y < τ v} = {τ : GBranch G.tree → ℝ | x < τ v} := by
      ext τ
      simp only [mem_setOf_eq, Option.some.injEq]
      exact ⟨fun h => h x rfl, fun h y hy => hy ▸ h⟩
    rw [this]
    exact measurableSet_lt measurable_const (measurable_pi_apply v)

theorem measurableSet_domFix (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (lb : GBranch G.tree → Option ℝ) :
    MeasurableSet (domFix G layer rt fix lb) :=
  ((WaveTurbulence.FlowerP5.measurableSet_splicedTimeDomainFix G layer rt fix).inter
    (measurableSet_splicedLBDomain lb)).inter (measurableSet_pinSlice fix)

/-- The pinned measure of the integration domain is at most `1`. -/
theorem fixMeasure_domFix_le (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (lb : GBranch G.tree → Option ℝ) :
    fixMeasure fix (domFix G layer rt fix lb) ≤ 1 := by
  have hsub : domFix G layer rt fix lb ⊆ Set.pi Set.univ (fun v : GBranch G.tree =>
      {x : ℝ | fix v = none → x ∈ Set.Icc (layer v : ℝ) (layer v + 1)}) := by
    intro t ht v _ hv
    exact (ht.1.1.1 v hv).1
  refine (measure_mono hsub).trans ?_
  rw [fixMeasure, Measure.pi_pi]
  refine Finset.prod_le_one fun v _ => ?_
  rcases hfv : fix v with _ | x
  · have : {x : ℝ | (none : Option ℝ) = none → x ∈ Set.Icc (layer v : ℝ) (layer v + 1)} =
        Set.Icc (layer v : ℝ) (layer v + 1) := by ext x; simp
    rw [this]
    simp [fixFactor, Real.volume_Icc]
  · simp only [fixFactor, Option.elim]
    exact prob_le_one

theorem extendFix_mem_pinSlice (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : G.extendFix fix τ ∈ pinSlice fix := by
  rw [extendFix_eq_extendFixI_fun G fix]
  exact extendFixI_mem_pinSlice fix τ

theorem extendFix_mem_domFix_iff (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (lb : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) :
    G.extendFix fix τ ∈ domFix G layer rt fix lb ↔ G.extendFix fix τ ∈ fixLB G layer rt fix lb :=
  ⟨fun h => h.1, fun h => ⟨h, extendFix_mem_pinSlice G fix τ⟩⟩

/-- A point of the integration domain lies in every domain that agrees with the kernel domain on the slice. -/
theorem mem_of_mem_domFix (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (lb : GBranch G.tree → Option ℝ) (Dom : Set (GBranch G.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch G.tree // fix b = none} → ℝ,
      G.extendFix fix τ ∈ Dom ↔ G.extendFix fix τ ∈ fixLB G layer rt fix lb)
    {τ : GBranch G.tree → ℝ} (hτ : τ ∈ domFix G layer rt fix lb) : τ ∈ Dom := by
  have he : G.extendFix fix (fun i => τ i.1) = τ := by
    rw [extendFix_eq_extendFixI_fun G fix]
    exact extendFixI_restrict fix τ hτ.2
  have h1 : G.extendFix fix (fun i => τ i.1) ∈ fixLB G layer rt fix lb := by
    rw [he]; exact hτ.1
  have := (hsliceD (fun i => τ i.1)).2 h1
  rwa [he] at this

/-- Two domains agreeing on the pinned slice have the same `fixMeasure` integrals. -/
theorem integral_indicator_congr_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Garden w)
    (fix : GBranch G.tree → Option ℝ) (D D' : Set (GBranch G.tree → ℝ))
    (h : ∀ τ : {b : GBranch G.tree // fix b = none} → ℝ, G.extendFix fix τ ∈ D ↔ G.extendFix fix τ ∈ D')
    (f : (GBranch G.tree → ℝ) → E) :
    ∫ τ, D.indicator f τ ∂(fixMeasure fix) = ∫ τ, D'.indicator f τ ∂(fixMeasure fix) := by
  rw [integral_fixMeasure, integral_fixMeasure]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  rw [← extendFix_eq_extendFixI_fun G fix]
  by_cases hτ : G.extendFix fix τ ∈ D
  · rw [indicator_of_mem hτ, indicator_of_mem ((h τ).1 hτ)]
  · rw [indicator_of_notMem hτ, indicator_of_notMem (fun h' => hτ ((h τ).2 h'))]

/-- The `fixMeasure` integral over the integration domain is the integral over the free times of the kernel domain. -/
theorem integral_domFix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Garden w)
    (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (lb : GBranch G.tree → Option ℝ) (f : (GBranch G.tree → ℝ) → E) :
    ∫ τ, (domFix G layer rt fix lb).indicator f τ ∂(fixMeasure fix) =
      ∫ τ : {b : GBranch G.tree // fix b = none} → ℝ,
        (fixLB G layer rt fix lb).indicator f (G.extendFix fix τ) := by
  rw [integral_fixMeasure]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  rw [← extendFix_eq_extendFixI_fun G fix]
  by_cases hτ : G.extendFix fix τ ∈ fixLB G layer rt fix lb
  · rw [indicator_of_mem hτ, indicator_of_mem ((extendFix_mem_domFix_iff G layer rt fix lb τ).2 hτ)]
  · rw [indicator_of_notMem hτ,
      indicator_of_notMem (fun h' => hτ ((extendFix_mem_domFix_iff G layer rt fix lb τ).1 h'))]

/-- A layer making the unpinned spliced domain empty (`⌈tt⌉ ≤ τ_v < tt`). -/
def dummyLayer (G : Garden w) (tt : Fin w → ℝ) : GBranch G.tree → ℕ := fun v => ⌈tt v.1.1⌉₊

theorem not_mem_splicedTimeDomain_dummyLayer (G : Garden w) (tt : Fin w → ℝ) (v : GBranch G.tree)
    (τ : GBranch G.tree → ℝ) : τ ∉ splicedTimeDomain G (dummyLayer G tt) tt := by
  intro h
  have h1 := (h.1 v).1
  have h2 := h.2.2 v
  have h3 := Nat.le_ceil (tt v.1.1)
  simp only [dummyLayer] at h1
  linarith

theorem mem_domFix_of_isEmpty (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (lb : GBranch G.tree → Option ℝ) (hE : IsEmpty (GBranch G.tree))
    (τ : GBranch G.tree → ℝ) : τ ∈ domFix G layer rt fix lb :=
  ⟨⟨⟨fun v => isEmptyElim v, fun v => isEmptyElim v⟩, fun v => isEmptyElim v⟩, fun v => isEmptyElim v⟩

/-- The unpinned domain of the dummy layer lies in every integration domain. -/
theorem splicedTimeDomain_dummyLayer_sub (G : Garden w) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ)
    (fix : GBranch G.tree → Option ℝ) (lb : GBranch G.tree → Option ℝ) :
    splicedTimeDomain G (dummyLayer G tt) tt ⊆ domFix G layer tt fix lb := by
  intro τ hτ
  by_cases hne : Nonempty (GBranch G.tree)
  · obtain ⟨v⟩ := hne
    exact absurd hτ (not_mem_splicedTimeDomain_dummyLayer G tt v τ)
  · exact mem_domFix_of_isEmpty G layer tt fix lb (not_nonempty_iff.mp hne) τ

/-- The pinned spliced kernel depends on the data only through the layers, hinges, edge amplitudes, gap specification,
frequencies, root times, pins, filters, indicator, lower bounds and the values of the hinge amplitude at bond momenta
(B3s's `MkSlots.splicedKernelMK_congr_data` with the lower bounds of ruling R187). -/
theorem splicedKernelMK_congr_dataL {d : ℕ} (G : Garden w) (D D' : SplicedKernelDataMK G d) (L γ η δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (hl : D.layer = D'.layer) (hh : D.hinges = D'.hinges)
    (he : D.edgeAmplitude = D'.edgeAmplitude) (hg : D.gapSpecification = D'.gapSpecification)
    (hf : D.frequency = D'.frequency) (hr : D.rootTime = D'.rootTime) (hfix : D.fix = D'.fix)
    (hfilt : D.filt = D'.filt) (hind : D.ind = D'.ind) (hlb : D.lb = D'.lb)
    (hha : ∀ k : GardenDart G → Mom d, D.hingeAmplitude (fun x => k x.1) = D'.hingeAmplitude (fun x => k x.1)) :
    splicedKernelMK G D L γ η δ base roots = splicedKernelMK G D' L γ η δ base roots := by
  unfold splicedKernelMK
  congr 1
  refine tsum_congr fun z => ?_
  have h0 : D.atomW (cosetDecoration G L base z.1) = D'.atomW (cosetDecoration G L base z.1) := by
    unfold SplicedKernelDataMK.atomW; rw [hfilt, hind]
  have h1 : splicedGapIndicator G D.toSplicedKernelData L γ η base z.1 =
      splicedGapIndicator G D'.toSplicedKernelData L γ η base z.1 := by
    unfold splicedGapIndicator; rw [hg]
  have h2 : splicedTimeIntegralMK G D L γ δ base z.1 = splicedTimeIntegralMK G D' L γ δ base z.1 := by
    unfold splicedTimeIntegralMK; rw [hl, hf, hr, hfix, hlb]
  have h3 : splicedEpsilon G D.hinges z.1 = splicedEpsilon G D'.hinges z.1 := by rw [hh]
  have h4 := hha (fun x => base + latticePoint L (bondIndex G z.1 x))
  rw [h0, h1, h2, h3, he]
  exact congrArg (fun c => _ * c * _) h4

/-! ## The assembled summand on a domain -/

section Dom

variable {S : Garden w} (A : AsmCtxH S d)

open scoped Classical in
/-- Main's assembled summand `AsmCtxH.gIH` with the unpinned spliced domain replaced by `Dom`. -/
def gIHD (Dom : Set (GBranch S.tree → ℝ)) (ξh : A.Xi) (κ : GenDecoration S d A.roots 0)
    (τ : GBranch S.tree → ℝ) : ℂ :=
  (if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
    (A.constWH ξh * A.E ξh.1 κ * A.hingeAmp ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1))) *
    Dom.indicator (fun τ =>
      phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.timeFacH ξh τ) τ

/-- The hinge hypothesis of an assembly context on a domain `Dom` (`AsmCtxH.hHk` with `Dom`). -/
def HkOn (Dom : Set (GBranch S.tree → ℝ)) : Prop :=
  ∀ κ : GenDecoration S d A.roots 0, A.selSk κ → ∀ τ ∈ Dom, ∀ j c,
    (∀ i, ‖(A.base + latticePoint A.L (κ.1 (A.hmom j i))) - latPt d (c i)‖ ≤ 1) →
    HasSum (fun l => (A.H.w j c l : ℂ) * A.H.a j c l (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i))) *
      fsPhase (A.H.m j c l) (fun i => clockOf S A.tt τ (A.hclk j i)))
      (A.Hk j (fun i => clockOf S A.tt τ (A.hclk j i)) (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i))))

/-- Main's RepH9 `norm_gIH_le` on a domain `Dom`. -/
theorem norm_gIHD_le (Dom : Set (GBranch S.tree → ℝ)) (ξh : A.Xi) (κ : GenDecoration S d A.roots 0)
    (τ : GBranch S.tree → ℝ) :
    ‖gIHD A Dom ξh κ τ‖ ≤ Dom.indicator (fun _ => ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) τ := by
  classical
  unfold gIHD
  by_cases hτ : τ ∈ Dom
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

/-- The summand on `Dom` with the atom weight of the decoration. -/
def gIHMD (Dom : Set (GBranch S.tree → ℝ)) (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode S.tree → Mom d) → ℝ) (ξh : A.Xi) (κ : GenDecoration S d A.roots 0)
    (τ : GBranch S.tree → ℝ) : ℂ :=
  atomWF filt ind (cosetDecoration S A.L A.base κ.1) * gIHD A Dom ξh κ τ

section Generic

variable (Dom : Set (GBranch S.tree → ℝ)) (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ))
  (ind : (GNode S.tree → Mom d) → ℝ)

theorem meas_gIHD (hDom : MeasurableSet Dom) (μ : Measure (GBranch S.tree → ℝ)) (ξh : A.Xi)
    (κ : GenDecoration S d A.roots 0) : AEStronglyMeasurable (gIHD A Dom ξh κ) μ := by
  classical
  unfold gIHD
  refine aestronglyMeasurable_const.mul ?_
  refine (Continuous.aestronglyMeasurable ?_).indicator hDom
  exact (Represents.continuous_phaseProd _ _ _ _).mul (A.continuous_timeFacH ξh)

theorem meas_gIHMD (hDom : MeasurableSet Dom) (μ : Measure (GBranch S.tree → ℝ)) (ξh : A.Xi)
    (κ : GenDecoration S d A.roots 0) : AEStronglyMeasurable (gIHMD A Dom filt ind ξh κ) μ :=
  aestronglyMeasurable_const.mul (meas_gIHD A Dom hDom μ ξh κ)

variable {filt ind} (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1)
include hfilt hind

theorem norm_gIHMD_le (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    ‖gIHMD A Dom filt ind ξh κ τ‖ ≤ Dom.indicator (fun _ => ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) τ := by
  unfold gIHMD
  rw [norm_mul]
  calc _ ≤ 1 * ‖gIHD A Dom ξh κ τ‖ :=
        mul_le_mul_of_nonneg_right (norm_atomWF_le filt ind hfilt hind _) (norm_nonneg _)
    _ = ‖gIHD A Dom ξh κ τ‖ := one_mul _
    _ ≤ _ := norm_gIHD_le A Dom ξh κ τ

theorem lintegral_gIHMD_le (hDom : MeasurableSet Dom) (μ : Measure (GBranch S.tree → ℝ)) (hμ : μ Dom ≤ 1)
    (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) :
    ∫⁻ τ, ‖gIHMD A Dom filt ind ξh κ τ‖ₑ ∂μ ≤ ENNReal.ofReal (‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) := by
  set c : ℝ := ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖ with hc
  calc ∫⁻ τ, ‖gIHMD A Dom filt ind ξh κ τ‖ₑ ∂μ
      ≤ ∫⁻ τ, Dom.indicator (fun _ => ENNReal.ofReal c) τ ∂μ := by
        refine lintegral_mono fun τ => ?_
        have := norm_gIHMD_le A Dom hfilt hind ξh κ τ
        by_cases hτ : τ ∈ Dom
        · simp only [Set.indicator_of_mem hτ] at this ⊢
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal this
        · simp only [Set.indicator_of_notMem hτ] at this ⊢
          have h0 : gIHMD A Dom filt ind ξh κ τ = 0 := norm_le_zero_iff.1 this
          rw [h0]; simp
    _ = ENNReal.ofReal c * μ Dom := lintegral_indicator_const hDom _
    _ ≤ ENNReal.ofReal c * 1 := by gcongr
    _ = _ := mul_one _

open scoped Classical in
theorem sum_lintegral_gIHMD_ne_top (hDom : MeasurableSet Dom) (μ : Measure (GBranch S.tree → ℝ))
    (hμ : μ Dom ≤ 1) :
    ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHMD A Dom filt ind ξh κ τ‖ₑ ∂μ ≠ ⊤ := by
  set N : ℝ≥0∞ := ((((⌊2 * A.L⌋₊ + 2) ^ d) ^ Fintype.card (Reg.Skeleton.SourcePair S) : ℕ) : ℝ≥0∞) with hN
  have h1 : ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHMD A Dom filt ind ξh κ τ‖ₑ ∂μ ≤
      ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ * N := by
    refine ENNReal.tsum_le_tsum fun ξh => ?_
    calc ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHMD A Dom filt ind ξh κ τ‖ₑ ∂μ
        ≤ ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.constWH ξh‖ * ENNReal.ofReal ‖A.E ξh.1 κ‖ := by
          refine ENNReal.tsum_le_tsum fun κ => ?_
          refine (lintegral_gIHMD_le A Dom hfilt hind hDom μ hμ ξh κ).trans (le_of_eq ?_)
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

/-! ## One assembled mode is a pinned spliced kernel (at the real layer) -/

section Pinned

variable (lay : GBranch S.tree → ℕ) (fix : GBranch S.tree → Option ℝ)
  (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ)) (ind : (GNode S.tree → Mom d) → ℝ)
  (lb : GBranch S.tree → Option ℝ)

/-- The kernel data of the assembled mode `ξh` at the layer `lay`, with pins, filters, indicator and lower bounds. -/
def DHMKD (ξh : A.Xi) : SplicedKernelDataMK S d where
  toSplicedKernelData := { A.DH ξh with layer := lay }
  fix := fix
  filt := filt
  ind := ind
  lb := lb

open scoped Classical in
/-- B3s's `tsum_int_gIHM` on the integration domain `domFix S lay A.tt fix lb`. -/
theorem tsum_int_gIHMD (ξh : A.Xi) :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order *
        ∑' κ : GenDecoration S d A.roots 0,
          ∫ τ, gIHMD A (domFix S lay A.tt fix lb) filt ind ξh κ τ ∂(fixMeasure fix) =
      A.constWH ξh * splicedKernelMK S (DHMKD A lay fix filt ind lb ξh) A.L A.γ A.η A.δ A.base A.roots := by
  have key : ∀ κ : GenDecoration S d A.roots 0,
      ∫ τ, gIHMD A (domFix S lay A.tt fix lb) filt ind ξh κ τ ∂(fixMeasure fix) =
      A.constWH ξh *
        ((DHMKD A lay fix filt ind lb ξh).atomW (cosetDecoration S A.L A.base κ.1) *
          (splicedEpsilon S (DHMKD A lay fix filt ind lb ξh).hinges κ.1 : ℂ) *
          (splicedGapIndicator S (DHMKD A lay fix filt ind lb ξh).toSplicedKernelData A.L A.γ A.η A.base κ.1 : ℂ) *
          (∏ x ∈ S.molecule.bonds, (DHMKD A lay fix filt ind lb ξh).edgeAmplitude x
            (A.base + latticePoint A.L (bondIndex S κ.1 x))) *
          (DHMKD A lay fix filt ind lb ξh).hingeAmplitude
            (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) *
          splicedTimeIntegralMK S (DHMKD A lay fix filt ind lb ξh) A.L A.γ A.δ A.base κ.1) := by
    intro κ
    unfold gIHMD gIHD
    rw [integral_const_mul, integral_const_mul]
    have hgap : splicedGapIndicator S (DHMKD A lay fix filt ind lb ξh).toSplicedKernelData A.L A.γ A.η A.base κ.1 =
        if A.selSk κ then 1 else 0 := A.hgs _ rfl κ
    rw [hgap]
    have hI : ∫ a, (domFix S lay A.tt fix lb).indicator (fun τ =>
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.timeFacH ξh τ) a ∂(fixMeasure fix) =
        splicedTimeIntegralMK S (DHMKD A lay fix filt ind lb ξh) A.L A.γ A.δ A.base κ.1 := by
      rw [integral_domFix]
      rfl
    have hE : A.E ξh.1 κ = ∏ x ∈ S.molecule.bonds, (DHMKD A lay fix filt ind lb ξh).edgeAmplitude x
        (A.base + latticePoint A.L (bondIndex S κ.1 x)) := rfl
    have hh : (DHMKD A lay fix filt ind lb ξh).hingeAmplitude
        (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) =
        A.hingeAmp ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) := rfl
    have hhin : (DHMKD A lay fix filt ind lb ξh).hinges = A.hinges := rfl
    have haw : (DHMKD A lay fix filt ind lb ξh).atomW (cosetDecoration S A.L A.base κ.1) =
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

end Pinned

end Dom

end WaveTurbulence.Flower.MkSlotsS
