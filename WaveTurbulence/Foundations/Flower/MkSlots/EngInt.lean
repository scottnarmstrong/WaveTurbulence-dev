/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.EngDefs

/-! # B3s MK-SLOTS ENGINE (2): the assembled expansion against a pinned time measure

Main's assembly context with vine factors `AsmCtxH` is reused unchanged; its summand `gIH` is a pointwise function of
the times. Here the summand is multiplied by the atom weight `atomWF filt ind` of the decoration (`gIHM`) and integrated
against a general time measure `μ` with `μ (splicedTimeDomain) ≤ 1` (copies of main's RepH9/RepH10 integral lemmas with
`μ` in place of `volume`), and against `fixMeasure fix`, where (under the slice hypothesis) one assembled mode is the
pinned spliced kernel `splicedKernelMK` of the data `DHMK` (RepH9 `tsum_int_gIH`, RepH11 `value_eqH`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkDefs
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ} {S : Garden w} (A : AsmCtxH S d)

/-- The summand of the assembled expansion with the atom weight of the decoration. -/
def gIHM (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ)) (ind : (GNode S.tree → Mom d) → ℝ)
    (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) : ℂ :=
  atomWF filt ind (cosetDecoration S A.L A.base κ.1) * A.gIH ξh κ τ

/-- The kernel data of the assembled mode `ξh` with pins, filters and indicator. -/
def DHMK (fix : GBranch S.tree → Option ℝ) (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode S.tree → Mom d) → ℝ) (ξh : A.Xi) (lb : GBranch S.tree → Option ℝ := fun _ => none) :
    SplicedKernelDataMK S d where
  toSplicedKernelData := A.DH ξh
  fix := fix
  filt := filt
  ind := ind
  lb := lb

section Generic

variable (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ)) (ind : (GNode S.tree → Mom d) → ℝ)

open scoped Classical in
theorem hasSum_gIHM (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    HasSum (fun ξh => gIHM A filt ind ξh κ τ) (atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
      ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ)) :=
  (A.hasSum_gIH κ τ).mul_left _

/-- Measurability of the summand against any time measure (RepH9 `meas_gIH`). -/
theorem meas_gIH_μ (μ : Measure (GBranch S.tree → ℝ)) (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) :
    AEStronglyMeasurable (A.gIH ξh κ) μ := by
  classical
  unfold AsmCtxH.gIH
  refine aestronglyMeasurable_const.mul ?_
  refine (Continuous.aestronglyMeasurable ?_).indicator
    (Represents.measurableSet_splicedTimeDomain S A.layer0 A.tt)
  exact (Represents.continuous_phaseProd _ _ _ _).mul (A.continuous_timeFacH ξh)

theorem meas_gIHM (μ : Measure (GBranch S.tree → ℝ)) (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) :
    AEStronglyMeasurable (gIHM A filt ind ξh κ) μ :=
  aestronglyMeasurable_const.mul (meas_gIH_μ A μ ξh κ)

variable {filt ind} (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1)
include hfilt hind

theorem norm_gIHM_le (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    ‖gIHM A filt ind ξh κ τ‖ ≤ (splicedTimeDomain S A.layer0 A.tt).indicator
      (fun _ => ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) τ := by
  unfold gIHM
  rw [norm_mul]
  calc _ ≤ 1 * ‖A.gIH ξh κ τ‖ :=
        mul_le_mul_of_nonneg_right (norm_atomWF_le filt ind hfilt hind _) (norm_nonneg _)
    _ = ‖A.gIH ξh κ τ‖ := one_mul _
    _ ≤ _ := A.norm_gIH_le ξh κ τ

/-- RepH10 `lintegral_gIH_le` against a time measure of mass `≤ 1` on the spliced domain. -/
theorem lintegral_gIHM_le (μ : Measure (GBranch S.tree → ℝ)) (hμ : μ (splicedTimeDomain S A.layer0 A.tt) ≤ 1)
    (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) :
    ∫⁻ τ, ‖gIHM A filt ind ξh κ τ‖ₑ ∂μ ≤ ENNReal.ofReal (‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) := by
  classical
  set c : ℝ := ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖ with hc
  calc ∫⁻ τ, ‖gIHM A filt ind ξh κ τ‖ₑ ∂μ
      ≤ ∫⁻ τ, (splicedTimeDomain S A.layer0 A.tt).indicator (fun _ => ENNReal.ofReal c) τ ∂μ := by
        refine lintegral_mono fun τ => ?_
        have := norm_gIHM_le A hfilt hind ξh κ τ
        by_cases hτ : τ ∈ splicedTimeDomain S A.layer0 A.tt
        · simp only [Set.indicator_of_mem hτ] at this ⊢
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal this
        · simp only [Set.indicator_of_notMem hτ] at this ⊢
          have h0 : gIHM A filt ind ξh κ τ = 0 := norm_le_zero_iff.1 this
          rw [h0]; simp
    _ = ENNReal.ofReal c * μ (splicedTimeDomain S A.layer0 A.tt) :=
        lintegral_indicator_const (Represents.measurableSet_splicedTimeDomain S A.layer0 A.tt) _
    _ ≤ ENNReal.ofReal c * 1 := by gcongr
    _ = _ := mul_one _

open scoped Classical in
/-- RepH10 `sum_lintegral_gIH_ne_top` against a time measure of mass `≤ 1` on the spliced domain. -/
theorem sum_lintegral_gIHM_ne_top (μ : Measure (GBranch S.tree → ℝ))
    (hμ : μ (splicedTimeDomain S A.layer0 A.tt) ≤ 1) :
    ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHM A filt ind ξh κ τ‖ₑ ∂μ ≠ ⊤ := by
  set N : ℝ≥0∞ := ((((⌊2 * A.L⌋₊ + 2) ^ d) ^ Fintype.card (Reg.Skeleton.SourcePair S) : ℕ) : ℝ≥0∞) with hN
  have h1 : ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHM A filt ind ξh κ τ‖ₑ ∂μ ≤
      ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ * N := by
    refine ENNReal.tsum_le_tsum fun ξh => ?_
    calc ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖gIHM A filt ind ξh κ τ‖ₑ ∂μ
        ≤ ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.constWH ξh‖ * ENNReal.ofReal ‖A.E ξh.1 κ‖ := by
          refine ENNReal.tsum_le_tsum fun κ => ?_
          refine (lintegral_gIHM_le A hfilt hind μ hμ ξh κ).trans (le_of_eq ?_)
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

/-! ## One assembled mode is a pinned spliced kernel -/

section Pinned

variable (fix : GBranch S.tree → Option ℝ) (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ))
  (ind : (GNode S.tree → Mom d) → ℝ) (lb : GBranch S.tree → Option ℝ)
  (hslice : ∀ τ : {b : GBranch S.tree // fix b = none} → ℝ,
    S.extendFix fix τ ∈ splicedTimeDomain S A.layer0 A.tt ↔
      S.extendFix fix τ ∈ splicedTimeDomainFix S A.layer0 A.tt fix ∩ splicedLBDomain lb)

include hslice in
open scoped Classical in
/-- RepH9 `tsum_int_gIH`, pinned: summed over the decorations and integrated against `fixMeasure fix`, the summand of
one assembled mode is `constWH ξh · K^{MK}_{G_sb}(DHMK ξh)`. -/
theorem tsum_int_gIHM (ξh : A.Xi) :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order *
        ∑' κ : GenDecoration S d A.roots 0, ∫ τ, gIHM A filt ind ξh κ τ ∂(fixMeasure fix) =
      A.constWH ξh * splicedKernelMK S (DHMK A fix filt ind ξh lb) A.L A.γ A.η A.δ A.base A.roots := by
  have key : ∀ κ : GenDecoration S d A.roots 0, ∫ τ, gIHM A filt ind ξh κ τ ∂(fixMeasure fix) =
      A.constWH ξh *
        ((DHMK A fix filt ind ξh lb).atomW (cosetDecoration S A.L A.base κ.1) *
          (splicedEpsilon S (DHMK A fix filt ind ξh lb).hinges κ.1 : ℂ) *
          (splicedGapIndicator S (DHMK A fix filt ind ξh lb).toSplicedKernelData A.L A.γ A.η A.base κ.1 : ℂ) *
          (∏ x ∈ S.molecule.bonds, (DHMK A fix filt ind ξh lb).edgeAmplitude x
            (A.base + latticePoint A.L (bondIndex S κ.1 x))) *
          (DHMK A fix filt ind ξh lb).hingeAmplitude (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) *
          splicedTimeIntegralMK S (DHMK A fix filt ind ξh lb) A.L A.γ A.δ A.base κ.1) := by
    intro κ
    unfold gIHM AsmCtxH.gIH
    rw [integral_const_mul, integral_const_mul]
    have hgap : splicedGapIndicator S (DHMK A fix filt ind ξh lb).toSplicedKernelData A.L A.γ A.η A.base κ.1 =
        if A.selSk κ then 1 else 0 := A.hgs (A.DH ξh) rfl κ
    rw [hgap]
    have hI : ∫ a, (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.timeFacH ξh τ) a ∂(fixMeasure fix) =
        splicedTimeIntegralMK S (DHMK A fix filt ind ξh lb) A.L A.γ A.δ A.base κ.1 :=
      integral_fixMeasure_indicator S (DHMK A fix filt ind ξh lb) A.L A.γ A.δ A.base κ.1 hslice
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

include hslice in
open scoped Classical in
/-- RepH11 `value_eqH`, pinned: the outer form against `fixMeasure fix` with the atom weight is
`Σ_{ξh} (ζ(G_sb) · constWH ξh) · K^{MK}_{G_sb}(DHMK ξh)`. -/
theorem value_eqHM (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1) :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
      ∑' κ : GenDecoration S d A.roots 0, atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
          ∫ τ, (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
            phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure fix)) =
      ∑' ξh : A.Xi, (S.zeta * A.constWH ξh) *
        splicedKernelMK S (DHMK A fix filt ind ξh lb) A.L A.γ A.η A.δ A.base A.roots := by
  have hμ := fixMeasure_splicedTimeDomain_le S A.layer0 A.tt fix
  have h1 : ∀ κ : GenDecoration S d A.roots 0, atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
      ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        ∫ τ, (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
          ∂(fixMeasure fix)) =
      ∫ τ, ∑' ξh, gIHM A filt ind ξh κ τ ∂(fixMeasure fix) := by
    intro κ
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ => ((hasSum_gIHM A filt ind κ τ).tsum_eq).symm)
  simp_rw [h1]
  have hswap := (sum_integral_sum_swap (fixMeasure fix) (gIHM A filt ind)
    (meas_gIHM A filt ind (fixMeasure fix)) (sum_lintegral_gIHM_ne_top A hfilt hind (fixMeasure fix) hμ)).1
  rw [hswap]
  calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
        ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫ τ, gIHM A filt ind ξh κ τ ∂(fixMeasure fix)
      = ∑' ξh : A.Xi, (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
          ∑' κ : GenDecoration S d A.roots 0, ∫ τ, gIHM A filt ind ξh κ τ ∂(fixMeasure fix) := by
        rw [tsum_mul_left]
    _ = _ := by
      refine tsum_congr fun ξh => ?_
      have := tsum_int_gIHM A fix filt ind lb hslice ξh
      calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
            ∑' κ : GenDecoration S d A.roots 0, ∫ τ, gIHM A filt ind ξh κ τ ∂(fixMeasure fix)
          = S.zeta * ((coupling d A.L A.γ A.δ : ℂ) ^ S.order *
            ∑' κ : GenDecoration S d A.roots 0, ∫ τ, gIHM A filt ind ξh κ τ ∂(fixMeasure fix)) := by ring
        _ = _ := by rw [this]; ring

end Pinned

end WaveTurbulence.Flower.MkSlots
