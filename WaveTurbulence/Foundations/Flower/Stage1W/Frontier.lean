/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1W.Defs
public import WaveTurbulence.Foundations.Flower.Stage1W.Bridge

/-! # STAGE1W-GLUE: Frontier (ported by source from the S-STAGE1W probe, see COPIED-SHA256SUMS). -/


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-! ## 6. Frontier placement: PLAN's `frontierW` is the `topPsi` node product of the frontier cutoffs -/

/-- PLAN §2.2 `frontierW` (verbatim from leanplan/probe/PlanProbe.lean). -/
def frontierW {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (Rf : Fin w → Option ℝ)
    (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ a : GNode LG.garden.tree,
    if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬ LG.IsFlowerNode a then
      (Rf a.1.1).elim 1 fun r => chi0 (‖k a‖ / r) else 1

/-- The per-tree frontier cutoff as a `topPsi` weight: `chi0 (‖x‖ / r)` at scale `some r`, `1` for `none`. -/
def frontierG {d : ℕ} (o : Option ℝ) : Mom d → ℂ :=
  fun x => (((o.elim 1 fun r => chi0 (‖x‖ / r)) : ℝ) : ℂ)

theorem frontierG_im {d : ℕ} (o : Option ℝ) (x : Mom d) : (frontierG o x).im = 0 := by
  simp [frontierG]

/-- **Placement bridge** (probe proof): on gardens with no flower node below layer `p` (capped gardens), the frontier
weight of the cores is the `topPsi` node product of `frontierG ∘ Rf`. -/
theorem frontierW_eq_nodeLabelProduct {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (Rf : Fin w → Option ℝ)
    (k : GNode LG.garden.tree → Mom d) (hfl : ∀ a, LG.IsFlowerNode a → ¬ LG.layer a < p) :
    ((frontierW LG p Rf k : ℝ) : ℂ) = nodeLabelProduct (fun j => topPsi p (frontierG (Rf j))) LG p k := by
  unfold frontierW nodeLabelProduct
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases hroot : a.1.2 = []
  · have hnt : ¬ LG.IsTopLeaf p a := fun h => h.2.1 hroot
    simp [hroot, hnt]
  · by_cases hlay : LG.layer a < p
    · by_cases hpar : LG.parentLayer p a = p
      · have hnf : ¬ LG.IsFlowerNode a := fun h => hfl a h hlay
        have ht : LG.IsTopLeaf p a := ⟨Or.inl hlay, hroot, hpar⟩
        simp [hroot, ht, hlay, hnf, topPsi, hpar, frontierG]
      · have hnt : ¬ LG.IsTopLeaf p a := fun h => hpar h.2.2
        simp [hroot, hnt, topPsi, hpar]
    · simp [hroot, hlay, topPsi]

/-! ## 7. `GPresented` instantiated by `FC23.bondMeasure` -/

open scoped FourierTransform in
/-- The frontier presentation constant: the `32 d`-th moment of the Fourier density of the fixed radial cutoff
(`FC23.radialSchwartz`), at least `1`.  Depends on `d` only. -/
def frontierConst (d : ℕ) : ℝ :=
  max 1 (∫ a : Mom d, (1 + ‖a‖) ^ (32 * d) * ‖𝓕 (FC23.radialSchwartz : SchwartzMap (Mom d) ℂ) a‖)

theorem one_le_frontierConst (d : ℕ) : 1 ≤ frontierConst d := le_max_left _ _

open scoped FourierTransform in
/-- **bondMeasure instantiation** (probe proof): every frontier cutoff `chi0 (‖·‖ / r)`, `r ≥ 1`, is
`GPresented (32 d)` with the constant `frontierConst d`, by the presentation `FC23.bondMeasure id 0 r`; its frequency
map `ξ ↦ r⁻¹ ξ` does not increase moments. -/
theorem gPresented_frontierCut (d : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    GPresented (32 * d) (fun x : Mom d => ((chi0 (‖x‖ / r) : ℝ) : ℂ)) (frontierConst d) := by
  set f : SchwartzMap (Mom d) ℂ := 𝓕 (FC23.radialSchwartz : SchwartzMap (Mom d) ℂ) with hf
  set J : ℕ := 32 * d with hJ
  have hpt : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ J ≤ 2 ^ J * (t ^ 0 + t ^ J) := by
    intro t ht
    rcases le_total t 1 with h1 | h1
    · calc (1 + t) ^ J ≤ 2 ^ J := pow_le_pow_left₀ (by linarith) (by linarith) J
        _ ≤ 2 ^ J * (t ^ 0 + t ^ J) := by
          have : (0 : ℝ) ≤ t ^ J := pow_nonneg ht J
          have h2 : (0 : ℝ) ≤ 2 ^ J := by positivity
          nlinarith
    · calc (1 + t) ^ J ≤ (2 * t) ^ J := pow_le_pow_left₀ (by linarith) (by linarith) J
        _ = 2 ^ J * t ^ J := mul_pow _ _ _
        _ ≤ 2 ^ J * (t ^ 0 + t ^ J) := by
          have h2 : (0 : ℝ) ≤ 2 ^ J := by positivity
          nlinarith
  have hint : Integrable (fun a : Mom d => (1 + ‖a‖) ^ J * ‖f a‖) volume := by
    have h1 := f.integrable_pow_mul volume J
    have h0 := f.integrable_pow_mul volume 0
    refine Integrable.mono' ((h0.add h1).const_mul (2 ^ J)) ?_ ?_
    · exact (((continuous_const.add continuous_norm).pow J).mul f.continuous.norm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun a => ?_
      have hn : 0 ≤ (1 + ‖a‖) ^ J * ‖f a‖ := by positivity
      rw [Real.norm_of_nonneg hn]
      have := mul_le_mul_of_nonneg_right (hpt ‖a‖ (norm_nonneg a)) (norm_nonneg (f a))
      simpa [Pi.add_apply, mul_add, add_mul, mul_assoc] using this
  have hr0 : 0 < r := by linarith
  refine ⟨Mom d, inferInstance, FC23.bondMeasure (ContinuousLinearMap.id ℝ (Mom d)) 0 r, ?_, fun x => ?_⟩
  · have hfreq : ∀ a : Mom d,
        ‖(r⁻¹ • ContinuousLinearMap.id ℝ (Mom d)).adjoint a‖ ≤ ‖a‖ := by
      intro a
      have h1 := ((r⁻¹ • ContinuousLinearMap.id ℝ (Mom d)).adjoint).le_opNorm a
      rw [LinearIsometryEquiv.norm_map] at h1
      have h2 : ‖r⁻¹ • ContinuousLinearMap.id ℝ (Mom d)‖ ≤ 1 := by
        refine (norm_smul_le (r⁻¹ : ℝ) (ContinuousLinearMap.id ℝ (Mom d))).trans ?_
        have h3 : ‖ContinuousLinearMap.id ℝ (Mom d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        have h4 : ‖r⁻¹‖ ≤ 1 := by
          rw [Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
          exact inv_le_one_of_one_le₀ hr
        calc ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Mom d)‖ ≤ 1 * 1 :=
              mul_le_mul h4 h3 (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ‖(r⁻¹ • ContinuousLinearMap.id ℝ (Mom d)).adjoint a‖
          ≤ ‖r⁻¹ • ContinuousLinearMap.id ℝ (Mom d)‖ * ‖a‖ := h1
        _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg a)
        _ = ‖a‖ := one_mul _
    calc momentMassMom J (FC23.bondMeasure (ContinuousLinearMap.id ℝ (Mom d)) 0 r)
        ≤ ∫⁻ a, ENNReal.ofReal ((1 + ‖a‖) ^ J * ‖f a‖) := by
          unfold momentMassMom
          refine lintegral_mono fun a => ?_
          simp only [FC23.bondMeasure, Cut2A.SpatialMeasure.affine, FC23.radialMeasure, id, smul_zero,
            inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
          rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
          gcongr
          exact hfreq a
      _ = ENNReal.ofReal (∫ a, (1 + ‖a‖) ^ J * ‖f a‖) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun a => by positivity)).symm
      _ ≤ ENNReal.ofReal (frontierConst d) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  · rw [FC23.frozen_bondMeasure_value _ _ hr0]
    simp

theorem gPresented_mono {d : ℕ} {J : ℕ} {g : Mom d → ℂ} {c c' : ℝ} (h : GPresented J g c) (hc : c ≤ c') :
    GPresented J g c' := by
  obtain ⟨α, hα, M, hM, hv⟩ := h
  exact ⟨α, hα, M, hM.trans (ENNReal.ofReal_le_ofReal hc), hv⟩

/-- The whole frontier class `frontierG o` (`o = none` or a scale `≥ 1`) is presented with `frontierConst d`. -/
theorem gPresented_frontierG (d : ℕ) (o : Option ℝ) (ho : ∀ r, o = some r → 1 ≤ r) :
    GPresented (32 * d) (frontierG (d := d) o) (frontierConst d) := by
  cases o with
  | none =>
    have e : (frontierG (d := d) none) = fun _ => (1 : ℂ) := by funext x; simp [frontierG]
    rw [e]
    exact gPresented_mono (gPresented_one _) (one_le_frontierConst d)
  | some r =>
    have e : (frontierG (d := d) (some r)) = fun x : Mom d => ((chi0 (‖x‖ / r) : ℝ) : ℂ) := by
      funext x; simp [frontierG]
    rw [e]
    exact gPresented_frontierCut d r (ho r rfl)

/-! ## 8. The consumer-facing specialisation (frontier cutoffs at scales `≥ L`) -/


end WaveTurbulence.Flower.Stage1W
