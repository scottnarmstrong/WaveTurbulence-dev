/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RDom2
public import WaveTurbulence.Foundations.Flower.MkSlots.PRedNode

/-! # B3s-HELPER3: node kernels on a general domain (relaxed PRED, part 1)

The twin of `MkSlots.PRedNode` with the time domain `kDomain LG up s` replaced by an arbitrary measurable set `Dom`
contained in the box `unitBoxR LG fix` (free branches in their open layer windows; pinned branches unconstrained,
they carry Dirac masses under `fixMeasure fix`), and with a bounded decoration weight `Θn` besides the momentum
weight `m`. Relaxed domains (`kDomainR`, `kDomainFix`) are of this kind.

* `unitBoxR`, `fixMeasure_unitBoxR_le_one`, `kDomainR_subset_unitBoxR`, `kDomainFix_subset_unitBoxR`;
* `kernelAllIntegrandD` (main's `kernelAllIntegrandN` on `Dom`; `kernelAllIntegrandD_kDomain`), integrability and the
  L¹ bound under `fixMeasure`;
* `kernelNodeWR` (the weighted node kernel on `Dom`), `kernelNodeWR_eq_tsum_integral_all`,
  `summable_integral_kernelAllIntegrandNWD_fix`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsB
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots

/-! ### The relaxed unit box -/

/-- Free branch times in the open unit window of their layer; pinned branches unconstrained. -/
def unitBoxR {w : ℕ} (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ) :
    Set (GBranch LG.garden.tree → ℝ) :=
  Set.pi Set.univ fun b => if fix b = none then Set.Ioo (LG.layer b.toNode : ℝ) (LG.layer b.toNode + 1) else Set.univ

theorem measurableSet_unitBoxR {w : ℕ} (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ) :
    MeasurableSet (unitBoxR LG fix) :=
  MeasurableSet.univ_pi fun b => by
    split_ifs
    · exact measurableSet_Ioo
    · exact MeasurableSet.univ

theorem fixMeasure_unitBoxR_le_one {w : ℕ} (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ) :
    fixMeasure fix (unitBoxR LG fix) ≤ 1 := by
  rw [unitBoxR, fixMeasure, Measure.pi_pi]
  refine Finset.prod_le_one fun b _ => ?_
  split_ifs with h
  · simp [fixFactor, h, Real.volume_Ioo]
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
    simp only [fixFactor, hv, Option.elim]
    exact prob_le_one

theorem kDomainR_subset_unitBoxR {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (upFree : GBranch LG.garden.tree → Prop) (sFree : Prop) :
    kDomainR LG up s fix upFree sFree ⊆ unitBoxR LG fix := by
  intro τ hτ b _
  show τ b ∈ (if fix b = none then Set.Ioo (LG.layer b.toNode : ℝ) (LG.layer b.toNode + 1) else Set.univ)
  split_ifs with h
  · exact ⟨((hτ b).1 h).1, ((hτ b).1 h).2.1⟩
  · exact Set.mem_univ _

theorem kDomainFix_subset_unitBoxR {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) : kDomainFix LG up fix ⊆ unitBoxR LG fix := by
  rw [← kDomainR_eq_kDomainFix]
  exact kDomainR_subset_unitBoxR LG up 0 fix _ _

theorem measurableSet_kDomainFix {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) : MeasurableSet (kDomainFix LG up fix) := by
  rw [← kDomainR_eq_kDomainFix]
  exact measurableSet_kDomainR _ _ _ _ _ _

/-! ### The literal summand on a domain -/

section General

variable {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Dom : Set (GBranch LG.garden.tree → ℝ)) (k₀ : Mom d)

/-- The literal summand of a node kernel on the time domain `Dom` (main's `kernelAllIntegrandN` is `Dom = kDomain`). -/
def kernelAllIntegrandD {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : GBranch LG.garden.tree → ℝ) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    Dom.indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ *
    ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

variable {Dom}

theorem measurable_kernelAllIntegrandD (hD : MeasurableSet Dom) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) : Measurable (kernelAllIntegrandD L γ δ LG A Dom k₀ κ) := by
  unfold kernelAllIntegrandD
  exact (measurable_const.mul ((LGSpine.continuous_phaseProd L γ δ LG.garden _).measurable.indicator hD)).mul
    measurable_const

theorem norm_kernelAllIntegrandD_le {fix : GBranch LG.garden.tree → Option ℝ} (hsub : Dom ⊆ unitBoxR LG fix)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : GBranch LG.garden.tree → ℝ) :
    ‖kernelAllIntegrandD L γ δ LG A Dom k₀ κ τ‖ ≤
      (unitBoxR LG fix).indicator (fun _ => inputNodeMajorant L LG A k₀ κ) τ := by
  have he := abs_epsDec_le_one LG.garden κ.1
  have hprod : 0 ≤ inputNodeMajorant L LG A k₀ κ := Finset.prod_nonneg fun _ _ => abs_nonneg _
  unfold kernelAllIntegrandD
  rw [norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  change |epsDec LG.garden κ.1| * ‖_‖ * inputNodeMajorant L LG A k₀ κ ≤ _
  by_cases hD : τ ∈ Dom
  · rw [Set.indicator_of_mem hD, Set.indicator_of_mem (hsub hD)]
    have hp : ‖phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1) τ‖ = 1 := by
      simp only [phaseProd, norm_prod]
      exact Finset.prod_eq_one fun b _ => Complex.norm_exp_ofReal_mul_I _
    rw [hp, mul_one]
    exact mul_le_mul_of_nonneg_right he hprod |>.trans_eq (one_mul _)
  · rw [Set.indicator_of_notMem hD, norm_zero, mul_zero, zero_mul]
    exact Set.indicator_nonneg (fun _ _ => hprod) _

theorem integrable_kernelAllIntegrandD_fix {fix : GBranch LG.garden.tree → Option ℝ} (hD : MeasurableSet Dom)
    (hsub : Dom ⊆ unitBoxR LG fix) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    Integrable (kernelAllIntegrandD L γ δ LG A Dom k₀ κ) (fixMeasure fix) :=
  integrable_of_norm_le_indicator (measurableSet_unitBoxR LG fix) (fixMeasure_unitBoxR_le_one LG fix) _
    (measurable_kernelAllIntegrandD L γ δ LG A k₀ hD κ).aestronglyMeasurable
    (norm_kernelAllIntegrandD_le L γ δ LG A k₀ hsub κ)

theorem integral_norm_kernelAllIntegrandD_fix_le {fix : GBranch LG.garden.tree → Option ℝ}
    (hsub : Dom ⊆ unitBoxR LG fix) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    ∫ τ, ‖kernelAllIntegrandD L γ δ LG A Dom k₀ κ τ‖ ∂(fixMeasure fix) ≤ inputNodeMajorant L LG A k₀ κ :=
  integral_norm_le_of_norm_le_indicator (measurableSet_unitBoxR LG fix) (fixMeasure_unitBoxR_le_one LG fix) _
    (Finset.prod_nonneg fun _ _ => abs_nonneg _) (norm_kernelAllIntegrandD_le L γ δ LG A k₀ hsub κ)

/-! ### The weighted node kernel on a domain -/

variable (Dom)

/-- The weighted literal summand: momentum weight `m` and decoration weight `Θn`. -/
def kernelAllIntegrandNWD {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (Θn : GenDecoration LG.garden d nroot nfl → ℂ) (κ : GenDecoration LG.garden d nroot nfl)
    (τ : GBranch LG.garden.tree → ℝ) : ℂ :=
  m (cosetDecoration LG.garden L k₀ κ.1) * Θn κ * kernelAllIntegrandD L γ δ LG A Dom k₀ κ τ

/-- **The weighted node kernel on the domain `Dom`, pins `fix`.** -/
def kernelNodeWR (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (Θn : GenDecoration LG.garden d nroot nfl → ℂ)
    (fix : GBranch LG.garden.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) * Θn κ *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ, Dom.indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ ∂(fixMeasure fix)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))

theorem integral_kernelAllIntegrandNWD_fix {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (Θn : GenDecoration LG.garden d nroot nfl → ℂ) (κ : GenDecoration LG.garden d nroot nfl)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    (∫ τ, kernelAllIntegrandNWD L γ δ LG A m Dom k₀ Θn κ τ ∂(fixMeasure fix)) =
      m (cosetDecoration LG.garden L k₀ κ.1) * Θn κ *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ, Dom.indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ ∂(fixMeasure fix)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) := by
  unfold kernelAllIntegrandNWD kernelAllIntegrandD
  rw [integral_const_mul, integral_mul_const, integral_const_mul]

theorem kernelNodeWR_eq_tsum_integral_all (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (Θn : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelNodeWR L γ δ LG A m Dom k₀ nroot nfl Θn fix =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl,
          ∫ τ, kernelAllIntegrandNWD L γ δ LG A m Dom k₀ Θn κ τ ∂(fixMeasure fix) := by
  unfold kernelNodeWR
  congr 1
  exact tsum_congr fun κ => (integral_kernelAllIntegrandNWD_fix L γ δ LG A m Dom k₀ Θn κ fix).symm

variable {Dom}

theorem integral_norm_kernelAllIntegrandNWD_fix_le {fix : GBranch LG.garden.tree → Option ℝ}
    (hsub : Dom ⊆ unitBoxR LG fix) (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm) {nroot : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (Θn : GenDecoration LG.garden d nroot nfl → ℂ) (CΘ : ℝ) (hΘ : ∀ κ, ‖Θn κ‖ ≤ CΘ)
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, ‖kernelAllIntegrandNWD L γ δ LG A m Dom k₀ Θn κ τ‖ ∂(fixMeasure fix)) ≤
      (Mm * CΘ) * inputNodeMajorant L LG A k₀ κ := by
  unfold kernelAllIntegrandNWD
  simp_rw [norm_mul]
  rw [integral_const_mul]
  have hMm : 0 ≤ Mm := (norm_nonneg _).trans (hm 0)
  have hC : 0 ≤ CΘ := (norm_nonneg _).trans (hΘ κ)
  exact mul_le_mul (mul_le_mul (hm _) (hΘ κ) (norm_nonneg _) hMm)
    (integral_norm_kernelAllIntegrandD_fix_le L γ δ LG A k₀ hsub κ) (integral_nonneg fun _ => norm_nonneg _)
    (mul_nonneg hMm hC)

theorem summable_integral_norm_kernelAllIntegrandNWD_fix {fix : GBranch LG.garden.tree → Option ℝ}
    (hsub : Dom ⊆ unitBoxR LG fix) (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (Θn : GenDecoration LG.garden d nroot nfl → ℂ) (CΘ : ℝ)
    (hΘ : ∀ κ, ‖Θn κ‖ ≤ CΘ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, ‖kernelAllIntegrandNWD L γ δ LG A m Dom k₀ Θn κ τ‖ ∂(fixMeasure fix)) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (fun κ => integral_norm_kernelAllIntegrandNWD_fix_le L γ δ LG A m k₀ hsub Mm hm Θn CΘ hΘ κ)
    ((summable_inputNodeMajorant L LG A k₀ nroot nfl hlone hA).mul_left (Mm * CΘ))

theorem summable_integral_kernelAllIntegrandNWD_fix {fix : GBranch LG.garden.tree → Option ℝ}
    (hsub : Dom ⊆ unitBoxR LG fix) (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (Θn : GenDecoration LG.garden d nroot nfl → ℂ) (CΘ : ℝ)
    (hΘ : ∀ κ, ‖Θn κ‖ ≤ CΘ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, kernelAllIntegrandNWD L γ δ LG A m Dom k₀ Θn κ τ ∂(fixMeasure fix)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun κ => norm_integral_le_integral_norm (kernelAllIntegrandNWD L γ δ LG A m Dom k₀ Θn κ))
    (summable_integral_norm_kernelAllIntegrandNWD_fix L γ δ LG A m k₀ hsub Mm hm nroot nfl Θn CΘ hΘ hlone hA)

end General

end WaveTurbulence.Flower.MkSlotsB
