/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.SkeletonReduction
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelUniformMajorant

/-! # Node-profile kernels: the garden kernel with an arbitrary input amplitude per node

REGRED-LEAF (RULINGS R24 D4).  `kernelNode A` is the garden kernel of TARGET (defkg0) in which the
factor `F_q(k_ℓ)` at an input leaf `ℓ` is replaced by `A ℓ (k_ℓ)`, for an arbitrary profile
`A : GNode → Mom d → ℝ`.  The layer kernel `kernelK F` is `A ℓ = F (layer ℓ)`; the leaf-modified kernel
`kernelLeaves H` of TARGET L2065–L2067 is `A ℓ = H ℓ.1` (the address of the node).  This module redoes
`AllTimeKernel` / `AllTimeKernelNorm` / `KernelIntegrand` of REGRED for `kernelNode`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRedLeaf
open MeasureTheory Finset Set TTree WaveTurbulence.RegRed

/-- The garden kernel with an arbitrary node profile `A` at the input leaves. -/
noncomputable def kernelNode {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

/-- The input-leaf majorant of the node kernel. -/
noncomputable def inputNodeMajorant {w d : ℕ} (L : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden, |A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)|

theorem summable_inputNodeMajorant {w d : ℕ} (L : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (inputNodeMajorant L LG A k₀ (nroot := nroot) (nfl := nfl)) := by
  classical
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let f : ι → (Fin d → ℤ) → ℝ := fun ℓ n => |A ℓ.1.toNode (k₀ + latticePoint L n)|
  have hf : Summable (fun z : ι → (Fin d → ℤ) => ∏ ℓ, f ℓ (z ℓ)) :=
    summable_pi_prod f (fun _ _ => abs_nonneg _) (fun ℓ => hA ℓ.1 ℓ.2)
  have h := hf.comp_injective (LGSpine.genDecoration_input_injective LG nroot nfl hlone)
  refine h.congr fun κ => ?_
  unfold inputNodeMajorant
  rw [← Finset.prod_coe_sort]
  rfl

/-- The actual KG summand before its time integration, with node profile `A`. -/
noncomputable def kernelIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : LG.garden.FreeBranch → ℝ) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1))
      (LG.garden.extendTime s τ) *
    ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

theorem integral_kernelIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, kernelIntegrandN L γ δ LG A up s k₀ κ τ) =
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
      ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) := by
  unfold kernelIntegrandN phaseIntegral
  rw [integral_mul_const, integral_const_mul]

theorem aestronglyMeasurable_kernelIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    AEStronglyMeasurable (kernelIntegrandN L γ δ LG A up s k₀ κ) :=
  ((LGSpine.aestronglyMeasurable_phaseIntegrand L γ δ LG up s
    (cosetDecoration LG.garden L k₀ κ.1)).const_mul _).mul_const _

theorem norm_kernelIntegrandN_le {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : LG.garden.FreeBranch → ℝ) :
    ‖kernelIntegrandN L γ δ LG A up s k₀ κ τ‖ ≤ inputNodeMajorant L LG A k₀ κ *
      (LGSpine.freeTimeBox LG).indicator (fun _ => (1 : ℝ)) τ := by
  have he := abs_epsDec_le_one LG.garden κ.1
  have hp := LGSpine.norm_phaseIntegrand_le_box L γ δ LG up s
    (cosetDecoration LG.garden L k₀ κ.1) τ
  have hprod : 0 ≤ inputNodeMajorant L LG A k₀ κ := prod_nonneg fun _ _ => abs_nonneg _
  unfold kernelIntegrandN
  rw [norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  change |epsDec LG.garden κ.1| * ‖_‖ * inputNodeMajorant L LG A k₀ κ ≤ _
  have hm := (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
    (by simpa only [one_mul] using hp)
  exact (mul_le_mul_of_nonneg_right hm hprod).trans_eq (mul_comm _ _)

theorem integrable_kernelIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    Integrable (kernelIntegrandN L γ δ LG A up s k₀ κ) :=
  ((LGSpine.integrable_freeTimeBox LG).const_mul (inputNodeMajorant L LG A k₀ κ)).mono'
    (aestronglyMeasurable_kernelIntegrandN L γ δ LG A up s k₀ κ)
    (Filter.Eventually.of_forall (norm_kernelIntegrandN_le L γ δ LG A up s k₀ κ))

theorem integral_norm_kernelIntegrandN_le {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, ‖kernelIntegrandN L γ δ LG A up s k₀ κ τ‖) ≤ inputNodeMajorant L LG A k₀ κ := by
  have h := integral_mono (integrable_kernelIntegrandN L γ δ LG A up s k₀ κ).norm
    ((LGSpine.integrable_freeTimeBox LG).const_mul (inputNodeMajorant L LG A k₀ κ))
    (norm_kernelIntegrandN_le L γ δ LG A up s k₀ κ)
  rw [integral_const_mul, integral_freeTimeBox, mul_one] at h
  exact h

/-! ### Full branching-time coordinates when there are no flowers -/

/-- The summand on full branching-time coordinates, with node profile `A`. -/
noncomputable def kernelAllIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : GBranch LG.garden.tree → ℝ) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ *
    ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

theorem kernelAllIntegrandN_allTimeEquiv {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : LG.garden.FreeBranch → ℝ) :
    kernelAllIntegrandN L γ δ LG A up s k₀ κ (allTimeEquiv LG.garden hG τ) =
      kernelIntegrandN L γ δ LG A up s k₀ κ τ := by
  unfold kernelAllIntegrandN kernelIntegrandN
  rw [extendTime_eq_allTimeEquiv LG.garden hG]

theorem integrable_kernelAllIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    Integrable (kernelAllIntegrandN L γ δ LG A up s k₀ κ) := by
  have hi := (measurePreserving_allTimeEquiv LG.garden hG).symm.integrable_comp_of_integrable
    (integrable_kernelIntegrandN L γ δ LG A up s k₀ κ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro τ
  exact (kernelAllIntegrandN_allTimeEquiv L γ δ LG A hG up s k₀ κ
    ((allTimeEquiv LG.garden hG).symm τ)).symm.trans
      (congrArg (kernelAllIntegrandN L γ δ LG A up s k₀ κ)
        ((allTimeEquiv LG.garden hG).apply_symm_apply τ))

theorem integral_kernelAllIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, kernelAllIntegrandN L γ δ LG A up s k₀ κ τ) =
      (∫ τ, kernelIntegrandN L γ δ LG A up s k₀ κ τ) := by
  apply ((measurePreserving_allTimeEquiv LG.garden hG).integral_comp'
    (kernelAllIntegrandN L γ δ LG A up s k₀ κ)).symm.trans
  exact integral_congr_ae
    (Filter.Eventually.of_forall (kernelAllIntegrandN_allTimeEquiv L γ δ LG A hG up s k₀ κ))

/-- No convergence premise is needed for this literal summand identity. -/
theorem kernelNode_eq_tsum_integral_all {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelNode L γ δ LG A up s k₀ nroot nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl,
          ∫ τ, kernelAllIntegrandN L γ δ LG A up s k₀ κ τ := by
  unfold kernelNode
  congr 1
  apply tsum_congr
  intro κ
  exact ((integral_kernelAllIntegrandN L γ δ LG A hG up s k₀ κ).trans
    (integral_kernelIntegrandN L γ δ LG A up s k₀ κ)).symm

theorem integral_norm_kernelAllIntegrandN_le {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, ‖kernelAllIntegrandN L γ δ LG A up s k₀ κ τ‖) ≤ inputNodeMajorant L LG A k₀ κ := by
  have h : (∫ τ, ‖kernelAllIntegrandN L γ δ LG A up s k₀ κ τ‖) =
      (∫ τ, ‖kernelIntegrandN L γ δ LG A up s k₀ κ τ‖) := by
    apply ((measurePreserving_allTimeEquiv LG.garden hG).integral_comp'
      (fun τ => ‖kernelAllIntegrandN L γ δ LG A up s k₀ κ τ‖)).symm.trans
    exact integral_congr_ae (Filter.Eventually.of_forall (fun τ => congrArg norm
      (kernelAllIntegrandN_allTimeEquiv L γ δ LG A hG up s k₀ κ τ)))
  exact h.trans_le (integral_norm_kernelIntegrandN_le L γ δ LG A up s k₀ κ)

theorem summable_integral_norm_kernelAllIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, ‖kernelAllIntegrandN L γ δ LG A up s k₀ κ τ‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_kernelAllIntegrandN_le L γ δ LG A hG up s k₀)
    (summable_inputNodeMajorant L LG A k₀ nroot nfl hlone hA)

theorem summable_integral_kernelAllIntegrandN {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, kernelAllIntegrandN L γ δ LG A up s k₀ κ τ) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun κ => norm_integral_le_integral_norm (kernelAllIntegrandN L γ δ LG A up s k₀ κ))
    (summable_integral_norm_kernelAllIntegrandN L γ δ LG A hG up s k₀ nroot nfl hlone hA)

end WaveTurbulence.RegRedLeaf
