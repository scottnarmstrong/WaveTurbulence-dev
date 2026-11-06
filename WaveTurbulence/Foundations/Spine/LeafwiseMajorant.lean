/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelUniformMajorant
/-! A uniform summable majorant for the actual multilinear leaf kernel. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Finset Set
noncomputable def leafInputMajorant {w d : ℕ} (L : ℝ) (H : LeafProfiles w d)
    (LG : LayeredGarden w) (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden,
    |H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)|

theorem summable_leafInputMajorant {w d : ℕ} (L : ℝ) (H : LeafProfiles w d)
    (LG : LayeredGarden w) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Summable (leafInputMajorant L H LG k₀ (nroot := nroot) (nfl := nfl)) := by
  classical
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let f : ι → (Fin d → ℤ) → ℝ := fun ℓ n => |H ℓ.1.1 (k₀ + latticePoint L n)|
  have hf : Summable (fun z : ι → (Fin d → ℤ) => ∏ ℓ, f ℓ (z ℓ)) :=
    summable_pi_prod f (fun _ _ => abs_nonneg _) (fun ℓ => hF ℓ.1 ℓ.2)
  have h := hf.comp_injective (genDecoration_input_injective LG nroot nfl hlone)
  refine h.congr fun κ => ?_
  unfold leafInputMajorant
  rw [← Finset.prod_coe_sort]
  rfl

/-- The majorant is uniform over the whole upper/lower time parameter space. -/
theorem norm_leafKernel_summand_le_leafInputMajorant {w d : ℕ} (L γ δ : ℝ)
    (H : LeafProfiles w d) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (s : ℝ) (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    ‖(epsDec LG.garden κ.1 : ℂ) *
      phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
      ∏ ℓ ∈ inputLeaves LG.garden,
        (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)‖ ≤
      leafInputMajorant L H LG k₀ κ := by
  rw [norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have he := abs_epsDec_le_one LG.garden κ.1
  have hp := norm_phaseIntegral_le_one L γ δ LG up s (cosetDecoration LG.garden L k₀ κ.1)
  have hprod : 0 ≤ leafInputMajorant L H LG k₀ κ := prod_nonneg fun _ _ => abs_nonneg _
  change |epsDec LG.garden κ.1| * ‖phaseIntegral L γ δ LG.garden (kDomain LG up s) s
    (cosetDecoration LG.garden L k₀ κ.1)‖ * leafInputMajorant L H LG k₀ κ ≤ _
  have hmul : |epsDec LG.garden κ.1| * ‖phaseIntegral L γ δ LG.garden (kDomain LG up s) s
      (cosetDecoration LG.garden L k₀ κ.1)‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by simpa only [one_mul] using hp)
  exact (mul_le_mul_of_nonneg_right hmul hprod).trans_eq (one_mul _)


end WaveTurbulence.LGSpine
