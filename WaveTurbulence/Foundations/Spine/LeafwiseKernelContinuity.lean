/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseMajorant
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity
/-! Continuity of the actual multilinear leaf kernel from its summable majorant. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Finset Set
/-- Uniform convergence transfers continuity of the literal phase integrals to the kernel.
Only summability on the input cosets and the source's lone-leaf restriction are needed. -/
theorem continuous_kernelLeaves_time {w d : ℕ} (L γ δ : ℝ) (H : LeafProfiles w d)
    (LG : LayeredGarden w) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Continuous (fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
      kernelLeaves L γ δ LG H x.1 x.2 k₀ nroot nfl) := by
  unfold kernelLeaves
  apply Continuous.mul continuous_const
  apply continuous_tsum
  · intro κ
    exact (continuous_const.mul
      (continuous_phaseIntegral_no_flower L γ δ LG hflower
        (cosetDecoration LG.garden L k₀ κ.1))).mul continuous_const
  · exact summable_leafInputMajorant L H LG k₀ nroot nfl hlone hF
  · intro κ x
    exact norm_leafKernel_summand_le_leafInputMajorant L γ δ H LG x.1 x.2 k₀ κ

/-- In particular the couple kernel has continuous two-time slices on the entire time plane. -/
theorem continuous_coupleLeaves_time {d : ℕ} (L γ δ : ℝ) (H : LeafProfiles 2 d)
    (LG : LayeredGarden 2) (hplain : LG.garden.IsPlain) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => coupleLeaves L γ δ LG H (ts 0) (ts 1) k) := by
  have hc := continuous_kernelLeaves_time L γ δ H LG k (fun _ => 0) 0
    (no_flowerParent_of_plain LG.garden hplain) (card_lone_le_one_of_plain LG.garden hplain) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) :=
    fun ts => ((fun b => if b.1.1 = 0 then ts 0 else ts 1), 0)
  have hu : Continuous u := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro b
    by_cases h : b.1.1 = 0
    · simpa only [h, ite_true] using (continuous_apply (0 : Fin 2))
    · simpa only [h, ite_false] using (continuous_apply (1 : Fin 2))
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    kernelLeaves L γ δ LG H x.1 x.2 k (fun _ => 0) 0) ∘ u)
  exact hc.comp hu


end WaveTurbulence.LGSpine
