/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueLeaves
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelUniformMajorant

/-!
# Absolute summability of leafwise kernel sums

The spine's uniform majorant (`KernelUniformMajorant`), for individual leaf profiles: if every profile has
absolutely summable lattice values at the base point, and each tree has at most one lone leaf, the
summand of the leafwise kernel is absolutely summable over the decorations
(`summable_norm_leavesSummand`), uniformly in the time parameters.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

/-- The product of the absolute input values. -/
noncomputable def leafMajorant {w d : ℕ} (L : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden, |H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)|

theorem summable_leafMajorant {w d : ℕ} (L : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Summable (leafMajorant L LG H k₀ (nroot := nroot) (nfl := nfl)) := by
  classical
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let f : ι → (Fin d → ℤ) → ℝ := fun ℓ n => |H ℓ.1.1 (k₀ + latticePoint L n)|
  have hf : Summable (fun z : ι → (Fin d → ℤ) => ∏ ℓ, f ℓ (z ℓ)) :=
    summable_pi_prod f (fun _ _ => abs_nonneg _) (fun ℓ => hH ℓ.1 ℓ.2)
  have h := hf.comp_injective (genDecoration_input_injective LG nroot nfl hlone)
  refine h.congr fun κ => ?_
  unfold leafMajorant
  rw [← Finset.prod_coe_sort]
  rfl

theorem norm_leavesSummand_le {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) :
    ‖leavesSummand L γ δ LG H up s k₀ κ‖ ≤ leafMajorant L LG H k₀ κ := by
  unfold leavesSummand leafMajorant
  rw [norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have he := abs_epsDec_le_one LG.garden κ.1
  have hp := norm_phaseIntegral_le_one L γ δ LG up s (cosetDecoration LG.garden L k₀ κ.1)
  have hprod : 0 ≤ ∏ ℓ ∈ inputLeaves LG.garden, |H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| :=
    prod_nonneg fun _ _ => abs_nonneg _
  calc |epsDec LG.garden κ.1| * ‖phaseIntegral L γ δ LG.garden (kDomain LG up s) s
        (cosetDecoration LG.garden L k₀ κ.1)‖ *
        ∏ ℓ ∈ inputLeaves LG.garden, |H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)|
      ≤ 1 * 1 * ∏ ℓ ∈ inputLeaves LG.garden,
          |H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| := by
        gcongr
    _ = _ := by ring

/-- **The leafwise kernel sum is absolutely summable.** -/
theorem summable_norm_leavesSummand {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d nroot nfl => ‖leavesSummand L γ δ LG H up s k₀ κ‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_leavesSummand_le L γ δ LG H up s k₀)
    (summable_leafMajorant L LG H k₀ nroot nfl hlone hH)

end WaveTurbulence.PL234
