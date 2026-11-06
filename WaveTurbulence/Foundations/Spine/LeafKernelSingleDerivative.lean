/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafKernelDerivativeSeries
public import WaveTurbulence.Foundations.Spine.LeafSummandDerivative
public import WaveTurbulence.Foundations.Spine.WeightedLeafKernel
/-! A coordinate derivative of the literal source kernel is the sum of kernels with one real
leaf derivative. The phase is unchanged, so every source oscillatory estimate is preserved. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem summable_leafSpatialSummand {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (hF : ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H l.1 (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      leafSpatialSummand L γ δ LG H up s κ k₀) := by
  apply (summable_leafKernel_summand L γ δ LG H up s k₀ nroot nfl hlone hF).congr
  intro κ
  rw [phaseIntegral_coset_eq_zero L γ δ LG.garden _ s k₀ κ.1 κ.2.1]
  rfl

theorem partialMom_kernelLeaves_single_leaf {w d B : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (hB : d + 1 ≤ B) (γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR 1 B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (j : Fin d) (k : Mom d)
    (hF : ∀ a : ActualInputLeaves LG.garden, ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ =>
        |singleLeafDerivative LG.garden H a j l.1 (k + latticePoint L n)|) :
    partialMom j (fun x => kernelLeaves L γ δ LG H up s x nroot nfl) k =
      ∑ l : ActualInputLeaves LG.garden,
        kernelLeaves L γ δ LG (singleLeafDerivative LG.garden H l j) up s k nroot nfl := by
  have hc' := fun l hl => Complex.ofRealCLM.contDiff.comp (hc l hl)
  rw [partialMom_kernelLeaves_spatial hd hL hB γ δ LG H C hc' hb up s nroot nfl hlone j k]
  have hdiff := fun l hl => (hc l hl).differentiable (by norm_num)
  simp_rw [partialMom_leafSpatialSummand L γ δ LG H up s hdiff]
  have hs (l : ActualInputLeaves LG.garden) (_ : l ∈ (univ : Finset (ActualInputLeaves LG.garden))) :=
    summable_leafSpatialSummand L γ δ LG (singleLeafDerivative LG.garden H l j)
      up s k nroot nfl hlone (hF l)
  rw [Summable.tsum_finsetSum hs, mul_sum]
  apply sum_congr rfl
  intro l _
  exact (kernelLeaves_eq_spatial_tsum L γ δ LG (singleLeafDerivative LG.garden H l j)
    up s nroot nfl k).symm

end WaveTurbulence.LGSpine
