/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.LevelNest
/-! Common spatial weights through the actual coherent-family sum in the
native S chart. The multiplier remains inside the lattice sum. -/
@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceK
variable {kind : Bool}
open MeasureTheory Finset

theorem summable_weighted_integrals {X Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f : X → Y → ℂ)
    (hf : Summable fun x => ∫ y, ‖f x y‖ ∂μ)
    (m : X → ℂ) (M : ℝ) (hM : 0 ≤ M) (hm : ∀ x, ‖m x‖ ≤ M) :
    Summable fun x => ∫ y, m x * f x y ∂μ := by
  apply Summable.of_norm_bounded (hf.mul_left M)
  intro x
  rw [integral_const_mul, norm_mul]
  exact mul_le_mul (hm x) (norm_integral_le_integral_norm _) (norm_nonneg _) hM

open VineEstS5C VineEstS5C.FlatMod VineEstS5B VineEstS4 Twist LFTwist RegRed Reg.Skeleton
variable {w d p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {J : Set ι}

/-- Pointwise coherent-family cancellation with the common factor retained.
No character is inserted into either exceptional coherent row. -/
theorem sum_weighted_stIntM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
    (m : (GNode A.skeleton.tree → Fin d → ℤ) → ℂ)
    (x : ExtS sp.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp.RS) :
    (∑ Z ∈ zpFinset p kind pstar J A sp hA, m x.val * stIntM (p := p) (kind := kind) κ lam A sp hA Z.1 x σ) =
      m x.val * (psiSB (p := p) (kind := kind) κ A sp hA x.val (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) *
        KtilM (p := p) (kind := kind) κ lam A sp hA (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ sp.sb.b)
          (κ.base + latticePoint κ.L (x.val (A.family.placement pstar).lower.toNode))
          (κ.base + latticePoint κ.L (x.val (A.family.placement pstar).retained.toNode))) := by
  rw [← mul_sum]
  exact congrArg (m x.val * ·) (sum_stIntM_eq κ lam A sp hA x σ)

/-- The class in the common S chart equals the weighted bundle kernel.
This establishes the finite coherent-family/Fubini step after member transport
to that chart; it does not assume or assert transport of the cut2 carrier. -/
theorem weighted_bundle_sum (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ r : ℕ, Summable fun n : Fin d → ℤ => |κ.F r (κ.base + latticePoint κ.L n)|)
    (m : (GNode A.skeleton.tree → Fin d → ℤ) → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ x, ‖m x‖ ≤ M) :
    (∑ Z ∈ zpFinset p kind pstar J A sp hA,
      ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f,
        ∫ σ : CLInternalTime sp.RS, m x.val * stIntM (p := p) (kind := kind) κ lam A sp hA Z.1 x σ) =
    ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
      m x.val * (psiSB (p := p) (kind := kind) κ A sp hA x.val (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) *
        KtilM (p := p) (kind := kind) κ lam A sp hA (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ sp.sb.b)
          (κ.base + latticePoint κ.L (x.val (A.family.placement pstar).lower.toNode))
          (κ.base + latticePoint κ.L (x.val (A.family.placement pstar).retained.toNode))) := by
  classical
  have hz := fun Z (hZ : Z ∈ zpFinset p kind pstar J A sp hA) =>
    (zp_stateM κ lam A sp hA hA0 hL hF hZ).2
  rw [← Summable.tsum_finsetSum (fun Z hZ =>
    summable_weighted_integrals volume _ (hz Z hZ).2 (fun x => m x.val) M hM (fun x => hm x.val))]
  apply tsum_congr
  intro x
  rw [← integral_finsetSum _ (fun Z hZ => ((hz Z hZ).1 x).const_mul (m x.val))]
  exact integral_congr_ae (Filter.Eventually.of_forall fun σ => sum_weighted_stIntM κ lam A sp hA m x σ)

end WaveTurbulence.VineSpaceK
