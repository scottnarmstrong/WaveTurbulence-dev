/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.Symbol
public import WaveTurbulence.Foundations.ApproxNT.PsiOne

/-! # From J3's l1 operator derivatives to the NT coordinate words

DH23 (maincoef2) and (propertypsi2). Each coordinate vector has l1 norm1,
so evaluating a derivative word incurs NO dimension-to-the-order factor.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open WithLp
open scoped ContDiff ENNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def euclideanToL1 : EuclideanSpace ℝ ι →L[ℝ] ClassJR.L1 ι :=
  (PiLp.continuousLinearEquiv 1 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).toContinuousLinearMap

omit [Fintype ι] in
private theorem euclideanToL1_single (i : ι) :
    euclideanToL1 (EuclideanSpace.single i (1 : ℝ)) = PiLp.single 1 i 1 := by
  rfl

/-- Every Euclidean coordinate-word derivative is bounded by the literal
l1 derivative norm used in the author's J3 symbol API. -/
theorem enorm_wordDeriv_le_dnorm {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) {k : ℕ} (v : Fin k → ι) (x : EuclideanSpace ℝ ι) :
    ‖ApproxNT.wordDeriv (fun y => f (ofLp y)) v x‖ₑ ≤
      ClassJR.dnorm k (fun α (_ : Unit) => f α) (ofLp x) () := by
  let F : ClassJR.L1 ι → ℂ := ClassJR.lift1 (fun α (_ : Unit) => f α) ()
  have hF : ContDiff ℝ ∞ F := ClassJR.contDiff_lift1 hf
  have he : (fun y : EuclideanSpace ℝ ι => f (ofLp y)) = F ∘ euclideanToL1 := rfl
  unfold ApproxNT.wordDeriv
  rw [he,euclideanToL1.iteratedFDeriv_comp_right hF x (by exact_mod_cast le_top)]
  change ‖(iteratedFDeriv ℝ k F (euclideanToL1 x))
      (fun m => euclideanToL1 (EuclideanSpace.single (v m) 1))‖ₑ ≤ _
  have h := (iteratedFDeriv ℝ k F (euclideanToL1 x)).le_opNorm
    (fun m => euclideanToL1 (EuclideanSpace.single (v m) 1))
  simp only [euclideanToL1_single,PiLp.norm_single,norm_one,Finset.prod_const_one,mul_one] at h
  change ‖(iteratedFDeriv ℝ k F (euclideanToL1 x))
      (fun m => euclideanToL1 (EuclideanSpace.single (v m) 1))‖ₑ ≤
      ‖iteratedFDeriv ℝ k F (euclideanToL1 x)‖ₑ
  rw [← ofReal_norm,← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [euclideanToL1_single] using h

end WaveTurbulence.RegAsymp
