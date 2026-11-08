/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Engine
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GenMerge
/-! Spatial multiplication through the actual split/glue equivalence.
A weight of the S restriction stays inside the outer momentum sum; the lower
kernel has its original unweighted coherent rows. -/
@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceK
open TTree RegRed MeasureTheory VineEstS2 VineEstS4 VineEstS5C
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

theorem rA_glue (RS : CLRegionData G S a b)
    (x y : GNode G.tree → Fin d → ℤ) : rA RS (glue RS x y) = rA RS x := by
  funext v
  unfold rA glue
  split_ifs <;> rfl

theorem glueAbsConv_spatialMul (RU : CLRegionData G (S ∪ T) a c)
    (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    (L : ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (Ψ : PsiT G d) (hΨ : GlueAbsConv RU RS RT L base t0 t1 t2 e f g h Ψ)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (M : ℝ) (hm : ∀ x, ‖m x‖ ≤ M) :
    GlueAbsConv RU RS RT L base t0 t1 t2 e f g h (spatialMul m Ψ) := by
  refine ⟨fun q => (hΨ.1 q).const_mul _, ?_⟩
  apply Summable.of_nonneg_of_le (fun q => integral_nonneg fun τ => norm_nonneg _) _ (hΨ.2.mul_left M)
  intro q
  change (∫ τ, ‖m (glue RS q.1.1 (clExtendIndices RT q.2.1)) *
    fGlue RU RS RT L base t0 t1 t2 e f g h Ψ q τ‖) ≤ _
  simp only [norm_mul, integral_const_mul]
  exact mul_le_mul_of_nonneg_right (hm _) (integral_nonneg fun τ => norm_nonneg _)

/-- Generic weighted Fubini with the S-side weight, derived from the original
unweighted factorization and absolute convergence. -/
theorem lkRaw_spatialMul_split (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : G.molecule.IsBlock (S ∪ T) a c)
    (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    (L : ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (ΨU : PsiT G d) (ΨS : (GNode G.tree → Fin d → ℤ) → (GBranch G.tree → ℝ) → ℂ)
    (ΨT : PsiT G d) (hL : L ≠ 0)
    (hfac : GlueFactors RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT)
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ S, u v = u' v) → ΨS x u = ΨS x u')
    (hlocT : ∀ x t (u u' : GBranch G.tree → ℝ), (∀ v ∈ T, u v = u' v) → ΨT x t u = ΨT x t u')
    (hAbs : GlueAbsConv RU RS RT L base t0 t1 t2 e f g h ΨU)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (M : ℝ) (hm : ∀ x, ‖m x‖ ≤ M) :
    lkRaw RU L base (spatialMul (fun x => m (rA RS x)) ΨU) ![t0, t1, t2] ![e, f, g, h] =
      ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
        (m (rA RS x.1) * ΨS x.1 (clLocalClock RS ![t0, t1, t2] σ)) *
          lkRaw RT L base ΨT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] (bdT RT L base x.1 g h) := by
  apply lkRaw_split_fubini hS hT hi hU RU RS RT L base t0 t1 t2 e f g h
    (spatialMul (fun x => m (rA RS x)) ΨU) (fun x u => m (rA RS x) * ΨS x u) ΨT hL
  · intro q τ
    change m (rA RS (glue RS q.1.1 (clExtendIndices RT q.2.1))) *
      fGlue RU RS RT L base t0 t1 t2 e f g h ΨU q τ = _
    rw [rA_glue, hfac q τ, mul_assoc]
  · intro x u u' hu
    rw [hlocS x u u' hu]
  · exact hlocT
  · exact glueAbsConv_spatialMul RU RS RT L base t0 t1 t2 e f g h ΨU hAbs
      (fun x => m (rA RS x)) M (fun x => hm _)

end WaveTurbulence.VineSpaceK
