/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeFactorIdentities
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Pointwise factorization of the actual full source kernel integrand -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

open scoped Classical in
theorem mask_mul_prod {ι : Type*} [Fintype ι] (A : Prop) (B : ι → Prop) (a : ℂ) (b : ι → ℂ) :
    (if A ∧ ∀ i, B i then a * ∏ i, b i else 0) =
      (if A then a else 0) * ∏ i, if B i then b i else 0 := by
  classical
  rw [Fintype.prod_ite_zero]
  by_cases ha : A <;> by_cases hb : ∀ i, B i <;> simp [ha,hb]

noncomputable def coreKernelIntegrand {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (top : ℝ)
    (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) : ℂ :=
  (epsDec S κ : ℂ) *
    (coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top).indicator
      (phaseProd L γ δ S (cosetDecoration S L k₀ κ)) τ

/-- TARGET redkg at the literal integrand level. Every factor on the right is
an actual native source kernel summand, with the proved independent centered
decoration and time coordinates. No factorization premise is supplied. -/
theorem kernelAllIntegrand_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch (D.forest hS) → ℝ) :
    kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ κ τ =
      coreKernelIntegrand D hS L γ δ layer top k₀ (collapseGenDecoration D hS κ).1 (nativeCoreClock D hS τ) *
        ∏ s : ReplacementSlot S, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀
          (collapseGenDecoration D hS κ).1 (nativeCoreClock D hS τ) s
          (restrictRelativeDecorations D hS κ s) (nativeTimeRestriction D hS τ s) := by
  classical
  let κS := collapseGenDecoration D hS κ
  let ρ := restrictRelativeDecorations D hS κ
  let τS := nativeCoreClock D hS τ
  let τN := nativeTimeRestriction D hS τ
  let E := fun s => nativeEpsilonFactor D hS s (ρ s)
  let P := fun s => nativePhaseFactor D hS L γ δ k₀ κS.1 s (ρ s) (τN s)
  let I := fun s => nativeInputFactor D hS L F layer k₀ κS.1 s (ρ s)
  let A := τS ∈ coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top
  let B := fun s => τN s ∈ nativeDomain D hS layer hLayer top τS s
  let Pc := phaseProd L γ δ S (cosetDecoration S L k₀ κS.1) τS
  have hd := nativeTimeDomain_reconstruction D hS layer hLayer top τ
  have hm : (if τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun _ => top) 0
      then Pc * ∏ s, P s else 0) = (if A then Pc else 0) * ∏ s, if B s then P s else 0 :=
    (ite_congr (propext hd) (fun _ => rfl) (fun _ => rfl)).trans (mask_mul_prod A B Pc P)
  simp_rw [nativeKernelIntegrand_eq_factors]
  unfold kernelAllIntegrand coreKernelIntegrand
  dsimp only [layeredReconstruction]
  simp only [Set.indicator_apply]
  change (epsDec (D.garden hS) κ.1 : ℂ) *
    (if τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 then
      phaseProd L γ δ (D.garden hS) (cosetDecoration (D.garden hS) L k₀ κ.1) τ else 0) *
      (∏ ℓ ∈ inputLeaves (D.garden hS), (F (layer ℓ.toNode)
        (cosetDecoration (D.garden hS) L k₀ κ.1 ℓ.toNode) : ℂ)) = _
  rw [epsilon_relative_reconstruction D hS κ,phaseProd_relative_reconstruction D hS L γ δ k₀ κ τ,
    inputProduct_relative_reconstruction D hS L F layer k₀ κ]
  change ((epsDec S κS.1 : ℂ) * ∏ s, E s) *
    (if τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun _ => top) 0
      then Pc * ∏ s, P s else 0) * (∏ s, I s) =
      ((epsDec S κS.1 : ℂ) * (if A then Pc else 0)) *
        ∏ s, E s * (if B s then P s else 0) * I s
  rw [hm,Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  ring

end WaveTurbulence.RegRed
