/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SingleLeafDerivative
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelSpatial
/-! Exact differentiation of a phase-invariant source summand updates one input leaf. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem partialMom_leafSpatialSummand {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (hH : ∀ l ∈ inputLeaves LG.garden, Differentiable ℝ (H l.1))
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (j : Fin d) (k : Mom d) :
    partialMom j (leafSpatialSummand L γ δ LG H up s κ) k =
      ∑ l : ActualInputLeaves LG.garden,
        leafSpatialSummand L γ δ LG (singleLeafDerivative LG.garden H l j) up s κ k := by
  classical
  let I := ActualInputLeaves LG.garden
  let f : I → Mom d → ℂ := fun l x => (H l.1.1 (x + latticePoint L (κ.1 l.1.toNode)) : ℂ)
  let c : ℂ := (epsDec LG.garden κ.1 : ℂ) * phaseIntegral L γ δ LG.garden
    (kDomain LG up s) s (cosetDecoration LG.garden L 0 κ.1)
  have hf (l : I) : Differentiable ℝ (f l) :=
    Complex.ofRealCLM.differentiable.comp
      ((hH l.1 l.2).comp (differentiable_id.add_const _))
  have hprod (J : LeafProfiles w d) (x : Mom d) :
      (∏ l : I, (J l.1.1 (x + latticePoint L (κ.1 l.1.toNode)) : ℂ)) =
        ∏ l ∈ inputLeaves LG.garden, (J l.1 (x + latticePoint L (κ.1 l.toNode)) : ℂ) :=
    prod_coe_sort (inputLeaves LG.garden)
      (fun l : GLeaf LG.garden.tree => (J l.1 (x + latticePoint L (κ.1 l.toNode)) : ℂ))
  have he : leafSpatialSummand L γ δ LG H up s κ = fun x => c * ∏ l : I, f l x := by
    funext x
    rw [hprod H x]
    rfl
  have hprodD := HasFDerivAt.finsetProd (u := (univ : Finset I))
    (fun l _ => (hf l k).hasFDerivAt)
  have hd := hprodD.const_mul c
  have hconst : partialMom j (fun x => c * ∏ l : I, f l x) k =
      c * partialMom j (fun x => ∏ l : I, f l x) k := by
    unfold partialMom
    rw [hd.fderiv, hprodD.fderiv]
    rfl
  rw [he, hconst, partialMom_prod_single_leaf univ f j k (fun l _ => hf l k), mul_sum]
  apply sum_congr rfl
  intro l _
  have hupdate : (fun a : I => Function.update f l (partialMom j (f l)) a k) =
      fun a : I => (singleLeafDerivative LG.garden H l j a.1.1
        (k + latticePoint L (κ.1 a.1.toNode)) : ℂ) := by
    funext a
    rw [singleLeafDerivative_input]
    by_cases ha : a = l
    · subst a
      simp only [Function.update_self, ite_true]
      exact partialMom_ofReal_translate j (H l.1.1) _ k (hH l.1 l.2 _)
    · simp only [Function.update_of_ne ha, ha, ite_false]
      rfl
  rw [show (∏ a : I, Function.update f l (partialMom j (f l)) a k) =
      ∏ a : I, (singleLeafDerivative LG.garden H l j a.1.1
        (k + latticePoint L (κ.1 a.1.toNode)) : ℂ) from
      congrArg (fun g : I → ℂ => ∏ a, g a) hupdate, hprod]
  rfl

end WaveTurbulence.LGSpine
