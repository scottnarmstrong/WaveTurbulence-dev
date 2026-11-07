/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.RootInputs
public import WaveTurbulence.Foundations.Spine.CentralDiffC
/-! # FL-POLAR: the pointwise (per-decoration) polarization of the leaf product. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

theorem typeProfiles_polForm {w d : ℕ} (LG : LayeredGarden w) (σ : ℝ) (j : Fin w) (i : Fin d)
    (g : TProf d w) (ℓ : GLeaf LG.garden.tree) (x : Mom d) :
    typeProfiles LG (polForm σ j i g) ℓ.1 x =
      typeCoeff σ j ℓ.1.1 (LG.garden.pair ℓ).1.1 * x i * typeProfiles LG g ℓ.1 x := by
  rw [typeProfiles_leaf, typeProfiles_leaf]
  rfl

theorem leafProd_polarize {w d : ℕ} (LG : LayeredGarden w) (σ : ℝ) (j : Fin w) (i : Fin d)
    (g : TProf d w) (k : GNode LG.garden.tree → Mom d) (X : ℝ)
    (hX : ∑ a ∈ inputLeaves LG.garden, typeCoeff σ j a.1.1 (LG.garden.pair a).1.1 * (k a.toNode) i = X)
    (M : ℕ) (hM : 1 ≤ M) (hcard : (inputLeaves LG.garden).card ≤ 2 * M) (lam : ℝ) (hlam : lam ≠ 0) :
    X * leafProd LG g k = ∑ m ∈ range (2 * M + 1), (CentralDiff.cw M m / lam) *
      leafProd LG (TProf.perturb g (polForm σ j i g) (lam * ((m : ℝ) - M))) k := by
  set S := inputLeaves LG.garden with hS
  have h := CentralDiff.polarization_extraction S M hM hcard
    (fun ℓ => ((typeProfiles LG g ℓ.1 (k ℓ.toNode) : ℝ) : ℂ))
    (fun ℓ => ((typeCoeff σ j ℓ.1.1 (LG.garden.pair ℓ).1.1 * (k ℓ.toNode) i *
      typeProfiles LG g ℓ.1 (k ℓ.toNode) : ℝ) : ℂ)) lam hlam
  have hL : ∑ a ∈ S, ((typeCoeff σ j a.1.1 (LG.garden.pair a).1.1 * (k a.toNode) i *
      typeProfiles LG g a.1 (k a.toNode) : ℝ) : ℂ) *
        ∏ l ∈ S.erase a, ((typeProfiles LG g l.1 (k l.toNode) : ℝ) : ℂ) =
      (X : ℂ) * ∏ l ∈ S, ((typeProfiles LG g l.1 (k l.toNode) : ℝ) : ℂ) := by
    have e : ∀ a ∈ S, ((typeCoeff σ j a.1.1 (LG.garden.pair a).1.1 * (k a.toNode) i *
        typeProfiles LG g a.1 (k a.toNode) : ℝ) : ℂ) *
          ∏ l ∈ S.erase a, ((typeProfiles LG g l.1 (k l.toNode) : ℝ) : ℂ) =
        ((typeCoeff σ j a.1.1 (LG.garden.pair a).1.1 * (k a.toNode) i : ℝ) : ℂ) *
          ∏ l ∈ S, ((typeProfiles LG g l.1 (k l.toNode) : ℝ) : ℂ) := by
      intro a ha
      rw [← Finset.mul_prod_erase S (fun l => ((typeProfiles LG g l.1 (k l.toNode) : ℝ) : ℂ)) ha]
      push_cast
      ring
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul, ← hX]
    push_cast
    rfl
  have hR : ∀ m : ℕ, ∏ l ∈ S, (((typeProfiles LG g l.1 (k l.toNode) : ℝ) : ℂ) +
      ((lam * ((m : ℝ) - M) : ℝ) : ℂ) * ((typeCoeff σ j l.1.1 (LG.garden.pair l).1.1 * (k l.toNode) i *
        typeProfiles LG g l.1 (k l.toNode) : ℝ) : ℂ)) =
      ((leafProd LG (TProf.perturb g (polForm σ j i g) (lam * ((m : ℝ) - M))) k : ℝ) : ℂ) := by
    intro m
    unfold leafProd
    push_cast
    refine prod_congr rfl fun l _ => ?_
    rw [typeProfiles_perturb]
    simp only [typeProfiles_polForm]
    push_cast
    ring
  rw [hL] at h
  simp only [hR] at h
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_sum]
  have hprod : ((leafProd LG g k : ℝ) : ℂ) = ∏ l ∈ S, ((typeProfiles LG g l.1 (k l.toNode) : ℝ) : ℂ) := by
    unfold leafProd; push_cast; rfl
  rw [hprod, h]

end WaveTurbulence.Flower.Polar
