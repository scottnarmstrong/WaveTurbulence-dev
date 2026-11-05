/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCoefficientEnumeration
public import WaveTurbulence.Foundations.RegAsymp.PhiProfile

/-! # The literal tree coefficient expansion in the physical NT energy profile -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR MainCoef WithLp
open scoped Classical

/-- Exact profile conversion for any representation of the original active tree variables. -/
theorem treeComponent_resProfile_of_representation {X : RegChain} {ζ : ℤˣ}
    {Z : Finset ClassJR.Addr}
    (hZ : Z ⊆ ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)))
    {F : (ClassJR.Addr → ℝ) → ℝ → ℝ → ℂ}
    {C : ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z} → ℝ) →
      ℝ × ℝ → ℂ}
    (hrep : ∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
      F α t s = ∫ lam, C (fun j => α (treeChosenAddress X ζ j)) lam * e2 lam t s) :
    ∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
      (∏ z ∈ Z, PhiZ nodeSgn z (α z))*F α t s =
        (∏ z ∈ Z, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
          ∫ lam, ApproxNT.resProfile (treeMarkedIndices (treeChosenAddress X ζ) Z)
            (fun Ω => C (ofLp Ω) lam) (fun j => α (treeChosenAddress X ζ j))*e2 lam t s := by
  intro α t s ht hs
  rw [hrep α t s ht hs, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro lam
  have hprod (f : ClassJR.Addr → ℂ) := prod_treeMarked (treeChosenAddress X ζ)
    (treeChosenAddress_injective X ζ) _ Z (range_treeChosenAddress X ζ) hZ f
  have hp := prod_phiZ_mul_eq_resProfile (treeMarkedIndices (treeChosenAddress X ζ) Z)
    (fun j => nodeSgn (treeChosenAddress X ζ j)) (fun j _ => nodeSgn_eq _)
    (fun Ω => C (ofLp Ω) lam) (fun j => α (treeChosenAddress X ζ j))
  have hphi : (∏ j ∈ treeMarkedIndices (treeChosenAddress X ζ) Z,
      PhiZ (fun i => nodeSgn (treeChosenAddress X ζ i)) j (α (treeChosenAddress X ζ j))) =
      ∏ z ∈ Z, PhiZ nodeSgn z (α z) := by
    simpa only [PhiZ] using hprod (fun z => PhiZ nodeSgn z (α z))
  have hw := hprod (fun z => ((nodeSgn z : ℂ) * Real.pi * Complex.I)⁻¹)
  calc
    _ = ((∏ j ∈ treeMarkedIndices (treeChosenAddress X ζ) Z,
        PhiZ (fun i => nodeSgn (treeChosenAddress X ζ i)) j (α (treeChosenAddress X ζ j))) *
        C (fun j => α (treeChosenAddress X ζ j)) lam) * e2 lam t s := by rw [hphi]; ring
    _ = ((∏ j ∈ treeMarkedIndices (treeChosenAddress X ζ) Z,
        ((nodeSgn (treeChosenAddress X ζ j) : ℂ) * Real.pi * Complex.I)⁻¹) *
        ApproxNT.resProfile (treeMarkedIndices (treeChosenAddress X ζ) Z)
          (fun Ω => C (ofLp Ω) lam) (fun j => α (treeChosenAddress X ζ j))) * e2 lam t s :=
      congrArg (fun v => v * e2 lam t s) hp
    _ = _ := by rw [hw]; ring


/-- A tree MCRep component has its exact NT profile on the unmarked independent source links. -/
theorem treeComponent_resProfile_representation {X : RegChain} {ζ : ℤˣ}
    {Z : Finset ClassJR.Addr}
    (hZ : Z ⊆ ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)))
    {θ a b A N : ℝ} {F : (ClassJR.Addr → ℝ) → ℝ → ℝ → ℂ}
    (hF : MCRep θ a b A N
      (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) \ Z : Finset ClassJR.Addr) F) :
    ∃ C : ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z} → ℝ) →
        ℝ × ℝ → ℂ,
      SRep θ a b A N C ∧ ∀ α t s, t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      (∏ z ∈ Z, PhiZ nodeSgn z (α z)) * F α t s =
        (∏ z ∈ Z, ((nodeSgn z : ℂ) * Real.pi * Complex.I)⁻¹) *
          ∫ lam, ApproxNT.resProfile (treeMarkedIndices (treeChosenAddress X ζ) Z)
            (fun Ω => C (ofLp Ω) lam) (fun j => α (treeChosenAddress X ζ j)) * e2 lam t s := by
  obtain ⟨C,hC,hrep⟩ := tree_sourceCoefficient_on_unmarkedLinks hF
  exact ⟨C,hC,treeComponent_resProfile_of_representation hZ hrep⟩

end WaveTurbulence.RegAsymp
