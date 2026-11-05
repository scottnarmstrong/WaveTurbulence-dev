/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeSourceProfile

/-! # One actual spectral profile family for every decoration of a regular tree -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR MainCoef WithLp Set
open scoped Classical

/-- DH23 (newsum1), temporal part, for original trees and a single source coefficient family. -/
theorem actual_tree_profile_expansion {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) :
    ∃ C : (Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset) →
        ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z.val} → ℝ) →
          ℝ × ℝ → ℂ,
      (∀ Z, SRep (1 - η / 8) (η / 4) (1 - η / 2) A (CTη η ^ (2 * X.size + 1)) (C Z)) ∧
      ∀ (d : ℕ) (L γ δ : ℝ) (LG : LayeredGarden 1),
        LG.garden.sig 0 = ζ → (∀ a, LG.layer a = 0) → X.DecodesTree LG.garden →
      ∀ k : GNode LG.garden.tree → Mom d, IsDecoration LG.garden k →
      ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∀ s' : ℝ,
        phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s' k =
          ∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
            (∏ z ∈ Z.val, ((nodeSgn z : ℂ) * Real.pi * Complex.I)⁻¹) *
              ∫ lam, ApproxNT.resProfile (treeMarkedIndices (treeChosenAddress X ζ) Z.val)
                (fun Ω => C Z (ofLp Ω) lam)
                (fun j => liftT (alphaOmegaT L γ δ LG.garden k) (treeChosenAddress X ζ j)) * e2 lam t s := by
  obtain ⟨G, hG, hF⟩ := actual_tree_time_expansion hη hη2 hA X hwf ζ
  have hrep (Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset) :=
    treeComponent_resProfile_representation (Finset.mem_powerset.mp Z.property)
      (hG Z.val (Finset.mem_powerset.mp Z.property))
  choose C hC hrepC using hrep
  refine ⟨C, hC, ?_⟩
  intro d L γ δ LG hζ h0 hX k hk t s hs hst ht s'
  rw [hF d L γ δ LG hζ h0 hX k hk t s hs hst ht s']
  calc
    _ = ∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
        (∏ z ∈ Z.val, PhiZ nodeSgn z (liftT (alphaOmegaT L γ δ LG.garden k) z)) *
          G Z.val (liftT (alphaOmegaT L γ δ LG.garden k)) t s :=
      (Finset.sum_coe_sort _ _).symm
    _ = _ := Finset.sum_congr rfl fun Z _ =>
      hrepC Z _ t s ⟨hs.trans hst.le, ht⟩ ⟨hs, hst.le.trans ht⟩

end WaveTurbulence.RegAsymp
