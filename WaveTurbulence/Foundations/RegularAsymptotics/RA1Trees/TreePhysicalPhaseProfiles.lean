/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeProfilesWithLeading
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePhysicalEnergy
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeKernelReindex

/-! # One actual tree phase-profile family with classified leading coefficients -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR MainCoef Links IncohInst WithLp
open scoped Classical

/-- The literal tree phase uses one original coefficient family with its exact classified
leading terms and physical NT parameter2δ, before any lattice or frequency exchange. -/
theorem actual_tree_physical_phase_profiles_classified {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) :
    ∃ C : (Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset) →
        ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z.val} → ℝ) →
          ℝ × ℝ → ℂ,
      (∀ Z, SRep (1 - η / 8) (η / 4) (1 - η / 2) A (CTη η ^ (2 * X.size + 1)) (C Z)) ∧
      (∀ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
        ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
          (∫ β, ∫ lam, C Z β lam*e2 lam t s) =
            if X.dominant = true ∧ IsSpecialSet (X.linksAt ζ (rootT ζ)) Z.val then
              (-1:ℂ)^Z.val.card*(X.JBtree 0 t s:ℂ) else 0) ∧
      ∀ (d : ℕ) (L γ δ : ℝ) (LG : LayeredGarden 1)
        (hζ : LG.garden.sig 0 = ζ),
        (∀ a, LG.layer a = 0) → ∀ hX : X.DecodesTree LG.garden,
      ∀ (t s : ℝ), 0 ≤ s → s < t → t ≤ 1 → ∀ k : Mom d,
      ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s
        (cosetDecoration LG.garden L k
          (treeDecOfParams hX (0:Fin d → ℤ) (fun j => (p (j,0),p (j,1)))).val) =
        ∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
          (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹) *
            ∫ lam, ApproxNT.resProfile (treeMarkedIndices (treeChosenAddress X ζ) Z.val)
              (fun Ω => C Z (ofLp Ω) lam)
              (fun j => (2*δ*L^(2*γ))*inner ℝ
                (latticePoint L (p (Fin.cast (by rw [hζ]) j,0)))
                (latticePoint L (p (Fin.cast (by rw [hζ]) j,1)))) * e2 lam t s := by
  obtain ⟨C,hC,hphase,hleading⟩ := tree_profiles_with_classified_leading hη hη2 hA X hwf ζ
  refine ⟨C,hC,hleading,?_⟩
  intro d L γ δ LG hζ h0 hX t s hs hst ht k p
  cases hζ
  rw [actual_tree_phaseIntegral_eq_Atilde L γ δ LG h0 hX
    (by
      rw [← tree_decOfParams_eq_coset hX L k]
      exact (treeDecOfParams hX k _).property.1) ⟨hs.trans hst.le,ht⟩ hst s]
  rw [hphase _ t s hs hst ht]
  simp_rw [tree_alphaOmega_chosen]
  rfl

end WaveTurbulence.RegAsymp
