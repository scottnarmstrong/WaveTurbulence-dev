/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalPhaseProfiles
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeKernelSpectralAgreement
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeFiniteProfileMixture

/-! # Original KTstar as classified profile mixtures, retaining its exact Wick coefficient -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ClassJR MainCoef ApproxNT WithLp Incoh Links IncohInst

/-- The exact squared Wick product in separate original x/y lattice arrays. -/
def treeWickArrayWeight {d n : ℕ}
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) : ℂ :=
  ((∏ j, linkWickFactor (g.1 j) (g.2 j):ℝ):ℂ)

theorem treeWickArrayWeight_norm_le {d n : ℕ}
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) : ‖treeWickArrayWeight g‖ ≤ 1 := by
  rw [treeWickArrayWeight,Complex.norm_real,Real.norm_eq_abs,Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_linkWickFactor_le _ _)

/-- The original tree kernel admits one exact family of actual profile mixtures whose
integrated coefficients have the source signed JBtree classification. All original
physical prefactors, root signs, squared Wick factors and the physical2delta remain. -/
theorem KTstar_classified_leaf_profile_mixtures {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) :
    ∃ C : (Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset) →
        ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z.val} → ℝ) →
          ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A (CTη η^(2*X.size+1)) (C Z)) ∧
      (∀ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
        ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
          (∫ β, ∫ lam, C Z β lam*e2 lam t s) =
            if X.dominant = true ∧ IsSpecialSet (X.linksAt ζ (rootT ζ)) Z.val then
              (-1:ℂ)^Z.val.card*(X.JBtree 0 t s:ℂ) else 0) ∧
      ∀ (d K M : ℕ) (L γ δ : ℝ) (LG : LayeredGarden 1) (hζ : LG.garden.sig 0 = ζ),
        (∀ a, LG.layer a = 0) → ∀ hX : X.DecodesTree LG.garden,
      ∀ B : ℝ, 0 ≤ B → 1 ≤ L → d+2 ≤ K → 2*d ≤ M →
      ∀ H : LGSpine.LeafProfiles 1 d,
      (∀ b, Fourier.spatialNorm K M (treeInputFunctionsL LG H b) ≤ ENNReal.ofReal B) →
      ∀ S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
        Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ),
      (∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
        ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c) →
      ∀ Ccover : ℝ, (∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length) →
      ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∀ k : Mom d,
      LGSpine.treeLeaves L γ δ LG H t s k =
        (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta*
          ∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
            (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
              ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (treeInputFunctionsL LG H) S) k u *
                pairedInverseProfile (fun lam => treeNormalizedScalar hX
                  (fun lam β γ' z => treeProfileArrayScalar L (2*δ*L^(2*γ)) treeWickArrayWeight z β γ'
                    (by cases hζ; exact treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val)
                    (by cases hζ; exact C Z) lam) S lam u) ![t,s]
                  ∂treeLeafCellMeasure S := by
  obtain ⟨C,hC,hlead,hphase⟩ := actual_tree_physical_phase_profiles_classified hη hη2 hA X hwf ζ
  refine ⟨C,hC,hlead,?_⟩
  intro d K M L γ δ LG hζ h0 hX B hB hL hK hM H hf S hcover Ccover hS t s hs hst ht k
  cases hζ
  have hH : treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s =
      fun g => treeWickArrayWeight g *
        ∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)))).powerset,
          (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
            ∫ lam, resProfile (treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val)
              (fun Ω => C Z (ofLp Ω) lam)
              (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s := by
    funext g
    unfold treeOriginalArrayCoefficient treeOriginalLatticeCoefficient treeWickArrayWeight
    rw [hphase d L γ δ LG rfl h0 hX t s hs hst ht 0
      (fun p => if p.2=0 then g.1 p.1 else g.2 p.1)]
    simp only [ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,Complex.ofReal_prod]
    rfl
  rw [treeLeaves_eq_tree_leaf_spectral_mixture L γ δ LG hX hwf h0 hB hL hK hM H hf S hcover hS hs hst ht k,hH]
  apply congrArg (fun v : ℂ => (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta*v)
  exact tree_leaf_mixture_finite_profiles hX hL (2*δ*L^(2*γ)) treeWickArrayWeight
    zero_le_one treeWickArrayWeight_norm_le _ _ C (fun Z => (hC Z).reg)
      (treeInputFunctionsL LG H) hK hM hB hf S hS ![t,s] k

end WaveTurbulence.RA1Leafwise
