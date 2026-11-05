/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalProfileKernel
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleProfilesClassified

/-! # One physical source profile family with its exact classified leading terms -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory TTree Links ClassJR MainCoef Set

/-- The literal source KQstar expands with the actual squared Wick factor,
its original leaf inputs, and NT profiles at the physical parameter2delta.
The finite special-set sum remains inside the lattice sum at this stage. -/
theorem KQstar_physical_classified_profiles {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      (∀ Z : (chosenSet Q.links).powerset,
        ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1,
          (∫ β, ∫ lam, C Z β lam*e2 lam t s) =
            if Q.dominant = true ∧ IsSpecialSet Q.links Z.val then
              (-1:ℂ)^Z.val.card*(Q.JB 0 t s:ℂ) else 0) ∧
      ∀ (d : ℕ) (L γ δ : ℝ) (LG : LayeredGarden 2)
        (_h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden),
      ∀ (F : Mom d → ℝ) (t : ℝ), t ∈ Icc (0:ℝ) 1 →
      ∀ s ∈ Icc (0:ℝ) 1, ∀ k : Mom d,
      KQstar L γ δ (fun _ => F) LG t s k =
        (coupling d L γ δ : ℂ)^LG.garden.order*LG.garden.zeta*
        ∑' θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ),
          let κ := ((integerLinkEquiv hQ hQ.1 d).symm θ).val
          ((∏ j, epsXY (θ j).1 (θ j).2^2 : ℝ):ℂ) *
            (∑ Z : (chosenSet Q.links).powerset,
              (∏ z ∈ Z.val, ((Cancel.zetaA z : ℂ)*Real.pi*Complex.I)⁻¹)*
                ∫ lam, ApproxNT.resProfile (markedLinkIndices Q Z.val)
                  (fun Ω => C Z (WithLp.ofLp Ω) lam)
                  (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (θ j).1)
                    (latticePoint L (θ j).2))*e2 lam t s) *
            ∏ ℓ ∈ inputLeaves LG.garden, (F (cosetDecoration LG.garden L k κ ℓ.toNode):ℂ) := by
  classical
  obtain ⟨C,hC,hBt,hclass⟩ := couple_profiles_with_classified_leading hη hη2 hA Q hwf
  refine ⟨C,hC,hclass,?_⟩
  intro d L γ δ LG h0 hQ F t ht s hs k
  rw [KQstar_integerLinkEquiv L γ δ F LG hQ hQ.1 t s k]
  apply congrArg (fun v : ℂ => (coupling d L γ δ : ℂ)^LG.garden.order*LG.garden.zeta*v)
  apply tsum_congr
  intro θ
  dsimp only
  rw [actual_phaseIntegral_eq_BtJR L γ δ LG h0 hQ
    (isDecoration_coset ((integerLinkEquiv hQ hQ.1 d).symm θ).property.1 L k) ht hs 0 0,
    hBt _ t s ht hs]
  simp_rw [alphaOmega_integerLinkEquiv_chosen]

end WaveTurbulence.RegAsymp
