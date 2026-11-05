/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalCellSpectrum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleProfilesClassified
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickPatternEnergy

/-! # The actual lattice time coefficient and its single classified NT profile family -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory TTree Links ClassJR MainCoef Set WithLp ApproxNT

/-- One original J3 family expands each actual squared-Wick lattice time
coefficient and retains every classified signed leading time integral. -/
theorem couple_lattice_profiles_classified {η A : ℝ}
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
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ k : Mom d,
      ∀ θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ),
        coupleLatticeTimeCoefficient L γ δ LG hQ t s k
          (linkPairArrayEquiv Q.links.length (Fin d → ℤ) θ) =
        ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ) *
          ∑ Z : (chosenSet Q.links).powerset,
            (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
              ∫ lam, resProfile (markedLinkIndices Q Z.val)
                (fun Ω => C Z (ofLp Ω) lam)
                (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam t s := by
  classical
  obtain ⟨C,hC,hBt,hclass⟩ := couple_profiles_with_classified_leading hη hη2 hA Q hwf
  refine ⟨C,hC,hclass,?_⟩
  intro d L γ δ LG h0 hQ t ht s hs k θ
  have hcoords : (fun j =>
      (linkPairArrayEquiv Q.links.length (Fin d → ℤ) θ (j,0),
       linkPairArrayEquiv Q.links.length (Fin d → ℤ) θ (j,1))) = θ := by
    funext j
    rfl
  unfold coupleLatticeTimeCoefficient
  rw [hcoords,actual_phaseIntegral_eq_BtJR L γ δ LG h0 hQ
    (isDecoration_coset ((integerLinkEquiv hQ hQ.1 d).symm θ).property.1 L k) ht hs 0 0,
    hBt _ t s ht hs]
  simp_rw [alphaOmega_integerLinkEquiv_chosen]
  have he : (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2)) =
      wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ := by
    funext j
    unfold wickLatticeEnergy
    ring
  rw [he]
  rfl

end WaveTurbulence.RegAsymp
