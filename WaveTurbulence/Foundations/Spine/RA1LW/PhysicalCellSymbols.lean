/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalCoefficientProfiles
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellProfileSum

/-! # One classified source family gives the exact normalized physical symbol in every cell -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR MainCoef WithLp Set

/-- The same original coefficient family identifies each normalized
physical cell with the masked leaf Fourier mixture of its actual weighted
NT symbols. All local lattice, leaf Fourier, finite-Z and temporal exchanges
are proved; no kernel-remainder identity is assumed. -/
theorem couple_physical_cell_symbols {η A : ℝ}
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
      ∀ (d K M : ℕ) (F : Fin (2*Q.links.length+1) → Mom d → ℂ) (B : ℝ), d+1 ≤ K → 0 ≤ B →
      (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B) →
      ∀ (L γ δ : ℝ) (LG : LayeredGarden 2) (_h0 : ∀ a, LG.layer a = 0)
        (hQ : Q.Decodes LG.garden), 0 < L →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ k : Mom d,
      ∀ (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (u : SourceCellIndex S),
      (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
        (∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          coupleLatticeTimeCoefficient L γ δ LG hQ t s k p *
            (coupleMomentumData hQ hQ.1).sourceCellWeight F S k
              (fun i j => latticePoint L (p (i,j))) u) =
      ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        sourceRootMask u.1 k *
          ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F u.1 α *
            ∑ Z : (chosenSet Q.links).powerset,
              (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
                pairedInverseProfile (fun lam => physicalWeightedCellSymbol L δ γ u.2.val
                  (fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,0)))
                  (fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,1)))
                  (markedLinkIndices Q Z.val) (C Z) lam) ![t,s]) := by
  classical
  obtain ⟨C,hC,hclass,hpoint⟩ := couple_lattice_profiles_classified hη hη2 hA Q hwf
  refine ⟨C,hC,hclass,?_⟩
  intro d K M F B hK hB hF L γ δ LG h0 hQ hL t ht s hs k S u
  rw [sourceCell_lattice_eq_masked_leafSpectrum hQ hQ.1 hK hB hF hL S u k,
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  let β := fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,0))
  let γ' := fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,1))
  let E := Equiv.arrowProdEquivProdArrow (Fin Q.links.length)
    (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let H := coupleLatticeTimeCoefficient L γ δ LG hQ t s k
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)
  have harr (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
      (latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm (E θ) =
        linkPairArrayEquiv Q.links.length (Fin d → ℤ) θ := by
    change linkPairArrayEquiv Q.links.length (Fin d → ℤ) (E.symm (E θ)) = _
    rw [E.symm_apply_apply]
  have hfreq : q*(∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
      halfCellAmplitude u.2.val β γ' (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*
        H ((latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g)) =
      ∑ Z : (chosenSet Q.links).powerset,
        (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
          pairedInverseProfile (fun lam => physicalWeightedCellSymbol L δ γ u.2.val β γ'
            (markedLinkIndices Q Z.val) (C Z) lam) ![t,s] := by
    rw [← E.tsum_eq]
    have he (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
        H ((latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm (E θ)) =
        ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
          ∑ Z : (chosenSet Q.links).powerset,
            (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
              ∫ lam, ApproxNT.resProfile (markedLinkIndices Q Z.val)
                (fun Ω => C Z (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam t s := by
      rw [harr]
      exact hpoint d L γ δ LG h0 hQ t ht s hs k θ
    simp_rw [he]
    exact halfCell_finite_profiles_eq_physicalSymbols hL δ γ ![t,s] u.2.val β γ'
      (fun Z => markedLinkIndices Q Z.val) C (fun Z => (hC Z).reg)
      (fun Z => ∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)
  let R : ℂ := ∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
    halfCellAmplitude u.2.val β γ' (fun j => latticePoint L (g.1 j))
      (fun j => latticePoint L (g.2 j))*
      H ((latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g)
  change q*R = _ at hfreq
  change q*(sourceRootMask u.1 k*((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*
    leafSpectrumCoefficient F u.1 α*R)) = _
  calc
    _ = sourceRootMask u.1 k*((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*
        leafSpectrumCoefficient F u.1 α*(q*R)) := by ring
    _ = _ := by rw [hfreq]

end WaveTurbulence.RA1Leafwise
