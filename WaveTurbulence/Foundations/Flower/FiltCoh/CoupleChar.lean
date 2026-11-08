/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.StarEngine
public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleEnvelopeU
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalCellSymbols
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalGlobalProfile

/-! # FILT-COH (b): a lattice character on a layer-zero couple shifts the cell modulations

The star weight of a decoration is a Fourier mixture of `e(⟨Ξ, k⟩) · e(⟨ν, x⟩)` (IncTop's
`couple_starWeight_eq_value`), `x` the link lattice momenta. The internal character `e(⟨ν, x⟩)` multiplies main's
lattice time coefficient; in every source cell it is absorbed by the half-cell amplitude, whose modulations become
`β + ν₀`, `γ' + ν₁` (`halfCellAmplitude_char`). The rest of main's cell identity
(`RA1Leafwise.couple_physical_cell_symbols`, sha256 in COPIED-SHA256SUMS) is unchanged. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice)
open scoped ENNReal

variable {d : ℕ}

/-- Shift a modulation array by one slot of a link frequency. -/
@[expose] def shiftL {n : ℕ} (β : Fin n → Mom d) (ν : PairedMomentum d n) (i : Fin 2) : Fin n → Mom d :=
  fun j => β j + ν (j, i)

theorem continuous_shiftL {n : ℕ} (i : Fin 2) :
    Continuous (fun p : (Fin n → Mom d) × PairedMomentum d n => shiftL p.1 p.2 i) := by
  unfold shiftL
  refine continuous_pi fun j => ((continuous_apply j).comp continuous_fst).add ?_
  exact ((PiLp.continuous_apply 2 _ (j, i))).comp continuous_snd

/-- The lattice character is absorbed by the half-cell amplitude. -/
theorem halfCellAmplitude_char {n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (ν : PairedMomentum d n) (L : ℝ) (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) :
    halfCellAmplitude z β γ' (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) *
      (Real.fourierChar (inner ℝ ν
        (pairedLattice L ((RA1Leafwise.latticeArrayProductEquiv n (Fin d → ℤ)).symm g))) : ℂ) =
    halfCellAmplitude z (shiftL β ν 0) (shiftL γ' ν 1)
      (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) := by
  have he : ∀ s : ℝ, (Real.fourierChar s : ℂ) = WeylSums.e s := fun _ => rfl
  have hin : inner ℝ ν (pairedLattice L ((RA1Leafwise.latticeArrayProductEquiv n (Fin d → ℤ)).symm g)) =
      ∑ j, (inner ℝ (ν (j,0)) (latticePoint L (g.1 j)) + inner ℝ (ν (j,1)) (latticePoint L (g.2 j))) := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.sum_univ_two]
    rfl
  rw [hin]
  unfold halfCellAmplitude shiftL
  simp only [Circle.smul_def, he, inner_add_left, WeylSums.e_add, WeylSums.e_sum, smul_eq_mul,
    Finset.prod_mul_distrib]
  ring

/-- **The twisted cell identity** (main's `couple_physical_cell_symbols` with the coefficient multiplied by a
lattice character): the physical symbols are evaluated at the shifted modulations. -/
theorem couple_char_cell_symbols {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      ∀ (d K M : ℕ) (F : Fin (2*Q.links.length+1) → Mom d → ℂ) (B : ℝ), d+1 ≤ K → 0 ≤ B →
      (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B) →
      ∀ (L γ δ : ℝ) (LG : LayeredGarden 2) (_h0 : ∀ a, LG.layer a = 0)
        (hQ : Q.Decodes LG.garden), 0 < L →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ k : Mom d,
      ∀ (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (u : SourceCellIndex S)
        (ν : PairedMomentum d Q.links.length),
      (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
        (∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          ((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) *
            RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p) *
            (coupleMomentumData hQ hQ.1).sourceCellWeight F S k
              (fun i j => latticePoint L (p (i,j))) u) =
      ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        sourceRootMask u.1 k *
          ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) *
            RA1Leafwise.leafSpectrumCoefficient F u.1 α *
            ∑ Z : (chosenSet Q.links).powerset,
              (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
                pairedInverseProfile (fun lam => physicalWeightedCellSymbol L δ γ u.2.val
                  (shiftL (fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,0))) ν 0)
                  (shiftL (fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,1))) ν 1)
                  (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam) ![t,s]) := by
  classical
  obtain ⟨C,hC,_hclass,hpoint⟩ := RA1Leafwise.couple_lattice_profiles_classified hη hη2 hA Q hwf
  refine ⟨C,hC,?_⟩
  intro d K M F B hK hB hF L γ δ LG h0 hQ hL t ht s hs k S u ν
  rw [RA1Leafwise.sourceCell_lattice_eq_masked_leafSpectrum hQ hQ.1 hK hB hF hL S u k
    (fun p => (Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) *
      RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p), ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  let β := fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,0))
  let γ' := fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,1))
  let E := Equiv.arrowProdEquivProdArrow (Fin Q.links.length)
    (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let H := RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)
  have harr (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
      (RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm (E θ) =
        RA1Leafwise.linkPairArrayEquiv Q.links.length (Fin d → ℤ) θ := by
    change RA1Leafwise.linkPairArrayEquiv Q.links.length (Fin d → ℤ) (E.symm (E θ)) = _
    rw [E.symm_apply_apply]
  have htw : (∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
      halfCellAmplitude u.2.val β γ' (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*
        ((Real.fourierChar (inner ℝ ν (pairedLattice L
          ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g))) : ℂ) *
          H ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g))) =
      ∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
      halfCellAmplitude u.2.val (shiftL β ν 0) (shiftL γ' ν 1) (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*
        H ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g) := by
    refine tsum_congr fun g => ?_
    rw [← mul_assoc, halfCellAmplitude_char]
  have hfreq : q*(∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
      halfCellAmplitude u.2.val (shiftL β ν 0) (shiftL γ' ν 1) (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*
        H ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g)) =
      ∑ Z : (chosenSet Q.links).powerset,
        (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
          pairedInverseProfile (fun lam => physicalWeightedCellSymbol L δ γ u.2.val
            (shiftL β ν 0) (shiftL γ' ν 1)
            (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam) ![t,s] := by
    rw [← E.tsum_eq]
    have he (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
        H ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm (E θ)) =
        ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
          ∑ Z : (chosenSet Q.links).powerset,
            (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
              ∫ lam, ApproxNT.resProfile (RA1Leafwise.markedLinkIndices Q Z.val)
                (fun Ω => C Z (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam t s := by
      rw [harr]
      exact hpoint d L γ δ LG h0 hQ t ht s hs k θ
    simp_rw [he]
    exact halfCell_finite_profiles_eq_physicalSymbols hL δ γ ![t,s] u.2.val (shiftL β ν 0) (shiftL γ' ν 1)
      (fun Z => RA1Leafwise.markedLinkIndices Q Z.val) C (fun Z => (hC Z).reg)
      (fun Z => ∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)
  rw [← htw] at hfreq
  let R : ℂ := ∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
    halfCellAmplitude u.2.val β γ' (fun j => latticePoint L (g.1 j))
      (fun j => latticePoint L (g.2 j))*
      ((Real.fourierChar (inner ℝ ν (pairedLattice L
          ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g))) : ℂ) *
        H ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g))
  change q*R = _ at hfreq
  change q*(sourceRootMask u.1 k*((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*
    RA1Leafwise.leafSpectrumCoefficient F u.1 α*R)) = _
  calc
    _ = sourceRootMask u.1 k*((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*
        RA1Leafwise.leafSpectrumCoefficient F u.1 α*(q*R)) := by ring
    _ = _ := by rw [hfreq]

end WaveTurbulence.Flower.FiltCoh
