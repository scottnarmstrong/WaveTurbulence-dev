/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.FiniteCellDecomposition
public import WaveTurbulence.Foundations.Incoh.LinkArrayCutoff

/-! # Uniform exact spectral decomposition of the actual regular couple -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links

/-- The finite spectral decomposition retains the actual C2 source carrier,
and its link-cell set is fixed before all root momenta and input functions. -/
theorem actual_couple_uniform_spectral_decomposition (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      ∀ c : Fin (2*Q.links.length+1) → Fin d → ℤ,
      ∃ S : Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
        (S.card : ℝ) ≤ C ^ Q.links.length ∧
        ∀ K M : ℕ, ∀ B : ℝ, d+1 ≤ K → 0 ≤ B →
        ∀ F : Fin (2*Q.links.length+1) → Mom d → ℂ, (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B) →
        ∀ ζ : Circle, ∀ k : Mom d, ∀ x : Fin Q.links.length → Fin 2 → Mom d,
          (ζ : ℂ) * coupleLeafCellProduct hQ hG F c k x =
            ∑ z ∈ S, ∫ ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ,
              (coupleMomentumData hQ hG).localizedSourceSpectralDensity ζ F c z k x ξ := by
  obtain ⟨C,hC,h⟩ := actual_couple_finite_cell_decomposition d hd
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG c
  obtain ⟨S,hS,hs⟩ := h G Q hQ hG c
  refine ⟨S,hS,?_⟩
  intro K M B hK hB F hF ζ k x
  calc
    _ = ∑ z ∈ S, (ζ : ℂ) * (coupleLeafCellProduct hQ hG F c k x *
        halfCellArrayWeight z (fun p => x p.1 p.2)) := by
      rw [← Finset.mul_sum,← hs F k x]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      have hh := (coupleMomentumData hQ hG).signed_localizedLeafWeight_eq_spectralIntegral ζ
        F c z hK hB hF k x
      simpa only [MomentumTreeData.localizedLeafWeight,coupleLeafCellProduct,mul_assoc] using hh

/-- Every actual localized lattice piece has finite support before any
spectral or time variable is introduced. -/
theorem actual_localized_lattice_support_finite {d : ℕ} {I : Type*} [Fintype I]
    {L : ℝ} (hL : 0 < L) (z : I → Fin d → ℤ) (A : (I → Fin d → ℤ) → ℂ) :
    (Function.support (fun p => A p * halfCellArrayWeight z (latticeMomentumArray L p))).Finite := by
  apply (finite_support_halfCellArrayWeight_lattice hL z).subset
  intro p hp
  change A p * halfCellArrayWeight z (latticeMomentumArray L p) ≠ 0 at hp
  exact (mul_ne_zero_iff.mp hp).2

end WaveTurbulence.RA1Leafwise
