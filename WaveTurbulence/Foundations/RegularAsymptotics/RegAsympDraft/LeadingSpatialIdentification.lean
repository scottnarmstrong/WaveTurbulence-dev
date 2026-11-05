/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeadingSpatialExpansion
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ActualLeafSingularRepresentation

/-! # The actual leading Fourier mixture is the original source singular integral -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Incoh Links Finset

/-- The two absolutely convergent expansions agree term for term. This
identifies the literal leading spatial mixture with the original cell
kernel's singular integral, before the recursive Mstar identification. -/
theorem leafLeadingSpatialProfile_eq_singInt_cellKernel {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    {F : Mom d → ℂ} {B C : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^Q.links.length) (J : Finset (Fin Q.links.length)) (k : Mom d)
    (hi : Integrable (fun p => maskedLeafScalarDensity hQ hG
      (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) F S ((0,0),p) k)
        (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) :
    leafLeadingSpatialProfile hQ hG J F S k = singInt J (leafSingularCellKernel hQ hG F S k) := by
  classical
  obtain ⟨Mcell,-,hcell⟩ := exists_cellOp_bound hd
  have hs := summable_leafSingularCellOutput_terms hQ hG hd hn hK hM hB hF S J (hcell J) hS k
  rw [singInt_leafSingularCellKernel_eq hQ hG hd hn hK hM hB hF S hS J k,
    tsum_leafSingularCellIndex S hs,leafLeadingSpatialProfile_eq_tsum hQ hG J F S k hi]
  apply tsum_congr
  intro c
  rw [← sum_coe_sort]
  apply sum_congr rfl
  intro z _hz
  exact leaf_leading_spectrum_eq_cell_ops hQ hG hd hn hK hM hB hF S J (hcell J) k c z

/-- For the original source covers, the actual singular leaf kernel has
the full spatial bound of its proven Fourier mixture. The covers are
chosen independently of the input norm and root momentum. -/
theorem actual_source_singInt_spatialNorm {d : ℕ} (hd : 3 ≤ d) :
    ∃ Ccover : ℝ, 0 < Ccover ∧ ∃ Mcell : ℝ, 1 ≤ Mcell ∧
      ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → ∀ N W K M : ℕ, d+2+N ≤ K → W+2*d ≤ M →
      ∀ Binput : ℝ, 0 ≤ Binput → ∀ F : Mom d → ℂ,
      Fourier.spatialNorm K M F ≤ ENNReal.ofReal Binput → ∀ J : Finset (Fin Q.links.length),
      Fourier.spatialNorm N W (fun k => singInt J (fun x y =>
        ∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
          (fun j i => if i=0 then x j else y j) a))) ≤
        ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
          ((1+2*Real.pi)*
            ((((2*max 1 (Real.sqrt d)+5)^(2*d))^Q.links.length*Mcell^Q.links.length*
              halfLinkFirstMomentConstant d^(2*Q.links.length))*spectralFrequencyLoss Q))) *
          (ENNReal.ofReal (Ccover^Q.links.length)*
            ENNReal.ofReal (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1)) := by
  classical
  obtain ⟨Ccover,hCcover,hcover⟩ := actual_source_leaf_singular_representation d hd
  obtain ⟨Mcell,hMcell,hsp⟩ := leafLeadingSpatialProfile_integrable_spatialNorm hd
  refine ⟨Ccover,hCcover,Mcell,hMcell,?_⟩
  intro G Q hQ hG hn N W K M hK hM Binput hBi F hF J
  obtain ⟨S,hS,hrep⟩ := hcover G Q hQ hG hn
  obtain ⟨hpoint,-⟩ := hrep K M Binput (by omega) (by omega) hBi F hF
  obtain ⟨hi,hbound⟩ := hsp G Q hQ hG hn J N W K M hK hM Binput Ccover hBi F hF S hS
  have heq : (fun k => singInt J (fun x y =>
      ∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a))) = leafLeadingSpatialProfile hQ hG J F S := by
    funext k
    have hfun : (fun (x y : Fin Q.links.length → Mom d) =>
      ∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) = leafSingularCellKernel hQ hG F S k := by
      funext x y
      exact hpoint k x y
    rw [hfun]
    exact (leafLeadingSpatialProfile_eq_singInt_cellKernel hQ hG hd hn (by omega)
      (by omega) hBi hF S hS J k (hi k)).symm
  rw [heq]
  exact hbound

end WaveTurbulence.RegAsymp
