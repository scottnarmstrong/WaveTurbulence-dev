/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalGlobalProfile

/-! # The original physical global profile has a threshold uniform over all codes -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR WithLp Set

/-- One original classified coefficient family gives the exact GLOBAL
physical kernel profile, with every exchange derived from source norms. -/
theorem couple_physical_global_profiles_uniform {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ClassJR.A1 ≤ A) :
    ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ Q : RegCpl, Q.wf = true →
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      (∀ Z : (chosenSet Q.links).powerset,
        ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1,
          (∫ β, ∫ lam, C Z β lam*e2 lam t s) =
            if Q.dominant = true ∧ IsSpecialSet Q.links Z.val then
              (-1:ℂ)^Z.val.card*(Q.JB 0 t s:ℂ) else 0) ∧
      ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ K M : ℕ, d+2 ≤ K → 2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ (LG : LayeredGarden 2) (_h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden),
      ∀ H : LGSpine.LeafProfiles 2 d,
      (∀ z, Fourier.spatialNorm K M (addrFam H z) ≤ ENNReal.ofReal Binput) →
      0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      (∀ c k x, (coupleMomentumData hQ hQ.1).inputCellWeight c k x ≠ 0 →
        ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c) →
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ k : Mom d,
      LGSpine.coupleLeaves L γ δ LG H t s k = LG.garden.zeta *
        ∑ Z : (chosenSet Q.links).powerset,
          (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
            pairedInverseProfile (fun lam => ∫ p, maskedLeafScalarDensity hQ hQ.1
              (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ'
                (markedLinkIndices Q Z.val) (C Z) lam)
              (leafFam hQ hQ.1 H) S (lam,p) k
                ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) ![t,s] := by
  classical
  intro Aorder
  obtain ⟨L₀,hjoint⟩ := source_physical_symbol_joint_integrable hd hγ hη0 hη hηγ hηγ' A hA0 Aorder
  refine ⟨max 2 L₀,?_⟩
  intro Q hwf
  obtain ⟨C,hC,hclass,hcell⟩ := couple_physical_cell_symbols hη0 (by linarith) hA Q hwf
  refine ⟨C,hC,hclass,?_⟩
  intro L hL δ hδ hδ1 K M hK hM Binput Ccover hBi LG h0 hQ H hF' hn hnlog S hcard hcover t ht s hs k
  have hF : ∀ a, Fourier.spatialNorm K M (leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal Binput := fun a => hF' _
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hL2
  have hi (Z : (chosenSet Q.links).powerset) := hjoint L ((le_max_right _ _).trans hL)
    δ hδ hδ1 LG.garden Q hQ hQ.1 hn hnlog (markedLinkIndices Q Z.val) (C Z)
    _ (hC Z) K M hK hM Binput Ccover hBi (leafFam hQ hQ.1 H) hF S hcard k
  have horder : LG.garden.order = 2*Q.links.length := by
    rw [Reg.size_eq_order hQ]
    have hh := couple_linksAt_length Q ((0:Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  rw [coupleLeaves_eq_sourceCell_lattice (by linarith : 1 ≤ L) γ δ LG h0 hQ
    (by omega) hM hBi hF S hcard ht.2 hs.2 k (fun c x => hcover c k x)]
  rw [horder]
  have hlocal (u : SourceCellIndex S) := hcell d K M (leafFam hQ hQ.1 H) Binput
    (by omega) hBi hF L γ δ LG h0 hQ hLpos t ht s hs k S u
  have he : (coupling d L γ δ:ℂ)^(2*Q.links.length)*
      (∑' u : SourceCellIndex S, ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
        coupleLatticeTimeCoefficient L γ δ LG hQ t s k p *
          (coupleMomentumData hQ hQ.1).sourceCellWeight (leafFam hQ hQ.1 H) S k
            (fun i j => latticePoint L (p (i,j))) u) =
      ∑ Z : (chosenSet Q.links).powerset,
        (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
          pairedInverseProfile (fun lam => ∫ p, maskedLeafScalarDensity hQ hQ.1
            (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ'
              (markedLinkIndices Q Z.val) (C Z) lam) (leafFam hQ hQ.1 H) S (lam,p) k
                ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) ![t,s] := by
    rw [← tsum_mul_left]
    simp only [coupling,← Complex.ofReal_pow]
    simp_rw [hlocal]
    exact masked_source_profiles_recombine hQ hQ.1
      (fun Z lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam)
      (fun Z => ∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)
      (leafFam hQ hQ.1 H) S k hi ![t,s]
  rw [mul_assoc,mul_left_comm ((coupling d L γ δ:ℂ)^(2*Q.links.length)) LG.garden.zeta,he]

end WaveTurbulence.RA1Leafwise
