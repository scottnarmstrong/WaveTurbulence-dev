/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceProfileCounting
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalDensityDecomposition
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalCellSymbols
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalCellLocalization

/-! # Global recombination of the original integrable source profiles -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp ClassJR Set

/-- Integrable original scalar source densities recombine over exactly
the original selected cells, with finite source-profile summation justified
by joint L1 rather than a formal interchange. -/
theorem masked_source_profiles_recombine {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} {I : Type*} [Fintype I]
    (R : I → (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (v : I → ℂ) (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hi : ∀ i, Integrable (fun q => maskedLeafScalarDensity hQ hG (R i) F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))))
    (t : Fin 2 → ℝ) :
    (∑' u : SourceCellIndex S, ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      sourceRootMask u.1 k *
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F u.1 α *
          ∑ i, v i*pairedInverseProfile (fun lam => R i lam
            (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 u.2.val) t)) =
    ∑ i, v i*pairedInverseProfile (fun lam => ∫ p,
      maskedLeafScalarDensity hQ hG (R i) F S (lam,p) k
        ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t := by
  classical
  let μ := leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  let : SFinite (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
    unfold leafSpatialMeasure
    infer_instance
  let f := fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
    ∑ i, v i*pairedInverseProfile (fun lam => maskedLeafScalarDensity hQ hG (R i) F S (lam,p) k) t
  have hif : Integrable f μ := integrable_finsetSum _ (fun i _ =>
    (integrable_pairedInverseProfile_samples μ (hi i) t).const_mul (v i))
  have hsupport : ∀ c z, z ∉ S c → ∀ α, f ((c,z),α) = 0 := by
    intro c z hz α
    simp only [f,pairedInverseProfile_maskedLeafScalarDensity,hz,ite_false,mul_zero,Finset.sum_const_zero]
  have hc := leafSpatial_integral_eq_sourceCellIndex S f hif hsupport
  have hpoint (u : SourceCellIndex S) (α : Fin (2*Q.links.length+1) → Fin d → ℝ) :
      f ((u.1,u.2.val),α) = sourceRootMask u.1 k *
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F u.1 α *
          ∑ i, v i*pairedInverseProfile (fun lam => R i lam
            (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 u.2.val) t) := by
    simp only [f,pairedInverseProfile_maskedLeafScalarDensity,u.2.property,ite_true]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hpoint] at hc
  rw [← hc]
  change (∫ p, ∑ i, v i*pairedInverseProfile (fun lam =>
    maskedLeafScalarDensity hQ hG (R i) F S (lam,p) k) t ∂μ) = _
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_pairedInverseProfile_samples μ (hi i) t).const_mul (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,← pairedInverseProfile_integral_swap μ (hi i) t]

/-- One original classified coefficient family gives the exact GLOBAL
physical kernel profile, with every exchange derived from source norms. -/
theorem couple_physical_global_profiles {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ClassJR.A1 ≤ A)
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
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ K M : ℕ, d+2 ≤ K → 2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ (LG : LayeredGarden 2) (_h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden),
      ∀ H : LGSpine.LeafProfiles 2 d,
      (∀ a, Fourier.spatialNorm K M (leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal Binput) →
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
  obtain ⟨C,hC,hclass,hcell⟩ := couple_physical_cell_symbols hη0 (by linarith) hA Q hwf
  refine ⟨C,hC,hclass,?_⟩
  intro Aorder
  obtain ⟨L₀,hjoint⟩ := source_physical_symbol_joint_integrable hd hγ hη0 hη hηγ hηγ' A hA0 Aorder
  refine ⟨max 2 L₀,?_⟩
  intro L hL δ hδ hδ1 K M hK hM Binput Ccover hBi LG h0 hQ H hF hn hnlog S hcard hcover t ht s hs k
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
