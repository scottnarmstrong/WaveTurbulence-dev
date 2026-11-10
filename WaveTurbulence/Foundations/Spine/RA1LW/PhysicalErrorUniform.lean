/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceLeadingApp
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalProfileSplit
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalGlobalUniform

/-! # Uniform source-kernel error assembly before the couple-code quantifier -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR ApproxNT WithLp Set

/-- Original source premises give the exact physical error decomposition
with both NT and Wick profiles evaluated at2delta and the factor4^-n. -/
theorem couple_physical_error_profiles_uniform {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
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
      ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ (LG : LayeredGarden 2) (_h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden),
      ∀ H : LGSpine.LeafProfiles 2 d,
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal Binput) →
      0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      (∀ c k x, (coupleMomentumData hQ hQ.1).inputCellWeight c k x ≠ 0 →
        ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c) →
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ k : Mom d,
      LGSpine.coupleLeaves L γ δ LG H t s k-LGSpine.LeafApp.couple δ 0 H Q t s k = LG.garden.zeta *
        ∑ Z : (chosenSet Q.links).powerset,
          (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
            ((4:ℂ)^Q.links.length)⁻¹*
            (sourceScalarProfile hQ hQ.1
              (fun lam β γ' z => localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z)
              (leafFam hQ hQ.1 H) S ![t,s] k +
            sourceScalarProfile hQ hQ.1
              (fun lam β γ' z => normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam)
              (leafFam hQ hQ.1 H) S ![t,s] k) := by
  classical
  intro Aorder
  obtain ⟨Lg,hglobal⟩ := couple_physical_global_profiles_uniform hd hγ hη0 hη hηγ hηγ' hA0 hA Aorder
  obtain ⟨Lr,hjoint⟩ := source_remainders_joint_integrable hd hγ hη0 hη hηγ hηγ' A hA0 Aorder
  refine ⟨max 2 (max Lg Lr),?_⟩
  intro Q hwf
  obtain ⟨C,hC,hclass,hglobal⟩ := hglobal Q hwf
  refine ⟨C,hC,hclass,?_⟩
  intro L hL δ hδ hδ1 Binput Ccover hBi LG h0 hQ H hF hn hnlog S hcard hcover t ht s hs k
  have hLg : Lg ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLr : Lr ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_left _ _).trans hL)
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos hLpos (-(η/2))).trans_le hδ
    linarith only [hh]
  have hk := hglobal L hLg δ hδ hδ1 (40*d) (40*d) (by omega) (by omega)
    Binput Ccover hBi LG h0 hQ H hF hn hnlog S hcard hcover t ht s hs k
  have ha := source_leading_eq_app_of_classified (γ := γ) hd hQ hn hLpos (ne_of_gt hδpos)
    C (by linarith : 0 ≤ 1-η/8) hC hclass hBi hF S hcard hcover ht hs k
  have hsplit (Z : (chosenSet Q.links).powerset) := by
    obtain ⟨hiN,hiW⟩ := hjoint L hLr (2*δ) hδ hδ1 LG.garden Q hQ hQ.1 hn hnlog
      (markedLinkIndices Q Z.val) (C Z) _ (hC Z) (40*d) (40*d) (by omega) (by omega)
      Binput Ccover hBi (leafFam hQ hQ.1 H) (fun a => hF _) S hcard k
    have hiA := source_leading_joint_integrable (F := leafFam hQ hQ.1 H) (γ := γ) hd hQ hQ.1 hn hLpos (ne_of_gt hδpos)
      (markedLinkIndices Q Z.val) (C Z) (by linarith : 0 ≤ 1-η/8) (hC Z)
      (by omega : d+2 ≤ 40*d) (by omega : 2*d ≤ 40*d) hBi (fun a => hF _) S hcard k
    exact physical_source_profile_split_of_joint_integrable hQ hQ.1 hLpos δ γ
      (markedLinkIndices Q Z.val) (C Z) (leafFam hQ hQ.1 H) S k hiN hiA hiW ![t,s]
  change LGSpine.coupleLeaves L γ δ LG H t s k = LG.garden.zeta *
    ∑ Z : (chosenSet Q.links).powerset,
      (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
        sourceScalarProfile hQ hQ.1
          (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam)
          (leafFam hQ hQ.1 H) S ![t,s] k at hk
  change LG.garden.zeta * ∑ Z : (chosenSet Q.links).powerset,
    (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
      sourceScalarProfile hQ hQ.1
        (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
          approxApp L (2*δ) γ (markedLinkIndices Q Z.val) (fun Ω => C Z (ofLp Ω) lam)
            (halfCellAmplitude z β γ')) (leafFam hQ hQ.1 H) S ![t,s] k = LGSpine.LeafApp.couple δ 0 H Q t s k at ha
  rw [hk,← ha,← mul_sub,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro Z _
  rw [hsplit Z]
  ring

end WaveTurbulence.RA1Leafwise
