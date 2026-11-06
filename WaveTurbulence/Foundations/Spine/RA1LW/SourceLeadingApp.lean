/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceLeadingTemporal
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceGardenSign
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceCoverSpectral
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceOriginalSingular
public import WaveTurbulence.Foundations.Spine.RA1LW.CoefficientClassification

/-! # Same-cover global leading profiles identify with the literal B2 app -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR ApproxNT WithLp Set TTree

/-- Conditional coefficient-family assembly: the explicitly classified
original source profiles give the literal B2 app, using proved source
singular identification rather than assuming any spatial recursion. -/
theorem source_leading_eq_app_of_classified {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hn : 0 < Q.links.length)
    {L δ γ : ℝ} (hL : 0 < L) (hδ : δ ≠ 0)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    {θ a b A N : ℝ} (hθ : 0 ≤ θ) (hC : ∀ Z, SRep θ a b A N (C Z))
    (hclass : ∀ Z : (chosenSet Q.links).powerset,
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1,
        (∫ β, ∫ lam, C Z β lam*e2 lam t s) =
          if Q.dominant = true ∧ IsSpecialSet Q.links Z.val then
            (-1:ℂ)^Z.val.card*(Q.JB 0 t s:ℂ) else 0)
    {H : LGSpine.LeafProfiles 2 d} {B Ccover : ℝ} (hB : 0 ≤ B)
    (hF : ∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    (hcover : ∀ c k x, (coupleMomentumData hQ hQ.1).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {t s : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) (k : Mom d) :
    G.zeta * ∑ Z : (chosenSet Q.links).powerset,
      (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
        pairedInverseProfile (fun lam => ∫ p, maskedLeafScalarDensity hQ hQ.1
          (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
            approxApp L (2*δ) γ (markedLinkIndices Q Z.val)
              (fun Ω => C Z (ofLp Ω) lam) (halfCellAmplitude z β γ'))
          (leafFam hQ hQ.1 H) S (lam,p) k
            ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) ![t,s] = LGSpine.LeafApp.couple δ 0 H Q t s k := by
  classical
  have hsize : Q.size = 2*Q.links.length := by
    have hh := couple_linksAt_length Q ((0:Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  have he (Z : (chosenSet Q.links).powerset) :
      pairedInverseProfile (fun lam => ∫ p, maskedLeafScalarDensity hQ hQ.1
          (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
            approxApp L (2*δ) γ (markedLinkIndices Q Z.val)
              (fun Ω => C Z (ofLp Ω) lam) (halfCellAmplitude z β γ'))
          (leafFam hQ hQ.1 H) S (lam,p) k
            ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) ![t,s] =
      ((2:ℂ)⁻¹^Q.size*(δ:ℂ)^(Q.size/2))*Cancel.cplJ Z.val Q (0,[]) (1,[]) t s *
        (LGSpine.LeafApp.cplMstar H Z.val Q (0,[]) (1,[]) k:ℂ) := by
    rw [masked_leading_profile_eq hQ hQ.1 hL hδ (markedLinkIndices Q Z.val) (C Z) hθ (hC Z)]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    rw [hclass Z t ht s hs,cplJ_eq_if_special Q Z.val (Finset.mem_powerset.mp Z.property) t ht s hs]
    by_cases hh : Q.dominant = true ∧ IsSpecialSet Q.links Z.val
    · rw [ite_eq_left hh,leafLeadingSpatialProfile_eq_source_of_cover (F := leafFam hQ hQ.1 H) hQ hQ.1 hd hn
        (by omega) (by omega) hB (fun a => hF (plusLeafEquiv hQ hQ.1 a).val.1) S hcard hcover,
        original_source_singInt_eq_Mstar hd hQ hQ.1 hh.1 hB hF Z.val hh.2 k]
      rw [hsize,Nat.mul_div_right _ (by omega : 0 < (2:ℕ))]
      have hp := physical_leading_app_prefactor Q.links.length δ
      calc
        _ = ((((δ/8)^Q.links.length:ℝ):ℂ)*(2:ℂ)^Q.links.length)*
            ((-1:ℂ)^Z.val.card*(Q.JB 0 t s:ℂ))*(LGSpine.LeafApp.cplMstar H Z.val Q (0,[]) (1,[]) k:ℂ) := by ring
        _ = _ := by rw [hp]
    · rw [ite_eq_right hh]
      simp only [mul_zero,zero_mul]
  simp_rw [he]
  rw [decoded_couple_zeta hQ]
  calc
    _ = ((2:ℂ)⁻¹^Q.size*(δ:ℂ)^(Q.size/2)*zetaOfTrees ![1,-1] ![Q.trees.1,Q.trees.2]) *
        ∑ Z : (chosenSet Q.links).powerset,
          (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
            Cancel.cplJ Z.val Q (0,[]) (1,[]) t s*(LGSpine.LeafApp.cplMstar H Z.val Q (0,[]) (1,[]) k:ℂ) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Z _
      ring
    _ = _ := by
      have hsum := Finset.sum_coe_sort (chosenSet Q.links).powerset
        (fun Z : Finset (Fin 2 × TTree.Path) =>
          (∏ z ∈ Z, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
            Cancel.cplJ Z Q (0,[]) (1,[]) t s*(LGSpine.LeafApp.cplMstar H Z Q (0,[]) (1,[]) k:ℂ))
      rw [hsum]
      simpa only [Cancel.zetaA] using assemble_couple_app_from_cplJ Q δ H t ht s hs k

end WaveTurbulence.RA1Leafwise
