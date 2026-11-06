/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.CoefficientEnumeration
public import WaveTurbulence.Foundations.Spine.RA1LW.ActualTimeExpansion
public import WaveTurbulence.Foundations.RegAsymp.PhiProfile

/-! # The literal special-address expansion in the NT energy profile -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory TTree Links ClassJR WithLp

/-- The marked independent links enumerate exactly the source address set. -/
theorem prod_marked_chosenNode (Q : RegCpl) (Z : Finset (Fin 2 × TTree.Path))
    (hZ : Z ⊆ chosenSet Q.links) (f : (Fin 2 × TTree.Path) → ℂ) :
    (∏ j ∈ markedLinkIndices Q Z, f (chosenNode Q j)) = ∏ z ∈ Z, f z := by
  apply Finset.prod_bij (fun j _ => chosenNode Q j)
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro i _ j _ hij
    exact chosenNode_injective Q hij
  · intro z hz
    obtain ⟨j,hj⟩ := (Set.ext_iff.mp (range_chosenNode Q) z).mpr (hZ hz)
    refine ⟨j,?_,hj⟩
    simp only [markedLinkIndices,Finset.mem_filter,Finset.mem_univ,true_and,hj,hz]
  · intro j _
    rfl

/-- Each actual J3 component has an exact NT profile representation on the
literal unmarked independent links, with unchanged SRep constants. -/
theorem sourceComponent_resProfile_representation {Q : RegCpl}
    {Z : Finset (Fin 2 × TTree.Path)} (hZ : Z ⊆ chosenSet Q.links)
    {θ a b A N : ℝ} {F : ((Fin 2 × TTree.Path) → ℝ) → ℝ → ℝ → ℂ}
    (hF : MCRep θ a b A N ↑(chosenSet Q.links \ Z) F) :
    ∃ C : ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z} → ℝ) → ℝ × ℝ → ℂ,
      SRep θ a b A N C ∧
      ∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
      (∏ z ∈ Z, PhiZ Cancel.zetaA z (α z))*F α t s =
        (∏ z ∈ Z, ((Cancel.zetaA z : ℂ)*Real.pi*Complex.I)⁻¹)*
          ∫ lam, ApproxNT.resProfile (markedLinkIndices Q Z)
            (fun Ω => C (ofLp Ω) lam) (fun j => α (chosenNode Q j))*e2 lam t s := by
  obtain ⟨C,hC,hrep⟩ := sourceCoefficient_on_unmarkedLinks hF
  refine ⟨C,hC,?_⟩
  intro α t s ht hs
  rw [hrep α t s ht hs,← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro lam
  have hphi := prod_marked_chosenNode Q Z hZ (fun z => PhiZ Cancel.zetaA z (α z))
  have hweight := prod_marked_chosenNode Q Z hZ
    (fun z => ((Cancel.zetaA z : ℂ)*Real.pi*Complex.I)⁻¹)
  have hp := prod_phiZ_mul_eq_resProfile (markedLinkIndices Q Z)
    (fun j => Cancel.zetaA (chosenNode Q j)) (fun j _ => Cancel.zetaA_pm (chosenNode Q j))
    (fun Ω => C (ofLp Ω) lam) (fun j => α (chosenNode Q j))
  have hphi' : (∏ j ∈ markedLinkIndices Q Z,
      PhiZ (fun i => Cancel.zetaA (chosenNode Q i)) j (α (chosenNode Q j))) =
      ∏ z ∈ Z, PhiZ Cancel.zetaA z (α z) := by
    simpa only [PhiZ] using hphi
  calc
    _ = ((∏ j ∈ markedLinkIndices Q Z, PhiZ (fun i => Cancel.zetaA (chosenNode Q i)) j
          (α (chosenNode Q j)))*C (fun j => α (chosenNode Q j)) lam)*e2 lam t s := by
      rw [hphi']
      ring
    _ = ((∏ j ∈ markedLinkIndices Q Z, ((Cancel.zetaA (chosenNode Q j):ℂ)*Real.pi*Complex.I)⁻¹)*
        ApproxNT.resProfile (markedLinkIndices Q Z)
          (fun Ω => C (ofLp Ω) lam) (fun j => α (chosenNode Q j)))*e2 lam t s :=
      congrArg (fun v => v*e2 lam t s) hp
    _ = _ := by rw [hweight]; ring

end WaveTurbulence.RA1Leafwise
