/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceProfileExpansion

/-! # NT profile conversion preserving one selected source coefficient family -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory TTree Links ClassJR WithLp

/-- A selected coefficient representation gives the exact NT profile,
without choosing a second coefficient family and losing its leading value. -/
theorem sourceComponent_resProfile_of_representation {Q : RegCpl}
    {Z : Finset (Fin 2 × TTree.Path)} (hZ : Z ⊆ chosenSet Q.links)
    (F : ((Fin 2 × TTree.Path) → ℝ) → ℝ → ℝ → ℂ)
    (C : ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z} → ℝ) → ℝ × ℝ → ℂ)
    (hrep : ∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
      F α t s = ∫ lam, C (fun j => α (chosenNode Q j)) lam*e2 lam t s) :
    ∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
      (∏ z ∈ Z, PhiZ Cancel.zetaA z (α z))*F α t s =
        (∏ z ∈ Z, ((Cancel.zetaA z : ℂ)*Real.pi*Complex.I)⁻¹)*
          ∫ lam, ApproxNT.resProfile (markedLinkIndices Q Z)
            (fun Ω => C (ofLp Ω) lam) (fun j => α (chosenNode Q j))*e2 lam t s := by
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
