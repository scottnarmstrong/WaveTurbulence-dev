/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceProfileExpansion
public import WaveTurbulence.Foundations.Spine.RA1LW.KernelReindex

/-! # Exact physical-energy profile expansion of the source couple kernel -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory TTree Links ClassJR MainCoef Set

/-- The selected source phase is the actual NT energy with parameter2delta. -/
theorem alphaOmega_integerLinkEquiv_chosen {d : ℕ} {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (L γ δ : ℝ) (k : Mom d)
    (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) (j : Fin Q.links.length) :
    alphaOmega L γ δ G (cosetDecoration G L k ((integerLinkEquiv hQ hQ.1 d).symm θ).val)
        (chosenNode Q j) =
      (2*δ*L^(2*γ))*inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2) := by
  have hj : (chosenNode Q j).2 ∈ (G.tree (chosenNode Q j).1).branching :=
    (chosenBranch hQ j).property
  erw [alphaOmega,dite_eq_left hj]
  change δ*L^(2*γ)*omegaNode G
    (cosetDecoration G L k ((integerLinkEquiv hQ hQ.1 d).symm θ).val) (chosenBranch hQ j) = _
  rw [chosen_energy_integerLinkEquiv hQ hQ.1 d θ L k j]
  ring

end WaveTurbulence.RA1Leafwise
