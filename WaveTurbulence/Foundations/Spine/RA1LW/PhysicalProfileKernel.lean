/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.ActualProfileExpansion
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

/-- The literal source KQstar expands with the actual squared Wick factor,
its original leaf inputs, and NT profiles at the physical parameter2delta.
The finite special-set sum remains inside the lattice sum at this stage. -/
theorem KQstar_physical_profile_expansion {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      ∀ (d : ℕ) (L γ δ : ℝ) (LG : LayeredGarden 2)
        (_h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden),
      ∀ (H : LGSpine.LeafProfiles 2 d) (t : ℝ), t ∈ Icc (0:ℝ) 1 →
      ∀ s ∈ Icc (0:ℝ) 1, ∀ k : Mom d,
      LGSpine.coupleLeaves L γ δ LG H t s k =
        (coupling d L γ δ : ℂ)^LG.garden.order*LG.garden.zeta*
        ∑' θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ),
          let κ := ((integerLinkEquiv hQ hQ.1 d).symm θ).val
          ((∏ j, epsXY (θ j).1 (θ j).2^2 : ℝ):ℂ) *
            (∑ Z : (chosenSet Q.links).powerset,
              (∏ z ∈ Z.val, ((Cancel.zetaA z : ℂ)*Real.pi*Complex.I)⁻¹)*
                ∫ lam, ApproxNT.resProfile (markedLinkIndices Q Z.val)
                  (fun Ω => C Z (WithLp.ofLp Ω) lam)
                  (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (θ j).1)
                    (latticePoint L (θ j).2))*e2 lam t s) *
            ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ ℓ.toNode):ℂ) := by
  classical
  obtain ⟨C,hC,hphase⟩ := actual_couple_profile_expansion hη hη2 hA Q hwf
  refine ⟨C,hC,?_⟩
  intro d L γ δ LG h0 hQ H t ht s hs k
  rw [coupleLeaves_integerLinkEquiv L γ δ H LG hQ hQ.1 t s k]
  apply congrArg (fun v : ℂ => (coupling d L γ δ : ℂ)^LG.garden.order*LG.garden.zeta*v)
  apply tsum_congr
  intro θ
  dsimp only
  rw [hphase d L γ δ LG h0 hQ _
    (isDecoration_coset ((integerLinkEquiv hQ hQ.1 d).symm θ).property.1 L k) t ht s hs 0 0]
  simp_rw [alphaOmega_integerLinkEquiv_chosen]

end WaveTurbulence.RA1Leafwise
