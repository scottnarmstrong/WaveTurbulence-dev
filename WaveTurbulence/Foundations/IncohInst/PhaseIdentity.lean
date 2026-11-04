/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.ClockTransport
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.WeylSums.QuadExpSum2

/-! # Exact source phases after the C2 clock reindexing -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Links

/-- The couple phase, with its exact source normalization, is the product of link phases. -/
theorem couple_phaseProd_eq_links {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {d : ℕ} (L γ δ : ℝ) {κ : GNode G.tree → Mom d} (hκ : IsDecoration G κ)
    (t : Fin Q.links.length → Fin 2 → ℝ) :
    phaseProd L γ δ G κ (coupleClockEquiv hQ t) =
      ∏ j, WeylSums.e ((((G.sign (chosenBranch hQ j).toNode : ℤˣ) : ℤ) : ℝ) * δ *
        L ^ (2 * γ) * (t j 0 - t j 1) *
          inner ℝ (xNode κ (chosenBranch hQ j)) (yNode κ (chosenBranch hQ j))) := by
  unfold phaseProd
  rw [← (coupleLinkEquiv hQ).prod_comp, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fin.prod_univ_two]
  change Complex.exp ((Real.pi * ((G.sign (coupleLinkBranch hQ j 0).toNode : ℤ) : ℝ) * δ *
    L ^ (2 * γ) * omegaNode G κ (coupleLinkBranch hQ j 0) *
      coupleClockEquiv hQ t (coupleLinkBranch hQ j 0) : ℝ) * Complex.I) *
    Complex.exp ((Real.pi * ((G.sign (coupleLinkBranch hQ j 1).toNode : ℤ) : ℝ) * δ *
    L ^ (2 * γ) * omegaNode G κ (coupleLinkBranch hQ j 1) *
      coupleClockEquiv hQ t (coupleLinkBranch hQ j 1) : ℝ) * Complex.I) = _
  have hpair := zeta_omega_link hQ hQ.1 hκ (List.get_mem Q.links j)
    (coupleLinkBranch hQ j 0) (coupleLinkBranch hQ j 1) rfl rfl
  simp only [coupleClockEquiv_apply]
  rw [← Complex.exp_add]
  unfold WeylSums.e
  congr 1
  have hω := omegaNode_eq hκ (chosenBranch hQ j)
  change omegaNode G κ (coupleLinkBranch hQ j 0) = _ at hω
  have hp : (Real.pi * ((G.sign (coupleLinkBranch hQ j 1).toNode : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      omegaNode G κ (coupleLinkBranch hQ j 1) * t j 1) =
      -(Real.pi * ((G.sign (coupleLinkBranch hQ j 0).toNode : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        omegaNode G κ (coupleLinkBranch hQ j 0) * t j 1) := by
    calc
      _ = Real.pi * δ * L ^ (2 * γ) *
        (((G.sign (coupleLinkBranch hQ j 1).toNode : ℤ) : ℝ) * omegaNode G κ (coupleLinkBranch hQ j 1)) * t j 1 := by ring
      _ = _ := by rw [hpair]; ring
  rw [hp, hω]
  push_cast
  rw [show coupleLinkBranch hQ j 0 = chosenBranch hQ j from rfl]
  ring

end WaveTurbulence.IncohInst
