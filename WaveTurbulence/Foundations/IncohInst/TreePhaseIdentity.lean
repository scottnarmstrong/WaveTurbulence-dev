/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.PhaseIdentity
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.WeylSums.QuadExpSum2

/-! # Exact source phases after the C2 clock reindexing -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Links

/-- The couple phase, with its exact source normalization, is the product of link phases. -/
theorem tree_phaseProd_eq_links {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {d : ℕ} (L γ δ : ℝ) {κ : GNode G.tree → Mom d} (hκ : IsDecoration G κ)
    (t : Fin (X.treeLinks (G.sig 0)).length → Fin 2 → ℝ) :
    phaseProd L γ δ G κ (treeClockEquiv hX t) =
      ∏ j, WeylSums.e ((((G.sign (treeChosenBranch hX j).toNode : ℤˣ) : ℤ) : ℝ) * δ *
        L ^ (2 * γ) * (t j 0 - t j 1) *
          inner ℝ (xNode κ (treeChosenBranch hX j)) (yNode κ (treeChosenBranch hX j))) := by
  unfold phaseProd
  rw [← (treeLinkEquiv hX).prod_comp, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fin.prod_univ_two]
  change Complex.exp ((Real.pi * ((G.sign (treeLinkBranch hX j 0).toNode : ℤ) : ℝ) * δ *
    L ^ (2 * γ) * omegaNode G κ (treeLinkBranch hX j 0) *
      treeClockEquiv hX t (treeLinkBranch hX j 0) : ℝ) * Complex.I) *
    Complex.exp ((Real.pi * ((G.sign (treeLinkBranch hX j 1).toNode : ℤ) : ℝ) * δ *
    L ^ (2 * γ) * omegaNode G κ (treeLinkBranch hX j 1) *
      treeClockEquiv hX t (treeLinkBranch hX j 1) : ℝ) * Complex.I) = _
  have hpair := tree_zeta_omega_link hX hκ (List.get_mem (X.treeLinks (G.sig 0)) j)
    (treeLinkBranch hX j 0) (treeLinkBranch hX j 1) rfl rfl
  simp only [treeClockEquiv_apply]
  rw [← Complex.exp_add]
  unfold WeylSums.e
  congr 1
  have hω := omegaNode_eq hκ (treeChosenBranch hX j)
  change omegaNode G κ (treeLinkBranch hX j 0) = _ at hω
  have hp : (Real.pi * ((G.sign (treeLinkBranch hX j 1).toNode : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      omegaNode G κ (treeLinkBranch hX j 1) * t j 1) =
      -(Real.pi * ((G.sign (treeLinkBranch hX j 0).toNode : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        omegaNode G κ (treeLinkBranch hX j 0) * t j 1) := by
    calc
      _ = Real.pi * δ * L ^ (2 * γ) *
        (((G.sign (treeLinkBranch hX j 1).toNode : ℤ) : ℝ) * omegaNode G κ (treeLinkBranch hX j 1)) * t j 1 := by ring
      _ = _ := by rw [hpair]; ring
  rw [hp, hω]
  push_cast
  rw [show treeLinkBranch hX j 0 = treeChosenBranch hX j from rfl]
  ring

end WaveTurbulence.IncohInst
