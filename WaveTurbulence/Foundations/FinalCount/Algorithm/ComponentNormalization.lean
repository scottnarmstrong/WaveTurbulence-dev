/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideCircuitRank
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideLinkProduct
import Mathlib.Tactic

/-! # Exact factorization of the full normalized counting weight -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def linkNormalization (M : Molecule V D) (d : ℕ) (L γ δ C1 : ℝ)
    (P : Finset V → ℝ) : ℝ :=
  L ^ (-((d : ℝ)-γ)*M.circuitRank)*(C1⁻¹*δ^(1/2 : ℝ))^M.circuitRank*
    appbLinkProduct M L γ δ P

theorem linkNormalization_nonneg (M : Molecule V D) (d : ℕ) {L δ C1 : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) (γ : ℝ)
    (P : Finset V → ℝ) (hP : ∀ S,0 ≤ P S) : 0 ≤ linkNormalization M d L γ δ C1 P := by
  have hB : 0 < C1⁻¹*δ^(1/2 : ℝ) := by positivity
  apply mul_nonneg (mul_nonneg (Real.rpow_nonneg hL.le _) (zpow_nonneg hB.le _))
  unfold appbLinkProduct
  apply prod_nonneg
  intro S hS
  unfold Molecule.ladderWeight
  apply le_min (sq_nonneg _)
  have hh := mul_nonneg (mul_nonneg hδ.le (Real.rpow_nonneg hL.le (2*γ))) (hP S)
  linarith only [hh]

/-- The normalizing constant and all actual link weights factor, so
component decomposition introduces no new size-dependent constant. -/
theorem linkNormalization_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (d : ℕ) {L δ C1 : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1)
    (γ : ℝ) (P : Finset V → ℝ) :
    linkNormalization M d L γ δ C1 P =
      linkNormalization (appbSideMolecule M S hS) d L γ δ C1 P*
        linkNormalization (appbSideMolecule M (M.atoms \ S) hS.complement) d L γ δ C1 P := by
  have hB : C1⁻¹*δ^(1/2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hr := circuitRank_closed_side_add M S hS
  have he : -((d : ℝ)-γ)*(M.circuitRank : ℝ) =
      -((d : ℝ)-γ)*((appbSideMolecule M S hS).circuitRank : ℝ)+
      -((d : ℝ)-γ)*((appbSideMolecule M (M.atoms \ S) hS.complement).circuitRank : ℝ) := by
    rw [hr,Int.cast_add]
    ring
  unfold linkNormalization
  rw [he,Real.rpow_add hL,hr,zpow_add₀ hB,linkProduct_closed_side M S hS L γ δ P]
  ring

end WaveTurbulence.Mole.AppbAlgorithm
