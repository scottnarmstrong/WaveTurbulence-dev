/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairWeights
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FourLabelScalar
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FiveLabelScalar
import Mathlib.Tactic

/-! # Exact normalization ratio at an affected double-rung position -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ladderWeight_one_le {L γ δ P : ℝ} (hL : 0 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : 0 ≤ δ) (hP : 0 ≤ P) : 1 ≤ Molecule.ladderWeight L γ δ P := by
  unfold Molecule.ladderWeight
  apply le_min
  · nlinarith only [hlog]
  · have ht := mul_nonneg (mul_nonneg hδ (Real.rpow_nonneg hL (2*γ))) hP
    linarith only [ht]

theorem freeNormalization_double_pair_ratio (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (hdeg : M.deg a = 3) (hdouble : M.bondsBetween a b = 2)
    {S : Finset V} (hS : S ∈ ladderCells M) (haS : a ∈ S)
    {d : ℕ} {L γ δ C1 : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1)
    (hlog : 0 < Real.log L^2) (P : Finset V → ℝ) (hP : ∀ T ∈ ladderCells M, 0 ≤ P T) :
    freeNormalization M (d := d) L γ δ C1 P /
      freeNormalization (Degen.eraseAtoms M {a,b}) (d := d) L γ δ C1 P =
    L^(-((d : ℝ)-γ)*((M.circuitRank-(Degen.eraseAtoms M {a,b}).circuitRank : ℤ) : ℝ)) *
      (C1⁻¹*δ^(1/2 : ℝ))^(M.circuitRank-(Degen.eraseAtoms M {a,b}).circuitRank) *
      Molecule.ladderWeight L γ δ (P S) := by
  have hpost := cellProduct_pos (Degen.eraseAtoms M {a,b}) (γ := γ) hL.le hδ.le hlog P
    (nonnegative_scales_erase M {a,b} P hP)
  have hW : cellProduct M L γ δ P / cellProduct (Degen.eraseAtoms M {a,b}) L γ δ P =
      Molecule.ladderWeight L γ δ (P S) := by
    apply (div_eq_iff hpost.ne').mpr
    rw [cellProduct_double_pair_eq M hM hab hdeg hdouble hS haS]
    ring
  unfold freeNormalization
  rw [Degen.circuit_normalization_ratio hL (by positivity : C1⁻¹*δ^(1/2 : ℝ) ≠ 0) hpost.ne',hW]

end WaveTurbulence.MoleProp
