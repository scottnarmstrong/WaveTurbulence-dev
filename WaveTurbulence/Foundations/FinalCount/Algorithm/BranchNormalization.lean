/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.RankSizeComparison
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Termination
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalizationRescale
import Mathlib.Tactic

/-! # The source C-plus normalization absorbs all binary graph choices -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm

private theorem binary_factor_identity (E : ℕ) (χ : ℤ) :
    (1/4 : ℝ)^χ*(2 : ℝ)^E = (2 : ℝ)^((E : ℤ)-2*χ) := by
  have hs : (1/4 : ℝ) = (2 : ℝ)^(-2 : ℤ) := by norm_num
  rw [hs,← zpow_mul,← zpow_natCast,← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

private theorem four_power_identity (w : ℕ) :
    (4 : ℝ)^(2*w) = (2 : ℝ)^(4*(w : ℤ)) := by
  rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num,← pow_mul]
  have he : 2*(2*w) = 4*w := by omega
  rw [he]
  simpa only [Int.natCast_mul,Nat.cast_ofNat] using (zpow_natCast (2 : ℝ) (4*w)).symm

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Raising C-plus by a factor four pays the entire 2^E choice-tree bound,
with an explicit remainder 4^(2w) at the non-degree-four atoms. -/
theorem branch_factor_le_nonFour (M : Molecule V D) (hM : M.IsMolecule)
    (w : ℕ) (hw : (M.atoms.filter (fun a => M.deg a ≠ 4)).card ≤ w) :
    (1/4 : ℝ)^M.circuitRank*(2 : ℝ)^M.bonds.card ≤ (4 : ℝ)^(2*w) := by
  have hV := atoms_le_rank_add_two_mul_of_nonFour_le M hM w hw
  have hE : M.bonds.card ≤ 2*M.atoms.card := (ofMolecule M).bonds_le_two_mul_atoms hM
  have he : (M.bonds.card : ℤ)-2*M.circuitRank ≤ 4*(w : ℤ) := by omega
  rw [binary_factor_identity,four_power_identity]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he

/-- For either dense input in DH23 Prop 10.2, the source circuit rank
absorbs every binary choice with no residual size-dependent factor. -/
theorem branch_factor_le_one_dense (M : Molecule V D)
    (hne : M.atoms.Nonempty) (hc : ∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b)
    (hE : 2*(M.atoms.card : ℤ)-2 ≤ M.bonds.card) :
    (1/4 : ℝ)^M.circuitRank*(2 : ℝ)^M.bonds.card ≤ 1 := by
  have hF := numComponents_eq_one M hne hc
  have he : (M.bonds.card : ℤ)-2*M.circuitRank ≤ 0 := by
    unfold Molecule.circuitRank
    rw [hF]
    omega
  rw [binary_factor_identity]
  simpa only [zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he

end WaveTurbulence.Mole.AppbAlgorithm
