/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadder
public import WaveTurbulence.Foundations.FinalCount.Degen.NormalizationFactors
import Mathlib.Tactic

/-! # Exact normalization for the adopted selected-ladder source reading -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def sourceNormalizationFactor (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ)
    (P : Finset V → ℝ) : ℝ :=
  L ^ (-((d : ℝ) - γ) * M.circuitRank) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
    sourceLadderProduct M L γ δ P

theorem sourceLadderProduct_pos (M : Molecule V D) {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hlog : 0 < Real.log L ^ 2) (P : Finset V → ℝ) (hP : ∀ S ∈ sourceMaximalLadders M, 0 ≤ P S) :
    0 < sourceLadderProduct M L γ δ P := by
  unfold sourceLadderProduct
  apply prod_pos
  intro S hS
  apply pow_pos
  unfold Molecule.ladderWeight
  apply lt_min hlog
  have hterm := mul_nonneg (mul_nonneg hδ (Real.rpow_nonneg hL (2 * γ))) (hP S hS)
  linarith only [hterm]

theorem sourceNormalizationFactor_pos (M : Molecule V D) {d : ℕ} {L γ δ C1 : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) (hlog : 0 < Real.log L ^ 2)
    (P : Finset V → ℝ) (hP : ∀ S ∈ sourceMaximalLadders M, 0 ≤ P S) :
    0 < sourceNormalizationFactor M (d := d) L γ δ C1 P := by
  unfold sourceNormalizationFactor
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hL _)
    (zpow_pos (by positivity : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ)) _)) (sourceLadderProduct_pos M hL.le hδ.le hlog P hP)

theorem sourceCountA_eq_normalization (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    sourceCountA M L γ δ C1 w Adm P =
      (M.countE L γ δ w Adm : ℝ≥0∞) * ENNReal.ofReal (sourceNormalizationFactor M (d := d) L γ δ C1 P) := rfl

/-- The exact actual normalized deletion ratio. No comparison of ladder
products or post-count is assumed; both are actual proved source quantities. -/
theorem sourceCountA_erase_constant_le_ratio (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} {L γ δ C1 : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1)
    (hlog : 0 < Real.log L ^ 2) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    {v : V} {e : D} (he : M.atom e = v) (hconstant : ∀ κ, Adm κ → ConstantAt M κ v)
    (Ppre Ppost : Finset V → ℝ)
    (hPpre : ∀ S ∈ sourceMaximalLadders M, 0 ≤ Ppre S)
    (hPpost : ∀ S ∈ sourceMaximalLadders (eraseAtoms M {v}), 0 ≤ Ppost S) :
    sourceCountA M L γ δ C1 w Adm Ppre ≤
      ENNReal.ofReal ((⌈(2 * L + 1) ^ d⌉₊ : ℝ) * sourceNormalizationFactor M (d := d) L γ δ C1 Ppre /
        sourceNormalizationFactor (eraseAtoms M {v}) (d := d) L γ δ C1 Ppost) *
      sourceCountA (eraseAtoms M {v}) L γ δ C1 w (eraseAdmissibility M {v} Adm) Ppost := by
  rw [sourceCountA_eq_normalization, sourceCountA_eq_normalization]
  exact normalized_count_mono (countE_erase_constant_atom_le M hM hL γ δ w Adm he hconstant)
    (sourceNormalizationFactor_pos M hL hδ hC hlog Ppre hPpre).le
    (sourceNormalizationFactor_pos (eraseAtoms M {v}) hL hδ hC hlog Ppost hPpost)

/-- The fixed-root branch retains its exact normalization without a
common-choice factor. Subsequent geometric comparison supplies its gain. -/
theorem sourceCountA_erase_fixed_le_ratio (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} {L γ δ C1 : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1)
    (hlog : 0 < Real.log L ^ 2) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    {v : V} {e : D} (he : M.atom e = v) (q : Fin d → ℤ)
    (hconstant : ∀ κ, Adm κ → ConstantAt M κ v) (hfixed : ∀ κ, Adm κ → κ e = q)
    (Ppre Ppost : Finset V → ℝ)
    (hPpre : ∀ S ∈ sourceMaximalLadders M, 0 ≤ Ppre S)
    (hPpost : ∀ S ∈ sourceMaximalLadders (eraseAtoms M {v}), 0 ≤ Ppost S) :
    sourceCountA M L γ δ C1 w Adm Ppre ≤
      ENNReal.ofReal (sourceNormalizationFactor M (d := d) L γ δ C1 Ppre /
        sourceNormalizationFactor (eraseAtoms M {v}) (d := d) L γ δ C1 Ppost) *
      sourceCountA (eraseAtoms M {v}) L γ δ C1 w (eraseAdmissibility M {v} Adm) Ppost := by
  rw [sourceCountA_eq_normalization, sourceCountA_eq_normalization]
  have hc := countE_erase_prescribed_label_le M hM L γ δ w Adm he q hconstant hfixed
  have hc' : M.countE L γ δ w Adm ≤ (1 : ℕ) *
      (eraseAtoms M {v}).countE L γ δ w (eraseAdmissibility M {v} Adm) := by simpa only [Nat.cast_one, one_mul] using hc
  simpa only [Nat.cast_one, one_mul] using normalized_count_mono hc'
    (sourceNormalizationFactor_pos M hL hδ hC hlog Ppre hPpre).le
    (sourceNormalizationFactor_pos (eraseAtoms M {v}) hL hδ hC hlog Ppost hPpost)

end WaveTurbulence.Degen
