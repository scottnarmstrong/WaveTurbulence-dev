/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ShapeFacts
import Mathlib.Tactic

/-!
# Counting case (d) blocks against the drafted weight multiplicity

Each such block contains a weight with positive exponent. The block
indices are disjoint, so the same unit of multiplicity is never spent
on two distinct bad blocks.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- Weight multiplicity inside one source block. -/
@[expose] def blockMultiplicity {d : ℕ} (D : SumintDatum d) (i : Fin D.S.I) : ℕ :=
  ∑ j : Fin (D.S.n i), (D.g ⟨i, j⟩ + D.g' ⟨i, j⟩)

/-- Summing block multiplicities gives exactly `M₁`. -/
theorem sum_blockMultiplicity {d : ℕ} (D : SumintDatum d) :
    ∑ i, blockMultiplicity D i = D.M₁ := by
  simp only [blockMultiplicity, SumintDatum.M₁, Fintype.sum_sigma]

/-- A case (d) block contains at least one unit of the drafted multiplicity. -/
theorem one_le_blockMultiplicity_of_case_d {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (i : Fin D.S.I) (hi : D.S.nor i = false) (hd : D.badKind i = 3) :
    1 ≤ blockMultiplicity D i := by
  obtain ⟨j, hj⟩ := (hD.2.2.2.2.2.2.2.2.2 i hi).2.2 hd
  have hh : 1 ≤ D.g ⟨i, j⟩ + D.g' ⟨i, j⟩ := by omega
  change 1 ≤ ∑ k : Fin (D.S.n i), (D.g ⟨i, k⟩ + D.g' ⟨i, k⟩)
  apply hh.trans
  exact Finset.single_le_sum (f := fun k : Fin (D.S.n i) => D.g ⟨i, k⟩ + D.g' ⟨i, k⟩)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

/-- The number of case (d) blocks is at most the available weight multiplicity. -/
theorem card_case_d_le_M₁ {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps) :
    (Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 3)).card ≤ D.M₁ := by
  classical
  rw [← sum_blockMultiplicity D, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact one_le_blockMultiplicity_of_case_d D hD i hi.1 hi.2
  · exact Nat.zero_le _

end WaveTurbulence.Sumint
