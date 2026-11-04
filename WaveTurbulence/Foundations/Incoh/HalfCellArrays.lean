/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.HalfLinkCellCover

/-!
# Finite arrays of actual half-width link cells

The array weights form an exact smooth partition. On a product of fixed
momentum balls all active array indices lie in a uniformly bounded finite set.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Literal product partition for a finite array of link momenta. -/
@[expose] def halfCellArrayWeight {d : ℕ} {I : Type*} [Fintype I]
    (c : I → Fin d → ℤ) (x : I → Mom d) : ℂ := ∏ i, halfLinkCell (c i) (x i)

/-- Actual finite cover of all half-cells meeting a product of localization balls. -/
@[expose] def halfCellArrayCover {d : ℕ} {I : Type*} [Fintype I]
    (a : I → Mom d) (R : ℝ) : Finset (I → Fin d → ℤ) :=
  by
    classical
    exact Fintype.piFinset (fun i => halfLinkCellCover (a i) R)

/-- Every active array belongs to the explicit finite product cover. -/
theorem mem_halfCellArrayCover {d : ℕ} {I : Type*} [Fintype I]
    {a x : I → Mom d} {R : ℝ} {c : I → Fin d → ℤ}
    (hx : ∀ i, ‖x i - a i‖ ≤ R) (hc : halfCellArrayWeight c x ≠ 0) :
    c ∈ halfCellArrayCover a R := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  exact mem_halfLinkCellCover (hx i) ((Finset.prod_ne_zero_iff.mp hc) i (Finset.mem_univ i))

/-- The array-cell count is exponential only in the actual number of momentum coordinates. -/
theorem card_halfCellArrayCover_le {d : ℕ} {I : Type*} [Fintype I]
    (a : I → Mom d) {R : ℝ} (hR : 0 ≤ R) :
    ((halfCellArrayCover a R).card : ℝ) ≤ ((4 * R + 3) ^ d) ^ Fintype.card I := by
  classical
  rw [halfCellArrayCover, Fintype.card_piFinset, Nat.cast_prod]
  calc
    _ ≤ ∏ _i : I, (4 * R + 3) ^ d := Finset.prod_le_prod₀
      (fun _ _ => Nat.cast_nonneg _) (fun i _ => card_halfLinkCellCover_le (a i) hR)
    _ = _ := by simp

/-- Every finite array of actual half-width profiles sums to one, pointwise. -/
theorem hasSum_halfCellArrayWeight {d : ℕ} {I : Type*} [Fintype I] (x : I → Mom d) :
    HasSum (fun c : I → Fin d → ℤ => halfCellArrayWeight c x) 1 := by
  classical
  let S := Fintype.piFinset (fun i => ApproxNT.thetaSupport ((2 : ℝ) • x i))
  have hz (c : I → Fin d → ℤ) (hc : c ∉ S) : halfCellArrayWeight c x = 0 := by
    have hn : ¬∀ i, c i ∈ ApproxNT.thetaSupport ((2 : ℝ) • x i) := by
      simpa only [S, Fintype.mem_piFinset] using hc
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [halfLinkCell, ApproxNT.thetaMom_sub_eq_zero hi, Complex.ofReal_zero]
  have hs : HasSum (fun c : I → Fin d → ℤ => halfCellArrayWeight c x)
      (∑ c ∈ S, halfCellArrayWeight c x) := hasSum_sum_of_ne_finset_zero hz
  convert hs using 1
  dsimp only [S, halfCellArrayWeight]
  rw [← Finset.prod_univ_sum (fun i => ApproxNT.thetaSupport ((2 : ℝ) • x i))
    (fun i c => halfLinkCell c (x i))]
  symm
  apply Finset.prod_eq_one
  intro i _
  simp_rw [halfLinkCell]
  rw [← Complex.ofReal_sum, ApproxNT.sum_thetaMom, Complex.ofReal_one]

end WaveTurbulence.Incoh
