/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BracketWeightSplit
public import WaveTurbulence.Foundations.XChain.ForestWeightSum
/-! Absolute leaf-weight sums retain external momentum decay. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem summable_lattice_bracket_weight {d : ℕ} (L b : ℝ) (hL : 1 ≤ L)
    (hb : (d : ℝ) + 1 ≤ b) :
    Summable (fun n : Fin d → ℤ => jbr (latticePoint L n) ^ (-b)) := by
  apply Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (jbr_pos _).le _)
    (fun n => Real.rpow_le_rpow_of_exponent_le (one_le_jbr _) (neg_le_neg hb))
  exact summable_jbr_rpow_neg hL

theorem tsum_forest_bracket_weight_le {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (L b : ℝ) (hL : 1 ≤ L) (hb : (d : ℝ) + 1 ≤ b) :
    (∑' κ : ForestDecoration top d n,
      (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b))) ≤
      (2 ^ Fintype.card (GLeaf top) : ℝ) ^ b *
        (∏ j, jbr (latticePoint L (n j))) ^ (-b) *
          (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ^ Fintype.card (GLeaf top) := by
  classical
  have hb0 : 0 ≤ b := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  let v : (Fin d → ℤ) → ℝ := fun m => jbr (latticePoint L m) ^ (-b)
  let A : ℝ := (2 ^ Fintype.card (GLeaf top) : ℝ) ^ b *
    (∏ j, jbr (latticePoint L (n j))) ^ (-b)
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd L n)) _)
  have hv : Summable v := summable_lattice_bracket_weight L b hL hb
  have hn : ∀ m, 0 ≤ v m := fun m => Real.rpow_nonneg (jbr_pos _).le _
  have hs := (forest_weight_summable top n v hv).mul_left A
  have hbound (κ : ForestDecoration top d n) := forest_leaf_decay_split top n κ L b hb0
  have hsum : Summable (fun κ : ForestDecoration top d n =>
      (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b))) := by
    exact Summable.of_nonneg_of_le (fun κ => Real.rpow_nonneg
      (prod_nonneg (fun l _ => (jbr_pos _).le)) _) hbound hs
  calc
    _ ≤ ∑' κ : ForestDecoration top d n, A * ∏ l : GLeaf top, v (κ.1 l.toNode) :=
      hsum.tsum_le_tsum hbound hs
    _ = A * ∑' κ : ForestDecoration top d n, ∏ l : GLeaf top, v (κ.1 l.toNode) := tsum_mul_left
    _ ≤ A * (∑' m, v m) ^ Fintype.card (GLeaf top) :=
      mul_le_mul_of_nonneg_left (tsum_forest_weight_le top n v hv hn) hA

end WaveTurbulence.Induct
