/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestRootWeights
/-! Split the input decay between external root weights and an absolutely summable leaf envelope. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem rpow_neg_split_le {X Y K b : ℝ} (hX : 0 < X) (hY : 0 < Y) (hK : 0 < K)
    (hb : 0 ≤ b) (h : X ≤ K * Y) :
    Y ^ (-(2 * b)) ≤ K ^ b * X ^ (-b) * Y ^ (-b) := by
  have hp : X ^ b ≤ K ^ b * Y ^ b := by
    simpa only [Real.mul_rpow hK.le hY.le] using Real.rpow_le_rpow hX.le h hb
  have hd : (Y ^ b)⁻¹ ≤ K ^ b * (X ^ b)⁻¹ := by
    have he : (1 : ℝ) / Y ^ b ≤ K ^ b / X ^ b :=
      (div_le_div_iff₀ (Real.rpow_pos_of_pos hY b) (Real.rpow_pos_of_pos hX b)).mpr (by simpa using hp)
    simpa only [one_div, div_eq_mul_inv, one_mul] using he
  have hpow : Y ^ (-(2 * b)) = Y ^ (-b) * Y ^ (-b) := by
    rw [← Real.rpow_add hY]
    congr 1
    ring
  rw [hpow]
  simpa only [Real.rpow_neg hY.le, Real.rpow_neg hX.le, mul_assoc] using
    mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr (Real.rpow_nonneg hY.le b))

theorem forest_leaf_decay_split {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) (L b : ℝ) (hb : 0 ≤ b) :
    (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)) ≤
      (2 ^ Fintype.card (GLeaf top) : ℝ) ^ b *
        (∏ j, jbr (latticePoint L (n j))) ^ (-b) *
          ∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode)) ^ (-b) := by
  have hy : 0 < ∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode)) :=
    prod_pos (fun l _ => jbr_pos _)
  have hx : 0 < ∏ j, jbr (latticePoint L (n j)) := zero_lt_one.trans_le (one_le_jbrProd L n)
  have h := rpow_neg_split_le hx hy (by positivity) hb (forest_roots_jbr_le top n κ L)
  have he := Real.finsetProd_rpow (univ : Finset (GLeaf top))
    (fun l => jbr (latticePoint L (κ.1 l.toNode))) (fun l _ => (jbr_pos _).le) (r := -b)
  rw [← he] at h
  exact h

end WaveTurbulence.Induct
