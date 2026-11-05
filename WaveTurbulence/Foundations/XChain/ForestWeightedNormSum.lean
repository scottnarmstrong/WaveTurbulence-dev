/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestBracketWeightSum
/-! A leaf-envelope bound gives absolute convergence and root-weighted norm control of any forest series. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem norm_tsum_le_of_forest_bracket_bound {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (L b M : ℝ) (hL : 1 ≤ L) (hb : (d : ℝ) + 1 ≤ b)
    (hM : 0 ≤ M) (f : ForestDecoration top d n → ℂ)
    (hf : ∀ κ, ‖f κ‖ ≤ M *
      (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b))) :
    ‖∑' κ, f κ‖ ≤ M * ((2 ^ Fintype.card (GLeaf top) : ℝ) ^ b *
      (∏ j, jbr (latticePoint L (n j))) ^ (-b) *
        (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ^ Fintype.card (GLeaf top)) := by
  have hb0 : 0 ≤ b := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hv := summable_lattice_bracket_weight L (2 * b) hL (by linarith)
  have ht := forest_weight_summable top n (fun m => jbr (latticePoint L m) ^ (-(2 * b))) hv
  have ht' : Summable (fun κ : ForestDecoration top d n =>
      (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b))) := by
    apply ht.congr
    intro κ
    exact Real.finsetProd_rpow univ _ (fun l _ => (jbr_pos _).le) _
  have hs := ht'.mul_left M
  have hnrm : Summable (fun κ => ‖f κ‖) :=
    Summable.of_nonneg_of_le (fun κ => norm_nonneg _) hf hs
  calc
    ‖∑' κ, f κ‖ ≤ ∑' κ, ‖f κ‖ := norm_tsum_le_tsum_norm hnrm
    _ ≤ ∑' κ : ForestDecoration top d n,
        M * (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)) :=
      hnrm.tsum_le_tsum hf hs
    _ = M * ∑' κ : ForestDecoration top d n,
        (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_forest_bracket_weight_le top n L b hL hb) hM

end WaveTurbulence.Induct
