/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! Positivity and exponent bookkeeping for the exact Japanese bracket in the ansatz. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem one_le_jbr {d : ℕ} (k : Mom d) : 1 ≤ jbr k := by
  have h : (1 : ℝ) ≤ 1 + ‖k‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  simpa only [Real.sqrt_one, jbr] using Real.sqrt_le_sqrt h

theorem jbr_pos {d : ℕ} (k : Mom d) : 0 < jbr k := zero_lt_one.trans_le (one_le_jbr k)

theorem one_le_jbrProd {w d : ℕ} (L : ℝ) (n : Fin w → (Fin d → ℤ)) : 1 ≤ ∏ j, jbr (latticePoint L (n j)) := by
  have h := prod_le_prod₀ (s := (univ : Finset (Fin w))) (f := fun _ => (1 : ℝ))
    (g := fun j => jbr (latticePoint L (n j))) (fun _ _ => zero_le_one)
    (fun j _ => one_le_jbr _)
  simpa only [prod_const_one] using h

theorem jbrProd_pair_rpow_half {d : ℕ} (L : ℝ) (n : Fin 2 → (Fin d → ℤ))
    (hn : n 0 = n 1) (Λ : ℝ) :
    (∏ j, jbr (latticePoint L (n j))) ^ (-Λ / 2) = jbr (latticePoint L (n 0)) ^ (-Λ) := by
  have hj := congrArg (fun m : Fin d → ℤ => jbr (latticePoint L m)) hn.symm
  rw [Fin.prod_univ_two, hj]
  have he : jbr (latticePoint L (n 0)) * jbr (latticePoint L (n 0)) =
      jbr (latticePoint L (n 0)) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
  rw [he, ← Real.rpow_mul (jbr_pos _).le]
  congr 1
  ring

end WaveTurbulence.Induct
