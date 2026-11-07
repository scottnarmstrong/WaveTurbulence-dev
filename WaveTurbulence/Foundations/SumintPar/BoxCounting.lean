/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PredecessorCounting
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-!
# Quantitative count of predecessor localization boxes

Each difference box has half-width `4Λ`. Since `Λ≥1`, its cardinality
is at most `(9Λ)^d`. The product bound in the exact datum then gives
an exponential count in the total number of variables.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- Fixed centers with the source radii give at most `(9^d A^d)^M` labels. -/
theorem source_predecessor_box_count {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ}
    {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (c : D.S.VIdx → Fin d → ℝ) :
    let choices := fun v => Counting.latticeBox (c v) (4 * (D.Λ v : ℝ))
    (predecessorLabelSet D.prev choices).Finite ∧
      ((predecessorLabelSet D.prev choices).ncard : ℝ) ≤
        ((9 : ℝ)^d * A^d)^D.S.M := by
  classical
  dsimp only
  obtain ⟨hf, hc⟩ := source_predecessor_labels_count D hD
    (fun v => Counting.latticeBox (c v) (4 * (D.Λ v : ℝ)))
  refine ⟨hf, ?_⟩
  have hv (v : D.S.VIdx) :
      ((Counting.latticeBox (c v) (4 * (D.Λ v : ℝ))).card : ℝ) ≤
        (9 * (D.Λ v : ℝ))^d := by
    have hΛ : (1 : ℝ) ≤ D.Λ v := by exact_mod_cast hD.2.1 v
    apply (Counting.card_latticeBox_le (c v) (by positivity)).trans
    apply pow_le_pow_left₀ (by positivity)
    linarith
  calc
    _ ≤ ∏ v, ((Counting.latticeBox (c v) (4 * (D.Λ v : ℝ))).card : ℝ) := by
      exact_mod_cast hc
    _ ≤ ∏ v, (9 * (D.Λ v : ℝ))^d :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun v _ => hv v)
    _ = (9 : ℝ)^(d * D.S.M) * (∏ v, (D.Λ v : ℝ))^d := by
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow,
        Finset.prod_const, Finset.card_univ, card_vector_index]
      rw [← pow_mul, Nat.mul_comm D.S.M d]
    _ ≤ (9 : ℝ)^(d * D.S.M) * (A^D.S.M)^d := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hD.2.2.1 d
      · positivity
    _ = _ := by simp only [mul_pow, ← pow_mul, Nat.mul_comm]

end WaveTurbulence.SumintPar
