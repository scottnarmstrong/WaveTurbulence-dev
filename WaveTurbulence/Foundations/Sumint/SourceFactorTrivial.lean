/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFactorSupport

/-!
# Uniform bounds when exit times fix an oscillatory factor

The positive Fourier endpoint fixes at most two input times. Affected
factors may be estimated by counting their fixed finite lattice support.
These estimates apply to the literal source summands and preserve the
number of momentum inputs in each factor.
-/

public section

namespace WaveTurbulence.Sumint

/-- The number of momentum inputs in a linear, pair or normal factor. -/
@[expose] def factorArity (S : SumintShape) : FactorIdx S → ℕ
  | .inl _ => 1
  | .inr (.inl _) => 2
  | .inr (.inr _) => 3

/-- Multiplying a nonnegative cutoff by the canonical character preserves its modulus. -/
theorem norm_nonneg_mul_fourierChar {c : ℝ} (hc : 0 ≤ c) (θ : ℝ) :
    ‖(c:ℂ)*(Real.fourierChar θ:ℂ)‖ = c := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc,Circle.norm_coe,mul_one]

/-- Every literal factor summand has modulus at most one. -/
theorem norm_sourceFactorTerm_le_one {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (a : FactorIdx D.S) (n : FactorInput D.S (Fin d → ℤ) a) :
    ‖sourceFactorTerm D L γ δ p ν r t τ a n‖ ≤ 1 := by
  rcases a with i | (a | i)
  · change ‖linearFactorTerm D L γ δ p ν r t τ i n‖ ≤ 1
    unfold linearFactorTerm
    rw [norm_nonneg_mul_fourierChar (inputCutoff_nonneg _ _)]
    exact inputCutoff_le_one _ _
  · change ‖pairFactorTerm D L γ δ p ν r t τ a n‖ ≤ 1
    unfold pairFactorTerm
    dsimp only
    rw [norm_nonneg_mul_fourierChar (mul_nonneg (inputCutoff_nonneg _ _) (inputCutoff_nonneg _ _))]
    exact (mul_le_mul (inputCutoff_le_one _ _) (inputCutoff_le_one _ _)
      (inputCutoff_nonneg _ _) zero_le_one).trans_eq (one_mul 1)
  · change ‖normalFactorTerm D L γ δ p ν r t τ i n‖ ≤ 1
    unfold normalFactorTerm
    dsimp only
    rw [norm_nonneg_mul_fourierChar (Finset.prod_nonneg (fun _ _ => inputCutoff_nonneg _ _))]
    exact Finset.prod_le_one₀ (fun _ _ => inputCutoff_nonneg _ _) (fun _ _ => inputCutoff_le_one _ _)

/-- Each factor support has the correct input-count exponent. -/
theorem card_sourceFactorSupport_le {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 ≤ L)
    (p : D.S.VIdx → Fin d → ℝ) (a : FactorIdx D.S) :
    ((sourceFactorSupport D L p a).card : ℝ) ≤ (8*L+1)^(d*factorArity D.S a) := by
  classical
  have hbox (q : Fin d → ℝ) :
      ((Counting.latticeBox (fun j => L*q j) (4*L)).card:ℝ) ≤ (8*L+1)^d := by
    simpa only [show 2*(4*L)+1 = 8*L+1 by ring] using
      Counting.card_latticeBox_le (fun j => L*q j) (by positivity : 0 ≤ 4*L)
  rcases a with i | (a | i)
  · change ((Counting.latticeBox (fun j => L*p (D.S.x0Slot i) j) (4*L)).card:ℝ) ≤
        (8*L+1)^(d*1)
    simpa only [Nat.mul_one] using hbox (p (D.S.x0Slot i))
  · change (((Counting.latticeBox (fun j => L*p (D.S.xSlot a.1 a.2) j) (4*L)).product
        (Counting.latticeBox (fun j => L*p (D.S.ySlot a.1 a.2) j) (4*L))).card:ℝ) ≤
        (8*L+1)^(d*2)
    have hc := Finset.card_product
      (Counting.latticeBox (fun j => L*p (D.S.xSlot a.1 a.2) j) (4*L))
      (Counting.latticeBox (fun j => L*p (D.S.ySlot a.1 a.2) j) (4*L))
    change ((Counting.latticeBox (fun j => L*p (D.S.xSlot a.1 a.2) j) (4*L)).product
      (Counting.latticeBox (fun j => L*p (D.S.ySlot a.1 a.2) j) (4*L))).card = _ at hc
    rw [hc,Nat.cast_mul,pow_mul,pow_two]
    exact mul_le_mul (hbox _) (hbox _) (Nat.cast_nonneg _) (by positivity)
  · change ((inputCutoffBox L (fun j => p (D.S.uSlot i.1 i.2 j))).card:ℝ) ≤ (8*L+1)^(d*3)
    simpa only [Fintype.card_fin] using card_inputCutoffBox_le hL (fun j => p (D.S.uSlot i.1 i.2 j))

/-- A uniform trivial bound on any actual source factor, even with all its times fixed. -/
theorem norm_tsum_sourceFactorTerm_le {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (a : FactorIdx D.S) :
    ‖∑' n : FactorInput D.S (Fin d → ℤ) a, sourceFactorTerm D L γ δ p ν r t τ a n‖ ≤
      (8*L+1)^(d*factorArity D.S a) := by
  classical
  rw [tsum_eq_sum (s := sourceFactorSupport D L p a)
    (fun n hn => sourceFactorTerm_eq_zero_of_not_support D hL γ δ p ν r t τ a n hn)]
  calc
    _ ≤ ∑ n ∈ sourceFactorSupport D L p a, ‖sourceFactorTerm D L γ δ p ν r t τ a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ sourceFactorSupport D L p a, (1:ℝ) :=
      Finset.sum_le_sum (fun n _ => norm_sourceFactorTerm_le_one D L γ δ p ν r t τ a n)
    _ = ((sourceFactorSupport D L p a).card:ℝ) := by simp
    _ ≤ _ := card_sourceFactorSupport_le D hL.le p a

end WaveTurbulence.Sumint
