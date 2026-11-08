/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkAsm.Helpers

/-! # A5 MK-ASM: product of component bounds over one structure. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkAsm

variable {P : WTParams} {p : ℕ} {t s b : ℝ}

/-- The product of the component bounds over the components of one structure: the `L`-exponent adds to
`B d (4Pm)`, the orders to `N`, and the gains multiply. -/
theorem norm_prod_val_le {B : ℝ} {Pm : ℕ} (hM : MarkedComponentBoundAtI B Pm P)
    (hγ : 1 / 2 < P.γ) (hp : p < P.D) (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t)
    (hb : 1 ≤ b) (hL : 0 < P.L) (hδ : 0 < P.δ) {m N : ℕ} (D : Fin m → CompData P p t s b)
    (hR : ∑ c, 2 * (D c).R = 4 * Pm) (hn : ∑ c, (D c).n = N) (hN : N ≤ P.N (p + 1) ^ 4) :
    ‖∏ c, (D c).val‖ ≤
      P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N * ∏ c, (D c).gain := by
  rw [norm_prod]
  have hc : ∀ c, ‖(D c).val‖ ≤ P.L ^ (B * P.d * (2 * (D c).R : ℕ)) * P.δ ^ (7 * P.ν * (D c).n) *
      b ^ (D c).n * (D c).gain := by
    intro c
    have h2 : (D c).R ≤ 2 * Pm := by
      have := Finset.single_le_sum (f := fun c => 2 * (D c).R) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    have h3 : (D c).n ≤ P.N (p + 1) ^ 4 := by
      have := Finset.single_le_sum (f := fun c => (D c).n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    exact CompData.norm_val_le hM hγ hp ht hs hb (D c) h2 h3
  have hprod : ∏ c, ‖(D c).val‖ ≤ ∏ c, (P.L ^ (B * P.d * (2 * (D c).R : ℕ)) * P.δ ^ (7 * P.ν * (D c).n) *
      b ^ (D c).n * (D c).gain) :=
    Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) (fun c _ => hc c)
  refine hprod.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← Real.rpow_sum_of_pos hL, ← Real.rpow_sum_of_pos hδ, Finset.prod_pow_eq_pow_sum, hn]
  congr 3
  · rw [← Finset.mul_sum]
    congr 1
    have : ((∑ c, 2 * (D c).R : ℕ) : ℝ) = ((4 * Pm : ℕ) : ℝ) := by rw [hR]
    rw [← this]
    push_cast
    rfl
  · rw [← Finset.mul_sum]
    congr 1
    have : ((∑ c, (D c).n : ℕ) : ℝ) = (N : ℝ) := by rw [hn]
    rw [← this]
    push_cast
    rfl

end WaveTurbulence.Flower.MkAsm
