/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.BoundCount
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Total
/-! FLOWER-P7: the piece bounds `Bound6`, `Bound42`, `Bound24` are at most (data count) times a power of `δ`
times the label weights `Wt6`, `Wt42`, `Wt24m`, `Wt24irr`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

/-- The numerical hypotheses of the weight bounds. -/
structure BoundNum (P : WTParams) (Creg : ℕ → ℝ) (Cr : ℝ) : Prop where
  hδ0 : 0 < P.δ
  hδ1 : P.δ ≤ 1
  hL : 1 ≤ P.L
  hν : 0 ≤ P.ν
  hν8 : 2 * P.ν ≤ 1 / 4
  hCr0 : 0 ≤ Cr
  hCreg : ∀ e, Creg e ≤ Cr
  hCreg0 : ∀ e, 0 ≤ Creg e
  hγ : P.γ ≤ P.d

section weights
variable {d : ℕ}

/-- The weight of a couple block with equal root labels. -/
noncomputable def Wcp (L : ℝ) (k : Mom d) (a : ℝ) (n0 n1 : Fin d → ℤ) : ℝ :=
  open scoped Classical in if n0 = n1 then gw L k a n0 else 0

noncomputable def Wt6 (L : ℝ) (k : Mom d) (a : ℝ) (n : Fin (2 * 3) → Fin d → ℤ) : ℝ := ∏ j, gw L k a (n j)

noncomputable def Wt42 (L : ℝ) (k : Mom d) (a : ℝ) (σ : Fin (2 * 2) ⊕ Fin 2 ≃ Fin (2 * 3)) (n : Fin (2 * 3) → Fin d → ℤ) : ℝ :=
  (∏ i : Fin (2 * 2), gw L k a (n (σ (.inl i)))) * Wcp L k a (n (σ (.inr 0))) (n (σ (.inr 1)))

noncomputable def Wt24irr (L : ℝ) (k : Mom d) (a : ℝ) (σ : Fin 2 ⊕ Fin (2 * 2) ≃ Fin (2 * 3)) (n : Fin (2 * 3) → Fin d → ℤ) : ℝ :=
  Wcp L k a (n (σ (.inl 0))) (n (σ (.inl 1))) * ∏ i : Fin (2 * 2), gw L k a (n (σ (.inr i)))

noncomputable def Wt24m (L : ℝ) (k : Mom d) (a : ℝ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin (2 * 2)) (σ : Fin 2 ⊕ Fin (2 * 2) ≃ Fin (2 * 3))
    (n : Fin (2 * 3) → Fin d → ℤ) : ℝ :=
  Wcp L k a (n (σ (.inl 0))) (n (σ (.inl 1))) *
    (Wcp L k a (n (σ (.inr (τ (.inl 0))))) (n (σ (.inr (τ (.inl 1))))) *
      Wcp L k a (n (σ (.inr (τ (.inr 0))))) (n (σ (.inr (τ (.inr 1))))))

theorem Wcp_nonneg (L : ℝ) (k : Mom d) (a : ℝ) (n0 n1 : Fin d → ℤ) : 0 ≤ Wcp L k a n0 n1 := by
  unfold Wcp; split_ifs
  · exact gw_nonneg _ _ _ _
  · exact le_rfl

theorem prod_gw_nonneg (L : ℝ) (k : Mom d) (a : ℝ) {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℤ) :
    0 ≤ ∏ i ∈ s, gw L k a (f i) := Finset.prod_nonneg fun _ _ => gw_nonneg _ _ _ _

theorem jbrProdAt_rpow (L : ℝ) (k : Mom d) {w : ℕ} (n : Fin w → Fin d → ℤ) (a : ℝ) :
    jbrProdAt L k n ^ (-a) = ∏ j, gw L k a (n j) := by
  unfold jbrProdAt gw
  rw [← Real.finset_prod_rpow _ _ (fun j _ => (WaveTurbulence.Induct.jbr_pos _).le)]

end weights

section bounds
variable {P : WTParams} {Creg : ℕ → ℝ} {Cr : ℝ}

theorem delta_pow_mul (hδ0 : 0 < P.δ) (x y : ℝ) : P.δ ^ x * P.δ ^ y = P.δ ^ (x + y) :=
  (Real.rpow_add hδ0 x y).symm

/-- The couple bracket is at most `(1 + Cr) δ^{2νe}`. -/
theorem bracket_le (hb : BoundNum P Creg Cr) (p : ℕ) (e : ℕ) :
    P.δ ^ (2 * P.ν * e) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
      Creg e * P.δ ^ ((e : ℝ) / 4) ≤ (1 + Cr) * P.δ ^ (2 * P.ν * e) := by
  have hLt : P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hb.hL (by
      have := theta_nonneg P (p + 1); have := theta_nonneg P p; linarith)
  have hX : 0 ≤ P.δ ^ (2 * P.ν * (e : ℝ)) := Real.rpow_nonneg hb.hδ0.le _
  have h1 : P.δ ^ (2 * P.ν * (e : ℝ)) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) ≤
      P.δ ^ (2 * P.ν * (e : ℝ)) := mul_le_of_le_one_right hX hLt
  have h2 : P.δ ^ ((e : ℝ) / 4) ≤ P.δ ^ (2 * P.ν * (e : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hb.hδ0 hb.hδ1 (by
      have : (0:ℝ) ≤ e := Nat.cast_nonneg e
      nlinarith [hb.hν8])
  have h3 : Creg e * P.δ ^ ((e : ℝ) / 4) ≤ Cr * P.δ ^ (2 * P.ν * (e : ℝ)) :=
    mul_le_mul (hb.hCreg e) h2 (Real.rpow_nonneg hb.hδ0.le _) hb.hCr0
  nlinarith

/-- A couple factor. -/
theorem cplFactor_le (hb : BoundNum P Creg Cr) (p : ℕ) (e : ℕ) (n0 n1 : Fin P.d → ℤ) (k : Mom P.d) :
    (open scoped Classical in
      if n0 = n1 then jbr (k + latticePoint P.L n0) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
        (P.δ ^ (2 * P.ν * e) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
          Creg e * P.δ ^ ((e : ℝ) / 4)) else 0) ≤
      (1 + Cr) * P.δ ^ (2 * P.ν * e) * Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) n0 n1 := by
  classical
  unfold Wcp
  split_ifs with h
  · subst h
    have := bracket_le hb p e
    have hg := gw_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) n0
    unfold gw at hg ⊢
    nlinarith [mul_le_mul_of_nonneg_left this hg]
  · simp [mul_zero]

/-- The couple factor is nonnegative. -/
theorem cplFactor_nonneg (hb : BoundNum P Creg Cr) (p : ℕ) (e : ℕ) (n0 n1 : Fin P.d → ℤ) (k : Mom P.d) :
    0 ≤ (open scoped Classical in
      if n0 = n1 then jbr (k + latticePoint P.L n0) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
        (P.δ ^ (2 * P.ν * e) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
          Creg e * P.δ ^ ((e : ℝ) / 4)) else 0) := by
  classical
  split_ifs
  · have h1 : 0 ≤ jbr (k + latticePoint P.L n0) ^ (-(4 * P.Lambda (p + 1) : ℝ)) := Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos _).le _
    have h2 : 0 ≤ P.δ ^ (2 * P.ν * (e : ℝ)) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
        Creg e * P.δ ^ ((e : ℝ) / 4) :=
      add_nonneg (mul_nonneg (Real.rpow_nonneg hb.hδ0.le _) (Real.rpow_nonneg (by linarith [hb.hL]) _))
        (mul_nonneg (hb.hCreg0 e) (Real.rpow_nonneg hb.hδ0.le _))
    exact mul_nonneg h1 h2
  · exact le_rfl

end bounds

end WaveTurbulence.FlowerP7
