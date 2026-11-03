/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Trilinear

/-!
# The weighted tame estimate with leaf-count weights

For the Taylor coefficients of (WKE) the large weight `(1 + |k|)^w` (`w` up to `4Λ`) must be split
among the three inputs of `𝒦` **without** a factor `3^w` per application (which would make the
geometric base of (taylorbound) depend on `Λ`, FINDINGS F10). We split it with weights `mᵢ > 0`
(in the application, `mᵢ = 2nᵢ + 1` is the number of leaves of the `i`-th subtree):

`(x₁ + x₂ + x₃)^w ≤ m^w ((x₁/m₁)^w + (x₂/m₂)^w + (x₃/m₃)^w)`, `m = m₁ + m₂ + m₃`

(`add_add_rpow_le_weighted`, a max argument valid for every real `w ≥ 0`). Only the fixed low
weight `s₀` is split with the factor `3^{s₀}`. The result (`abs_collisionTerm_le_weighted`):
if `(1+|y|)^{w+s₀} |gᵢ(y)| ≤ mᵢ^w hᵢ` and `(1+|y|)^{s₀} |gᵢ(y)| ≤ Lᵢ`, then

`(1+|k|)^{w+s₀} |𝒦ⱼ(g₁,g₂,g₃)(k)| ≤ 3 · 3^{s₀} · tameConst d s₀ · m^w (h₁L₂L₃ + L₁h₂L₃ + L₁L₂h₃)`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace WaveTurbulence

variable {d : ℕ}

/-- Leaf-count weight splitting: `(x₁+x₂+x₃)^w ≤ m^w Σᵢ (xᵢ/mᵢ)^w`, `m = Σ mᵢ`. -/
theorem add_add_rpow_le_weighted {x₁ x₂ x₃ m₁ m₂ m₃ w : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hx₃ : 0 ≤ x₃) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hw : 0 ≤ w) :
    (x₁ + x₂ + x₃) ^ w ≤
      (m₁ + m₂ + m₃) ^ w * ((x₁ / m₁) ^ w + (x₂ / m₂) ^ w + (x₃ / m₃) ^ w) := by
  have q₁ : 0 ≤ x₁ / m₁ := div_nonneg hx₁ hm₁.le
  have q₂ : 0 ≤ x₂ / m₂ := div_nonneg hx₂ hm₂.le
  have q₃ : 0 ≤ x₃ / m₃ := div_nonneg hx₃ hm₃.le
  have r₁ := Real.rpow_nonneg q₁ w; have r₂ := Real.rpow_nonneg q₂ w
  have r₃ := Real.rpow_nonneg q₃ w
  have key : ∀ q, 0 ≤ q → x₁ / m₁ ≤ q → x₂ / m₂ ≤ q → x₃ / m₃ ≤ q →
      q ^ w ≤ (x₁ / m₁) ^ w + (x₂ / m₂) ^ w + (x₃ / m₃) ^ w →
      (x₁ + x₂ + x₃) ^ w ≤
        (m₁ + m₂ + m₃) ^ w * ((x₁ / m₁) ^ w + (x₂ / m₂) ^ w + (x₃ / m₃) ^ w) := by
    intro q hq h₁ h₂ h₃ hqw
    have e₁ : x₁ ≤ m₁ * q := by rw [div_le_iff₀ hm₁] at h₁; linarith
    have e₂ : x₂ ≤ m₂ * q := by rw [div_le_iff₀ hm₂] at h₂; linarith
    have e₃ : x₃ ≤ m₃ * q := by rw [div_le_iff₀ hm₃] at h₃; linarith
    calc (x₁ + x₂ + x₃) ^ w ≤ ((m₁ + m₂ + m₃) * q) ^ w :=
          Real.rpow_le_rpow (by positivity) (by linarith) hw
      _ = (m₁ + m₂ + m₃) ^ w * q ^ w := Real.mul_rpow (by positivity) hq
      _ ≤ _ := mul_le_mul_of_nonneg_left hqw (by positivity)
  rcases le_total (x₂ / m₂) (x₁ / m₁) with a | a <;>
    rcases le_total (x₃ / m₃) (x₁ / m₁) with b | b <;>
    rcases le_total (x₃ / m₃) (x₂ / m₂) with c | c
  all_goals first
    | exact key (x₁ / m₁) q₁ le_rfl (by linarith) (by linarith) (by linarith)
    | exact key (x₂ / m₂) q₂ (by linarith) le_rfl (by linarith) (by linarith)
    | exact key (x₃ / m₃) q₃ (by linarith) (by linarith) le_rfl (by linarith)

section Weighted

variable {g₁ g₂ g₃ : Mom d → ℝ} {h₁ h₂ h₃ L₁ L₂ L₃ m₁ m₂ m₃ w s₀ : ℝ}

/-- The high-weight hypothesis `(1 + |y|)^{w+s₀} |g(y)| ≤ mᵂ h`. -/
@[expose] def HighBound (w s₀ μ h : ℝ) (g : Mom d → ℝ) : Prop :=
  ∀ y, (1 + ‖y‖) ^ (w + s₀) * |g y| ≤ μ ^ w * h

theorem HighBound.nonneg {w s₀ μ h : ℝ} {g : Mom d → ℝ} (hμ : 0 < μ)
    (hb : HighBound w s₀ μ h g) : 0 ≤ h := by
  have := (mul_nonneg (by positivity) (abs_nonneg _)).trans (hb 0)
  exact (mul_nonneg_iff_of_pos_left (Real.rpow_pos_of_pos hμ w)).mp this

theorem HighBound.div_mul_le {w s₀ μ h : ℝ} {g : Mom d → ℝ} (hμ : 0 < μ)
    (hb : HighBound w s₀ μ h g) (y : Mom d) :
    ((1 + ‖y‖) / μ) ^ w * (1 + ‖y‖) ^ s₀ * |g y| ≤ h := by
  have hy : 0 < 1 + ‖y‖ := by positivity
  have e : ((1 + ‖y‖) / μ) ^ w * (1 + ‖y‖) ^ s₀ * |g y| =
      ((1 + ‖y‖) ^ (w + s₀) * |g y|) / μ ^ w := by
    rw [Real.div_rpow hy.le hμ.le, Real.rpow_add hy]; field_simp
  rw [e, div_le_iff₀ (Real.rpow_pos_of_pos hμ w)]
  linarith [hb y]

theorem HighBound.div_le {w s₀ μ h : ℝ} {g : Mom d → ℝ} (hμ : 0 < μ)
    (hb : HighBound w s₀ μ h g) (y : Mom d) :
    ((1 + ‖y‖) / μ) ^ w * |g y| ≤ h * wt s₀ y := by
  have hy : 0 < 1 + ‖y‖ := by positivity
  have e : ((1 + ‖y‖) / μ) ^ w * |g y| =
      (((1 + ‖y‖) / μ) ^ w * (1 + ‖y‖) ^ s₀ * |g y|) * wt s₀ y := by
    unfold wt; rw [Real.rpow_neg hy.le]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right (hb.div_mul_le hμ y) (wt_nonneg _ _)

theorem HighBound.at_le {w s₀ μ m h : ℝ} {g : Mom d → ℝ} (hw : 0 ≤ w) (hμ : 0 < μ)
    (hμm : μ ≤ m) (hb : HighBound w s₀ μ h g) (k : Mom d) :
    (1 + ‖k‖) ^ (w + s₀) * |g k| ≤ m ^ w * h :=
  (hb k).trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hμ.le hμm hw) (hb.nonneg hμ))

/-- Converting a weighted bound at `k` into the form with `wt (w + s₀) k`. -/
theorem le_of_weighted {w s₀ X B : ℝ} (k : Mom d) (hb : (1 + ‖k‖) ^ (w + s₀) * X ≤ B) :
    X ≤ B * wt (w + s₀) k := by
  calc X = wt (w + s₀) k * ((1 + ‖k‖) ^ (w + s₀) * X) := by
        rw [← mul_assoc, wt_mul_rpow, one_mul]
    _ ≤ wt (w + s₀) k * B := mul_le_mul_of_nonneg_left hb (wt_nonneg _ _)
    _ = B * wt (w + s₀) k := mul_comm _ _

theorem le_three_sum_of_le {A B C a b c x y z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h3 : 1 ≤ A)
    (hB : 0 ≤ B) (hX : C ≤ B * a * x) :
    C ≤ A * B * (a + b + c) * (x + y + z) := by
  have e1 : a ≤ a + b + c := by linarith
  have e2 : x ≤ x + y + z := by linarith
  calc C ≤ B * a * x := hX
    _ ≤ B * (a + b + c) * (x + y + z) := by gcongr
    _ ≤ A * (B * (a + b + c) * (x + y + z)) := le_mul_of_one_le_left (by positivity) h3
    _ = _ := by ring

theorem gain_weighted (hw : 0 ≤ w) (hs₀ : 0 ≤ s₀) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hh₁ : HighBound w s₀ m₁ h₁ g₁) (hh₂ : HighBound w s₀ m₂ h₂ g₂)
    (hh₃ : HighBound w s₀ m₃ h₃ g₃) (hL₁ : DecayBound L₁ s₀ g₁) (hL₂ : DecayBound L₂ s₀ g₂)
    (hL₃ : DecayBound L₃ s₀ g₃) (k ℓ x : Mom d) :
    (1 + ‖k‖) ^ (w + s₀) * |g₁ (k + ℓ) * g₂ (k + ℓ + x) * g₃ (k + x)| ≤
      3 ^ s₀ * (m₁ + m₂ + m₃) ^ w * (h₁ * L₂ * L₃ + L₁ * h₂ * L₃ + L₁ * L₂ * h₃) *
        (wt s₀ (k + ℓ + x) * wt s₀ (k + x) + wt s₀ (k + ℓ) * wt s₀ (k + x)
          + wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x)) := by
  have hL₁0 := hL₁.C_nonneg; have hL₂0 := hL₂.C_nonneg; have hL₃0 := hL₃.C_nonneg
  have hh₁0 := hh₁.nonneg hm₁; have hh₂0 := hh₂.nonneg hm₂; have hh₃0 := hh₃.nonneg hm₃
  have hW₁ := wt_nonneg s₀ (k + ℓ); have hW₂ := wt_nonneg s₀ (k + ℓ + x)
  have hW₃ := wt_nonneg s₀ (k + x)
  rw [abs_mul, abs_mul]
  have hF₁ := abs_nonneg (g₁ (k + ℓ)); have hF₂ := abs_nonneg (g₂ (k + ℓ + x))
  have hF₃ := abs_nonneg (g₃ (k + x))
  have hx₁ : 0 < 1 + ‖k + ℓ‖ := by positivity
  have hx₂ : 0 < 1 + ‖k + ℓ + x‖ := by positivity
  have hx₃ : 0 < 1 + ‖k + x‖ := by positivity
  have hk : (k + ℓ) - (k + ℓ + x) + (k + x) = k := by abel
  have hnorm : 1 + ‖k‖ ≤ (1 + ‖k + ℓ‖) + (1 + ‖k + ℓ + x‖) + (1 + ‖k + x‖) := by
    have h1 := norm_add_le ((k + ℓ) - (k + ℓ + x)) (k + x)
    have h2 := norm_sub_le (k + ℓ) (k + ℓ + x)
    rw [hk] at h1
    linarith
  have sw := (Real.rpow_le_rpow (by positivity) hnorm hw).trans
    (add_add_rpow_le_weighted hx₁.le hx₂.le hx₃.le hm₁ hm₂ hm₃ hw)
  have ss := one_add_norm_rpow_le_three (k + ℓ) (k + ℓ + x) (k + x) hs₀
  rw [hk] at ss
  have a₁ := hh₁.div_mul_le hm₁ (k + ℓ); have a₂ := hh₂.div_mul_le hm₂ (k + ℓ + x)
  have a₃ := hh₃.div_mul_le hm₃ (k + x)
  have b₁ := hh₁.div_le hm₁ (k + ℓ); have b₂ := hh₂.div_le hm₂ (k + ℓ + x)
  have b₃ := hh₃.div_le hm₃ (k + x)
  have c₁ := hL₁.rpow_mul_le (k + ℓ); have c₂ := hL₂.rpow_mul_le (k + ℓ + x)
  have c₃ := hL₃.rpow_mul_le (k + x)
  have d₁ := hL₁.le_wt (k + ℓ); have d₂ := hL₂.le_wt (k + ℓ + x); have d₃ := hL₃.le_wt (k + x)
  have hy₁ : 0 ≤ ((1 + ‖k + ℓ‖) / m₁) ^ w := by positivity
  have hy₂ : 0 ≤ ((1 + ‖k + ℓ + x‖) / m₂) ^ w := by positivity
  have hy₃ : 0 ≤ ((1 + ‖k + x‖) / m₃) ^ w := by positivity
  have hz₁ : 0 ≤ (1 + ‖k + ℓ‖) ^ s₀ := by positivity
  have hz₂ : 0 ≤ (1 + ‖k + ℓ + x‖) ^ s₀ := by positivity
  have hz₃ : 0 ≤ (1 + ‖k + x‖) ^ s₀ := by positivity
  have hP : 0 ≤ (1 + ‖k‖) ^ w := by positivity
  have hQ : 0 ≤ (1 + ‖k‖) ^ s₀ := by positivity
  have h3 : 0 ≤ (3 : ℝ) ^ s₀ := by positivity
  have hmw : 0 ≤ (m₁ + m₂ + m₃) ^ w := by positivity
  rw [Real.rpow_add (by positivity : (0 : ℝ) < 1 + ‖k‖)]
  generalize |g₁ (k + ℓ)| = F₁ at *
  generalize |g₂ (k + ℓ + x)| = F₂ at *
  generalize |g₃ (k + x)| = F₃ at *
  generalize wt s₀ (k + ℓ) = W₁ at *
  generalize wt s₀ (k + ℓ + x) = W₂ at *
  generalize wt s₀ (k + x) = W₃ at *
  generalize ((1 + ‖k + ℓ‖) / m₁) ^ w = y₁ at *
  generalize ((1 + ‖k + ℓ + x‖) / m₂) ^ w = y₂ at *
  generalize ((1 + ‖k + x‖) / m₃) ^ w = y₃ at *
  generalize (1 + ‖k + ℓ‖) ^ s₀ = z₁ at *
  generalize (1 + ‖k + ℓ + x‖) ^ s₀ = z₂ at *
  generalize (1 + ‖k + x‖) ^ s₀ = z₃ at *
  generalize (1 + ‖k‖) ^ w = P at *
  generalize (1 + ‖k‖) ^ s₀ = Q at *
  generalize (m₁ + m₂ + m₃) ^ w = mw at *
  generalize (3 : ℝ) ^ s₀ = T at *
  have t11 : y₁ * z₁ * (F₁ * F₂ * F₃) ≤ h₁ * L₂ * L₃ * (W₂ * W₃) := by
    calc y₁ * z₁ * (F₁ * F₂ * F₃) = (y₁ * z₁ * F₁) * F₂ * F₃ := by ring
      _ ≤ h₁ * (L₂ * W₂) * (L₃ * W₃) := by gcongr
      _ = _ := by ring
  have t12 : y₁ * z₂ * (F₁ * F₂ * F₃) ≤ h₁ * L₂ * L₃ * (W₁ * W₃) := by
    calc y₁ * z₂ * (F₁ * F₂ * F₃) = (y₁ * F₁) * (z₂ * F₂) * F₃ := by ring
      _ ≤ (h₁ * W₁) * L₂ * (L₃ * W₃) := by gcongr
      _ = _ := by ring
  have t13 : y₁ * z₃ * (F₁ * F₂ * F₃) ≤ h₁ * L₂ * L₃ * (W₁ * W₂) := by
    calc y₁ * z₃ * (F₁ * F₂ * F₃) = (y₁ * F₁) * F₂ * (z₃ * F₃) := by ring
      _ ≤ (h₁ * W₁) * (L₂ * W₂) * L₃ := by gcongr
      _ = _ := by ring
  have t21 : y₂ * z₁ * (F₁ * F₂ * F₃) ≤ L₁ * h₂ * L₃ * (W₂ * W₃) := by
    calc y₂ * z₁ * (F₁ * F₂ * F₃) = (z₁ * F₁) * (y₂ * F₂) * F₃ := by ring
      _ ≤ L₁ * (h₂ * W₂) * (L₃ * W₃) := by gcongr
      _ = _ := by ring
  have t22 : y₂ * z₂ * (F₁ * F₂ * F₃) ≤ L₁ * h₂ * L₃ * (W₁ * W₃) := by
    calc y₂ * z₂ * (F₁ * F₂ * F₃) = F₁ * (y₂ * z₂ * F₂) * F₃ := by ring
      _ ≤ (L₁ * W₁) * h₂ * (L₃ * W₃) := by gcongr
      _ = _ := by ring
  have t23 : y₂ * z₃ * (F₁ * F₂ * F₃) ≤ L₁ * h₂ * L₃ * (W₁ * W₂) := by
    calc y₂ * z₃ * (F₁ * F₂ * F₃) = F₁ * (y₂ * F₂) * (z₃ * F₃) := by ring
      _ ≤ (L₁ * W₁) * (h₂ * W₂) * L₃ := by gcongr
      _ = _ := by ring
  have t31 : y₃ * z₁ * (F₁ * F₂ * F₃) ≤ L₁ * L₂ * h₃ * (W₂ * W₃) := by
    calc y₃ * z₁ * (F₁ * F₂ * F₃) = (z₁ * F₁) * F₂ * (y₃ * F₃) := by ring
      _ ≤ L₁ * (L₂ * W₂) * (h₃ * W₃) := by gcongr
      _ = _ := by ring
  have t32 : y₃ * z₂ * (F₁ * F₂ * F₃) ≤ L₁ * L₂ * h₃ * (W₁ * W₃) := by
    calc y₃ * z₂ * (F₁ * F₂ * F₃) = F₁ * (z₂ * F₂) * (y₃ * F₃) := by ring
      _ ≤ (L₁ * W₁) * L₂ * (h₃ * W₃) := by gcongr
      _ = _ := by ring
  have t33 : y₃ * z₃ * (F₁ * F₂ * F₃) ≤ L₁ * L₂ * h₃ * (W₁ * W₂) := by
    calc y₃ * z₃ * (F₁ * F₂ * F₃) = F₁ * F₂ * (y₃ * z₃ * F₃) := by ring
      _ ≤ (L₁ * W₁) * (L₂ * W₂) * h₃ := by gcongr
      _ = _ := by ring
  have hF : 0 ≤ F₁ * F₂ * F₃ := by positivity
  calc P * Q * (F₁ * F₂ * F₃)
      ≤ (mw * (y₁ + y₂ + y₃)) * (T * (z₁ + z₂ + z₃)) * (F₁ * F₂ * F₃) := by gcongr
    _ = T * mw * ((y₁ * z₁ * (F₁ * F₂ * F₃) + y₁ * z₂ * (F₁ * F₂ * F₃)
          + y₁ * z₃ * (F₁ * F₂ * F₃)) + (y₂ * z₁ * (F₁ * F₂ * F₃) + y₂ * z₂ * (F₁ * F₂ * F₃)
          + y₂ * z₃ * (F₁ * F₂ * F₃)) + (y₃ * z₁ * (F₁ * F₂ * F₃)
          + y₃ * z₂ * (F₁ * F₂ * F₃) + y₃ * z₃ * (F₁ * F₂ * F₃))) := by ring
    _ ≤ T * mw * ((h₁ * L₂ * L₃ * (W₂ * W₃) + h₁ * L₂ * L₃ * (W₁ * W₃)
          + h₁ * L₂ * L₃ * (W₁ * W₂)) + (L₁ * h₂ * L₃ * (W₂ * W₃) + L₁ * h₂ * L₃ * (W₁ * W₃)
          + L₁ * h₂ * L₃ * (W₁ * W₂)) + (L₁ * L₂ * h₃ * (W₂ * W₃)
          + L₁ * L₂ * h₃ * (W₁ * W₃) + L₁ * L₂ * h₃ * (W₁ * W₂))) := by
        have : 0 ≤ T * mw := by positivity
        gcongr
    _ = _ := by ring

theorem loss_weighted (hw : 0 ≤ w) (hs₀ : 0 ≤ s₀) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hh₁ : HighBound w s₀ m₁ h₁ g₁) (hh₂ : HighBound w s₀ m₂ h₂ g₂)
    (hh₃ : HighBound w s₀ m₃ h₃ g₃) (hL₁ : DecayBound L₁ s₀ g₁) (hL₂ : DecayBound L₂ s₀ g₂)
    (hL₃ : DecayBound L₃ s₀ g₃) (j : Fin 4) (hj : j ≠ 0) (k ℓ x : Mom d) :
    (1 + ‖k‖) ^ (w + s₀) * |collisionKernel j g₁ g₂ g₃ k ℓ x| ≤
      3 ^ s₀ * (m₁ + m₂ + m₃) ^ w * (h₁ * L₂ * L₃ + L₁ * h₂ * L₃ + L₁ * L₂ * h₃) *
        (wt s₀ (k + ℓ + x) * wt s₀ (k + x) + wt s₀ (k + ℓ) * wt s₀ (k + x)
          + wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x)) := by
  have hL₁0 := hL₁.C_nonneg; have hL₂0 := hL₂.C_nonneg; have hL₃0 := hL₃.C_nonneg
  have hh₁0 := hh₁.nonneg hm₁; have hh₂0 := hh₂.nonneg hm₂; have hh₃0 := hh₃.nonneg hm₃
  have hW₁ := wt_nonneg s₀ (k + ℓ); have hW₂ := wt_nonneg s₀ (k + ℓ + x)
  have hW₃ := wt_nonneg s₀ (k + x)
  have h3 : (1 : ℝ) ≤ 3 ^ s₀ := Real.one_le_rpow (by norm_num) hs₀
  have hm := (by positivity : (0 : ℝ) ≤ (m₁ + m₂ + m₃) ^ w)
  have t1 : 0 ≤ h₁ * L₂ * L₃ := by positivity
  have t2 : 0 ≤ L₁ * h₂ * L₃ := by positivity
  have t3 : 0 ≤ L₁ * L₂ * h₃ := by positivity
  have u1 : 0 ≤ wt s₀ (k + ℓ + x) * wt s₀ (k + x) := by positivity
  have u2 : 0 ≤ wt s₀ (k + ℓ) * wt s₀ (k + x) := by positivity
  have u3 : 0 ≤ wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x) := by positivity
  fin_cases j
  · exact absurd rfl hj
  · show (1 + ‖k‖) ^ (w + s₀) * |g₁ k * g₂ (k + ℓ + x) * g₃ (k + x)| ≤ _
    rw [abs_mul, abs_mul]
    have a := hh₁.at_le hw hm₁ (by linarith : m₁ ≤ m₁ + m₂ + m₃) k
    have d₂ := hL₂.le_wt (k + ℓ + x); have d₃ := hL₃.le_wt (k + x)
    refine le_three_sum_of_le t1 t2 t3 u1 u2 u3 h3 hm ?_
    calc (1 + ‖k‖) ^ (w + s₀) * (|g₁ k| * |g₂ (k + ℓ + x)| * |g₃ (k + x)|)
        = ((1 + ‖k‖) ^ (w + s₀) * |g₁ k|) * |g₂ (k + ℓ + x)| * |g₃ (k + x)| := by ring
      _ ≤ ((m₁ + m₂ + m₃) ^ w * h₁) * (L₂ * wt s₀ (k + ℓ + x)) * (L₃ * wt s₀ (k + x)) := by
          gcongr
      _ = _ := by ring
  · show (1 + ‖k‖) ^ (w + s₀) * |g₁ (k + ℓ) * g₂ k * g₃ (k + x)| ≤ _
    rw [abs_mul, abs_mul]
    have a := hh₂.at_le hw hm₂ (by linarith : m₂ ≤ m₁ + m₂ + m₃) k
    have d₁ := hL₁.le_wt (k + ℓ); have d₃ := hL₃.le_wt (k + x)
    refine (le_three_sum_of_le t2 t1 t3 u2 u1 u3 h3 hm ?_).trans_eq (by ring)
    calc (1 + ‖k‖) ^ (w + s₀) * (|g₁ (k + ℓ)| * |g₂ k| * |g₃ (k + x)|)
        = |g₁ (k + ℓ)| * ((1 + ‖k‖) ^ (w + s₀) * |g₂ k|) * |g₃ (k + x)| := by ring
      _ ≤ (L₁ * wt s₀ (k + ℓ)) * ((m₁ + m₂ + m₃) ^ w * h₂) * (L₃ * wt s₀ (k + x)) := by
          gcongr
      _ = _ := by ring
  · show (1 + ‖k‖) ^ (w + s₀) * |g₁ (k + ℓ) * g₂ (k + ℓ + x) * g₃ k| ≤ _
    rw [abs_mul, abs_mul]
    have a := hh₃.at_le hw hm₃ (by linarith : m₃ ≤ m₁ + m₂ + m₃) k
    have d₁ := hL₁.le_wt (k + ℓ); have d₂ := hL₂.le_wt (k + ℓ + x)
    refine (le_three_sum_of_le t3 t1 t2 u3 u1 u2 h3 hm ?_).trans_eq (by ring)
    calc (1 + ‖k‖) ^ (w + s₀) * (|g₁ (k + ℓ)| * |g₂ (k + ℓ + x)| * |g₃ k|)
        = |g₁ (k + ℓ)| * |g₂ (k + ℓ + x)| * ((1 + ‖k‖) ^ (w + s₀) * |g₃ k|) := by ring
      _ ≤ (L₁ * wt s₀ (k + ℓ)) * (L₂ * wt s₀ (k + ℓ + x)) * ((m₁ + m₂ + m₃) ^ w * h₃) := by
          gcongr
      _ = _ := by ring

/-- The pointwise weighted kernel bound for each of the four kernels. -/
theorem abs_collisionKernel_le_weighted (hw : 0 ≤ w) (hs₀ : 0 ≤ s₀) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hh₁ : HighBound w s₀ m₁ h₁ g₁) (hh₂ : HighBound w s₀ m₂ h₂ g₂)
    (hh₃ : HighBound w s₀ m₃ h₃ g₃) (hL₁ : DecayBound L₁ s₀ g₁) (hL₂ : DecayBound L₂ s₀ g₂)
    (hL₃ : DecayBound L₃ s₀ g₃) (j : Fin 4) (k ℓ x : Mom d) :
    |collisionKernel j g₁ g₂ g₃ k ℓ x| ≤
      3 ^ s₀ * (m₁ + m₂ + m₃) ^ w * (h₁ * L₂ * L₃ + L₁ * h₂ * L₃ + L₁ * L₂ * h₃) *
        wt (w + s₀) k * (wt s₀ (k + ℓ + x) * wt s₀ (k + x) + wt s₀ (k + ℓ) * wt s₀ (k + x)
          + wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x)) := by
  refine (le_of_weighted (w := w) (s₀ := s₀) (B := 3 ^ s₀ * (m₁ + m₂ + m₃) ^ w *
    (h₁ * L₂ * L₃ + L₁ * h₂ * L₃ + L₁ * L₂ * h₃) *
    (wt s₀ (k + ℓ + x) * wt s₀ (k + x) + wt s₀ (k + ℓ) * wt s₀ (k + x)
      + wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x))) k ?_).trans_eq (by ring)
  by_cases hj : j = 0
  · subst hj
    exact gain_weighted hw hs₀ hm₁ hm₂ hm₃ hh₁ hh₂ hh₃ hL₁ hL₂ hL₃ k ℓ x
  · exact loss_weighted hw hs₀ hm₁ hm₂ hm₃ hh₁ hh₂ hh₃ hL₁ hL₂ hL₃ j hj k ℓ x

/-- **Weighted tame estimate with leaf-count weights.** For `d ≥ 2`, `s₀ > 2d`, `w ≥ 0`, `mᵢ > 0`,
`(1+|y|)^{w+s₀}|gᵢ(y)| ≤ mᵢ^w hᵢ` and `(1+|y|)^{s₀}|gᵢ(y)| ≤ Lᵢ`:
`(1+|k|)^{w+s₀} |𝒦ⱼ(g₁,g₂,g₃)(k)| ≤ 3·3^{s₀}·tameConst d s₀·(m₁+m₂+m₃)^w (h₁L₂L₃ + L₁h₂L₃ + L₁L₂h₃)`.
The large weight `w` costs `(Σ mᵢ)^w`, not `3^w`. -/
theorem abs_collisionTerm_le_weighted (hd : 2 ≤ d) (hs₀ : 2 * (d : ℝ) < s₀) (hw : 0 ≤ w)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hh₁ : HighBound w s₀ m₁ h₁ g₁)
    (hh₂ : HighBound w s₀ m₂ h₂ g₂) (hh₃ : HighBound w s₀ m₃ h₃ g₃) (hL₁ : DecayBound L₁ s₀ g₁)
    (hL₂ : DecayBound L₂ s₀ g₂) (hL₃ : DecayBound L₃ s₀ g₃) (j : Fin 4) (k : Mom d) :
    (1 + ‖k‖) ^ (w + s₀) * |collisionTerm j g₁ g₂ g₃ k| ≤
      3 * 3 ^ s₀ * tameConst d s₀ * (m₁ + m₂ + m₃) ^ w *
        (h₁ * L₂ * L₃ + L₁ * h₂ * L₃ + L₁ * L₂ * h₃) := by
  have hs₀' : 0 ≤ s₀ := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hL₁0 := hL₁.C_nonneg; have hL₂0 := hL₂.C_nonneg; have hL₃0 := hL₃.C_nonneg
  have hh₁0 := hh₁.nonneg hm₁; have hh₂0 := hh₂.nonneg hm₂; have hh₃0 := hh₃.nonneg hm₃
  set S := h₁ * L₂ * L₃ + L₁ * h₂ * L₃ + L₁ * L₂ * h₃
  have hS : 0 ≤ S := by positivity
  set m := m₁ + m₂ + m₃
  have h3 : (0 : ℝ) < 3 ^ (w + s₀) := by positivity
  set c := 3 ^ s₀ * m ^ w * S / 3 ^ (w + s₀)
  have hc : 0 ≤ c := by positivity
  have hc3 : c * 3 ^ (w + s₀) = 3 ^ s₀ * m ^ w * S := div_mul_cancel₀ _ h3.ne'
  have key := abs_deltaInt_le_tame (s := w + s₀) (F := collisionKernel j g₁ g₂ g₃ k) hd hs₀
    zero_le_one zero_le_one zero_le_one zero_le_one zero_le_one zero_le_one k hc
    (fun ℓ x => by
      refine (abs_collisionKernel_le_weighted hw hs₀' hm₁ hm₂ hm₃ hh₁ hh₂ hh₃ hL₁ hL₂ hL₃ j k ℓ
        x).trans ?_
      have hP : wt s₀ (k + ℓ + x) * wt s₀ (k + x) ≤ wt (s₀ / 2) ℓ * wt (s₀ / 2) (k + x) := by
        have h := one_add_norm_rpow_neg_mul_le (k + x) ℓ hs₀'
        have e : k + x + ℓ = k + ℓ + x := by abel
        rw [e] at h; exact h
      have hQ : wt s₀ (k + ℓ) * wt s₀ (k + x) ≤ wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + x) :=
        mul_le_mul (wt_anti (by linarith) _) (wt_anti (by linarith) _) (wt_nonneg _ _)
          (wt_nonneg _ _)
      have hR : wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x) ≤
          wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + ℓ + x) :=
        mul_le_mul (wt_anti (by linarith) _) (wt_anti (by linarith) _) (wt_nonneg _ _)
          (wt_nonneg _ _)
      have hRHS : ∑ i : Fin 3, c * tameA k (w + s₀) (s₀ / 2) 1 1 1 1 1 1 i ℓ *
          (1 + ‖tameB k i ℓ + x‖) ^ (-(s₀ / 2)) =
          c * 3 ^ (w + s₀) * wt (w + s₀) k * (wt (s₀ / 2) ℓ * wt (s₀ / 2) (k + x)
            + wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + x)
            + wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + ℓ + x)) := by
        simp only [Fin.sum_univ_three, tameA, tameB, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        simp only [wt]
        ring
      rw [hRHS, hc3]
      have hWk := wt_nonneg (w + s₀) k
      have : 0 ≤ 3 ^ s₀ * m ^ w * S * wt (w + s₀) k := by positivity
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hP hQ) hR) this)
  calc (1 + ‖k‖) ^ (w + s₀) * |collisionTerm j g₁ g₂ g₃ k|
      ≤ c * (tameConst d s₀ * 3 ^ (w + s₀) * (1 * 1 * 1 + 1 * 1 * 1 + 1 * 1 * 1)) := key
    _ = 3 * tameConst d s₀ * (c * 3 ^ (w + s₀)) := by ring
    _ = _ := by rw [hc3]; ring

end Weighted

end WaveTurbulence
