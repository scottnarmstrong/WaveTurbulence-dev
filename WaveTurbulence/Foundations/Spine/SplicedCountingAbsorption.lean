/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedInterpolation
/-! TARGET L2086–L2116: exact logarithmic bookkeeping for countA, ladder Fourier bounds,
and the dyadic-choice losses. The disputed count itself is not proved or assumed here. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

/-- The C1/delta slack absorbs fixed exponential enumeration costs; the countA gain absorbs
both dyadic losses and the Fourier L1 loss. In applications e=eta^6, a=delta^(5nu),
u=log(delta), l=log(L), b=log(log(L)), and q=q_sk≤p_sb. -/
theorem spliced_counting_exponent_le {c c₀ u l b a e ν n R ρ p q : ℝ}
    (hc : 0 ≤ c) (hu : u ≤ 0) (hl : 0 ≤ l) (he : 0 ≤ e)
    (hn : 0 ≤ n) (hR : 1 ≤ R) (hρ : 0 ≤ ρ) (hp : 0 ≤ p)
    (hq : q ≤ p) (ha : a ≤ e) (hb : b ≤ e * l)
    (hsmall : c + c₀ + 5 * ν * u ≤ 0) :
    n * (2 * c - 5 * ν * u + c₀) + (R - 1) * (u / 2 - c) +
        (-4 * e * (ρ + p) + a * ρ - (R - 1) * (1 / 4 + 1 / 40)) * l +
        (ρ + p) * b ≤
      n * (c - 10 * ν * u) + (-e * (ρ + q) - (R - 1) * (1 / 4 + 1 / 50)) * l := by
  have hδ : n * (2 * c - 5 * ν * u + c₀) ≤ n * (c - 10 * ν * u) :=
    mul_le_mul_of_nonneg_left (by linarith [hsmall]) hn
  have hroot : (R - 1) * (u / 2 - c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hR) (by linarith)
  have hlogs : (ρ + p) * b ≤ (ρ + p) * (e * l) :=
    mul_le_mul_of_nonneg_left hb (add_nonneg hρ hp)
  have haρ := mul_le_mul_of_nonneg_right ha hρ
  have hqp := mul_le_mul_of_nonneg_left hq he
  have hcoef : -4 * e * (ρ + p) + a * ρ + (ρ + p) * e ≤ -e * (ρ + q) := by
    nlinarith [mul_nonneg he hρ, mul_nonneg he hp]
  have hgain : -4 * e * (ρ + p) + a * ρ + (ρ + p) * e -
      (R - 1) * (1 / 4 + 1 / 40) ≤
      -e * (ρ + q) - (R - 1) * (1 / 4 + 1 / 50) := by
    linarith
  have hgainL := mul_le_mul_of_nonneg_right hgain hl
  nlinarith

end WaveTurbulence.LGSpine
