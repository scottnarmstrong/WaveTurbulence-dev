/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.NormalBlockPower
public import WaveTurbulence.Foundations.Sumint.SourceScalePowers

/-!
# The normal endpoint half-moment gives a strict incoherence gain

In the low-gamma range the three powers, after multiplication by the
trivial linear factor, have reserves beta/2, gamma, and gamma. Fixed
delta-dependent coefficients are absorbed at the later lattice threshold.
The resulting beta/20 reserve is uniform in source data and multiplicities.
-/

public section

namespace WaveTurbulence.Sumint

/-- Numerical normalization of the physical cubic endpoint strip in the low-gamma branch. -/
theorem exists_low_gamma_cubic_endpoint_power_bound (d : ℕ) {γ : ℝ}
    (hγ : γ ∈ Set.Ioc (0:ℝ) (1/2)) (β : ℝ) (hβ : 0 < β) (hβγ : β < 20*γ)
    (Cs Cm k δ : ℝ) (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm) (hk : 0 ≤ k) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      k*L^(d:ℝ)*((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
        (Cs*(4*L)^(3*d)*(Real.sqrt (L^(-β))+(16*sourceHalfScale L γ δ)^(-(1/2:ℝ)))+
          (1+2*L^(-β))*Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L))) ≤
      L^(4*((d:ℝ)-γ)-β/20) := by
  let As := Cs*(8:ℝ)^(-2:ℝ)*δ^(-2:ℝ)*4^(3*d)
  let Ac := (8:ℝ)^(-(1/2:ℝ))*δ^(-(1/2:ℝ))
  let Am := Cm*(8:ℝ)^(-2:ℝ)*δ^(-2:ℝ)*4^(3*(d:ℝ)+γ-2*min γ (1-γ))
  have hAs : 0 ≤ As := by dsimp [As]; positivity
  have hAc : 0 ≤ Ac := by dsimp [Ac]; positivity
  have hAm : 0 ≤ Am := by dsimp [Am]; positivity
  have hg : min γ (1-γ) = γ := min_eq_left (by linarith [hγ.2])
  have he₀ : 4*(d:ℝ)-4*γ-β/2 < 4*((d:ℝ)-γ)-β/20 := by linarith only [hβ]
  have he₁ : 4*(d:ℝ)-5*γ < 4*((d:ℝ)-γ)-β/20 := by linarith only [hβγ]
  have he₂ : 4*(d:ℝ)-3*γ-2*min γ (1-γ) < 4*((d:ℝ)-γ)-β/20 := by rw [hg]; linarith only [hβγ]
  obtain ⟨R,hR,hbound⟩ := exists_three_power_sum_le (k*As) (k*As*Ac) (9*k*Am)
    (4*(d:ℝ)-4*γ-β/2) (4*(d:ℝ)-5*γ) (4*(d:ℝ)-3*γ-2*min γ (1-γ))
    (4*((d:ℝ)-γ)-β/20) he₀ he₁ he₂
  refine ⟨R,hR,?_⟩
  intro L hL
  have hL2 : 2 ≤ L := hR.trans hL
  have hL1 : 1 ≤ L := by linarith only [hL2]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hsmall : L^(-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hβ])
  have hsqrt : Real.sqrt (L^(-β)) = L^(-β/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hLp.le]
    congr 1
    ring
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlog4 : Real.log (4*L) ≤ 3*Real.log L := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hLp.ne']
    have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hL2
    have he : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
      norm_num
    rw [he]
    linarith only [h2]
  have hs : (16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹*
      (Cs*(4*L)^(3*d)) = As*L^(3*(d:ℝ)-4*γ) := by
    have he := source_scale_inv_sq_mul_nat_pow hLp (by norm_num : (0:ℝ) < 16) hδ
      (by norm_num : (0:ℝ) ≤ 4) γ (3*d)
    have hn : ((3*d:ℕ):ℝ)-4*γ = 3*(d:ℝ)-4*γ := by push_cast; ring
    rw [hn] at he
    calc
      _ = Cs*((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹*(4*L)^(3*d)) := by ring
      _ = _ := by rw [he]; dsimp [As]; norm_num; ring
  have hc : (16*sourceHalfScale L γ δ)^(-(1/2:ℝ)) = Ac*L^(-γ) := by
    have he := source_scale_rpow hLp (by norm_num : (0:ℝ) < 16) hδ
      (by norm_num : (0:ℝ) ≤ 1) γ (1/2) 0
    simpa only [Real.rpow_zero,mul_one,show (16:ℝ)/2 = 8 by norm_num,
      show (0:ℝ)-2*γ*(1/2) = -γ by ring,Ac] using he
  have hm : (16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹*
      (Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))) =
      Am*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)) := by
    have he := source_scale_inv_sq_mul_rpow hLp (by norm_num : (0:ℝ) < 16) hδ
      (by norm_num : (0:ℝ) ≤ 4) γ (3*(d:ℝ)+γ-2*min γ (1-γ))
    have hn : 3*(d:ℝ)+γ-2*min γ (1-γ)-4*γ = 3*(d:ℝ)-3*γ-2*min γ (1-γ) := by ring
    rw [hn] at he
    calc
      _ = Cm*((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))) := by ring
      _ = _ := by rw [he]; dsimp [Am]; norm_num; ring
  have hminor : (1+2*L^(-β))* (Am*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)))*Real.log (4*L) ≤
      9*Am*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L := by
    have hlen : 1+2*L^(-β) ≤ 3 := by linarith only [hsmall]
    have hm0 : 0 ≤ Am*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)) := by positivity
    have hlog40 : 0 ≤ Real.log (4*L) := Real.log_nonneg (by linarith only [hL2])
    calc
      _ ≤ 3*(Am*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)))*Real.log (4*L) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlen hm0) hlog40
      _ ≤ 3*(Am*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)))*(3*Real.log L) :=
        mul_le_mul_of_nonneg_left hlog4 (by positivity)
      _ = _ := by ring
  have hp₀ : L^(d:ℝ)*(L^(3*(d:ℝ)-4*γ)*L^(-β/2)) = L^(4*(d:ℝ)-4*γ-β/2) := by
    rw [← Real.rpow_add hLp,← Real.rpow_add hLp]; congr 1; ring
  have hp₁ : L^(d:ℝ)*(L^(3*(d:ℝ)-4*γ)*L^(-γ)) = L^(4*(d:ℝ)-5*γ) := by
    rw [← Real.rpow_add hLp,← Real.rpow_add hLp]; congr 1; ring
  have hp₂ : L^(d:ℝ)*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)) = L^(4*(d:ℝ)-3*γ-2*min γ (1-γ)) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  calc
    _ = k*L^(d:ℝ)*(As*L^(3*(d:ℝ)-4*γ)*(L^(-β/2)+Ac*L^(-γ))+
        (1+2*L^(-β))*(Am*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)))*Real.log (4*L)) := by
      rw [← hs,← hm,← hsqrt,← hc]
      ring
    _ ≤ k*L^(d:ℝ)*(As*L^(3*(d:ℝ)-4*γ)*(L^(-β/2)+Ac*L^(-γ))+
        9*Am*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hminor) (by positivity)
    _ = (k*As)*L^(4*(d:ℝ)-4*γ-β/2)+(k*As*Ac)*L^(4*(d:ℝ)-5*γ)+
        (9*k*Am)*L^(4*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L := by
      calc
        _ = (k*As)*(L^(d:ℝ)*(L^(3*(d:ℝ)-4*γ)*L^(-β/2)))+
          (k*As*Ac)*(L^(d:ℝ)*(L^(3*(d:ℝ)-4*γ)*L^(-γ)))+
          (9*k*Am)*(L^(d:ℝ)*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)))*Real.log L := by ring
        _ = _ := by rw [hp₀,hp₁,hp₂]
    _ ≤ _ := hbound L hL

end WaveTurbulence.Sumint
