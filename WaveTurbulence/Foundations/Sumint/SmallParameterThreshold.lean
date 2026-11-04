/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SmallParameterConditions

/-!
# An explicit positive source eta threshold

Take eta0 = epsilon squared, with epsilon the minimum of
1/(10000(d+1)), gammaBase/100 and the positive high-gamma margin/100.
It is chosen before A, the WKE data, delta and the step count.
-/

public section
open Set
namespace WaveTurbulence.Sumint

/-- All numerical margins hold uniformly below an explicit positive eta threshold. -/
theorem exists_sumintSmallness_threshold (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η ∈ Ioc (0:ℝ) η0, SumintSmallness d γ η := by
  classical
  let H := if 1/2 < γ then min (2*γ-1) (1-γ) else 1
  have hH : 0 < H := by
    dsimp [H]
    split_ifs with hg
    · exact lt_min (by linarith) (by linarith [hγ.2])
    · norm_num
  let ε := min (1/(10000*((d:ℝ)+1))) (min (gammaBase γ/100) (H/100))
  have hbase := gammaBase_pos hγ
  have hd0 : 0 ≤ (d:ℝ) := Nat.cast_nonneg _
  have hd3 : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < 10000*((d:ℝ)+1) := by positivity
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεD : ε*((d:ℝ)+1) ≤ 1/10000 := by
    have hh := (le_div_iff₀ hden).mp (show ε ≤ 1/(10000*((d:ℝ)+1)) from min_le_left _ _)
    nlinarith only [hh]
  have hεsmall : ε ≤ 1/10000 := by
    have hp := mul_nonneg hε.le hd0
    nlinarith only [hp,hεD]
  have hεbase : ε ≤ gammaBase γ/100 := (min_le_right _ _).trans (min_le_left _ _)
  have hεH : ε ≤ H/100 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε^2,sq_pos_of_pos hε,?_⟩
  intro η hη
  have heta_eps : η ≤ ε := hη.2.trans (by nlinarith only [hεsmall,hε.le])
  have heta_small : η ≤ 1/10000 := heta_eps.trans hεsmall
  have heta_one : η ≤ 1 := by linarith only [heta_small]
  have hsqrt : Real.sqrt η ≤ ε := Real.sqrt_le_iff.mpr ⟨hε.le,hη.2⟩
  have hbeta : partitionExponent η ≤ η := partitionExponent_le_eta hη.1.le heta_one
  have hpow8 : η^8 ≤ η := by
    simpa only [pow_one] using pow_le_pow_of_le_one hη.1.le heta_one (by norm_num : 1 ≤ 8)
  have hsq : η^2 ≤ η := by
    simpa only [pow_one] using pow_le_pow_of_le_one hη.1.le heta_one (by norm_num : 1 ≤ 2)
  have heta_base : η ≤ gammaBase γ/100 := heta_eps.trans hεbase
  have hgammaBaseLeft : gammaBase γ ≤ γ := min_le_left _ _
  have hgammaBaseRight : gammaBase γ ≤ 1-γ := min_le_right _ _
  have hpair : 1-γ ≤ 2*((d:ℝ)-1)*(1-γ) := by
    have hp := mul_nonneg (show 0 ≤ 2*((d:ℝ)-1)-1 by linarith only [hd3])
      (show 0 ≤ 1-γ by linarith only [hγ.2])
    nlinarith only [hp]
  have hη2 : 2*η^2 ≤ 1 := by nlinarith only [hsq,heta_small]
  refine ⟨hη.1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · linarith only [heta_base,hbase]
  · linarith only [heta_small]
  · linarith only [heta_base,hgammaBaseRight,hbase]
  · exact hsqrt.trans (hεbase.trans (by linarith only [hbase]))
  · linarith only [hbeta,heta_base,hgammaBaseLeft,hbase]
  · linarith only [hbeta,heta_base,hgammaBaseRight,hbase,hpair]
  · linarith only [hbeta,heta_base,hgammaBaseLeft,hbase]
  · intro hg
    have hHval : H = min (2*γ-1) (1-γ) := ite_eq_left hg
    have hβH : partitionExponent η ≤ H/100 := hbeta.trans (heta_eps.trans hεH)
    rw [← hHval]
    linarith only [hβH,hH]
  · linarith only [hpow8,heta_small]
  · linarith only [hpow8,heta_small]
  · linarith only [hsqrt,hεsmall]
  · have hdη := mul_le_mul_of_nonneg_left heta_eps hd0
    nlinarith only [hdη,hsqrt,hεD,hε.le]
  · linarith only [hsq,heta_base,hbase]
  · calc
      2*η^8 = η^6*(2*η^2) := by ring
      _ ≤ η^6*1 := mul_le_mul_of_nonneg_left hη2 (pow_nonneg hη.1.le _)
      _ = _ := mul_one _

end WaveTurbulence.Sumint
