/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ShiftedSpectralMoment
public import WaveTurbulence.Foundations.RegAsymp.OrderLoss

/-! # The actual modulation-frequency loss is geometric in the half-order -/

public section
namespace WaveTurbulence.RegAsymp
open Links

/-- The computed source-order loss fits one fixed geometric factor,
including the trivial couple. -/
theorem spectralFrequencyLoss_le_geometric (Q : RegCpl) :
    spectralFrequencyLoss Q ≤ (9*(1+4*Real.pi)) ^ Q.links.length := by
  have hsize : Q.size = 2*Q.links.length := by
    have hh := couple_linksAt_length Q ((0 : Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  by_cases hn : Q.links.length=0
  · simp [spectralFrequencyLoss,hn]
  have hn0 : 0 ≤ (Q.links.length:ℝ) := Nat.cast_nonneg _
  have hC : 1 ≤ 1+4*Real.pi := by have := Real.pi_pos; linarith
  have hp := leaf_polynomial_le_geometric Q.links.length 2
  have hp' : (2*(Q.links.length:ℝ)+1)^2 ≤ (9:ℝ)^Q.links.length := by norm_num at hp ⊢; exact hp
  have hCp : 1+4*Real.pi ≤ (1+4*Real.pi)^Q.links.length :=
    le_self_pow₀ hC hn
  have hbase : spectralFrequencyLoss Q ≤ (1+4*Real.pi)*(2*(Q.links.length:ℝ)+1)^2 := by
    have h1 : 1 ≤ (2*(Q.links.length:ℝ)+1)^2 := by nlinarith
    have h2 : (Q.links.length:ℝ)*(2*(Q.links.length:ℝ)+1) ≤ (2*(Q.links.length:ℝ)+1)^2 :=
      by
        have hb : (Q.links.length:ℝ) ≤ 2*(Q.links.length:ℝ)+1 := by linarith
        have hh := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 2*(Q.links.length:ℝ)+1)
        simpa only [pow_two] using hh
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 4*Real.pi)
    unfold spectralFrequencyLoss
    rw [hsize]
    push_cast
    nlinarith
  calc
    _ ≤ (1+4*Real.pi)*(2*(Q.links.length:ℝ)+1)^2 := hbase
    _ ≤ (1+4*Real.pi)*9^Q.links.length := mul_le_mul_of_nonneg_left hp' (by positivity)
    _ ≤ (1+4*Real.pi)^Q.links.length * 9^Q.links.length :=
      mul_le_mul_of_nonneg_right hCp (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end WaveTurbulence.RegAsymp
