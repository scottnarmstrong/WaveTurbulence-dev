/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Top
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Final
public import WaveTurbulence.Foundations.FinalCount.Prop102Bridge
public import WaveTurbulence.Foundations.FinalCount.OpD
import Mathlib.Tactic

/-! # `Case6TopLow`: sub-cases (6b), (6d) of Prop 9.6 case (6) at `γ ≤ 1/2` (packet L6-COUNT; M2 §4.10)

`case6TopLow_proved : Case6TopLow d γ η` (L6's statement, `P96/Case6.lean`). By `c6_top_core`,
`𝔄 ≲ f · L^{−(γ−3η)/2 + η²/8 − 3γ/5 + η²/8}` with `f = L^{−(γ+3η)/2} R₁⁻¹` the `α`-factor of the chain atom; interpolated
with the rough bound (`rough96`, weight `η³`) as in main's `case_six` (`endgame`) against `finalRHS ≥ f L^e`
(`finalRHS_ge_split`), the margin is `3γ/5 − 4η − O(η²)` (`case6_top_arith_low`). Inputs: Prop 10.2(1) at `η, η/2, η/4`
(main's `prop102InputSz`), operation (d) at `η, η/2` (main's `opDInput`), `c6d_key` (operation (e)). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8 WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.GammaLow.FinalCount

/-- The exponent arithmetic of (6b)/(6d) at `γ ≤ 1/2`: margin `3γ/5 − 4η − O(η²)`. -/
theorem case6_top_arith_low {d : ℕ} {γ η : ℝ} (hd : 3 ≤ d) (hγ1 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ γ / 1000) :
    η ^ 3 * (16 * (d : ℝ) + 28) * (2 + 1 + 1) +
        (1 - η ^ 3) * (-(γ - 3 * η) / 2 + η ^ 2 / 8 + (-(3 / 5 * γ) + η ^ 2 / 8)) ≤
      (2 - 1) * ((γ - 5 * η) / 2) + ((γ + 2 * η ^ 2) * 1 - (2 * γ + 5 * η ^ 2) * 1) := by
  obtain ⟨h1, h2, _, h4⟩ := small_facts_low hd hγ1 hγ2 hη hsm
  have hη3 : η ^ 3 ≤ 1 / 100 := by
    have : η ^ 3 ≤ η := by
      have hη1 : η ≤ 1 := by linarith
      calc η ^ 3 = η * η ^ 2 := by ring
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hη.le hη1) hη.le
        _ = η := mul_one η
    linarith
  have hη3' : 0 ≤ η ^ 3 := by positivity
  have hη2 : η ^ 2 ≤ η / 6000 := by
    calc η ^ 2 = η * η := sq η
      _ ≤ η * (1 / 6000) := mul_le_mul_of_nonneg_left h2 hη.le
      _ = η / 6000 := by ring
  have hBl : -(11 / 10 * γ) ≤ -(γ - 3 * η) / 2 + η ^ 2 / 8 + (-(3 / 5 * γ) + η ^ 2 / 8) := by
    have := sq_nonneg η; linarith
  have hηB := mul_le_mul_of_nonneg_left hBl hη3'
  have hηγ : η ^ 3 * γ ≤ 1 / 100 * γ := mul_le_mul_of_nonneg_right hη3 hγ1.le
  have hN : η ^ 3 * (16 * (d : ℝ) + 28) ≤ η ^ 2 / 30 := h4
  linarith [hN, hηB, hηγ, hη2, h1]

/-- **`Case6TopLow`** (sub-cases (6b), (6d) of Prop 9.6 case (6) at `0 < γ ≤ 1/2`). -/
theorem case6TopLow_proved (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    Case6TopLow.{u, v} d γ η := by
  classical
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  have hsm' : (d : ℝ) * η ≤ γ / 1000 := by rw [hγ0] at hsm; exact hsm
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  obtain ⟨h1, h2, _, _⟩ := small_facts_low hd hγ.1 hγ.2 hη hsm'
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hηmax : η ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  have hη2 : 0 < η / 2 := by positivity
  have hη4 : 0 < η / 2 / 2 := by positivity
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨Ce, Ke, hCe, _, hc6d⟩ := c6d_key.{u, v} d hd γ hγ η hη hηmax
  obtain ⟨Cp1, _, hp1⟩ := prop102InputSz.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨Cp2, _, hp2⟩ := prop102InputSz.{u, v} d hd γ (η / 2) hγ01 hη2 (by linarith) (by linarith)
  obtain ⟨Cp4, _, hp4⟩ := prop102InputSz.{u, v} d hd γ (η / 2 / 2) hγ01 hη4 (by linarith) (by linarith)
  obtain ⟨Cd1, _, hd1⟩ := opDInput.{u, v} d γ η hη
  obtain ⟨Cd2, _, hd2⟩ := opDInput.{u, v} d γ (η / 2) hη2
  refine ⟨max (max C₀ Ce) (max (max Cp1 Cp2) (max Cp4 (max Cd1 Cd2))),
    le_trans hC₀ (le_trans (le_max_left _ _) (le_max_left _ _)), fun m C1 hC1 δ hδ => ?_⟩
  have hC₀' : C₀ ≤ C1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC1
  have hCe' : Ce ≤ C1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC1
  have hCp1' : Cp1 ≤ C1 :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hC1
  have hCp2' : Cp2 ≤ C1 :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hC1
  have hCp4' : Cp4 ≤ C1 :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hC1
  have hCd1' : Cd1 ≤ C1 := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hC1
  have hCd2' : Cd2 ≤ C1 := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hC1
  have hC11 : 1 ≤ C1 := le_trans hC₀ hC₀'
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 hC₀'
  obtain ⟨Re, _, hRe⟩ := hc6d C1 hCe' δ hδ
  obtain ⟨Rp1, hRp1⟩ := hp1 m C1 hCp1' δ hδ
  obtain ⟨Rp2, hRp2⟩ := hp2 m C1 hCp2' δ hδ
  obtain ⟨Rp4, hRp4⟩ := hp4 m C1 hCp4' δ hδ
  obtain ⟨Kd1, Bd1, Rd1, hRd1⟩ := hd1 C1 hCd1' δ hδ
  obtain ⟨Kd2, Bd2, Rd2, hRd2⟩ := hd2 C1 hCd2' δ hδ
  have hε8 : 0 < η ^ 2 / 8 := by positivity
  have hε16 : 0 < η ^ 2 / 16 := by positivity
  obtain ⟨R3, _, hR3⟩ := const_log_le_rpow (C := 2 * (3 ^ d * (2 * d * δ⁻¹ + 1))) 8 hε8
  obtain ⟨R4, _, hR4⟩ := const_log_le_rpow (C := Kd1) Bd1 hε16
  obtain ⟨R5, _, hR5⟩ := const_log_le_rpow (C := Kd2) Bd2 hε16
  obtain ⟨R6, _, hR6⟩ := const_log_le_rpow (C := Ke * (2 * δ⁻¹)) 78 hε8
  set R₀ : ℝ := max (max (max L₀ Re) (max Rp1 Rp2)) (max (max Rp4 (max Rd1 Rd2))
    (max (max R3 R4) (max (max R5 R6) (Real.exp 1)))) with hR₀
  refine ⟨R₀, le_trans hL₀1 (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase hlab
  have hA := le_max_left (max (max L₀ Re) (max Rp1 Rp2)) (max (max Rp4 (max Rd1 Rd2))
    (max (max R3 R4) (max (max R5 R6) (Real.exp 1))))
  have hB := le_max_right (max (max L₀ Re) (max Rp1 Rp2)) (max (max Rp4 (max Rd1 Rd2))
    (max (max R3 R4) (max (max R5 R6) (Real.exp 1))))
  rw [← hR₀] at hA hB
  have hLL₀ : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hA)) hL
  have hLRe : Re ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hA)) hL
  have hLp1 : Rp1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hA)) hL
  have hLp2 : Rp2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hA)) hL
  have hLp4 : Rp4 ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hB)) hL
  have hLd1 : Rd1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hB))) hL
  have hLd2 : Rd2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hB))) hL
  have hL3 : R3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hB))) hL
  have hL4 : R4 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hB))) hL
  have hL5 : R5 ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hB)))) hL
  have hL6 : R6 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hB)))) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hB))) hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have h102a : Prop102At.{u, v} d L γ δ η C1 m := hRp1 L hLp1
  have h102b : Prop102At.{u, v} d L γ δ (η / 2) C1 m := hRp2 L hLp2
  have h102c : Prop102At.{u, v} d L γ δ (η / 2 / 2) C1 m := hRp4 L hLp4
  have hKe : Ke * (2 * δ⁻¹) * Real.log L ^ (78 : ℕ) ≤ L ^ (η ^ 2 / 8) := by
    have := hR6 L hL6
    rwa [show (78 : ℝ) = ((78 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  obtain ⟨v₁, hv₁, hA2⟩ := c6_top_core (m := m) hγ hη (by linarith) hL1 hlog hδ hC11 h102a h102b h102c
    (hRd1 L hLd1) (hRd2 L hLd2) (hR4 L hL4) (hR5 L hL5) hKe (hRe L hLRe) M cls odd Adm P hS hF hsz hP hMA hfr
    hnodd hnc hcase hlab
  obtain ⟨hv₁A, hv₁α⟩ := mem_filter.mp hv₁
  have hlab₁ := hF.labRange v₁ hv₁A hv₁α
  set R0 := (cls v₁).lab with hR0
  have hR0pos : 0 < R0 := lt_of_lt_of_le (inv_pos.mpr hLp) hlab₁.1
  have hRinv : L ^ (γ - η) ≤ R0⁻¹ := by
    have : (L ^ (-γ + η))⁻¹ = L ^ (γ - η) := by rw [← Real.rpow_neg hLp.le]; congr 1; ring
    rw [← this]; exact inv_anti₀ hR0pos hlab₁.2
  set f : ℝ := L ^ (-(γ + 3 * η) / 2) * R0⁻¹ with hf
  have hfge : L ^ ((γ - 5 * η) / 2) ≤ f := by
    calc L ^ ((γ - 5 * η) / 2) = L ^ (-(γ + 3 * η) / 2) * L ^ (γ - η) := by
          rw [← Real.rpow_add hLp]; congr 1; ring
      _ ≤ f := mul_le_mul_of_nonneg_left hRinv (Real.rpow_nonneg hLp.le _)
  have hf1 : 1 ≤ f := le_trans (Real.one_le_rpow hL1 (by linarith [hγ.1, h1])) hfge
  have hX : 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) ≤
      f * L ^ (-(γ - 3 * η) / 2 + η ^ 2 / 8) := by
    have hlog0 : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hL1) _
    have hδ0 : 0 < δ := hδ.1
    have t1 : R0⁻¹ * L ^ (-γ) = f * L ^ (-(γ - 3 * η) / 2) := by
      have : L ^ (-γ) = L ^ (-(γ + 3 * η) / 2) * L ^ (-(γ - 3 * η) / 2) := by
        rw [← Real.rpow_add hLp]; congr 1; ring
      rw [hf, this]; ring
    have t2 : L ^ (γ - 1) ≤ f * L ^ (-(γ - 3 * η) / 2) := by
      calc L ^ (γ - 1) ≤ L ^ ((γ - 5 * η) / 2 + -(γ - 3 * η) / 2) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hγ.2, h2])
        _ = L ^ ((γ - 5 * η) / 2) * L ^ (-(γ - 3 * η) / 2) := Real.rpow_add hLp _ _
        _ ≤ f * L ^ (-(γ - 3 * η) / 2) := mul_le_mul_of_nonneg_right hfge (Real.rpow_nonneg hLp.le _)
    set g : ℝ := f * L ^ (-(γ - 3 * η) / 2) with hg
    have hg0 : 0 ≤ g := by positivity
    have hinv : (R0 / 2)⁻¹ = 2 * R0⁻¹ := by rw [inv_div]; field_simp
    have hCnn : 0 ≤ 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) := by positivity
    have hsum : 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) ≤
        (3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g := by
      have e : (d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) = 2 * (d : ℝ) * δ⁻¹ * (R0⁻¹ * L ^ (-γ)) := by
        rw [hinv]; ring
      rw [e, t1]
      have hdd : 0 ≤ 2 * (d : ℝ) * δ⁻¹ := by positivity
      calc 3 ^ d * (2 * (d : ℝ) * δ⁻¹ * g + L ^ (γ - 1)) ≤ 3 ^ d * (2 * (d : ℝ) * δ⁻¹ * g + g) := by gcongr
        _ = (3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g := by ring
    calc 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)
        ≤ ((3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g) * Real.log L ^ (8 : ℝ) :=
          mul_le_mul_of_nonneg_right hsum hlog0
      _ ≤ ((2 * (3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1))) * Real.log L ^ (8 : ℝ)) * g := by
          have h0 := mul_nonneg (mul_nonneg hCnn hg0) hlog0
          have e : ((2 * (3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1))) * Real.log L ^ (8 : ℝ)) * g =
              ((3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g) * Real.log L ^ (8 : ℝ) +
                ((3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g) * Real.log L ^ (8 : ℝ) := by ring
          rw [e]; linarith
      _ ≤ L ^ (η ^ 2 / 8) * g := mul_le_mul_of_nonneg_right (hR3 L hL3) hg0
      _ = f * L ^ (-(γ - 3 * η) / 2 + η ^ 2 / 8) := by
          rw [hg, Real.rpow_add hLp]; ring
  have hf0 : 0 ≤ f * L ^ (-(γ - 3 * η) / 2 + η ^ 2 / 8) := by positivity
  have hA2' : M.countA L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (f * L ^ (-(γ - 3 * η) / 2 + η ^ 2 / 8 + (-(3 / 5 * γ) + η ^ 2 / 8))) := by
    refine hA2.trans ((mul_le_mul' (ENNReal.ofReal_le_ofReal hX) le_rfl).trans ?_)
    rw [← ENNReal.ofReal_mul hf0, mul_assoc, ← Real.rpow_add hLp]
  have hA1 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have hsplit := finalRHS_ge_split M cls odd hL1 hη.le hF.labRange hv₁
  obtain ⟨e, hfin', he_def⟩ : ∃ e : ℝ, L ^ (-(γ + 3 * η) / 2) * ((cls v₁).lab)⁻¹ * L ^ e ≤
      finalRHS M cls odd L γ η ∧ e =
      ((((alphaAtoms M.atoms cls).card : ℝ) - 1) * ((γ - 5 * η) / 2) +
        ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
          (2 * min γ (1 - γ) + 5 * η ^ 2) * (open Classical in if odd then (0 : ℝ) else 1)) +
        (-(η ^ 5) * (M.rho : ℝ))) := ⟨_, hsplit, rfl⟩
  have hkey := case6_top_arith_low hd hγ.1 hγ.2 hη hsm'
  have he : η ^ 3 * (-η ^ 2 * (M.rho : ℝ) + (16 * (d : ℝ) + 28) *
        (((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) + 1)) +
      (1 - η ^ 3) * (-(γ - 3 * η) / 2 + η ^ 2 / 8 + (-(3 / 5 * γ) + η ^ 2 / 8)) ≤ e := by
    rw [he_def, card_deg_ne_four_even hS hnodd, card_nonEps, hγ0, if_neg hnodd, hcase.1, hcase.2]
    push_cast
    linear_combination hkey
  have hend := endgame hL1 hf1 hA1 hA2' hθ0 hθ1 he
  refine hend.trans (ENNReal.ofReal_le_ofReal ?_)
  calc f * L ^ e = L ^ (-(γ + 3 * η) / 2) * ((cls v₁).lab)⁻¹ * L ^ e := by rw [hf]
    _ ≤ _ := hfin'

end WaveTurbulence.GammaLow.FinalCount.Count
