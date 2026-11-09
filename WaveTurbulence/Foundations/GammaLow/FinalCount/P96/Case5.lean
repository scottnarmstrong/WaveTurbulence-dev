/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Case5Final
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Case23
import Mathlib.Tactic

/-! # Prop 9.6 at `0 < γ ≤ 1/2`, case (5): `V_α = V_β = 1` (DH23 L1887–L1889; M2 §4.9)

Port of main's `case_five_of_vine` / `case5_finish` / `case5_arith` (`FinalCount/Case5*.lean`) with `γ₀ = γ`:
operation (c) on the `α`-chain (printed (operc) suffices, REF-M2 §2.3), Prop 10.4(1) `prop104_one` (all `γ`):
`𝔄₁ ≲ L^{−4γ₀/7}` unless `𝕄₁ ≅ Q′_m`, excluded by main's `case5VineS2_proved` (the vine (II) is LG). Margin
`γ/14 − 3η/2 − 3η² − O(η³)` (M2 §4.9). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8.P101

/-- The exponent arithmetic of case (5). -/
theorem case5_arith_low {d : ℕ} {γ η ρ c : ℝ} (hd : 3 ≤ d) (hγ1 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ γ / 1000) (hρ : 0 ≤ ρ) (hc : c ≤ 2) :
    η ^ 3 * (-η ^ 2 * ρ + (16 * (d : ℝ) + 28) * (c + 1)) +
      (1 - η ^ 3) * (-(γ - 3 * η) / 2 - 4 / 7 * γ + η ^ 2 / 8) ≤
      -γ - 3 * η ^ 2 - η ^ 5 * ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := small_facts_low hd hγ1 hγ2 hη hsm
  have hη3 : η ^ 3 ≤ 1 / 100 := by nlinarith [pow_pos hη 2]
  have hη2 : η ^ 2 ≤ 1 / 100 := by nlinarith
  have hN : η ^ 3 * (16 * (d : ℝ) + 28) ≤ η ^ 2 / 30 := h4
  have hN0 : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
  have hc1 : c + 1 ≤ 3 := by linarith
  have e1 : η ^ 3 * (16 * (d : ℝ) + 28) * (c + 1) ≤ η ^ 3 * (16 * (d : ℝ) + 28) * 3 := by
    by_cases hc0 : 0 ≤ c + 1
    · exact mul_le_mul_of_nonneg_left hc1 hN0
    · have : η ^ 3 * (16 * (d : ℝ) + 28) * (c + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 (by linarith)
      linarith
  have e2 : η ^ 3 * (-η ^ 2 * ρ) = -(η ^ 5 * ρ) := by ring
  nlinarith [pow_pos hη 2, pow_pos hη 3, mul_pos hη hη]


/-- **Case (5) finish.** -/
theorem case5_finish_low {d : ℕ} (hd : 3 ≤ d) {γ η δ L K B R0 ρ c rhs : ℝ} {A : ℝ≥0∞}
    (hγ1 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hη : 0 < η) (hsm : (d : ℝ) * η ≤ γ / 1000) (hδ : 0 < δ)
    (hL1 : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hR0 : L⁻¹ ≤ R0 ∧ R0 ≤ L ^ (-γ + η)) (hK0 : 0 ≤ K)
    (hconst : 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * (K * Real.log L ^ B) ≤ L ^ (η ^ 2 / 8))
    (hρ : 0 ≤ ρ) (hc : c ≤ 2)
    (hA1 : A ≤ ENNReal.ofReal (L ^ (-η ^ 2 * ρ + (16 * (d : ℝ) + 28) * (c + 1))))
    (hA2 : A ≤ ENNReal.ofReal (3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) *
      Real.log L ^ (8 : ℝ) * (K * Real.log L ^ B) * L ^ (-(4 / 7 * γ))))
    (hrhs : L ^ (-(γ + 3 * η) / 2) * R0⁻¹ * L ^ (-γ - 3 * η ^ 2 - η ^ 5 * ρ) ≤ rhs) :
    A ≤ ENNReal.ofReal rhs := by
  obtain ⟨s1, s2, s3, s4⟩ := small_facts_low hd hγ1 hγ2 hη hsm
  have hLp : 0 < L := by linarith
  have hR0pos : 0 < R0 := lt_of_lt_of_le (inv_pos.mpr hLp) hR0.1
  have hRinv : L ^ (γ - η) ≤ R0⁻¹ := by
    have : (L ^ (-γ + η))⁻¹ = L ^ (γ - η) := by rw [← Real.rpow_neg hLp.le]; congr 1; ring
    rw [← this]; exact inv_anti₀ hR0pos hR0.2
  set f : ℝ := L ^ (-(γ + 3 * η) / 2) * R0⁻¹ with hf
  have hfge : L ^ ((γ - 5 * η) / 2) ≤ f := by
    calc L ^ ((γ - 5 * η) / 2) = L ^ (-(γ + 3 * η) / 2) * L ^ (γ - η) := by
          rw [← Real.rpow_add hLp]; congr 1; ring
      _ ≤ f := mul_le_mul_of_nonneg_left hRinv (Real.rpow_nonneg hLp.le _)
  have hf1 : 1 ≤ f := le_trans (Real.one_le_rpow hL1 (by linarith)) hfge
  set Kc : ℝ := K * Real.log L ^ B with hKc
  have hlogB : 0 ≤ Real.log L ^ B := Real.rpow_nonneg (by linarith) _
  have hKc0 : 0 ≤ Kc := mul_nonneg hK0 hlogB
  have hlog0 : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (by linarith) _
  have t1 : R0⁻¹ * L ^ (-γ) = f * L ^ (-(γ - 3 * η) / 2) := by
    have : L ^ (-γ) = L ^ (-(γ + 3 * η) / 2) * L ^ (-(γ - 3 * η) / 2) := by
      rw [← Real.rpow_add hLp]; congr 1; ring
    rw [hf, this]; ring
  have t2 : L ^ (γ - 1) ≤ f * L ^ (-(γ - 3 * η) / 2) := by
    calc L ^ (γ - 1) ≤ L ^ ((γ - 5 * η) / 2 + -(γ - 3 * η) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
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
  have hpow4 : 0 ≤ L ^ (-(4 / 7 * γ)) := Real.rpow_nonneg hLp.le _
  have hX : 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) * Kc *
      L ^ (-(4 / 7 * γ)) ≤ f * L ^ (-(γ - 3 * η) / 2 - 4 / 7 * γ + η ^ 2 / 8) := by
    calc _ ≤ ((3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g) * Real.log L ^ (8 : ℝ) * Kc * L ^ (-(4 / 7 * γ)) := by
          gcongr
      _ = (3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * Kc) * g * L ^ (-(4 / 7 * γ)) := by ring
      _ ≤ L ^ (η ^ 2 / 8) * g * L ^ (-(4 / 7 * γ)) := by
          gcongr
      _ = f * L ^ (-(γ - 3 * η) / 2 - 4 / 7 * γ + η ^ 2 / 8) := by
          have : L ^ (-(γ - 3 * η) / 2 - 4 / 7 * γ + η ^ 2 / 8) =
              L ^ (-(γ - 3 * η) / 2) * L ^ (-(4 / 7 * γ)) * L ^ (η ^ 2 / 8) := by
            rw [← Real.rpow_add hLp, ← Real.rpow_add hLp] <;> congr 1 <;> ring
          rw [this, hg]; ring
  have hA2' : A ≤ ENNReal.ofReal (f * L ^ (-(γ - 3 * η) / 2 - 4 / 7 * γ + η ^ 2 / 8)) :=
    hA2.trans (ENNReal.ofReal_le_ofReal hX)
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have he := case5_arith_low hd hγ1 hγ2 hη hsm hρ hc
  have hend := endgame hL1 hf1 hA1 hA2' hθ0 hθ1 he
  refine hend.trans (ENNReal.ofReal_le_ofReal ?_)
  exact hrhs


theorem case_five_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1)
    (hv : Case5VineS2.{u, v} d γ η) :
    EvenCaseAt.{u, v} d γ η (fun a b => a = 1 ∧ b = 1) := by
  classical
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  rw [hγ0] at hsm
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  obtain ⟨s1, s2, s3, s4⟩ := small_facts_low hd hγ.1 hγ.2 hη hsm
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hη2max : η / 2 ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  have hη4 : 0 < η / 2 / 2 := by positivity
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨Cd, hCd, hopd⟩ := opDInput.{u, v} d γ η hη
  obtain ⟨Cp, hCp, h104⟩ := prop104_one.{u, v} d hd γ hγ01 (η / 2) (by positivity) hη2max
    (prop102InputSz.{u, v} d hd γ (η / 2 / 2) hγ01 hη4 (by rw [hγ0]; linarith) (by linarith))
  refine ⟨max (max C₀ Cd) (2 * Cp), le_trans hC₀ ((le_max_left _ _).trans (le_max_left _ _)), fun m C1 hC1 δ hδ => ?_⟩
  have hC1a : C₀ ≤ C1 := (le_max_left _ _).trans ((le_max_left _ _).trans hC1)
  have hC1b : Cd ≤ C1 := (le_max_right _ _).trans ((le_max_left _ _).trans hC1)
  have hC1c : C1 ≥ 2 * Cp := (le_max_right _ _).trans hC1
  have hC11 : 1 ≤ C1 := le_trans hC₀ hC1a
  have hδ0 := hδ.1
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 hC1a
  obtain ⟨Kd, Bd, Rd, hRd⟩ := hopd C1 hC1b δ hδ
  obtain ⟨R104, hR104⟩ := h104 m C1 hC1c δ hδ
  set K : ℝ := max Kd 0 + 1 with hK
  set B : ℝ := max Bd 0 with hB
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨R3, hR31, hR3⟩ := const_log_le_rpow (C := 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * K) (8 + B) (ε := η ^ 2 / 8)
    (by positivity)
  refine ⟨max (max (max L₀ Rd) (max R104 R3)) (Real.exp 1), le_trans hL₀1 (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)), ?_⟩
  intro L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcnd
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLRd : Rd ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLR104 : R104 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLR3 : R3 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  by_cases hA : ∃ κ, Adm κ
  swap
  · push Not at hA
    rw [countA_zero_of_noAdm M L γ δ C1 Adm P hA]; exact bot_le
  obtain ⟨κ0, hκ0⟩ := hA
  obtain ⟨hα, hβ⟩ := hcnd
  obtain ⟨a₀, b₀, ha₀, hb₀, hαa, hβb, hab, hchar, hdeg2a, hdeg2b, hdeg4⟩ := c5_atoms hS hnodd hα hβ
  have hEps : ∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → (cls v).IsEps := by
    intro v hv h1 h2
    by_contra hn
    rcases (hchar v hv).mp hn with h | h
    · exact h1 h
    · exact h2 h
  have han : ¬ (cls a₀).IsEps := alpha_not_eps hαa
  have hbn : ¬ (cls b₀).IsEps := beta_not_eps hβb
  obtain ⟨K0, hK0c, ha₀K⟩ := exists_chainSet M cls ha₀ han
  have hKsub : ∀ v ∈ K0, v = a₀ ∨ v = b₀ := fun v hv => (hchar v (hK0c.2.1 hv)).mp (hK0c.2.2.1 v hv)
  -- the gap of the α-atom
  have hlab := hF.labRange a₀ ha₀ hαa
  set R0 := (cls a₀).lab with hR0
  have hR0pos : 0 < R0 := lt_of_lt_of_le (inv_pos.mpr hLp) hlab.1
  have hdv : M.deg a₀ = 2 := hdeg2a
  have hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ K0 ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      R0 / 2 ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := by
    intro κ hκ
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_darts M hdv
    exact ⟨x, y, hx ▸ ha₀K, hy.trans hx.symm, hxy, (hF.alphaGap κ hκ a₀ ha₀ hαa x y hx hy hxy).1⟩
  have hNB : ∀ v ∈ M.atoms, (cls v).IsEps → ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ → M.IsAlphaCut v v₂ x₁ x₂ :=
    fun v hv hε v₂ x₁ x₂ hc => noBeta_eps hS hF hLp hκ0 hv hε hc
  have hconst : 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * (K * Real.log L ^ B) ≤ L ^ (η ^ 2 / 8) := by
    have h := hR3 L hLR3
    have hl0 : 0 < Real.log L := by linarith
    rw [Real.rpow_add hl0] at h
    calc _ = 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * K * (Real.log L ^ (8 : ℝ) * Real.log L ^ B) := by ring
      _ ≤ _ := h
  have hKge : 1 ≤ K * Real.log L ^ B := by
    have h1 : 1 ≤ K := by rw [hK]; have := le_max_right Kd 0; linarith
    have h2 : 1 ≤ Real.log L ^ B := Real.one_le_rpow hlog (le_max_right Bd 0)
    nlinarith
  -- the common bound
  have hbound : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal
      (3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) *
        (K * Real.log L ^ B) * L ^ (-(4 / 7 * min γ (1 - γ)))) := by
    have hcost0 : 0 ≤ 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) := by
      have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Real.log L) (8 : ℝ)
      positivity
    have hKc0 : 0 ≤ K * Real.log L ^ B := by linarith
    have hP104 : P104At.{u, v} d γ δ (η / 2) C1 L m := hR104 L hLR104
    by_cases hb : b₀ ∈ K0
    · have hKeq : K0 = {a₀, b₀} := by
        ext x; constructor
        · intro hx; rcases hKsub x hx with rfl | rfl <;> simp
        · intro hx; rcases mem_insert.mp hx with rfl | h
          · exact ha₀K
          · rw [mem_singleton.mp h]; exact hb
      have := s1_key (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) (ρ := R0 / 2) hγ01 hL1 hlog hδ hC11
        (half_pos hR0pos) hP104 M cls odd Adm P hS hF hnodd hnc hη hP hMA hsz ha₀ hb₀ hab hdeg2a hdeg2b hdeg4 hEps
        hK0c hKeq hAdm hfr hNB
      refine this.trans ?_
      rw [← ENNReal.ofReal_mul hcost0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hX := Real.rpow_nonneg hLp.le (-(4 / 7 * min γ (1 - γ)))
      nlinarith [mul_le_mul_of_nonneg_left hKge hcost0, mul_nonneg hcost0 hX]
    · have hKeq : K0 = {a₀} := by
        ext x; constructor
        · intro hx; rcases hKsub x hx with rfl | rfl
          · simp
          · exact absurd hx hb
        · intro hx; rw [mem_singleton.mp hx]; exact ha₀K
      have hKb : IsChainSet M cls {b₀} := chain_single_b hb₀ hbn hK0c hchar hb ha₀K
      have hK1 : IsChainSet M cls {a₀} := hKeq ▸ hK0c
      have hAdm' : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ ({a₀} : Finset V) ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
          R0 / 2 ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := by
        intro κ hκ; rw [hKeq] at hAdm; exact hAdm κ hκ
      have := s2_key (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) (ρ := R0 / 2) (Kd := Kd) (Bd := Bd) hγ01 hL1 hlog hδ
        hC11 (half_pos hR0pos) hP104 (hRd L hLRd) M cls odd Adm P hS hF hnodd hnc hη hP hMA hsz ha₀ hb₀ hab hdeg2a
        hdeg2b hdeg4 hEps hK1 hKb hAdm' hfr hNB
        (hv L M cls odd Adm hS hF ⟨κ0, hκ0⟩ hnodd hfr ha₀ hb₀ hab hαa hβb hdeg2a hdeg2b hdeg4 hK1 hKb)
      refine this.trans ?_
      have hl : Real.log L ^ Bd ≤ Real.log L ^ B := Real.rpow_le_rpow_of_exponent_le hlog (le_max_left Bd 0)
      have hl0 : 0 ≤ Real.log L ^ Bd := Real.rpow_nonneg (by linarith) _
      have hKd : Kd * Real.log L ^ Bd ≤ K * Real.log L ^ B := by
        have h1 : Kd * Real.log L ^ Bd ≤ max Kd 0 * Real.log L ^ Bd := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0
        have h2 : max Kd 0 * Real.log L ^ Bd ≤ max Kd 0 * Real.log L ^ B :=
          mul_le_mul_of_nonneg_left hl (le_max_right _ _)
        have h3 : max Kd 0 * Real.log L ^ B ≤ K * Real.log L ^ B :=
          mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (Real.rpow_nonneg (by linarith) _)
        linarith
      calc _ ≤ ENNReal.ofReal (3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) *
            (ENNReal.ofReal (K * Real.log L ^ B) * ENNReal.ofReal (L ^ (-(4 / 7 * min γ (1 - γ))))) :=
            mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hKd) le_rfl)
        _ = _ := ofReal_mul3 hcost0 hKc0
  -- the final interpolation
  have hA1 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hcard : (M.atoms.filter fun a => M.deg a ≠ 4).card = 2 := by
    rw [card_deg_ne_four_even hS hnodd, card_nonEps, hα, hβ]
  have hsplit := finalRHS_ge_split M cls odd hL1 hη.le hF.labRange (v₀ := a₀) (mem_filter.mpr ⟨ha₀, hαa⟩)
  rw [hγ0] at hbound
  refine case5_finish_low hd hγ.1 hγ.2 hη hsm hδ0 hL1 hlog ⟨hlab.1, hlab.2⟩ hK0 hconst
    (ρ := (M.rho : ℝ)) (c := 2) (Nat.cast_nonneg _) (le_refl _) ?_ hbound ?_
  · refine hA1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    congr 1
    rw [hcard]; push_cast; ring
  · refine le_trans (le_of_eq ?_) hsplit
    rw [hR0]
    congr 2
    rw [hα, hβ, if_neg hnodd, hγ0]; push_cast; ring


/-- Case (5) at `γ ≤ 1/2` in the shape `EvenCaseAt`. -/
theorem case_five_low_even (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    EvenCaseAt.{u, v} d γ η (fun a b => a = 1 ∧ b = 1) :=
  case_five_low d hd γ hγ η hη hsm hηs (case5VineS2_proved d γ η)

end WaveTurbulence.GammaLow.FinalCount
