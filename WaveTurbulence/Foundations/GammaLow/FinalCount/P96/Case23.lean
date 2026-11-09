/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Case23_96
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Odd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ops.ChainLow
import Mathlib.Tactic

/-! # Prop 9.6 at `0 < γ ≤ 1/2`, cases (2) and (3) (DH23 L1878–L1881; M2 §4.6–4.7)

Ports of main's `case_two` / `case_three` (`FinalCount/Case23_96.lean`) with `γ₀ = γ`:
* (2) `V_β ≥ 3`: operation (c) with the SHARP bound (`chain_A_bound_triv`, trivial branch `3^d L^γ`; erratum F-M2-1:
  the printed (operc) loses `1 − 2γ` here), then Prop 10.1′: `𝔄₀ ≲ L^{γ₀ + η²/8}`. Margin `≥ η²(1 − 4/30)` (M2 §4.6).
* (3) `V_β = 2, V_α ≥ 1` or `V_β = 1, V_α ≥ 3`: operation (c) through an `α`-atom (`chain_A_bound_low`, the printed
  ρ⁻¹ form suffices, REF-M2 §2.3), margins `(γ − 3η)/2 − …`, `(γ − 13η)/2 − …` (M2 §4.7). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8.P101

/-- Common smallness facts for `η ≪_{d,γ} 1` at `γ ≤ 1/2` (`γ₀ = γ`). -/
theorem small_facts_low {d : ℕ} {γ η : ℝ} (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ γ / 1000) :
    η ≤ γ / 3000 ∧ η ≤ 1 / 6000 ∧ η ^ 3 * (16 * (d : ℝ) + 28) ≤ γ / 30 * η ^ 2 ∧
      η ^ 3 * (16 * (d : ℝ) + 28) ≤ η ^ 2 / 30 := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : η ≤ γ / 3000 := by nlinarith
  have h2 : η ≤ 1 / 6000 := by linarith
  have e : η ^ 3 * (16 * (d : ℝ) + 28) = η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) := by ring
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [e]; nlinarith [pow_pos hη 2]
  · rw [e]; nlinarith [pow_pos hη 2]

/-- Case (2) arithmetic at `γ ≤ 1/2`: `𝔄₀ ≲ L^{γ + η²/8}` interpolated with roughbd beats (finalcount). -/
theorem case2_arith_low {d : ℕ} {γ η Va Vb : ℝ} (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ γ / 1000) (hVa : 0 ≤ Va) (hVb : 3 ≤ Vb) :
    η ^ 3 * (16 * (d : ℝ) + 28) * (Va + Vb + 1) + (1 - η ^ 3) * (γ + η ^ 2 / 8) ≤
      Va * ((γ - 5 * η) / 2) + ((γ + 2 * η ^ 2) * Vb - (2 * γ + 5 * η ^ 2) * 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := small_facts_low hd hγ0 hγ1 hη hsm
  have hc : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
  have hν : η ^ 3 * (16 * (d : ℝ) + 28) ≤ γ / 10 := by
    nlinarith [pow_pos hη 2, pow_le_one₀ hη.le (by linarith : η ≤ 1) (n := 2)]
  have hc1 : γ / 10 ≤ (γ - 5 * η) / 2 := by nlinarith
  have hc2 : γ / 10 ≤ γ + 2 * η ^ 2 := by nlinarith [pow_pos hη 2]
  have hη3 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  set N := η ^ 3 * (16 * (d : ℝ) + 28) with hN
  have hw : 0 ≤ Vb - 3 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hc1 hVa, mul_le_mul_of_nonneg_left hc2 hw,
    mul_le_mul_of_nonneg_right hν hVa, mul_le_mul_of_nonneg_right hν hw, pow_pos hη 2, pow_pos hη 3,
    mul_nonneg hγ0.le (pow_pos hη 3).le]

/-- Case (3) arithmetic at `γ ≤ 1/2`. -/
theorem case3_arith_low {d : ℕ} {γ η Va Vb : ℝ} (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ γ / 1000) (hcase : (Vb = 2 ∧ 1 ≤ Va) ∨ (Vb = 1 ∧ 3 ≤ Va)) :
    η ^ 3 * (16 * (d : ℝ) + 28) * (Va + Vb + 1) - (1 - η ^ 3) * ((γ - 3 * η) / 2) + (1 - η ^ 3) * (η ^ 2 / 8) ≤
      (Va - 1) * ((γ - 5 * η) / 2) + ((γ + 2 * η ^ 2) * Vb - (2 * γ + 5 * η ^ 2) * 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := small_facts_low hd hγ0 hγ1 hη hsm
  have hν : η ^ 3 * (16 * (d : ℝ) + 28) ≤ γ / 10 := by
    nlinarith [pow_pos hη 2, pow_le_one₀ hη.le (by linarith : η ≤ 1) (n := 2)]
  have hc1 : γ / 10 ≤ (γ - 5 * η) / 2 := by nlinarith
  have hη3 : η ^ 3 ≤ 1 / 100 := by nlinarith [pow_pos hη 2]
  have hη2 : η ^ 2 ≤ 1 / 100 := by nlinarith
  have hη2' : η ^ 2 ≤ η / 6000 := by nlinarith
  set N := η ^ 3 * (16 * (d : ℝ) + 28) with hN
  have hN0 : 0 ≤ N := by positivity
  rcases hcase with ⟨hb, ha⟩ | ⟨hb, ha⟩
  · subst hb
    have hu : 0 ≤ Va - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hν hu, mul_le_mul_of_nonneg_left hc1 hu, pow_pos hη 2, pow_pos hη 3,
      mul_nonneg (pow_pos hη 3).le hγ0.le]
  · subst hb
    have hu : 0 ≤ Va - 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hν hu, mul_le_mul_of_nonneg_left hc1 hu, pow_pos hη 2, pow_pos hη 3,
      mul_nonneg (pow_pos hη 3).le hγ0.le]

/-- **Case (2): `V_β ≥ 3`.** -/
theorem case_two_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → ¬ odd →
        (¬ ∀ a ∈ M.atoms, M.deg a = 2) → 3 ≤ (betaAtoms M.atoms cls).card →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  rw [hγ0] at hsm
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  obtain ⟨h1, h2, h3, h4⟩ := small_facts_low hd hγ.1 hγ.2 hη hsm
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hηmax : η ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨Cs, hCs, hchain⟩ := chain_A_bound_triv.{u, v} d hd γ hγ01 η hη hηmax
  refine ⟨max C₀ Cs, le_trans hC₀ (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 ((le_max_left _ _).trans hC1)
  obtain ⟨Rc, hRc1, hRc⟩ := hchain C1 ((le_max_right _ _).trans hC1) δ hδ
  obtain ⟨R3, hR31, hR3⟩ := const_log_le_rpow (C := 3 ^ d) (ε := η ^ 2 / 8) 8 (by positivity)
  refine ⟨max (max L₀ Rc) (max R3 (Real.exp 1)), le_trans hL₀1 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hnodd hnc hVb
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLRc : Rc ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLR3 : R3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hδ0 := hδ.1
  -- the chain through a β-atom
  obtain ⟨b, hbβ⟩ := card_pos.mp (by omega : 0 < (betaAtoms M.atoms cls).card)
  obtain ⟨hbA, hbB⟩ := mem_filter.mp hbβ
  have hbn : ¬ (cls b).IsEps := beta_not_eps hbB
  obtain ⟨K, hK, hbK⟩ := exists_chainSet M cls hbA hbn
  have hdb : M.deg b = 2 := by
    have := (hS.classes b hbA).mpr hbn
    rcases hS.evenDeg hnodd b hbA with h | h <;> omega
  have hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      L⁻¹ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := by
    intro κ hκ
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_darts M hdb
    exact ⟨x, y, hx ▸ hbK, hy.trans hx.symm, hxy,
      gap_lower_of_ne hLp (hF.betaGap κ hκ b hbA hbB x y hx hy hxy)⟩
  have hA2 := hRc L hLRc L⁻¹ (inv_pos.mpr hLp) M cls odd Adm P hS hF hnodd hnc hP hMA K hK hAdm
  -- A ≲ L^{γ₀+η²/8} with γ₀ = γ (sharp operation (c), trivial branch)
  have hX : 3 ^ d * L ^ γ * Real.log L ^ (8 : ℝ) ≤ 1 * L ^ (γ + η ^ 2 / 8) := by
    rw [one_mul, Real.rpow_add hLp]
    calc 3 ^ d * L ^ γ * Real.log L ^ (8 : ℝ) = (3 ^ d * Real.log L ^ (8 : ℝ)) * L ^ γ := by ring
      _ ≤ L ^ (η ^ 2 / 8) * L ^ γ := mul_le_mul_of_nonneg_right (hR3 L hLR3) (Real.rpow_nonneg hLp.le _)
      _ = L ^ γ * L ^ (η ^ 2 / 8) := mul_comm _ _
  have hA2' : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (1 * L ^ (γ + η ^ 2 / 8)) :=
    hA2.trans (ENNReal.ofReal_le_ofReal hX)
  have hA1 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have hfin := finalRHS_ge M cls odd hL1 hη.le hF.labRange
  obtain ⟨e, hfin', he_def⟩ : ∃ e : ℝ, L ^ e ≤ finalRHS M cls odd L γ η ∧ e =
      (((alphaAtoms M.atoms cls).card : ℝ) * ((γ - 5 * η) / 2) +
        ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
          (2 * min γ (1 - γ) + 5 * η ^ 2) * (open Classical in if odd then (0 : ℝ) else 1)) +
        (-(η ^ 5) * (M.rho : ℝ))) := ⟨_, hfin, rfl⟩
  have hVb3 : (3 : ℝ) ≤ ((betaAtoms M.atoms cls).card : ℝ) := by exact_mod_cast hVb
  have hkey := case2_arith_low (d := d) (γ := γ) (η := η) (Va := ((alphaAtoms M.atoms cls).card : ℝ))
    (Vb := ((betaAtoms M.atoms cls).card : ℝ)) hd hγ.1 hγ.2 hη hsm (Nat.cast_nonneg _) hVb3
  have he : η ^ 3 * (-η ^ 2 * (M.rho : ℝ) + (16 * (d : ℝ) + 28) *
        (((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) + 1)) + (1 - η ^ 3) * (γ + η ^ 2 / 8) ≤ e := by
    rw [he_def, card_deg_ne_four_even hS hnodd, card_nonEps, hγ0, if_neg hnodd]
    push_cast
    nlinarith [hkey]
  have hend := endgame hL1 le_rfl hA1 hA2' hθ0 hθ1 he
  exact hend.trans (ENNReal.ofReal_le_ofReal (by rw [one_mul]; exact hfin'))



/-- **Case (3): `V_β = 2, V_α ≥ 1` or `V_β = 1, V_α ≥ 3`.** -/
theorem case_three_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → ¬ odd →
        (¬ ∀ a ∈ M.atoms, M.deg a = 2) →
        (((betaAtoms M.atoms cls).card = 2 ∧ 1 ≤ (alphaAtoms M.atoms cls).card) ∨
          ((betaAtoms M.atoms cls).card = 1 ∧ 3 ≤ (alphaAtoms M.atoms cls).card)) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  rw [hγ0] at hsm
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  obtain ⟨h1, h2, h3, h4⟩ := small_facts_low hd hγ.1 hγ.2 hη hsm
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hηmax : η ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨Cs, hCs, hchain⟩ := chain_A_bound_low.{u, v} d hd γ hγ01 η hη hηmax
  refine ⟨max C₀ Cs, le_trans hC₀ (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 ((le_max_left _ _).trans hC1)
  obtain ⟨Rc, hRc1, hRc⟩ := hchain C1 ((le_max_right _ _).trans hC1) δ hδ
  obtain ⟨R3, hR31, hR3⟩ := const_log_le_rpow (C := 2 * (3 ^ d * (2 * d * δ⁻¹ + 1))) (ε := η ^ 2 / 8) 8 (by positivity)
  refine ⟨max (max L₀ Rc) (max R3 (Real.exp 1)), le_trans hL₀1 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hnodd hnc hcase
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLRc : Rc ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLR3 : R3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hδ0 := hδ.1
  -- an α-atom
  have hVa1 : 1 ≤ (alphaAtoms M.atoms cls).card := by rcases hcase with h | h <;> omega
  obtain ⟨v₀, hv₀⟩ := card_pos.mp (by omega : 0 < (alphaAtoms M.atoms cls).card)
  obtain ⟨hv₀A, hv₀α⟩ := mem_filter.mp hv₀
  have hv₀n : ¬ (cls v₀).IsEps := alpha_not_eps hv₀α
  obtain ⟨K, hK, hv₀K⟩ := exists_chainSet M cls hv₀A hv₀n
  have hdv : M.deg v₀ = 2 := by
    have := (hS.classes v₀ hv₀A).mpr hv₀n
    rcases hS.evenDeg hnodd v₀ hv₀A with h | h <;> omega
  have hlab := hF.labRange v₀ hv₀A hv₀α
  set R0 := (cls v₀).lab with hR0
  have hR0pos : 0 < R0 := lt_of_lt_of_le (inv_pos.mpr hLp) hlab.1
  have hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      R0 / 2 ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := by
    intro κ hκ
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_darts M hdv
    exact ⟨x, y, hx ▸ hv₀K, hy.trans hx.symm, hxy, (hF.alphaGap κ hκ v₀ hv₀A hv₀α x y hx hy hxy).1⟩
  have hA2 := hRc L hLRc (R0 / 2) (by positivity) M cls odd Adm P hS hF hnodd hnc hP hMA K hK hAdm
  -- A ≲ f L^{-(γ-3η)/2 + η²/8}
  have hRinv : L ^ (γ - η) ≤ R0⁻¹ := by
    have : (L ^ (-γ + η))⁻¹ = L ^ (γ - η) := by rw [← Real.rpow_neg hLp.le]; congr 1; ring
    rw [← this]; exact inv_anti₀ hR0pos hlab.2
  set f : ℝ := L ^ (-(γ + 3 * η) / 2) * R0⁻¹ with hf
  have hfge : L ^ ((γ - 5 * η) / 2) ≤ f := by
    calc L ^ ((γ - 5 * η) / 2) = L ^ (-(γ + 3 * η) / 2) * L ^ (γ - η) := by
          rw [← Real.rpow_add hLp]; congr 1; ring
      _ ≤ f := mul_le_mul_of_nonneg_left hRinv (Real.rpow_nonneg hLp.le _)
  have hf1 : 1 ≤ f := le_trans (Real.one_le_rpow hL1 (by linarith [hγ.1, h1])) hfge
  have hX : 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) ≤
      f * L ^ (-(γ - 3 * η) / 2 + η ^ 2 / 8) := by
    have hlog0 : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hL1) _
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
          nlinarith [mul_nonneg (mul_nonneg hCnn hg0) hlog0]
      _ ≤ L ^ (η ^ 2 / 8) * g := mul_le_mul_of_nonneg_right (hR3 L hLR3) hg0
      _ = f * L ^ (-(γ - 3 * η) / 2 + η ^ 2 / 8) := by
          rw [hg, Real.rpow_add hLp]; ring
  have hA2' : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (f * L ^ (-(γ - 3 * η) / 2 + η ^ 2 / 8)) :=
    hA2.trans (ENNReal.ofReal_le_ofReal hX)
  have hA1 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have hsplit := finalRHS_ge_split M cls odd hL1 hη.le hF.labRange hv₀
  obtain ⟨e, hfin', he_def⟩ : ∃ e : ℝ, L ^ (-(γ + 3 * η) / 2) * ((cls v₀).lab)⁻¹ * L ^ e ≤ finalRHS M cls odd L γ η ∧ e =
      ((((alphaAtoms M.atoms cls).card : ℝ) - 1) * ((γ - 5 * η) / 2) +
        ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
          (2 * min γ (1 - γ) + 5 * η ^ 2) * (open Classical in if odd then (0 : ℝ) else 1)) +
        (-(η ^ 5) * (M.rho : ℝ))) := ⟨_, hsplit, rfl⟩
  have hcase' : ((betaAtoms M.atoms cls).card : ℝ) = 2 ∧ 1 ≤ ((alphaAtoms M.atoms cls).card : ℝ) ∨
      ((betaAtoms M.atoms cls).card : ℝ) = 1 ∧ 3 ≤ ((alphaAtoms M.atoms cls).card : ℝ) := by
    rcases hcase with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact Or.inl ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
    · exact Or.inr ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
  have hkey := case3_arith_low (d := d) (γ := γ) (η := η) (Va := ((alphaAtoms M.atoms cls).card : ℝ))
    (Vb := ((betaAtoms M.atoms cls).card : ℝ)) hd hγ.1 hγ.2 hη hsm
    (by rcases hcase' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact Or.inl ⟨h1', h2'⟩
        · exact Or.inr ⟨h1', h2'⟩)
  have he : η ^ 3 * (-η ^ 2 * (M.rho : ℝ) + (16 * (d : ℝ) + 28) *
        (((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) + 1)) +
      (1 - η ^ 3) * (-(γ - 3 * η) / 2 + η ^ 2 / 8) ≤ e := by
    rw [he_def, card_deg_ne_four_even hS hnodd, card_nonEps, hγ0, if_neg hnodd]
    push_cast
    linear_combination hkey
  have hend := endgame hL1 hf1 hA1 hA2' hθ0 hθ1 he
  refine hend.trans (ENNReal.ofReal_le_ofReal ?_)
  calc f * L ^ e = L ^ (-(γ + 3 * η) / 2) * ((cls v₀).lab)⁻¹ * L ^ e := by rw [hf]
    _ ≤ _ := hfin'

end WaveTurbulence.GammaLow.FinalCount
