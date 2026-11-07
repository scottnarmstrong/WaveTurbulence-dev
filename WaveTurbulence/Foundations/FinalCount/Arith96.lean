/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Prop96Statement
import Mathlib.Tactic

/-! # Prop 9.6: arithmetic of the right-hand side (finalcount)

Lower bounds of `finalRHS` by powers of `L`, and the absorption of constants into small powers of `L`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8

/-- A constant is absorbed by a positive power of `L` for `L` large. -/
theorem const_le_rpow {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ L ≥ R, C ≤ L ^ ε := by
  refine ⟨max 1 ((C + 1) ^ (1 / ε)), le_max_left _ _, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have h1 : (C + 1) ^ (1 / ε) ≤ L := (le_max_right _ _).trans hL
  have h2 : ((C + 1) ^ (1 / ε)) ^ ε ≤ L ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
  rw [← Real.rpow_mul (by linarith)] at h2
  rw [one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at h2
  linarith

/-- Absorption of a constant times a polylog into a power: `C (log L)^s ≤ L^ε` for `L` large. -/
theorem const_log_le_rpow {C ε : ℝ} (s : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ L ≥ R, C * Real.log L ^ s ≤ L ^ ε := by
  have h := (isLittleO_log_rpow_rpow_atTop s hε).def (c := 1 / (|C| + 1)) (by positivity)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp h
  refine ⟨max R (Real.exp 1), le_trans (Real.one_le_exp (by norm_num)) (le_max_right _ _), fun L hL => ?_⟩
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have h1 := hR L hLR
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog s), Real.norm_of_nonneg (Real.rpow_nonneg hL0.le ε)] at h1
  have h2 : (|C| + 1) * Real.log L ^ s ≤ L ^ ε := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ |C| + 1)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  calc C * Real.log L ^ s ≤ (|C| + 1) * Real.log L ^ s :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Real.rpow_nonneg hlog s)
    _ ≤ L ^ ε := h2


section rhs
open Classical
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem alpha_factor_ge {L γ η R : ℝ} {κ : ℕ} (hL : 1 ≤ L) (hη : 0 ≤ η) (hR : 0 < R)
    (hRu : R ≤ L ^ (-γ + η)) :
    L ^ ((γ - 5 * η) / 2) ≤ L ^ (-(γ + 3 * η) / 2 + (κ : ℝ) * η) * R⁻¹ := by
  have hL0 : 0 < L := by linarith
  have h1 : L ^ (γ - η) ≤ R⁻¹ := by
    have : (L ^ (-γ + η))⁻¹ = L ^ (γ - η) := by
      rw [← Real.rpow_neg hL0.le]; congr 1; ring
    rw [← this]
    exact inv_anti₀ hR hRu
  have h2 : L ^ ((γ - 5 * η) / 2) ≤ L ^ (-(γ + 3 * η) / 2 + (κ : ℝ) * η) * L ^ (γ - η) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by nlinarith [Nat.cast_nonneg (α := ℝ) κ])
  calc _ ≤ _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hL0.le _)

theorem alphaProd_ge (M : Molecule V D) (cls : V → Cls) {L γ η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hlab : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η)) :
    L ^ (((alphaAtoms M.atoms cls).card : ℝ) * ((γ - 5 * η) / 2)) ≤
      ∏ v ∈ alphaAtoms M.atoms cls, (L ^ (-(γ + 3 * η) / 2 + ((cls v).kap : ℝ) * η) * ((cls v).lab)⁻¹) := by
  have hL0 : 0 < L := by linarith
  have hprod : ∏ v ∈ alphaAtoms M.atoms cls, L ^ ((γ - 5 * η) / 2) = L ^ (((alphaAtoms M.atoms cls).card : ℝ) * ((γ - 5 * η) / 2)) := by
    rw [prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, mul_comm]
  rw [← hprod]
  apply Finset.prod_le_prod₀
  · exact fun _ _ => Real.rpow_nonneg hL0.le _
  intro v hv
  have hv' := (mem_filter.mp hv)
  have := hlab v hv'.1 hv'.2
  exact alpha_factor_ge hL hη (lt_of_lt_of_le (inv_pos.mpr hL0) this.1) this.2

theorem finalRHS_ge (M : Molecule V D) (cls : V → Cls) (odd : Prop) {L γ η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hlab : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η)) :
    L ^ (((alphaAtoms M.atoms cls).card : ℝ) * ((γ - 5 * η) / 2) +
      ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
        (2 * min γ (1 - γ) + 5 * η ^ 2) * (open Classical in if odd then (0 : ℝ) else 1)) +
      (-(η ^ 5) * (M.rho : ℝ))) ≤ finalRHS M cls odd L γ η := by
  have hL0 : 0 < L := by linarith
  unfold finalRHS
  simp only []
  rw [Real.rpow_add hL0, Real.rpow_add hL0]
  have h := alphaProd_ge M cls hL hη hlab
  have h1 := Real.rpow_nonneg hL0.le ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
        (2 * min γ (1 - γ) + 5 * η ^ 2) * (open Classical in if odd then (0 : ℝ) else 1))
  have h2 := Real.rpow_nonneg hL0.le (-(η ^ 5) * (M.rho : ℝ))
  have hnn : 0 ≤ ∏ v ∈ alphaAtoms M.atoms cls, (L ^ (-(γ + 3 * η) / 2 + ((cls v).kap : ℝ) * η) * ((cls v).lab)⁻¹) := by
    refine Finset.prod_nonneg fun v hv => ?_
    have hv' := mem_filter.mp hv
    have := hlab v hv'.1 hv'.2
    exact mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.mpr ((inv_pos.mpr hL0).le.trans this.1))
  exact mul_le_mul (mul_le_mul_of_nonneg_right h h1) le_rfl h2 (mul_nonneg hnn h1)


theorem alphaProd_ge_sub (M : Molecule V D) (cls : V → Cls) {L γ η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hlab : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η))
    (T : Finset V) (hT : T ⊆ alphaAtoms M.atoms cls) :
    L ^ ((T.card : ℝ) * ((γ - 5 * η) / 2)) ≤
      ∏ v ∈ T, (L ^ (-(γ + 3 * η) / 2 + ((cls v).kap : ℝ) * η) * ((cls v).lab)⁻¹) := by
  have hL0 : 0 < L := by linarith
  have hprod : ∏ v ∈ T, L ^ ((γ - 5 * η) / 2) = L ^ ((T.card : ℝ) * ((γ - 5 * η) / 2)) := by
    rw [prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, mul_comm]
  rw [← hprod]
  apply Finset.prod_le_prod₀
  · exact fun _ _ => Real.rpow_nonneg hL0.le _
  intro v hv
  have hv' := (mem_filter.mp (hT hv))
  have := hlab v hv'.1 hv'.2
  exact alpha_factor_ge hL hη (lt_of_lt_of_le (inv_pos.mpr hL0) this.1) this.2

/-- `finalRHS` with one distinguished `α`-atom `v₀` split off. -/
theorem finalRHS_ge_split (M : Molecule V D) (cls : V → Cls) (odd : Prop) {L γ η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hlab : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η))
    {v₀ : V} (hv₀ : v₀ ∈ alphaAtoms M.atoms cls) :
    L ^ (-(γ + 3 * η) / 2) * ((cls v₀).lab)⁻¹ *
      L ^ ((((alphaAtoms M.atoms cls).card : ℝ) - 1) * ((γ - 5 * η) / 2) +
        ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
          (2 * min γ (1 - γ) + 5 * η ^ 2) * (if odd then (0 : ℝ) else 1)) +
        (-(η ^ 5) * (M.rho : ℝ))) ≤ finalRHS M cls odd L γ η := by
  have hL0 : 0 < L := by linarith
  unfold finalRHS
  simp only []
  rw [← Finset.mul_prod_erase _ _ hv₀]
  set T := (alphaAtoms M.atoms cls).erase v₀ with hT
  have hTsub : T ⊆ alphaAtoms M.atoms cls := erase_subset _ _
  have hTc : (T.card : ℝ) = ((alphaAtoms M.atoms cls).card : ℝ) - 1 := by
    rw [hT, card_erase_of_mem hv₀, Nat.cast_sub (card_pos.mpr ⟨v₀, hv₀⟩)]; simp
  have hprod := alphaProd_ge_sub M cls hL hη hlab T hTsub
  rw [hTc] at hprod
  have hv' := mem_filter.mp hv₀
  have hl := hlab v₀ hv'.1 hv'.2
  have hlabpos : 0 < (cls v₀).lab := lt_of_lt_of_le (inv_pos.mpr hL0) hl.1
  have hf : L ^ (-(γ + 3 * η) / 2) * ((cls v₀).lab)⁻¹ ≤
      L ^ (-(γ + 3 * η) / 2 + ((cls v₀).kap : ℝ) * η) * ((cls v₀).lab)⁻¹ := by
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hlabpos.le)
    exact Real.rpow_le_rpow_of_exponent_le hL (by nlinarith [Nat.cast_nonneg (α := ℝ) (cls v₀).kap])
  have hexp : L ^ ((((alphaAtoms M.atoms cls).card : ℝ) - 1) * ((γ - 5 * η) / 2) +
        ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
          (2 * min γ (1 - γ) + 5 * η ^ 2) * (if odd then (0 : ℝ) else 1)) +
        (-(η ^ 5) * (M.rho : ℝ))) =
      L ^ ((((alphaAtoms M.atoms cls).card : ℝ) - 1) * ((γ - 5 * η) / 2)) *
        L ^ ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
          (2 * min γ (1 - γ) + 5 * η ^ 2) * (if odd then (0 : ℝ) else 1)) *
        L ^ (-(η ^ 5) * (M.rho : ℝ)) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0]
  rw [hexp]
  have h1 := Real.rpow_nonneg hL0.le ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
        (2 * min γ (1 - γ) + 5 * η ^ 2) * (if odd then (0 : ℝ) else 1))
  have h2 := Real.rpow_nonneg hL0.le (-(η ^ 5) * (M.rho : ℝ))
  have hfn : 0 ≤ L ^ (-(γ + 3 * η) / 2) * ((cls v₀).lab)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.mpr hlabpos.le)
  have hfull : 0 ≤ L ^ (-(γ + 3 * η) / 2 + ((cls v₀).kap : ℝ) * η) * ((cls v₀).lab)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.mpr hlabpos.le)
  have hcore : L ^ (-(γ + 3 * η) / 2) * ((cls v₀).lab)⁻¹ *
        L ^ ((((alphaAtoms M.atoms cls).card : ℝ) - 1) * ((γ - 5 * η) / 2)) ≤
      (L ^ (-(γ + 3 * η) / 2 + ((cls v₀).kap : ℝ) * η) * ((cls v₀).lab)⁻¹) *
        ∏ v ∈ T, (L ^ (-(γ + 3 * η) / 2 + ((cls v).kap : ℝ) * η) * ((cls v).lab)⁻¹) :=
    mul_le_mul hf hprod (Real.rpow_nonneg hL0.le _) hfull
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcore h1) h2 |>.trans_eq' (by ring)

end rhs
end WaveTurbulence.FinalCountG8
