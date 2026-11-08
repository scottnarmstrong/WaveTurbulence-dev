/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkAsm.CoreF

/-! # A5 MK-ASM: Core-G at fixed parameters, from the component bound and the conditional helper G.

The `R_j`-integration of `R_j⁻¹ R_j^{-1/18}` over the shell `[2^{j₂-1} L, 2^{j₂} L]` is done here: each of the `2Pm`
factors contributes `a^{-1/18}` with `a = 2^{j₂-1} L`, which is `2^{1/18} (2^{j₂} L)^{-1/18}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkAsm

/-- `(a^{-1/18})^{2 Pm} = 2^{Pm/9} X^{-Pm/9}` for `a = X / 2`. -/
theorem shell_pow {X : ℝ} (hX : 0 < X) (Pm : ℕ) :
    (((X / 2) ^ (-(1 / 18 : ℝ))) ^ (2 * Pm)) = (2 : ℝ) ^ ((Pm : ℝ) / 9) * X ^ (-((Pm : ℝ) / 9)) := by
  have h1 : (X / 2) ^ (-(1 / 18 : ℝ)) = X ^ (-(1 / 18 : ℝ)) * (2 : ℝ) ^ ((1 / 18 : ℝ)) := by
    rw [div_eq_mul_inv, Real.mul_rpow hX.le (by norm_num), Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  rw [h1, mul_pow, ← Real.rpow_natCast (X ^ (-(1 / 18 : ℝ))), ← Real.rpow_natCast ((2 : ℝ) ^ (1 / 18 : ℝ)),
    ← Real.rpow_mul hX.le, ← Real.rpow_mul (by norm_num), mul_comm]
  have e1 : (-(1 / 18 : ℝ)) * ((2 * Pm : ℕ) : ℝ) = -((Pm : ℝ) / 9) := by push_cast; ring
  have e2 : (1 / 18 : ℝ) * ((2 * Pm : ℕ) : ℝ) = (Pm : ℝ) / 9 := by push_cast; ring
  rw [e1, e2]

/-- Core-G at fixed parameters. -/
theorem coreG_at {B : ℝ} (hB : B ≤ 24000) {Pm : ℕ} {P : WTParams}
    (hM : MarkedComponentBoundAtI B Pm P) (hcaps : CapsDecompGAt Pm P)
    (hν : 0 < P.ν) (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1) (hL : 1 ≤ P.L)
    (hthr : ∀ N p : ℕ, N ≤ P.N (p + 1) ^ 4 →
      ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) * 2 ^ Pm ≤ (P.L ^ (4000 * P.d)) ^ Pm) :
    Fam.FlowerCoreGainAt BcMK Pm P := by
  intro hγ p hp t ht s hs n n' ζ N hN kind dagger h b hb hh Rf j₂ hj₂ hRf hdecay
  obtain ⟨Str, _, m, D, hcard, hsum, heq⟩ :=
    hcaps (by linarith) hγ p hp t ht s hs n n' ζ N hN kind dagger h b hb hh Rf j₂ hj₂ hRf hdecay
  rw [heq]
  have hL0 : 0 < P.L := by linarith
  set a : ℝ := 2 ^ (j₂ - 1) * P.L with ha
  have ha0 : 0 < a := by positivity
  set X : ℝ := (2 : ℝ) ^ j₂ * P.L with hXdef
  have hX0 : 0 < X := by positivity
  have haX : a = X / 2 := by
    rw [ha, hXdef]
    obtain ⟨k, rfl⟩ : ∃ k, j₂ = k + 1 := ⟨j₂ - 1, by omega⟩
    simp [pow_succ]
    ring
  set K0 : ℝ := P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N with hK0
  have hb0 : 0 ≤ b := by linarith
  have hK0nn : 0 ≤ K0 := by positivity
  -- pointwise bound on the box
  have hpt : ∀ Rs ∈ shellBox (2 * Pm) P.L j₂,
      ‖∑ x, ∏ c, (D Rs x c).val‖ ≤
        (Fintype.card Str : ℝ) * K0 * (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) := by
    intro Rs hRs
    have hRj : ∀ j, a ≤ Rs j ∧ Rs j ≤ X := fun j => by
      have := hRs j (Set.mem_univ j)
      exact this
    have hstruct : ∀ x, ‖∏ c, (D Rs x c).val‖ ≤ K0 * ∏ j : Fin (2 * Pm), ((Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))) := by
      intro x
      obtain ⟨h1, h2, h3⟩ := hsum Rs hRs x
      by_cases hne : ∀ c, (D Rs x c).A.Nonempty
      · have := norm_prod_val_le hM hγ hp ht hs hb hL0 hδ (D Rs x) h1 h2 hN
        rw [h3 hne] at this
        exact this
      · -- an empty class has value `0`
        obtain ⟨c₀, hc₀⟩ := not_forall.1 hne
        have hA0 : (D Rs x c₀).A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hc₀
        have hv0 : (D Rs x c₀).val = 0 := by
          unfold CompData.val; rw [hA0, Finset.sum_empty]
        rw [Finset.prod_eq_zero (Finset.mem_univ c₀) hv0, norm_zero]
        have hpos : 0 ≤ ∏ j : Fin (2 * Pm), ((Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))) := by
          refine Finset.prod_nonneg fun j _ => ?_
          have hr : 0 < Rs j := lt_of_lt_of_le ha0 (hRj j).1
          positivity
        exact mul_nonneg hK0nn hpos
    have hg : ∀ j, (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) ≤ a⁻¹ * a ^ (-(1 / 18 : ℝ)) := by
      intro j
      have hr : 0 < Rs j := lt_of_lt_of_le ha0 (hRj j).1
      have h1 : (Rs j)⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 (hRj j).1
      have h2 : (Rs j) ^ (-(1 / 18 : ℝ)) ≤ a ^ (-(1 / 18 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha0 (hRj j).1 (by norm_num)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hprod : ∏ j : Fin (2 * Pm), ((Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))) ≤
        (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) := by
      have := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin (2 * Pm))))
        (f := fun j => (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))) (g := fun _ => a⁻¹ * a ^ (-(1 / 18 : ℝ)))
        (fun j _ => by
          have hr : 0 < Rs j := lt_of_lt_of_le ha0 (hRj j).1
          positivity) (fun j _ => hg j)
      simpa using this
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x, ‖∏ c, (D Rs x c).val‖
        ≤ ∑ _x : Str, K0 * (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) :=
          Finset.sum_le_sum fun x _ => (hstruct x).trans (mul_le_mul_of_nonneg_left hprod hK0nn)
      _ = _ := by simp; ring
  -- the integral over the box
  have hvol : (volume (shellBox (2 * Pm) P.L j₂)).toReal = a ^ (2 * Pm) := by
    have : shellBox (2 * Pm) P.L j₂ = Set.Icc (fun _ : Fin (2 * Pm) => a) (fun _ => X) := by
      unfold shellBox
      exact Set.pi_univ_Icc _ _
    rw [this, Real.volume_Icc_pi_toReal (fun j => by
      show a ≤ X
      rw [haX]; linarith)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have : X - a = a := by rw [haX]; ring
    rw [this]
  have hfin : volume (shellBox (2 * Pm) P.L j₂) < ⊤ := by
    have : shellBox (2 * Pm) P.L j₂ = Set.Icc (fun _ : Fin (2 * Pm) => a) (fun _ => X) := by
      unfold shellBox
      exact Set.pi_univ_Icc _ _
    rw [this]
    exact measure_Icc_lt_top
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun Rs : Fin (2 * Pm) → ℝ =>
    ∑ x, ∏ c, (D Rs x c).val) hfin hpt
  refine hint.trans ?_
  have hreal : volume.real (shellBox (2 * Pm) P.L j₂) = a ^ (2 * Pm) := hvol
  rw [hreal]
  -- (a⁻¹ a^{-1/18})^{2Pm} a^{2Pm} = (a^{-1/18})^{2Pm}
  have hcalc : (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) * a ^ (2 * Pm) =
      (a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hcnt : (Fintype.card Str : ℝ) * 2 ^ Pm ≤ (P.L ^ (4000 * P.d)) ^ Pm := by
    refine le_trans ?_ (hthr N p hN)
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have habs := absorb_L (d := P.d) (Pm := Pm) hL hB hcnt
  have hdel := delta_mono (N := N) hδ hδ1 hν
  have h2le : (2 : ℝ) ^ ((Pm : ℝ) / 9) ≤ 2 ^ Pm := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _
    linarith
  have hLB : 0 ≤ P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) := by positivity
  have hδN : 0 ≤ P.δ ^ (7 * P.ν * (N : ℝ)) := by positivity
  have hbN : 0 ≤ b ^ N := by positivity
  have hXpow : 0 ≤ X ^ (-((Pm : ℝ) / 9)) := by positivity
  calc (Fintype.card Str : ℝ) * K0 * (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) * a ^ (2 * Pm)
      = (Fintype.card Str : ℝ) * K0 * ((a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm)) := by rw [mul_assoc _ _ (a ^ (2 * Pm)) |>.symm.symm]; rw [mul_assoc, hcalc]; ring
    _ = (Fintype.card Str : ℝ) * K0 * ((2 : ℝ) ^ ((Pm : ℝ) / 9) * X ^ (-((Pm : ℝ) / 9))) := by
        rw [haX, shell_pow hX0]
    _ ≤ ((Fintype.card Str : ℝ) * 2 ^ Pm * P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ))) * P.δ ^ (7 * P.ν * (N : ℝ)) *
          b ^ N * X ^ (-((Pm : ℝ) / 9)) := by
        rw [hK0]
        have hc0 : (0 : ℝ) ≤ Fintype.card Str := Nat.cast_nonneg _
        have : (Fintype.card Str : ℝ) * (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N) *
            ((2 : ℝ) ^ ((Pm : ℝ) / 9) * X ^ (-((Pm : ℝ) / 9))) ≤
            (Fintype.card Str : ℝ) * (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N) *
            (2 ^ Pm * X ^ (-((Pm : ℝ) / 9))) := by gcongr
        calc _ ≤ _ := this
          _ = _ := by ring
    _ ≤ P.L ^ (BcMK P.d * (Pm : ℝ)) * P.δ ^ (6 * P.ν * (N : ℝ)) * b ^ N * X ^ (-((Pm : ℝ) / 9)) := by
        gcongr
    _ = _ := by rw [hXdef]

end WaveTurbulence.Flower.MkAsm
