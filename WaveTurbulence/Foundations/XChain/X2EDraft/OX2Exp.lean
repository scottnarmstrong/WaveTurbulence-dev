/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerFinal
public import WaveTurbulence.Foundations.XChain.X2EDraft.CoefWeight
public import WaveTurbulence.Foundations.XChain.X2EDraft.CutWeights
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Part2
public import WaveTurbulence.Foundations.XChain.CplDraft.Dt

/-!
# O-X2-EXP

**Statements.**
- `m1Gain_le`, `m2_pow_le`: the coefficient gains are within `x2Bound`'s cutoff factors, up to `L^{(80d+1)P}`;
- `coefGain_mul_bracket_le`: `K · (∏_j ⟨n − ζ n'⟩)^{−(Λ_p/4 − 20d)} ≤ x2Bound`;
- `ox2Exp_body`: `OX2ExpBody` under `X2Sizes` (all kinds, patterns `plain`/`dRoot`, `†`, cutoffs), from `x2_core`
  with the coefficient weight `coef_weight_le` and `cutWeightsOK`;
- **`oX2Exp : OX2Exp`**;
- **`fixedpoint_of_closed_gates`**: X3's `fixedpoint_of_gates` with O-X2-EXP and O-X3-CPL discharged.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.X2E

open Finset MeasureTheory Set Induct SysAPI Cpl
open scoped Classical

/-! ## The gains against `x2Bound` -/

theorem m1Gain_le (L : ℝ) (hL4 : 4 ≤ L) (d Pm : ℕ) (cut1 : Option ℕ) :
    m1Gain L d Pm cut1 ≤
      L ^ (80 * d * Pm : ℝ) * (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * L) ^ (-(80 * d * Pm : ℝ))) := by
  have hL1 : 1 ≤ L := by linarith
  have he : (0 : ℝ) ≤ 80 * d * Pm := by positivity
  cases cut1 with
  | none =>
    change (1 : ℝ) ≤ L ^ (80 * d * Pm : ℝ) * 1
    rw [mul_one]
    exact Real.one_le_rpow hL1 he
  | some j₁ =>
    change (if 1 ≤ j₁ then (2 ^ j₁ * L / 4) ^ (-(80 * d * Pm : ℝ)) else 1) ≤
      L ^ (80 * d * Pm : ℝ) * ((2 : ℝ) ^ j₁ * L) ^ (-(80 * d * Pm : ℝ))
    have hM : (0 : ℝ) < 2 ^ j₁ * L := by positivity
    by_cases hj : 1 ≤ j₁
    · rw [ite_eq_left hj, Real.div_rpow hM.le (by norm_num), div_eq_mul_inv, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hM.le _)
      rw [← Real.rpow_neg (by norm_num), neg_neg]
      exact Real.rpow_le_rpow (by norm_num) hL4 he
    · rw [ite_eq_right hj]
      have h0 : j₁ = 0 := by omega
      subst h0
      rw [pow_zero, one_mul, ← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]

theorem m2_pow_le (L γ δ : ℝ) (hδ : 0 < δ) (hγ : 0 ≤ γ) (hL1 : 1 ≤ L) (hLδ : (8 / δ) ^ 2 ≤ L) (Pm : ℕ)
    (hPm : 1 ≤ Pm) (pat : FixPat) (cut2 : Option ℕ) :
    m2Tree L γ δ pat cut2 ^ (2 * Pm) ≤
      L ^ (Pm : ℝ) * (cut2.elim 1 fun j₂ => if ∀ _j : Fin (2 * Pm), pat = .plain then
        ((2 : ℝ) ^ j₂ * L) ^ (-(Pm / 9 : ℝ)) else 1) := by
  have hL0 : 0 < L := by linarith
  have hLP : (1 : ℝ) ≤ L ^ (Pm : ℝ) := Real.one_le_rpow hL1 (Nat.cast_nonneg _)
  have hall : (∀ _j : Fin (2 * Pm), pat = .plain) ↔ pat = .plain :=
    ⟨fun h => h ⟨0, by omega⟩, fun h _ => h⟩
  cases cut2 with
  | none =>
    change (1 : ℝ) ^ (2 * Pm) ≤ L ^ (Pm : ℝ) * 1
    rw [one_pow, mul_one]
    exact hLP
  | some j₂ =>
    change (if pat = .plain ∧ 1 ≤ j₂ then 8 / (Real.pi * δ * L ^ (2 * γ) * (2 ^ j₂ * L)) else 1) ^ (2 * Pm) ≤
      L ^ (Pm : ℝ) * (if ∀ _j : Fin (2 * Pm), pat = .plain then ((2 : ℝ) ^ j₂ * L) ^ (-(Pm / 9 : ℝ)) else 1)
    have hM1 : (1 : ℝ) ≤ 2 ^ j₂ * L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hL1
    have hM0 : (0 : ℝ) < 2 ^ j₂ * L := by linarith
    by_cases h : pat = .plain ∧ 1 ≤ j₂
    · rw [ite_eq_left h, ite_eq_left (hall.mpr h.1)]
      set M : ℝ := 2 ^ j₂ * L
      have hLγ : 1 ≤ L ^ (2 * γ) := Real.one_le_rpow hL1 (by linarith)
      have hden : δ * M ≤ Real.pi * δ * L ^ (2 * γ) * M := by
        have : δ * M * 1 ≤ δ * M * (Real.pi * L ^ (2 * γ)) :=
          mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith [Real.pi_gt_three]) hLγ)
            (by positivity)
        nlinarith
      have h1 : 8 / (Real.pi * δ * L ^ (2 * γ) * M) ≤ (8 / δ) / M := by
        rw [div_div]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      have h2 : (8 / (Real.pi * δ * L ^ (2 * γ) * M)) ^ (2 * Pm) ≤ ((8 / δ) / M) ^ (2 * Pm) :=
        pow_le_pow_left₀ (by positivity) h1 _
      refine h2.trans ?_
      rw [div_pow, pow_mul]
      have h3 : ((8 / δ) ^ 2) ^ Pm ≤ L ^ (Pm : ℝ) := by
        rw [Real.rpow_natCast]
        exact pow_le_pow_left₀ (by positivity) hLδ _
      have h4 : 1 / M ^ (2 * Pm) ≤ M ^ (-(Pm / 9 : ℝ)) := by
        rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hM0.le]
        apply Real.rpow_le_rpow_of_exponent_le hM1
        push_cast
        have : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _
        linarith
      calc ((8 / δ) ^ 2) ^ Pm / M ^ (2 * Pm) = ((8 / δ) ^ 2) ^ Pm * (1 / M ^ (2 * Pm)) := by ring
        _ ≤ L ^ (Pm : ℝ) * M ^ (-(Pm / 9 : ℝ)) :=
            mul_le_mul h3 h4 (by positivity) (zero_le_one.trans hLP)
    · rw [ite_eq_right h, one_pow]
      by_cases hp : pat = .plain
      · rw [ite_eq_left (hall.mpr hp)]
        have hj : j₂ = 0 := by
          by_contra hj
          exact h ⟨hp, by omega⟩
        subst hj
        rw [pow_zero, one_mul, ← Real.rpow_add hL0]
        exact Real.one_le_rpow hL1 (by
          have : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _
          linarith)
      · rw [ite_eq_right (fun h' => hp (hall.mp h')), mul_one]
        exact hLP

/-- **The coefficient gain and the bracket are within `x2Bound`.** -/
theorem coefGain_mul_bracket_le (P : WTParams) {p : ℕ} (hd : 1 ≤ P.d) (hδ : 0 < P.δ) (hγ : 0 ≤ P.γ)
    (hL4 : 4 ≤ P.L) (hLδ : (8 / P.δ) ^ 2 ≤ P.L) (Pm : ℕ) (hPm : 1 ≤ Pm) (ζ : ℤˣ) (n n' : Fin P.d → ℤ)
    (pat : FixPat) (cut1 cut2 : Option ℕ) (b : ℝ) (hb : 2 * (P.Lambda (p + 1) : ℝ) ≤ b) :
    (m2Tree P.L P.γ P.δ pat cut2 ^ (2 * Pm) * m1Gain P.L P.d Pm cut1) * bracketW P ζ n n' Pm b ≤
      x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => pat) cut1 cut2 := by
  have hL1 : 1 ≤ P.L := by linarith
  set c1 := cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))
  set c2 := cut2.elim 1 fun j₂ => if ∀ _j : Fin (2 * Pm), pat = .plain then
    ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1
  have hc1 : 0 ≤ c1 := by
    cases cut1 with
    | none => exact zero_le_one
    | some j => exact Real.rpow_nonneg (by positivity) _
  have hc2 : 0 ≤ c2 := by
    cases cut2 with
    | none => exact zero_le_one
    | some j =>
      change 0 ≤ if ∀ _j : Fin (2 * Pm), pat = .plain then ((2 : ℝ) ^ j * P.L) ^ (-(Pm / 9 : ℝ)) else 1
      split_ifs
      · exact Real.rpow_nonneg (by positivity) _
      · exact zero_le_one
  have h1 := m1Gain_le P.L hL4 P.d Pm cut1
  have h2 := m2_pow_le P.L P.γ P.δ hδ hγ hL1 hLδ Pm hPm pat cut2
  have hW := bracketW_le P ζ n n' Pm b hb
  have hW0 := bracketW_nonneg P ζ n n' Pm b
  have hm2 : 0 ≤ m2Tree P.L P.γ P.δ pat cut2 ^ (2 * Pm) :=
    pow_nonneg (m2Tree_nonneg P.L P.γ P.δ hδ (by linarith) pat cut2) _
  have hm1 := m1Gain_nonneg P.L (by linarith) P.d Pm cut1
  have hexp : P.L ^ (Pm : ℝ) * P.L ^ (80 * P.d * Pm : ℝ) ≤
      P.L ^ ((if ∀ _j : Fin (2 * Pm), pat = .plain then (1 : ℝ) else 2) * (100 * P.d : ℝ) ^ 3 * Pm) := by
    rw [← Real.rpow_add (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
    have hPm' : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _
    have hc : (1 : ℝ) ≤ (if ∀ _j : Fin (2 * Pm), pat = .plain then (1 : ℝ) else 2) := by split_ifs <;> norm_num
    have hd3 : (P.d : ℝ) ≤ (P.d : ℝ) ^ 3 := by
      have hsq : (1 : ℝ) ≤ (P.d : ℝ) ^ 2 := one_le_pow₀ hd'
      calc (P.d : ℝ) = P.d * 1 := (mul_one _).symm
        _ ≤ P.d * (P.d : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
        _ = (P.d : ℝ) ^ 3 := by ring
    have hcube : 80 * (P.d : ℝ) + 1 ≤ (100 * P.d) ^ 3 := by
      calc 80 * (P.d : ℝ) + 1 ≤ 1000000 * P.d := by linarith
        _ ≤ 1000000 * (P.d : ℝ) ^ 3 := by linarith
        _ = (100 * P.d) ^ 3 := by ring
    have h0 : (0 : ℝ) ≤ (100 * P.d) ^ 3 * Pm := by positivity
    calc (Pm : ℝ) + 80 * P.d * Pm = (80 * P.d + 1) * Pm := by ring
      _ ≤ (100 * P.d) ^ 3 * Pm := mul_le_mul_of_nonneg_right hcube hPm'
      _ ≤ (if ∀ _j : Fin (2 * Pm), pat = .plain then (1 : ℝ) else 2) * ((100 * P.d) ^ 3 * Pm) :=
          le_mul_of_one_le_left h0 hc
      _ = _ := by ring
  have hj0 : 0 ≤ jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ)) :=
    Real.rpow_nonneg (jbr_pos _).le _
  unfold x2Bound
  calc (m2Tree P.L P.γ P.δ pat cut2 ^ (2 * Pm) * m1Gain P.L P.d Pm cut1) * bracketW P ζ n n' Pm b ≤
      ((P.L ^ (Pm : ℝ) * c2) * (P.L ^ (80 * P.d * Pm : ℝ) * c1)) *
        jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ)) :=
        mul_le_mul (mul_le_mul h2 h1 hm1 (by positivity)) hW hW0 (by positivity)
    _ = jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
        (P.L ^ (Pm : ℝ) * P.L ^ (80 * P.d * Pm : ℝ)) * c1 * c2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hj0) hc1) hc2

/-! ## The body -/

theorem ox2Exp_body.{u} (Pm : ℕ) (P : WTParams) (C : ℝ) (hS : X2Sizes Pm P C) : OX2ExpBody.{u} Pm P := by
  classical
  intro Ω _ μ _ g hG p hp a Fev R E Et ha t ht s hs n n' ζ kind pat dagger cut1 cut2 hpat _
  obtain ⟨hd, hδ, hδ1, hγ, hq, hLexp, hC, hCL, hbase, hφ, hstage⟩ := hS.cpl
  obtain ⟨hN, hNdim, hbN⟩ := hstage p hp
  have hL1 : 1 ≤ P.L := (by linarith [Real.add_one_le_exp (2 : ℝ)] : (1 : ℝ) ≤ Real.exp 2).trans hLexp
  have he1 := Real.exp_one_gt_d9
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hL4 : 4 ≤ P.L := by nlinarith
  have hc : |coupling P.d P.L P.γ P.δ| ≤ 1 := abs_coupling_le_one hL1 hγ hδ.le hδ1
  have hΛ := lambda_eq_base_mul_succ P hp
  have hΛs := lambda_succ_ge P hd hp
  have hΛr : (P.Lambda p : ℝ) = 40 * P.d * P.Lambda (p + 1) := by exact_mod_cast hΛ
  have hΛsr : 40 * (P.d : ℝ) ≤ P.Lambda (p + 1) := by exact_mod_cast hΛs
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  set b : ℝ := (P.Lambda p : ℝ) / 4 - 20 * P.d
  have hb : (P.d : ℝ) + 1 ≤ b := by simp only [b]; rw [hΛr]; nlinarith
  have hb2 : 2 * (P.Lambda (p + 1) : ℝ) ≤ b := by simp only [b]; rw [hΛr]; nlinarith
  have hbN' : b ≤ (P.N (p + 1) : ℝ) := by
    have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
    simp only [b]
    linarith
  set K := m2Tree P.L P.γ P.δ pat cut2 ^ (2 * Pm) * m1Gain P.L P.d Pm cut1
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg (m2Tree_nonneg P.L P.γ P.δ hδ (by linarith) pat cut2) _)
    (m1Gain_nonneg P.L (by linarith) P.d Pm cut1)
  have hcw : CoefW P p kind pat dagger cut1 cut2 ζ t s Pm b K := by
    intro tops κ
    have h := coef_weight_le P.L P.γ P.δ p pat dagger cut1 cut2 t s hc hδ hL4 hs.1 hs.2 ht.2.le
      (fun j => (tops j).1) κ (P.Lambda p : ℝ)
    have he : -(2 * b) = -((P.Lambda p : ℝ) / 2 - 40 * P.d) := by simp only [b]; ring
    rw [he]
    exact h
  have hcut : ∀ x : FlIdx (P.N p) (P.N (p + 1)) pat kind ζ Pm p, CutWeightsOK P.L (d := P.d)
      (fun j => ne_flower_of_mem_kernelTrees pat (x.1 j).2) (mkFlowerAt x.2.1.1 x.2.1.2 x.2.2)
      (fun j => kernelTrees_sign (P.N (p + 1)) pat kind ζ (x.1 j).2) cut1 cut2 :=
    fun x => cutWeightsOK _ _ _ P.L cut1 cut2
  obtain ⟨hint, hbd⟩ := x2_core Pm P C hS Ω μ g hG p hp a Fev R E Et ha t ht s hs n n' ζ kind pat dagger cut1 cut2
    hpat hcut b K hb hbN' hK hcw
  refine ⟨hint, hbd.trans ?_⟩
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (coefGain_mul_bracket_le P hd hδ hS.gamma_nonneg hL4 hS.L_delta Pm hS.pm ζ n n'
    pat cut1 cut2 b hb2) (Real.exp_pos _).le

/-- **O-X2-EXP.** -/
theorem oX2Exp.{u} : OX2Exp.{u} :=
  wtprefixP_x2Sizes.mono fun Pm P ⟨C, hS⟩ => ox2Exp_body Pm P C hS

end WaveTurbulence.X2E
