/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.V2Chain.PrefixS
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Part2
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Assembly
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Couple
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Est

/-!
# V2-CHAIN: the X3 assembly with `γ` restricted to `S`

The theorems `flowerest1_of_gates`, `cplMoments_of_gates`, `part2_of_X2`, `fixedpoint_of_parts` of the X-chain
(`FlowerDraft.X2Est`, `FlowerDraft.X2Couple`, `FixedptDraft.X3Part2`, `FixedptDraft.X3Assembly`) re-stated for
`WTPrefixS S` / `WTPrefixPS S`. The proofs are those of the originals, byte for byte, except that the hypothesis
`hS : γ ∈ S` is passed to every gate (the combinators `and`, `small`, `mono`, `large` of `V2Chain.PrefixS`) and
that the unconditional inputs `OX2Exp`, `OX3Cpl` enter through `ofFull`. No mathematical step uses `γ`
beyond `γ ∈ (0,1)`: the restriction threads through mechanically.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.V2Chain

open WaveTurbulence WaveTurbulence.Fixedpt
open MeasureTheory Finset Set SysAPI
open scoped ENNReal

universe u

variable {S : Set ℝ}

theorem flowerest1S_of_gates (hG : WTPrefixPS S B112Body) (hE : OX2Exp.{u}) :
    WTPrefixPS S X2Body.{u} := by
  refine ((WTPrefixPS.and B112Body_const hG (WTPrefixPS.ofFull hE)).small (fun ν => Real.exp (-(25 / ν))) fun ν _ =>
    Real.exp_pos _).mono ?_
  rintro Pm P ⟨⟨hB, hX⟩, hPm, hν, hδ, hδν, hL⟩
  classical
  intro Ω _ μ _ g hg p hp a Fev R E Et hA t ht s hs n n' ζ kind pat dagger cut1 cut2 hpat hcut
  obtain ⟨hint, hexp⟩ := hX Ω μ g hg p hp a Fev R E Et hA t ht s hs n n' ζ kind pat dagger cut1 cut2 hpat hcut
  refine ⟨hint, ?_⟩
  have hRB : RemainderBound P R p := fun q hq => (hA q hq).2.1.1
  set Ntr := P.N (p + 1)
  set B := x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => pat) cut1 cut2
  set I := ∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ
  set fS : ℕ → ℂ := fun N => flowerSumP P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat)
    (dagger.map fun c _ => c) cut1 cut2 ζ t s n n'
  have hB0 : 0 ≤ B := x2Bound_nonneg P (by linarith) Pm p ζ n n' _ cut1 cut2
  set q := P.δ ^ (2 * P.ν)
  have hq0 : 0 ≤ q := Real.rpow_nonneg hδ.le _
  have hq50 : q ≤ Real.exp (-50) := by
    calc q ≤ Real.exp (-(25 / P.ν)) ^ (2 * P.ν) := Real.rpow_le_rpow hδ.le hδν (by positivity)
      _ = Real.exp (-50) := by
          rw [← Real.exp_mul]
          congr 1
          field_simp
          ring
  have hq : q ≤ 1 / 2 := hq50.trans (by
    have := Real.add_one_le_exp (-50 : ℝ)
    have h2 : Real.exp (-50) * Real.exp 50 = 1 := by rw [← Real.exp_add]; simp
    have h3 : (51 : ℝ) ≤ Real.exp 50 := by linarith [Real.add_one_le_exp (50 : ℝ)]
    nlinarith [Real.exp_pos (-50 : ℝ)])
  -- the per-order bound
  have hord : ∀ N ∈ Finset.range (Ntr ^ 4 + 1), ‖fS N‖ ≤ B * q ^ N := by
    intro N hN
    have hN' : N ≤ Ntr ^ 4 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)
    have h := (hB p hp R hRB).1 t ht s hs n n' ζ N hN' kind (fun _ => pat) (dagger.map fun c _ => c)
      cut1 cut2 hcut
    have hq' : P.δ ^ (2 * P.ν * N) = q ^ N := by
      rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
    refine h.trans (le_of_eq ?_)
    rw [hq']
    simp only [B, x2Bound]
    ring
  -- the low orders vanish for `𝒴`, `𝒲`
  set A : ℕ := if kind = .X then 0 else 2 * Pm * (Ntr + 1)
  have hlow : ∀ N, N < A → fS N = 0 := by
    intro N hN
    by_cases hk : kind = .X
    · simp [A, hk] at hN
    · simp only [A, hk, ite_false] at hN
      exact flowerSum_eq_zero_of_lt P _ p N kind hk _ _ cut1 cut2 ζ t s n n' hN
  have hsum : ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖fS N‖ ≤ 2 * B * q ^ A := by
    calc ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖fS N‖
        ≤ ∑ N ∈ (Finset.range (Ntr ^ 4 + 1)).filter (A ≤ ·), B * q ^ N := by
          rw [Finset.sum_filter]
          refine Finset.sum_le_sum fun N hN => ?_
          split_ifs with h
          · exact hord N hN
          · rw [hlow N (not_le.1 h), norm_zero]
      _ = B * ∑ N ∈ (Finset.range (Ntr ^ 4 + 1)).filter (A ≤ ·), q ^ N := by rw [Finset.mul_sum]
      _ ≤ B * (2 * q ^ A) := mul_le_mul_of_nonneg_left
          (sum_pow_le_two_mul hq0 hq _ A fun N hN => (Finset.mem_filter.1 hN).2) hB0
      _ = 2 * B * q ^ A := by ring
  have hI0 : 0 ≤ I := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ => by positivity)
  have hIle : I ≤ 2 * B * q ^ A + B * Real.exp (-(101 * Ntr : ℝ)) := by
    have h1 : I = ‖((I : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hI0]
    rw [h1]
    calc ‖((I : ℝ) : ℂ)‖ ≤ ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1), fS N‖ +
          ‖((I : ℝ) : ℂ) - ∑ N ∈ Finset.range (Ntr ^ 4 + 1), fS N‖ := norm_le_insert' _ _
      _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖fS N‖ + B * Real.exp (-(101 * Ntr : ℝ)) :=
          add_le_add (norm_sum_le _ _) hexp
      _ ≤ _ := add_le_add hsum le_rfl
  have he101 : Real.exp (-(101 * Ntr : ℝ)) ≤ Real.exp (-(100 * Ntr : ℝ)) :=
    Real.exp_le_exp.2 (by have : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg _; linarith)
  have he100 : Real.exp (-(100 * Ntr : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg _; linarith)
  cases kind with
  | X =>
    have hA0 : A = 0 := by simp [A]
    rw [hA0, pow_zero] at hIle
    show I ≤ 3 * B * 1
    nlinarith
  | Y | W =>
    have hAq : q ^ A ≤ Real.exp (-(100 * Ntr : ℝ)) := by
      have hA' : 2 * (Ntr + 1) ≤ A := by
        simp only [A, reduceCtorEq, ite_false]
        nlinarith
      calc q ^ A ≤ q ^ (2 * (Ntr + 1)) := pow_le_pow_of_le_one hq0 (hq.trans (by norm_num)) hA'
        _ ≤ Real.exp (-50) ^ (2 * (Ntr + 1)) := pow_le_pow_left₀ hq0 hq50 _
        _ = Real.exp (-(100 * (Ntr + 1) : ℝ)) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ Real.exp (-(100 * Ntr : ℝ)) := Real.exp_le_exp.2 (by linarith)
    show I ≤ 3 * B * Real.exp (-(100 * Ntr : ℝ))
    nlinarith


theorem cplMomentsS_of_gates (hG : WTPrefixPS S B112Body) (hL : WTPrefixS S Gates.LayergardenBody)
    (hW : WTPrefixS S Gates.WkeTaylorBody) (hC : OX3Cpl.{u}) : WTPrefixS S CplMomBody.{u} := by
  have h1 : WTPrefixS S fun P => (∃ Pm, B112Body Pm P) ∧ Gates.LayergardenBody P ∧ OX3CplBody.{u} P :=
    WTPrefixS.and (fun P C₁ C₂ h => h.imp fun Pm hP => B112Body_const Pm P C₁ C₂ hP)
      hG.toWTPrefixS (WTPrefixS.and (fun P C₁ C₂ h => by rw [layergardenBody_update_x2]; exact h) hL (WTPrefixS.ofFull hC))
  have h2 := (WTPrefixS.and (fun P C₁ C₂ h => ⟨h.1.imp fun Pm hP => B112Body_const Pm P C₁ C₂ hP, by
        rw [layergardenBody_update_x2]; exact h.2.1, by rw [OX3CplBody_update]; exact h.2.2⟩) h1 hW).small
    (fun ν C₁ => min (Real.exp (-(101 / ν))) (1 / (4 * C₁)))
    (fun ν C₁ hν hC₁ => lt_min (Real.exp_pos _) (by positivity))
    (fun d C₂ => max (Real.exp (100 * d + 11)) (4 * C₂ + 3))
  refine h2.mono ?_
  rintro P ⟨⟨⟨⟨Pm, hB⟩, hLG, hX⟩, hWT⟩, hd, hν, hC₁, hδ, hδf, hC₂, hLg, hL2⟩
  intro Ω _ μ _ g hg p hp a Fev R E Et hA t ht n v
  obtain ⟨hint, hexp⟩ := hX Ω μ g hg p hp a Fev R E Et hA t ht n v
  refine ⟨hint, ?_⟩
  have hRB : RemainderBound P R p := fun q hq => (hA q hq).2.1.1
  set Ntr := P.N (p + 1)
  set k := latticePoint P.L n
  set J := jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ))
  have hJ0 : 0 ≤ J := Real.rpow_nonneg (jbr_pos' k).le _
  have hLpos : 0 < P.L := by linarith
  have hI0 : 0 ≤ ∫ ω in Fev p, ‖cplRand P (a ω p) p v t n‖ ^ 2 ∂μ :=
    setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ => by positivity)
  -- small parameters
  have hδ1 : P.δ ≤ Real.exp (-(101 / P.ν)) := hδf.trans (min_le_left _ _)
  have hδ2 : P.δ ≤ 1 / (4 * P.C₁) := hδf.trans (min_le_right _ _)
  set q1 := P.δ ^ P.ν
  have hq10 : 0 ≤ q1 := Real.rpow_nonneg hδ.le _
  have hq1e : q1 ≤ Real.exp (-101) := by
    calc q1 ≤ Real.exp (-(101 / P.ν)) ^ P.ν := Real.rpow_le_rpow hδ.le hδ1 hν.le
      _ = Real.exp (-101) := by rw [← Real.exp_mul]; congr 1; field_simp
  have he101 : Real.exp (-101) ≤ 1 / 2 := by
    have := Real.add_one_le_exp (101 : ℝ)
    have h2 : Real.exp (-101) * Real.exp 101 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-101 : ℝ)]
  have hq1 : q1 ≤ 1 / 2 := hq1e.trans he101
  have hN0 : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg _
  have hLlog := P.N_ge_log (by omega) ((le_max_left _ _).trans hLg) (p + 1)
  -- `L^{100d} ≤ e^{N - 10}`
  have hLpow : P.L ^ (100 * P.d : ℝ) ≤ Real.exp (Ntr - 10) := by
    rw [Real.rpow_def_of_pos hLpos]
    exact Real.exp_le_exp.2 (by nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ P.L)])
  have hexp101 : Real.exp (-(101 * Ntr : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  -- `ℒ₀`-type sums
  have hL0sum : ∀ dt : Bool, ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1),
      coupleSum P (inputsF P R) p N .L0 dt t k‖ ≤ J * Real.exp (-(100 * Ntr : ℝ)) := by
    intro dt
    have hterm : ∀ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .L0 dt t k‖ ≤
        if 2 * (Ntr + 1) ≤ N then J * P.L ^ (100 * P.d : ℝ) * q1 ^ N else 0 := by
      intro N hN
      split_ifs with hlow
      · have := (hB p hp R hRB).2 t ht k N (Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)) .L0 dt
          (fun h => absurd h (by intro h'; cases h'))
        refine this.trans (le_of_eq ?_)
        rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
      · rw [coupleSum_L0_eq_zero_of_lt P _ p N dt t k (not_le.1 hlow), norm_zero]
    calc ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1), coupleSum P (inputsF P R) p N .L0 dt t k‖
        ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .L0 dt t k‖ := norm_sum_le _ _
      _ ≤ ∑ N ∈ (Finset.range (Ntr ^ 4 + 1)).filter (2 * (Ntr + 1) ≤ ·), J * P.L ^ (100 * P.d : ℝ) * q1 ^ N := by
          rw [Finset.sum_filter]; exact Finset.sum_le_sum hterm
      _ = J * P.L ^ (100 * P.d : ℝ) * ∑ N ∈ (Finset.range (Ntr ^ 4 + 1)).filter (2 * (Ntr + 1) ≤ ·), q1 ^ N := by
          rw [Finset.mul_sum]
      _ ≤ J * P.L ^ (100 * P.d : ℝ) * (2 * q1 ^ (2 * (Ntr + 1))) := by
          gcongr
          exact sum_pow_le_two_mul hq10 hq1 _ _ fun N hN => (Finset.mem_filter.1 hN).2
      _ ≤ J * Real.exp (Ntr - 10) * (2 * Real.exp (-101) ^ (2 * (Ntr + 1))) := by
          gcongr
      _ = J * (2 * Real.exp (Ntr - 10 - 202 * (Ntr + 1))) := by
          rw [← Real.exp_nat_mul, mul_assoc, ← mul_assoc (Real.exp _) 2, mul_comm (Real.exp _) 2,
            mul_assoc 2, ← Real.exp_add]
          push_cast; ring_nf
      _ ≤ J * Real.exp (-(100 * Ntr : ℝ)) := by
          gcongr
          have : Real.exp (Ntr - 10 - 202 * (Ntr + 1)) ≤ Real.exp (-(100 * Ntr : ℝ) - 1) :=
            Real.exp_le_exp.2 (by linarith)
          have h2 : 2 * Real.exp (-(100 * Ntr : ℝ) - 1) ≤ Real.exp (-(100 * Ntr : ℝ)) := by
            rw [Real.exp_sub]
            have := Real.add_one_le_exp (1 : ℝ)
            rw [mul_div_assoc']
            rw [div_le_iff₀ (Real.exp_pos 1)]
            nlinarith [Real.exp_pos (-(100 * Ntr : ℝ))]
          linarith
  have hL2' : (1 : ℝ) ≤ P.L ^ 2 := one_le_pow₀ (by linarith)
  have hLd1 : (1 : ℝ) ≤ P.L ^ (100 * P.d : ℝ) := Real.one_le_rpow (by linarith) (by positivity)
  cases v with
  | L0 =>
    have := real_le_of_complex hI0 (hL0sum false) hexp
    show _ ≤ J * P.L ^ 2 * Real.exp (-(100 * Ntr : ℝ))
    have he : Real.exp (-(101 * Ntr : ℝ)) ≤ Real.exp (-(100 * Ntr : ℝ)) := Real.exp_le_exp.2 (by linarith)
    have hee := Real.exp_pos (-(100 * Ntr : ℝ))
    have h4 := mul_le_mul_of_nonneg_left he hJ0
    have hJe := mul_nonneg hJ0 hee.le
    have hL4 : (4 : ℝ) ≤ P.L ^ 2 := by nlinarith
    have h5 : 2 * (J * Real.exp (-(100 * Ntr : ℝ))) ≤ J * P.L ^ 2 * Real.exp (-(100 * Ntr : ℝ)) := by
      have := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ P.L ^ 2 by linarith) hJe
      linarith
    linarith
  | L0Dt =>
    have := real_le_of_complex hI0 (hL0sum true) hexp
    show _ ≤ J * P.L ^ 2 * P.L ^ (100 * P.d : ℝ) * Real.exp (-(100 * Ntr : ℝ))
    have he : Real.exp (-(101 * Ntr : ℝ)) ≤ Real.exp (-(100 * Ntr : ℝ)) := Real.exp_le_exp.2 (by linarith)
    have hee := Real.exp_pos (-(100 * Ntr : ℝ))
    have h3 : 2 * (J * Real.exp (-(100 * Ntr : ℝ))) ≤ J * P.L ^ 2 * P.L ^ (100 * P.d : ℝ) *
        Real.exp (-(100 * Ntr : ℝ)) := by
      have h2L : (2 : ℝ) ≤ P.L ^ 2 * P.L ^ (100 * P.d : ℝ) := by nlinarith
      have hJe := mul_nonneg hJ0 hee.le
      have := mul_le_mul_of_nonneg_right h2L hJe
      linarith
    have h4 := mul_le_mul_of_nonneg_left he hJ0
    linarith
  | aTrDt =>
    have hsum : ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1), coupleSum P (inputsF P R) p N .tr true t k‖ ≤
        J * P.L ^ (100 * P.d : ℝ) * 2 := by
      calc _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .tr true t k‖ := norm_sum_le _ _
        _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), J * P.L ^ (100 * P.d : ℝ) * q1 ^ N := by
            refine Finset.sum_le_sum fun N hN => ?_
            have := (hB p hp R hRB).2 t ht k N (Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)) .tr true
              (fun _ => rfl)
            refine this.trans (le_of_eq ?_)
            rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
        _ = J * P.L ^ (100 * P.d : ℝ) * ∑ N ∈ Finset.range (Ntr ^ 4 + 1), q1 ^ N := by rw [Finset.mul_sum]
        _ ≤ J * P.L ^ (100 * P.d : ℝ) * (2 * q1 ^ 0) := by
            gcongr
            exact sum_pow_le_two_mul hq10 hq1 _ 0 fun _ _ => Nat.zero_le _
        _ = J * P.L ^ (100 * P.d : ℝ) * 2 := by ring
    have := real_le_of_complex hI0 hsum hexp
    show _ ≤ J * P.L ^ 2 * P.L ^ (100 * P.d : ℝ)
    have hJL := mul_nonneg hJ0 (le_trans zero_le_one hLd1)
    have hL4 : (4 : ℝ) ≤ P.L ^ 2 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left hexp101 hJ0
    have h5 : J ≤ J * P.L ^ (100 * P.d : ℝ) := le_mul_of_one_le_right hJ0 hLd1
    have h6 := mul_le_mul_of_nonneg_right hL4 hJL
    nlinarith
  | aTr =>
    have hWp := (hWT p hp).2.2
    have hLGp := hLG p hp R hRB t ⟨ht.1, ht.2.le⟩
    set x := P.C₁ * P.δ
    have hx0 : 0 ≤ x := mul_nonneg (by linarith) hδ.le
    have hx : x ≤ 1 / 4 := by
      have hC₁pos : 0 < P.C₁ := by linarith
      calc x ≤ P.C₁ * (1 / (4 * P.C₁)) := mul_le_mul_of_nonneg_left hδ2 hC₁pos.le
        _ = 1 / 4 := by field_simp
    set q2 := P.δ ^ (2 * P.ν)
    have hq20 : 0 ≤ q2 := Real.rpow_nonneg hδ.le _
    have hq2 : q2 ≤ 1 / 2 := by
      have : q2 = q1 ^ 2 := by
        simp only [q2, q1]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
        congr 1
        push_cast
        ring
      rw [this]
      nlinarith
    have hterm : ∀ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .tr false t k‖ ≤
        J * q2 ^ N + J * (P.C₂ * x ^ (N / 2)) := by
      intro N hN
      have hNle : N ≤ Ntr ^ 4 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)
      rw [WaveTurbulence.FlowerProbes.coupleSum_tr]
      have hcR := hLGp N hNle |>.2.2
      have hθ : 0 ≤ (4 * P.theta (p + 1) + P.theta p) / 5 := by
        unfold WTParams.theta
        have h20 : 0 ≤ P.η ^ 20 := by positivity
        positivity
      have hcast : (-(((4 * P.Lambda (p + 1) : ℕ)) : ℝ)) = -(4 * P.Lambda (p + 1) : ℝ) := by push_cast; ring
      have hcRpt := le_jbr_rpow_neg (norm_le_of_SNorm_le (by positivity) hcR k)
      have hU := le_jbr_rpow_neg (norm_le_of_SNormR_le (by positivity) (hWp (N / 2) t ⟨ht.1.le, ht.2.le⟩) k)
      rw [hcast] at hcRpt hU
      have hsplit : truncSumC P (inputsF P R) (p + 1) N t k = coupleRemainder P R p N t k +
          (if Even N then (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p (N / 2) t k : ℂ) else 0) := by
        simp only [coupleRemainder]; ring
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine hcRpt.trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hJ0
        have hLθ : P.L ^ (-((4 * P.theta (p + 1) + P.theta p) / 5)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
        rw [show -(4 * P.theta (p + 1) + P.theta p) / 5 = -((4 * P.theta (p + 1) + P.theta p) / 5) by ring,
          Real.rpow_mul hδ.le, Real.rpow_natCast]
        exact mul_le_of_le_one_left (pow_nonneg hq20 _) hLθ
      · split_ifs
        · rw [Complex.norm_real, Real.norm_eq_abs]
          exact hU
        · rw [norm_zero]; exact mul_nonneg hJ0 (mul_nonneg (by linarith) (pow_nonneg hx0 _))
    have hsum : ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1), coupleSum P (inputsF P R) p N .tr false t k‖ ≤
        J * 2 + J * (P.C₂ * 4) := by
      calc _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .tr false t k‖ :=
            norm_sum_le _ _
        _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), (J * q2 ^ N + J * (P.C₂ * x ^ (N / 2))) :=
            Finset.sum_le_sum hterm
        _ = J * ∑ N ∈ Finset.range (Ntr ^ 4 + 1), q2 ^ N +
              J * (P.C₂ * ∑ N ∈ Finset.range (Ntr ^ 4 + 1), x ^ (N / 2)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ J * (2 * q2 ^ 0) + J * (P.C₂ * 4) := by
            gcongr
            · exact sum_pow_le_two_mul hq20 hq2 _ 0 fun _ _ => Nat.zero_le _
            · exact sum_pow_half_le hx0 hx _
        _ = J * 2 + J * (P.C₂ * 4) := by ring
    have := real_le_of_complex hI0 hsum hexp
    show _ ≤ J * P.L ^ 2
    have hL43 : 4 * P.C₂ + 3 ≤ P.L := (le_max_right _ _).trans hLg
    have hLL : P.L ≤ P.L ^ 2 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left hexp101 hJ0
    have h5 : 3 + 4 * P.C₂ ≤ P.L ^ 2 := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 hJ0
    linarith


theorem part2S_of_X2 (h : WTPrefixPS S X2Body.{u}) : WTPrefixS S Part2Body.{u} := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ hS
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  set Pm := max P₀ (100 * (d + 1) ^ 2)
  have hPm : 100 * ((d : ℝ) + 1) ^ 2 ≤ Pm := by
    have : 100 * (d + 1) ^ 2 ≤ Pm := le_max_right _ _
    exact_mod_cast this
  obtain ⟨δ₀, hδ₀, H⟩ := H Pm (le_max_left _ _)
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  obtain ⟨L₁, hL₁, H1⟩ := exists_L0_part2 d D Pm (by omega) hPm
  refine ⟨C₂, hC₂, max L₀ L₁, hL₀.trans (le_max_left _ _), fun L hL => ?_⟩
  exact part2Body_of_X2 (H L ((le_max_left _ _).trans hL)) hPm hd (hL₁.trans ((le_max_right _ _).trans hL))
    fun p hp kind => H1 _ rfl rfl ((le_max_right _ _).trans hL) p hp kind


theorem fixedpointS_of_parts (hcpl : WTPrefixS S CplMomBody.{u}) (h2 : WTPrefixS S Part2Body.{u}) :
    WTPrefixS S Gates.FixedpointBody.{u} := by
  have h := WTPrefixS.large (WTPrefixS.and (fun P C₁ C₂ h => by rw [CplMomBody_update]; exact h) hcpl h2)
    gFix
  refine h.mono ?_
  rintro P ⟨⟨hC, h2P⟩, hd, hγ, hδ0, hδ1, hLg, hL2⟩
  intro Ω _ μ _ g hg p hp a Fev R E Et hA
  have hL1 : 1 ≤ P.L := by linarith
  have hL0 : 0 < P.L := by linarith
  have hd1 : 1 ≤ P.d := by omega
  have hLe : Real.exp (100 * P.d + 11) ≤ P.L := le_trans (le_max_left _ _) hLg
  have hLa : 16 * 2 ^ (P.d + 1) * latConst P.d ≤ P.L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLg
  have hLb : 18 * 3 ^ (5 / 4 * ((40 * P.d) ^ P.D : ℕ) + 1 : ℝ) * 4 ^ (P.d + 1) * latConst P.d ^ 2 ≤ P.L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLg
  set N : ℕ := P.N (p + 1) with hNdef
  have hNlog := WTParams.N_ge_log P hd1 hLe (p + 1)
  have hlogL : 0 ≤ Real.log P.L := Real.log_nonneg hL1
  have hN1 : (1 : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ 100 * P.d * Real.log P.L := by positivity
    linarith
  obtain ⟨hΛ40, hΛD⟩ := Lambda_ge P hp hd1
  set Λ' : ℕ := P.Lambda (p + 1) with hΛ'def
  have hΛ'r : (P.d : ℝ) + 1 ≤ Λ' := by
    have : ((40 * P.d : ℕ) : ℝ) ≤ Λ' := by exact_mod_cast hΛ40
    push_cast at this
    have : (1 : ℝ) ≤ P.d := by exact_mod_cast hd1
    linarith
  set Λ : ℝ := 5 / 4 * (Λ' : ℝ) with hΛdef
  have hΛ : (P.d : ℝ) + 1 ≤ Λ := by
    have : (0 : ℝ) ≤ Λ' := Nat.cast_nonneg _
    linarith
  -- the ansatz at `p`
  have hAp : AnsatzAt P μ g a Fev R E Et p := hA p le_rfl
  have hpI : (p : ℝ) ∈ Icc (0 : ℝ) p := ⟨Nat.cast_nonneg p, le_rfl⟩
  have hsol : ∀ ω ∈ Fev p, IsASolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) (a ω) :=
    fun ω hω => SysAPI.AnsatzAt.isASolution hAp hω
  have haP : ∀ k, Measurable fun ω => a ω p k := fun k => SysAPI.AnsatzAt.measurable hAp hpI k
  have hsum : ∀ ω ∈ Fev p, Summable fun k => ‖a ω p k‖ :=
    fun ω hω => SysAPI.IsASolution.summable_norm hL0 (hsol ω hω) hpI
  have hmom := hC Ω μ g hg p hp a Fev R E Et hA
  obtain ⟨C2, hC2m, hC2inv, hC2prob, hC2op⟩ := h2P Ω μ g hg p hp a Fev R E Et hA
  -- the excluded event
  set C : Set ((Fin P.d → ℤ) → ℂ) := {b | Summable fun k => ‖b k‖} ∩ Good1Q P p ∩ C2 with hCdef
  have hCm : MeasurableSet C :=
    (measurableSet_summable_norm.inter (measurableSet_good1Q P p hL0)).inter hC2m
  have hCinv : ∀ φ, IsCubicPhase φ → ∀ b ∈ C, (fun k => φ k * b k) ∈ C := by
    rintro φ hφ b ⟨⟨hbs, hb1⟩, hb2⟩
    exact ⟨⟨(summable_mul_phase hφ).2 hbs, good1Q_mul_phase P p hL0 hφ hbs hb1⟩, hC2inv φ hφ b hb2 hbs⟩
  obtain ⟨F', hF'sub, hF'm, hF'sym, hF'C, hdiff⟩ := exists_symmetric_subevent hL0 P.φin hg.1
    (Nat.cast_nonneg p) (SysAPI.AnsatzAt.isSymmetricEvent hAp) hsol hCm hCinv
  refine ⟨F', hF'sub, hF'm, hF'sym, ?_, ?_⟩
  · -- the probability
    have hrapid : μ (initialRapidEvent P.L P.φin g)ᶜ = 0 :=
      ae_iff.1 (initialRapidEvent_ae hL0 P.φin g fun n => ⟨(hg.1 n).aemeasurable, hg.2.2 n⟩)
    have hsub2 : Fev p ∩ {ω | a ω p ∉ C} ⊆
        (Fev p ∩ {ω | a ω p ∉ Good1 P p}) ∪ (Fev p ∩ {ω | a ω p ∉ C2}) := by
      rintro ω ⟨hω, hnot⟩
      by_cases h1 : a ω p ∈ Good1 P p
      · exact Or.inr ⟨hω, fun h2 => hnot ⟨⟨hsum ω hω, good1Q_of_good1 P p (hsum ω hω) h1⟩, h2⟩⟩
      · exact Or.inl ⟨hω, h1⟩
    have hP1 : μ (Fev p ∩ {ω | a ω p ∉ Good1 P p}) ≤
        ENNReal.ofReal (Real.exp (-(4 * (N : ℝ))) / 2) :=
      (part1_prob P p μ (SysAPI.AnsatzAt.measurableSet hAp) haP hsum hmom hL1 hΛ'r).trans
        (ENNReal.ofReal_le_ofReal (part1Bound_le P p hd1 hLe hLa))
    have hE : 0 ≤ Real.exp (-(4 * (N : ℝ))) / 2 := by positivity
    have htot : μ (Fev p \ F') ≤ ENNReal.ofReal (Real.exp (-(4 * (N : ℝ)))) :=
      calc μ (Fev p \ F') ≤ μ ((initialRapidEvent P.L P.φin g)ᶜ ∪ (Fev p ∩ {ω | a ω p ∉ C})) :=
            measure_mono hdiff
        _ ≤ μ (initialRapidEvent P.L P.φin g)ᶜ + μ (Fev p ∩ {ω | a ω p ∉ C}) := measure_union_le _ _
        _ ≤ 0 + (μ (Fev p ∩ {ω | a ω p ∉ Good1 P p}) + μ (Fev p ∩ {ω | a ω p ∉ C2})) :=
            add_le_add (le_of_eq hrapid) ((measure_mono hsub2).trans (measure_union_le _ _))
        _ ≤ 0 + (ENNReal.ofReal (Real.exp (-(4 * (N : ℝ))) / 2) +
              ENNReal.ofReal (Real.exp (-(4 * (N : ℝ))) / 2)) := by
            gcongr
        _ = ENNReal.ofReal (Real.exp (-(4 * (N : ℝ)))) := by
            rw [zero_add, ← ENNReal.ofReal_add hE hE]
            congr 1
            ring
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le htot
  · -- the clauses
    intro ω hω
    dsimp only
    obtain ⟨⟨hbs, hb1⟩, hb2⟩ := hF'C ω hω
    have hG1 := good1_of_good1Q P p hL0 hbs hb1
    have hwt : ∀ n : Fin P.d → ℤ, jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) ≤
        wt P.L Λ n := fun n =>
      Real.rpow_le_rpow_of_exponent_le (one_le_jbr _) (by
        have : (0 : ℝ) ≤ Λ' := Nat.cast_nonneg _
        rw [hΛdef]; linarith)
    have hα : ∀ s ∈ Icc (p : ℝ) (p + 1), ∀ k, ‖aTr P.L P.γ P.δ p N (a ω p) s k‖ ≤
        Real.exp (3 * (N : ℝ)) * wt P.L Λ k := fun s hs k => by
      refine (hG1.1 s hs k).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hwt k) (Real.exp_pos _).le
    have hL0eq : ∀ (b : Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) (t : ℝ) (n : Fin P.d → ℤ),
        Lop P.L P.γ P.δ p N (a ω p) 0 b t n = Lop P.L P.γ P.δ p N (a ω p) 0 (fun _ _ => 0) t n :=
      fun b t n => by
        rw [L0_eq P.L P.γ P.δ hL0 p N hbs b t n, L0_eq P.L P.γ P.δ hL0 p N hbs (fun _ _ => 0) t n]
    have h0 : ∀ (b : ArrI p P.d) (t : Icc (p : ℝ) (p + 1)) (n : Fin P.d → ℤ),
        ‖Lop P.L P.γ P.δ p N (a ω p) 0 b t n‖ ≤ Real.exp (-(20 * (N : ℝ))) * wt P.L Λ n := fun b t n => by
      rw [hL0eq]
      refine (hG1.2 t t.2 n).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hwt n) (Real.exp_pos _).le
    have hops := hC2op (a ω p) hb2 hbs
    have hK0 : 0 ≤ triK P.d P.L P.γ P.δ Λ := triK_nonneg P.L P.γ P.δ
    have hKle : triK P.d P.L P.γ P.δ Λ ≤ Real.exp (4 * (N : ℝ)) / 18 := by
      refine triK_le P p hd1 hLe hγ.2 hδ0 hδ1 (le_trans ?_ hLb)
      have h3 : (3 : ℝ) ^ (Λ + 1) ≤ 3 ^ (5 / 4 * ((40 * P.d) ^ P.D : ℕ) + 1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have : (Λ' : ℝ) ≤ ((40 * P.d) ^ P.D : ℕ) := by exact_mod_cast hΛD
        rw [hΛdef]; linarith
      have hS := latConst_nonneg P.d
      gcongr
    have hM : 2 * ENNReal.ofReal (Real.exp (2 * (N : ℝ))) ≤ ENNReal.ofReal (Real.exp (3 * (N : ℝ))) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have he : (2 : ℝ) ≤ Real.exp (N : ℝ) := by
        have := Real.add_one_le_exp (N : ℝ)
        linarith
      calc 2 * Real.exp (2 * (N : ℝ)) ≤ Real.exp (N : ℝ) * Real.exp (2 * (N : ℝ)) := by
            gcongr
        _ = Real.exp (3 * (N : ℝ)) := by rw [← Real.exp_add]; ring_nf
    obtain ⟨c3, c4, c5, c6, c7⟩ := fixedpoint_core P.L P.γ P.δ N hbs hL1 hΛ (α := Real.exp (3 * (N : ℝ)))
      (ε₀ := Real.exp (-(20 * (N : ℝ)))) (ρ := Real.exp (-(10 * (N : ℝ)))) (κ := Real.exp (3 * (N : ℝ)))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hα h0
      (ENNReal.ofReal (Real.exp (2 * (N : ℝ)))) hM
      (fun c hc => (hops c hc).2.2) (fun c hc => (hops c hc).1) (fun c hc => (hops c hc).2.1)
      (by
        have := fix_small hN1 hK0 hKle
        have e : Real.exp (-(20 * (N : ℝ))) = Real.exp (-(10 * (N : ℝ))) ^ 2 := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        calc Real.exp (3 * (N : ℝ)) * (Real.exp (-(20 * (N : ℝ))) +
              3 * triK P.d P.L P.γ P.δ Λ * Real.exp (-(10 * (N : ℝ))) ^ 2 * Real.exp (3 * (N : ℝ)) +
              triK P.d P.L P.γ P.δ Λ * Real.exp (-(10 * (N : ℝ))) ^ 3) ≤ Real.exp (-(10 * (N : ℝ))) := this
          _ = _ := rfl)
      (fix_contr hN1 hK0 hKle)
    exact ⟨fun t ht n => hG1.1 t ht n, fun b t n => by rw [hL0eq]; exact hG1.2 t t.2 n,
      c3, c4, c5, c6, c7⟩


end WaveTurbulence.V2Chain
