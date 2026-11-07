/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import WaveTurbulence.Foundations.FlowerTop.P7Context
public import WaveTurbulence.Foundations.FlowerTop.P7Numerics
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerReg.Thresholds
public import WaveTurbulence.Foundations.Spine.StageInputBounds
public import WaveTurbulence.Foundations.Spine.CoherentProfileInputBounds
public import WaveTurbulence.Foundations.Spine.CoherentChoiceAbsorption

/-! The full couple clause: build regular premises uniformly in the remainder, then choose L. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open FlowerP7 LGSpine Filter Set

/-- The couple conclusion in the frozen flower body, with all source quantifiers. -/
abbrev CoupleClauseAt (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4,
      ∀ kind dt, (kind = TreeKind.tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)

/-- Earlier source gates and parameter bounds carried into the late-L argument. -/
abbrev P7LateHyp (C₀ : ℕ → ℝ → ℕ) (P : WTParams) : Prop :=
  NonregularHyp C₀ P ∧
    (LeafwiseCoherentApproximationOrder0At P ∧ LeafwiseIncoherentDecayAt P) ∧
      CoherentSmallParameters P

/-- GardenNum, CoupleNum, hE, regular-family premises and the context are derived here. -/
theorem p7_clause_late (C₀ : ℕ → ℝ → ℕ) (hC₀ : ∀ d γ, 2 ≤ C₀ d γ)
    (P : WTParams) (hγ : P.γ < 1)
    (hQ : ∀ L : ℝ, P.L ≤ L → P7LateHyp C₀ {P with L := L}) :
    ∀ᶠ L : ℝ in atTop, CoupleClauseAt {P with L := L} := by
  have hbase := hQ P.L le_rfl
  have hs₀ : CoherentSmallParameters P := hbase.2.2
  have hd3 : 3 ≤ P.d := hbase.1.2.2.2.1
  have hd1 : 1 ≤ P.d := by omega
  have hC₁ : 1 ≤ P.C₁ := hbase.1.2.1.c1_ge
  obtain ⟨hsol, htime, hD, _⟩ := hbase.1.1.2
  obtain ⟨Cφ, hCφ1, hφ⟩ := exists_uniform_SNormR hsol.1 (P.Lambda 0) (P.Lambda 0)
  have hCφ : 0 ≤ Cφ := zero_le_one.trans hCφ1
  let U : NNReal := ⟨Cφ + 1, by linarith⟩
  let m : Fin P.D → ℕ := fun p => P.Lambda (p.1 + 1)
  let K : Fin P.D → NNReal := fun p => ⟨max 1
    (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m p) *
      ((P.d : ℝ) ^ (40 * P.d + 4 * m p) * U)), by positivity⟩
  choose Dc hDc hchoice using fun p : Fin P.D =>
    exists_coherent_choice_bound P.d (m p) (4 * m p)
  let Hs : Fin P.D → ℝ := fun p => Dc p * (K p : ℝ) ^ (4 * m p + 4 * m p) * (2 : ℝ) ^ (9 * p.1)
  let Cr : Fin P.D → ℝ := fun p => max (Cφ + 1)
    (Dc p * P.C₁ * (K p : ℝ) ^ (4 * m p + 4 * m p) + 1)
  have ha : 0 < P.gamma1 - Real.sqrt P.η :=
    lt_of_le_of_lt (by positivity : 0 ≤ 2 * P.η ^ 20) hs₀.exponent_reserve
  have hdim : (0 : ℝ) < 50 * P.d := by
    have : (1 : ℝ) ≤ P.d := by exact_mod_cast hd1
    linarith
  have hthr := FlowerReg.eventually_regular_thresholds ha hdim P.D Hs Cr
  have hctx := eventually_p7_context C₀ hC₀ P (fun L hL => (hQ L hL).1) Cφ hCφ hφ
  filter_upwards [hthr, hctx, eventually_p7_loss_all P hd1 Cr,
    eventually_ge_atTop P.L] with L ht hg he hLP
  let Q : WTParams := {P with L := L}
  obtain ⟨G, hGC, hnums⟩ := hg
  have hs : CoherentSmallParameters Q := (hQ L hLP).2.2
  have hL1 : 1 ≤ Q.L := by change 1 ≤ L; linarith [ht.1]
  have hlow : LowProfileAt Q := (hQ L hLP).1.1.1.2.2.2.2
  intro p hp R hR t htt k N hN kind dt hkdt
  let i : Fin P.D := ⟨p,hp⟩
  have hi := all_stage_input_bounds Q hd1 hL1 hs.delta_pos.le htime hlow hC₁ hCφ hφ hp R hR
  have hhigh := coherent_input_high_bound Q hd1 hL1 hp R hR hCφ
    (coherent_profile_high_bound Q hd1 hs.delta_pos.le htime hCφ hφ hp)
  have hm : 0 < Q.Lambda (p + 1) := by
    exact lt_of_lt_of_le (by change 0 < 40 * P.d; omega)
      (forty_dim_le_Lambda Q hd1 (Nat.succ_le_of_lt hp))
  let H : RegPremises Q (inputsF Q R) p := {
    hsC := fun L' hL' => (hQ L' (hLP.trans hL')).2.1.1
    hsI := (hQ L hLP).2.1.2
    hs := hs
    hd := hd1
    hL := hL1
    hC₁ := hC₁
    hp := hp
    hm := hm
    U := U
    Kc := K i
    hKc := le_max_left _ _
    hU := by change 1 ≤ Cφ + 1; linarith
    hcF := fun r hr => (hi r hr).1
    hlowF := fun r hr => (hi r hr).2.2
    hhighF := fun r hr => (hi r hr).2.1
    hhighP := hhigh
    hmod := le_max_right _ _
    D := Dc i
    hD := hDc i
    hchoice := hchoice i
    hr := ht.2.2.2 p hp.le
    hlargeI := ht.2.1 i
    C0 := Cφ + 1
    hC0 := by linarith
    h0 := abs_inputsF_le Q hd1 hL1 hs.delta_pos hp R hR htime hCφ hφ }
  have hnums' := hnums p hp
  rw [← hGC] at hnums'
  exact FlowerP7.coupleSum_total_bound (C₀ P.d P.γ) Q G hp R hR
    (p7_one_le_R Q hd1 G.hlog p) hN htt k kind dt hkdt
    (gamma_le_dim Q hd1 hγ) hnums'.1 hnums'.2 H (he i)

end WaveTurbulence.FlowerTop
