/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimeDiagonal
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The actual tree leading time factor as a finite bivariate polynomial -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set

/-- One actual term c t^a s^b of the source leading time polynomial. -/
structure TreeTimeTerm where
  upperPower : ℕ
  lowerPower : ℕ
  coeff : ℝ

/-- Literal evaluation of a finite source time term. -/
def TreeTimeTerm.eval (z : TreeTimeTerm) (t s : ℝ) : ℝ :=
  z.coeff * t ^ z.upperPower * s ^ z.lowerPower

/-- Integrating one source monomial from s to t gives exactly these two terms. -/
def TreeTimeTerm.integrate (p : ℕ) (A : ℝ) (z : TreeTimeTerm) : List TreeTimeTerm :=
  [⟨p + z.upperPower + 1, z.lowerPower, A * z.coeff / (p + z.upperPower + 1 : ℕ)⟩,
    ⟨0, p + z.upperPower + z.lowerPower + 1, -(A * z.coeff / (p + z.upperPower + 1 : ℕ))⟩]

/-- The polynomial is computed directly from the original regular-chain code and its original
couple time factors at (1,1); there is no supplied approximation or norm hypothesis. -/
def treeTimePolynomial : RegChain → List TreeTimeTerm
  | .nil => [⟨0, 0, 1⟩]
  | .pair _ r g _ rest =>
    (treeTimePolynomial rest).flatMap (TreeTimeTerm.integrate
      (coupleTimeDegree r + coupleTimeDegree g) (r.JB 0 1 1 * g.JB 0 1 1))

/-- Exact finite polynomial antiderivative, including the original lower-time boundary term. -/
theorem TreeTimeTerm.integrate_eval (p : ℕ) (A : ℝ) (z : TreeTimeTerm) (t s : ℝ) :
    ((z.integrate p A).map (fun q => q.eval t s)).sum =
      ∫ u in s..t, A * u ^ p * z.eval u s := by
  have hi : (∫ u in s..t, A * u ^ p * z.eval u s) =
      (A * z.coeff * s ^ z.lowerPower) * ∫ u in s..t, u ^ (p + z.upperPower) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [TreeTimeTerm.eval, pow_add]
    ring
  rw [hi, integral_pow]
  simp only [TreeTimeTerm.integrate, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, TreeTimeTerm.eval, pow_zero, add_zero, mul_one]
  have hpow : s ^ (p + z.upperPower + z.lowerPower + 1) =
      s ^ (p + z.upperPower + 1) * s ^ z.lowerPower := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  push_cast
  ring

/-- A finite polynomial antiderivative commutes with the source term enumeration. -/
theorem integral_treeTimePolynomial (zs : List TreeTimeTerm) (p : ℕ) (A t s : ℝ) :
    (∫ u in s..t, A * u ^ p * (zs.map (fun z => z.eval u s)).sum) =
      ((zs.flatMap (TreeTimeTerm.integrate p A)).map (fun z => z.eval t s)).sum := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hz : Continuous (fun u : ℝ => A * u ^ p * z.eval u s) := by
      unfold TreeTimeTerm.eval
      fun_prop
    have hzs : Continuous (fun u : ℝ => A * u ^ p * (zs.map (fun z => z.eval u s)).sum) := by
      apply Continuous.mul (continuous_const.mul (continuous_pow p))
      have hh : ∀ z ∈ zs, Continuous (fun u : ℝ => z.eval u s) := by
        intro z _
        unfold TreeTimeTerm.eval
        fun_prop
      exact continuous_list_sum _ hh
    simp only [List.map_cons, List.sum_cons, mul_add, List.flatMap_cons,
      List.map_append, List.sum_append]
    rw [intervalIntegral.integral_add (hz.intervalIntegrable s t) (hzs.intervalIntegrable s t), ih,
      z.integrate_eval]

/-- On the forward source triangle, the literal JBchain is exactly the computed polynomial. -/
theorem chain_JB_eq_treeTimePolynomial : ∀ (X : RegChain) (t s : ℝ), 0 ≤ s → s ≤ t →
    X.JBchain 0 s t (fun _ => 1) = ((treeTimePolynomial X).map (fun z => z.eval t s)).sum
  | .nil, _, _, _, _ => by simp [RegChain.JBchain, treeTimePolynomial, TreeTimeTerm.eval]
  | .pair m r g inner rest, t, s, hs, hst => by
    rw [RegChain.JBchain]
    calc
      _ = ∫ u in s..t, (r.JB 0 1 1 * g.JB 0 1 1) *
          u ^ (coupleTimeDegree r + coupleTimeDegree g) *
          ((treeTimePolynomial rest).map (fun z => z.eval u s)).sum := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with u hu
        intro humem
        rw [uIoc_of_le hst] at humem
        have hu0 : 0 < u := hs.trans_lt humem.1
        rw [couple_JB_diagonal_eq r hu0, couple_JB_diagonal_eq g hu0,
          chain_JB_eq_treeTimePolynomial rest u s hs humem.1.le, pow_add]
        ring
      _ = _ := integral_treeTimePolynomial _ _ _ _ _

/-- The actual B2 tree leading factor agrees with this polynomial on its exact time box. -/
theorem tree_JB_eq_treeTimePolynomial (X : RegChain) (t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    X.JBtree 0 t s = ((treeTimePolynomial X).map (fun z => z.eval t s)).sum := by
  unfold RegChain.JBtree
  rw [max_eq_left hs]
  exact chain_JB_eq_treeTimePolynomial X t s hs hst

end WaveTurbulence.RegAsymp
