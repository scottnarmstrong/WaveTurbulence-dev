/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain31
public import WaveTurbulence.Foundations.FinalCount.AsmTerm16c
public import WaveTurbulence.Foundations.FinalCount.GL19
/-! **FINALCOUNT LOW-CHAIN, session 6 (6): the terminal exponent with loop credit (`term_exponentL`).**  `term_arithL` is `term_arith` with the
budget `4(R-1)` replaced by a free `S` and the debit `(η⁵-4η⁶)/2` by a free `ε ≤ (η⁵-4η⁶)ρ`.  `UntCL` adds `LowFree` to the untouched class
and uses the EFFECTIVE index `r` in the odd clause.  `term_exponentL`: with `R' = r + k` (the `Good` index) and the cluster rank drops
`j K + k_K` (`Σ k_K = k`), the cluster and component exponents add up to the exponent of `Yz r`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

theorem term_arithL (a b η C₀ q m e J ib iso F F₅ Fim₅ R₅ R S ε ρ ρ₅ β₅ Vβ Z₅ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hC₀ : 1 ≤ C₀) (hq : 0 ≤ q)
    (hF₅ : F₅ = F - J + e + ib - m - iso) (hR₅ : R₅ + 2 * m + iso ≤ R + e + ib) (hFim : Fim₅ ≤ R₅)
    (hρ : ρ ≤ ρ₅ + m + iso) (hiso0 : 0 ≤ iso) (hiso : iso ≤ e) (hm : 0 ≤ m) (he : 0 ≤ e) (hβ : β₅ ≤ Vβ)
    (hS : 0 ≤ S) (hZ : Z₅ ≤ e + 4 * S + 3 * q) (hε : ε ≤ (η ^ 5 - 4 * η ^ 6) * ρ) :
    -(η ^ 3 + 3 * η) * q + a * (m - J) - η * e - C₀ * η ^ 5 * (m + e) + b * β₅ - a * (F₅ - Fim₅) - η ^ 5 * ρ₅ + η * Z₅ ≤
      a * R + 4 * η * S - ε - 4 * η ^ 6 * ρ - a * F + b * Vβ := by
  have hη5 : 0 < η ^ 5 := by positivity
  have hη3 : 0 < η ^ 3 := by positivity
  have h46 : 4 * η ^ 6 ≤ η ^ 5 := by nlinarith [mul_pos hη5 hη]
  have e1 : a * F₅ = a * (F - J + e + ib - m - iso) := by rw [hF₅]
  have e2 : a * Fim₅ ≤ a * R₅ := mul_le_mul_of_nonneg_left hFim ha
  have e3 : a * R₅ ≤ a * (R + e + ib - 2 * m - iso) := mul_le_mul_of_nonneg_left (by linarith) ha
  have e4 : b * β₅ ≤ b * Vβ := mul_le_mul_of_nonneg_left hβ hb
  have e5 : η * Z₅ ≤ η * (e + 4 * S + 3 * q) := mul_le_mul_of_nonneg_left hZ hη.le
  have e6 : η ^ 5 * (ρ - m - iso) ≤ η ^ 5 * ρ₅ := mul_le_mul_of_nonneg_left (by linarith) hη5.le
  have e7 : η ^ 5 * (m + e) ≤ C₀ * η ^ 5 * (m + e) := by
    have : 0 ≤ (C₀ - 1) * (η ^ 5 * (m + e)) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have e8 : η ^ 5 * iso ≤ η ^ 5 * e := mul_le_mul_of_nonneg_left hiso hη5.le
  have e10 : 0 ≤ η ^ 3 * q := mul_nonneg hη3.le hq
  nlinarith

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **Untouched component, LOW form**: tame-free, with no `ε`-atom of degree `< 3`, and (odd only if the effective index is `1`). -/
def UntCL (hf : HSt V D₀) (Tm : V → Prop) (r : ℕ) (a : V) : Prop :=
  TameFree hf Tm a ∧ LowFree hf a ∧ (CompOdd hf a → r = 1)

/-- The exponent of the component bound (LOW form). -/
noncomputable def exaL (γ η : ℝ) (hf : HSt V D₀) (Tm : V → Prop) (r : ℕ) (a : V) : ℝ :=
  (gam0 γ + 2 * η ^ 2) *
      ((WaveTurbulence.FinalCountG8.betaAtoms (compMol (hf.op5 Tm).s.M a).atoms (cl8 hf)).card : ℝ)
    - (if UntCL hf Tm r a ∧ ¬ CompOdd hf a then eraseA γ η else 0)
    - η ^ 5 * ((compMol (hf.op5 Tm).s.M a).rho : ℝ)
    + (if UntCL hf Tm r a then 0 else
        η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ))

/-- The sum of the component exponents. -/
theorem sum_exaL (γ η : ℝ) (hf : HSt V D₀) (Tm : V → Prop) (r : ℕ) (Rs : Finset V) (hR : CompRep (hf.op5 Tm).s.M Rs) :
    ∑ a ∈ Rs, exaL γ η hf Tm r a =
      (gam0 γ + 2 * η ^ 2) * ((WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card : ℝ)
        - eraseA γ η * ((Rs.filter fun a => UntCL hf Tm r a ∧ ¬ CompOdd hf a).card : ℝ)
        - η ^ 5 * ((hf.op5 Tm).s.M.rho : ℝ)
        + η * ∑ a ∈ Rs.filter (fun a => ¬ UntCL hf Tm r a),
            (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) := by
  unfold exaL
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hb : ∑ a ∈ Rs, ((WaveTurbulence.FinalCountG8.betaAtoms (compMol (hf.op5 Tm).s.M a).atoms (cl8 hf)).card : ℝ) =
      ((WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card : ℝ) := by
    rw [← Nat.cast_sum, sum_beta_comp hR]
  have hρ : ∑ a ∈ Rs, ((compMol (hf.op5 Tm).s.M a).rho : ℝ) = ((hf.op5 Tm).s.M.rho : ℝ) := by
    rw [← Nat.cast_sum, ← hR.rho_sum]
  rw [hb, hρ]
  have h1 : ∑ a ∈ Rs, (if UntCL hf Tm r a ∧ ¬ CompOdd hf a then eraseA γ η else 0) =
      eraseA γ η * ((Rs.filter fun a => UntCL hf Tm r a ∧ ¬ CompOdd hf a).card : ℝ) := by
    rw [← Finset.sum_filter]; simp [mul_comm]
  have h2 : ∑ a ∈ Rs, (if UntCL hf Tm r a then (0 : ℝ) else
        η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ)) =
      η * ∑ a ∈ Rs.filter (fun a => ¬ UntCL hf Tm r a),
        (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : UntCL hf Tm r a <;> simp [h]
  rw [h1, h2]



end WaveTurbulence.FinalCountAsm
