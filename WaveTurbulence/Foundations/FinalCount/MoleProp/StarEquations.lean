/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarLabels
public import WaveTurbulence.Foundations.CountLemmas.AtomCount
public import WaveTurbulence.Foundations.CountLemmas.CountLemma
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # The exact finite local momentum and energy equations at a removed atom -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sum_dartsAt_eq_ordered (M : Molecule V D) (v : V) {r : ℕ}
    (e : Fin r ≃ IncidentDart M v) {A : Type*} [AddCommMonoid A] (f : D → A) :
    ∑ x ∈ M.dartsAt v, f x = ∑ i : Fin r, f (e i).val := by
  classical
  apply sum_bij (fun x hx => e.symm ⟨x,(Mole.mem_dartsAt M v x).mp hx⟩)
  · intro x hx
    exact mem_univ _
  · intro x hx y hy hxy
    have heq := e.symm.injective hxy
    exact congrArg Subtype.val heq
  · intro i hi
    refine ⟨(e i).val,(Mole.mem_dartsAt M v _).mpr (e i).property,?_⟩
    exact e.symm_apply_apply i
  · intro x hx
    simp only [Equiv.apply_symm_apply]

/-- Actual source momentum, written on an enumeration of the incident darts. -/
theorem ordered_star_momentum (M : Molecule V D) {d r : ℕ} (L : ℝ) (w : Mom d)
    {v : V} (hv : v ∈ M.atoms) (e : Fin r ≃ IncidentDart M v)
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L w c κ) :
    ∑ i : Fin r, M.dartSign (e i).val • Molecule.kvec L w κ (e i).val = c v := by
  rw [← sum_dartsAt_eq_ordered M v e (fun x => M.dartSign x • Molecule.kvec L w κ x)]
  exact hd.2 v hv

/-- Actual source energy tolerance, on the same local enumeration. -/
theorem ordered_star_energy (M : Molecule V D) {d r : ℕ} (L γ δ : ℝ) (w : Mom d)
    {v : V} (hv : v ∈ M.atoms) (e : Fin r ≃ IncidentDart M v)
    {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hr : M.IsRestricted L γ δ w β k0 κ) :
    |∑ i : Fin r, M.dartSign (e i).val * ‖Molecule.kvec L w κ (e i).val‖ ^ 2 - β v| ≤
      δ⁻¹ * L ^ (-2 * γ) := by
  rw [← sum_dartsAt_eq_ordered M v e (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2)]
  exact hr.1 v hv

end WaveTurbulence.MoleProp
