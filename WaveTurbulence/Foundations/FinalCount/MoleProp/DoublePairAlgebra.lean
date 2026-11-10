/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

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

/-! # Exact four-label coordinates for DH23 basiccount(3)

Both opposite and equal rung orientations are included. The two external
rails have opposite incidence directions. Charges remain arbitrary.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- Literal four labels: indices 0,1 are the double rung and 2,3 the rails.
False means oppositely directed rungs; true means equally directed rungs. -/
def doublePairLabels {E : Type*} [AddCommGroup E] (same : Bool) (a b x y : E) : Fin 4 → E :=
  if same then ![x+a,y+a,x+y+a,x+y+a+(a+b)] else ![x+a,x+y+a,y+a,y-b]

/-- The two actual fixed momentum equations, in canonical directions. -/
def DoublePairMomentum {E : Type*} [AddCommGroup E] (same : Bool) (a b : E) (k : Fin 4 → E) : Prop :=
  if same then k 0+k 1-k 2=a ∧ -k 0-k 1+k 3=b
  else k 0-k 1+k 2=a ∧ -k 0+k 1-k 3=b

def doublePairCoordinates {E : Type*} [AddCommGroup E] (same : Bool) (a : E) (k : Fin 4 → E) : E × E :=
  (k 0-a,if same then k 1-a else k 2-a)

theorem doublePairLabels_reconstruct {E : Type*} [AddCommGroup E] (same : Bool)
    (a b : E) (k : Fin 4 → E) (hk : DoublePairMomentum same a b k) :
    k = doublePairLabels same a b (doublePairCoordinates same a k).1 (doublePairCoordinates same a k).2 := by
  cases same
  · have h := hk
    change k 0-k 1+k 2=a ∧ -k 0+k 1-k 3=b at h
    have h1 : k 1 = k 0+k 2-a := by rw [← h.1]; abel
    have h3 : k 3 = k 2-a-b := by rw [← h.2,← h.1]; abel
    funext i
    fin_cases i <;> simp [doublePairLabels,doublePairCoordinates,h1,h3]
    all_goals abel
  · have h := hk
    change k 0+k 1-k 2=a ∧ -k 0-k 1+k 3=b at h
    have h2 : k 2 = k 0+k 1-a := by rw [← h.1]; abel
    have h3 : k 3 = k 0+k 1+b := by rw [← h.2]; abel
    funext i
    fin_cases i <;> simp [doublePairLabels,doublePairCoordinates,h2,h3] <;> abel

/-- First vertex's signed physical energy. -/
noncomputable def doublePairEnergyOne {d : ℕ} (same : Bool) (k : Fin 4 → Mom d) : ℝ :=
  if same then ‖k 0‖^2+‖k 1‖^2-‖k 2‖^2 else ‖k 0‖^2-‖k 1‖^2+‖k 2‖^2

/-- Second vertex's signed physical energy. -/
noncomputable def doublePairEnergyTwo {d : ℕ} (same : Bool) (k : Fin 4 → Mom d) : ℝ :=
  if same then -‖k 0‖^2-‖k 1‖^2+‖k 3‖^2 else -‖k 0‖^2+‖k 1‖^2-‖k 3‖^2

theorem doublePair_first_energy {d : ℕ} (same : Bool) (a b x y : Mom d) :
    doublePairEnergyOne same (doublePairLabels same a b x y) = ‖a‖^2-2*inner ℝ x y := by
  cases same <;> simp [doublePairEnergyOne,doublePairLabels,norm_add_sq_real,inner_add_left]
  all_goals simp only [real_inner_comm y x,real_inner_comm a x,real_inner_comm a y]
  all_goals ring

theorem doublePair_combined_energy {d : ℕ} (same : Bool) (a b x y : Mom d) :
    doublePairEnergyOne same (doublePairLabels same a b x y) +
      doublePairEnergyTwo same (doublePairLabels same a b x y) =
      2*inner ℝ (a+b) (if same then x+y else y) + 2*inner ℝ (a+b) a +
        (if same then 1 else -1)*‖a+b‖^2 := by
  cases same <;> simp [doublePairEnergyOne,doublePairEnergyTwo,doublePairLabels,
    norm_add_sq_real,norm_sub_sq_real,inner_add_left,inner_add_right]
  all_goals simp only [real_inner_comm a x,real_inner_comm b x,real_inner_comm a y,real_inner_comm b y,real_inner_comm b a]
  all_goals ring

/-- Two source energy tolerances imply the exact coupled bilinear and
strip constraints. The combined energy tolerance is twice the original
one, canceled by the factor two in the strip identity. -/
theorem doublePair_coupled_constraints {d : ℕ} (same : Bool) (a b x y : Mom d)
    (β₁ β₂ τ : ℝ) (hτ : 0 ≤ τ)
    (h₁ : |doublePairEnergyOne same (doublePairLabels same a b x y)-β₁| ≤ τ)
    (h₂ : |doublePairEnergyTwo same (doublePairLabels same a b x y)-β₂| ≤ τ) :
    |inner ℝ x y - (‖a‖^2-β₁)/2| ≤ τ ∧
      |inner ℝ (a+b) (if same then x+y else y) -
        (β₁+β₂-2*inner ℝ (a+b) a-(if same then 1 else -1)*‖a+b‖^2)/2| ≤ τ := by
  have hs : |(doublePairEnergyOne same (doublePairLabels same a b x y)+
      doublePairEnergyTwo same (doublePairLabels same a b x y))-(β₁+β₂)| ≤ 2*τ := by
    calc
      _ = |(doublePairEnergyOne same (doublePairLabels same a b x y)-β₁)+
          (doublePairEnergyTwo same (doublePairLabels same a b x y)-β₂)| := by congr 1; ring
      _ ≤ |doublePairEnergyOne same (doublePairLabels same a b x y)-β₁|+
          |doublePairEnergyTwo same (doublePairLabels same a b x y)-β₂| := abs_add_le _ _
      _ ≤ τ+τ := add_le_add h₁ h₂
      _ = 2*τ := by ring
  rw [doublePair_first_energy] at h₁
  rw [doublePair_combined_energy] at hs
  obtain ⟨h₁l,h₁u⟩ := abs_le.mp h₁
  obtain ⟨hsl,hsu⟩ := abs_le.mp hs
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

end WaveTurbulence.MoleProp
