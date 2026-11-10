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
public import WaveTurbulence.Foundations.CountLemmas.PositiveAtomReduction
import Mathlib.Tactic

/-! # Exact affine coordinates for the terminal K4 local count

DH23 basiccount(5), Revision_Submit.tex L2108–2118. The three source tuples
are (1,2,4),(2,3,5),(3,4,6). This module handles the canonical balanced
orientation (-,+,+),(-,+,+),(-,-,+). It does not assert the missing
three-energy lattice bound or identify arbitrary orientations with this one.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- Six literal bond labels after eliminating the three canonical momentum
equations. The three free variables are labels 2,4,3 in source numbering. -/
def k4Labels {E : Type*} [AddCommGroup E] (a b c x y z : E) : Fin 6 → E :=
  ![x+y-a,x,z,y,b+x-z,c+y+z]

/-- Conversely the source momentum equations recover all six labels from
labels 2,4,3. No choice of lattice coset or loss of a finite multiplicity occurs. -/
theorem k4Labels_reconstruct {E : Type*} [AddCommGroup E] (a b c : E) (k : Fin 6 → E)
    (ha : -k 0+k 1+k 3=a) (hb : -k 1+k 2+k 4=b) (hc : -k 2-k 3+k 5=c) :
    k = k4Labels a b c (k 1) (k 3) (k 2) := by
  have h0 : k 0 = k 1+k 3-a := by rw [← ha]; abel
  have h4 : k 4 = b+k 1-k 2 := by rw [← hb]; abel
  have h5 : k 5 = c+k 3+k 2 := by rw [← hc]; abel
  funext i
  fin_cases i <;> simp [k4Labels,h0,h4,h5]

/-- The first source energy equation is the exact bilinear constraint. -/
theorem k4_first_energy {d : ℕ} (a x y : Mom d) :
    -‖x+y-a‖^2+‖x‖^2+‖y‖^2 = ‖a‖^2-2*inner ℝ (x-a) (y-a) := by
  simp only [norm_sub_sq_real,norm_add_sq_real,inner_sub_left,inner_sub_right,
    inner_add_left,inner_add_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm a y]
  ring

/-- The second source energy equation is a genuine sphere constraint on
the remaining free label, with the actual affine center retained. -/
theorem k4_second_energy {d : ℕ} (b x z : Mom d) :
    -‖x‖^2+‖z‖^2+‖b+x-z‖^2 =
      2*‖z-(1/2 : ℝ) • (b+x)‖^2+‖b+x‖^2/2-‖x‖^2 := by
  have hs : z+(b+x-z)=b+x := by abel
  have he := two_vector_square_identity z (b+x-z)
  rw [hs] at he
  linarith only [he]

/-- The third source energy equation is the independent strip with
coefficient r=c+y; this coefficient is an actual opposite-rail difference. -/
theorem k4_third_energy {d : ℕ} (c y z : Mom d) :
    -‖z‖^2-‖y‖^2+‖c+y+z‖^2 =
      2*inner ℝ (c+y) z+‖c+y‖^2-‖y‖^2 := by
  rw [norm_add_sq_real]
  ring

end WaveTurbulence.MoleProp
