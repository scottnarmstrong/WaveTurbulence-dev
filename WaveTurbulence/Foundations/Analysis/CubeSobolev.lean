/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.IntervalSobolev
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# The elementary cube Sobolev inequality

An iterated-integral formulation of DH21 (10.5), L2428. Each coordinate is
differentiated either zero or one times. The recursion lists the resulting
`2^n` terms without choosing an enumeration of subsets of the coordinates.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Sum of the `L¹` norms of all square-free mixed derivatives on the unit
cube, written as iterated Lebesgue integrals. At the recursive step, the
first term leaves the first coordinate undifferentiated, and the second
term differentiates it. Thus there are exactly `2^n` terms. Extended norms
make the definition meaningful without integrability assumptions. -/
@[expose] noncomputable def cubeSobolevL1 : (n : ℕ) → ((Fin n → ℝ) → E) → ℝ≥0∞
  | 0, f => ‖f (fun i => Fin.elim0 i)‖ₑ
  | n + 1, f =>
      (∫⁻ t in Icc (0 : ℝ) 1, cubeSobolevL1 n (fun x => f (Fin.cons t x))) +
      ∫⁻ t in Icc (0 : ℝ) 1,
        cubeSobolevL1 n (fun x => deriv (fun s => f (Fin.cons s x)) t)

theorem contDiff_cons_const {n : ℕ} (t : ℝ) :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => (Fin.cons t x : Fin (n + 1) → ℝ)) := by
  apply contDiff_pi.2
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin n → ℝ => t))
  · simpa only [Fin.cons_succ] using contDiff_apply ℝ (fun _ : Fin n => ℝ) j

theorem contDiff_cons_curve {n : ℕ} (x : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => (Fin.cons t x : Fin (n + 1) → ℝ)) := by
  apply contDiff_pi.2
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · convert (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)) using 1
    ext t
    rfl
  · simpa only [Fin.cons_succ] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => x j))

theorem contDiff_deriv_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → E}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => deriv (fun s => f (Fin.cons s x)) t) := by
  have hc : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)) := by
    apply contDiff_pi.2
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using (contDiff_snd : ContDiff ℝ ∞
        (fun p : (Fin n → ℝ) × ℝ => p.2))
    · convert ((contDiff_apply ℝ (fun _ : Fin n => ℝ) j).comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : (Fin n → ℝ) × ℝ → Fin n → ℝ))) using 1
      ext p
      rfl
  have hfc : ContDiff ℝ ∞ (Function.uncurry
      (fun (x : Fin n → ℝ) (s : ℝ) => f (Fin.cons s x))) := hf.comp hc
  have hd := hfc.fderiv_apply (n := ∞) (g := fun _ : Fin n → ℝ => t)
    (k := fun _ : Fin n → ℝ => (1 : ℝ)) contDiff_const contDiff_const (by simp)
  simpa only [fderiv_apply_one_eq_deriv] using hd

/-- The whole-space analogue of `cubeSobolevL1`: the sum of the integrals
of all square-free mixed derivatives, of orders at most `n`, on `ℝ^n`.
As in the cube version, the formula uses iterated Lebesgue integrals. -/
@[expose] noncomputable def wholeSobolevL1 : (n : ℕ) → ((Fin n → ℝ) → E) → ℝ≥0∞
  | 0, f => ‖f (fun i => Fin.elim0 i)‖ₑ
  | n + 1, f =>
      (∫⁻ t, wholeSobolevL1 n (fun x => f (Fin.cons t x))) +
      ∫⁻ t, wholeSobolevL1 n (fun x => deriv (fun s => f (Fin.cons s x)) t)

end WaveTurbulence.Analysis
