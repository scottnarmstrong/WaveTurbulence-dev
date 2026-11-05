/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.BinaryResonantDecay
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Actual derivative and gradient decay of the binary Nstar kernels -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory

variable {d : ℕ}

/-- The original x derivative of each two-child source resonant kernel. -/
def binaryResonantDerivative (j : Fin 3) (f g : Mom d → ℝ)
    (Df Dg : Mom d → Mom d →L[ℝ] ℝ) (k ℓ x : Mom d) : Mom d →L[ℝ] ℝ :=
  match j with
  | 0 => f (k+ℓ+x) • Dg (k+x) + g (k+x) • Df (k+ℓ+x)
  | 1 => f (k+ℓ) • Dg (k+x)
  | _ => f (k+ℓ) • Dg (k+ℓ+x)

/-- The displayed derivative is the derivative of the actual source kernel. -/
theorem hasFDerivAt_binaryResonant {f g : Mom d → ℝ}
    {Df Dg : Mom d → Mom d →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (j : Fin 3) (k ℓ x : Mom d) :
    HasFDerivAt (binaryResonantKernel j f g k ℓ)
      (binaryResonantDerivative j f g Df Dg k ℓ x) x := by
  have hf' (a : Mom d) : HasFDerivAt (fun x => f (a+x)) (Df (a+x)) x := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using
      (hf (a+x)).comp x ((hasFDerivAt_id x).const_add a)
  have hg' (a : Mom d) : HasFDerivAt (fun x => g (a+x)) (Dg (a+x)) x := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using
      (hg (a+x)).comp x ((hasFDerivAt_id x).const_add a)
  fin_cases j
  · exact (hf' (k+ℓ)).mul (hg' k)
  · exact (hg' k).const_mul (f (k+ℓ))
  · exact (hg' (k+ℓ)).const_mul (f (k+ℓ))

/-- Joint continuity of the literal derivative needs only the stated
continuous input functions and their actual continuous derivatives. -/
theorem continuous_binaryResonantDerivative {f g : Mom d → ℝ}
    {Df Dg : Mom d → Mom d →L[ℝ] ℝ} (hf : Continuous f) (hg : Continuous g)
    (hDf : Continuous Df) (hDg : Continuous Dg) (j : Fin 3) (k : Mom d) :
    Continuous (fun p : Mom d × Mom d => binaryResonantDerivative j f g Df Dg k p.1 p.2) := by
  fin_cases j
  · exact ((hf.comp (by fun_prop)).smul (hDg.comp (by fun_prop))).add
      ((hg.comp (by fun_prop)).smul (hDf.comp (by fun_prop)))
  · exact (hf.comp (by fun_prop)).smul (hDg.comp (by fun_prop))
  · exact (hf.comp (by fun_prop)).smul (hDg.comp (by fun_prop))

/-- The actual derivative norm has an integrable DeltaKernel envelope
with the same exponent and only twice the original binary weight. -/
theorem deltaKernel_norm_binaryResonantDerivative {C N : ℝ}
    (hd : 2 ≤ d) (hN : 2*(d:ℝ) < N) {f g : Mom d → ℝ}
    {Df Dg : Mom d → Mom d →L[ℝ] ℝ} (hf : Continuous f) (hg : Continuous g)
    (hDf : Continuous Df) (hDg : Continuous Dg)
    (hfb : DecayBound C N f) (hgb : DecayBound C N g)
    (hDfb : DecayBound C N (fun x => ‖Df x‖)) (hDgb : DecayBound C N (fun x => ‖Dg x‖))
    (j : Fin 3) (k : Mom d) :
    DeltaKernel (fun ℓ x => ‖binaryResonantDerivative j f g Df Dg k ℓ x‖)
      (fun ℓ => 2*binaryResonantWeight j C N k ℓ) (binaryResonantShift j k) (N/2) := by
  have hfAbs : DecayBound C N (fun x => |f x|) := fun x => by simpa only [abs_abs] using hfb x
  have hgAbs : DecayBound C N (fun x => |g x|) := fun x => by simpa only [abs_abs] using hgb x
  have hleft := deltaKernel_binaryResonant hd hN hf.abs hDg.norm hfAbs hDgb j k
  have hright := deltaKernel_binaryResonant hd hN hDf.norm hg.abs hDfb hgAbs j k
  refine ⟨(continuous_binaryResonantDerivative hf hg hDf hDg j k).norm,?_,hleft.dim,?_⟩
  · intro ℓ x
    have hl := hleft.bound ℓ x
    have hr := hright.bound ℓ x
    have hdom : ‖binaryResonantDerivative j f g Df Dg k ℓ x‖ ≤
        |binaryResonantKernel j (fun x => |f x|) (fun x => ‖Dg x‖) k ℓ x| +
        |binaryResonantKernel j (fun x => ‖Df x‖) (fun x => |g x|) k ℓ x| := by
      fin_cases j
      · change ‖f (k+ℓ+x) • Dg (k+x) + g (k+x) • Df (k+ℓ+x)‖ ≤
          abs (|f (k+ℓ+x)| * ‖Dg (k+x)‖) + abs (‖Df (k+ℓ+x)‖ * |g (k+x)|)
        apply (norm_add_le _ _).trans_eq
        simp only [norm_smul,Real.norm_eq_abs,abs_abs,abs_mul,abs_norm]
        ring
      · change ‖f (k+ℓ) • Dg (k+x)‖ ≤ abs (|f (k+ℓ)| * ‖Dg (k+x)‖) + abs (‖Df (k+ℓ)‖*|g (k+x)|)
        rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_abs,abs_norm]
        exact le_add_of_nonneg_right (abs_nonneg _)
      · change ‖f (k+ℓ) • Dg (k+ℓ+x)‖ ≤ abs (|f (k+ℓ)| * ‖Dg (k+ℓ+x)‖) + abs (‖Df (k+ℓ)‖*|g (k+ℓ+x)|)
        rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_abs,abs_norm]
        exact le_add_of_nonneg_right (abs_nonneg _)
    rw [abs_norm]
    exact hdom.trans ((add_le_add hl hr).trans_eq (by ring))
  · simpa only [mul_left_comm] using hleft.integrable.const_mul (2:ℝ)

end WaveTurbulence.RegAsymp
