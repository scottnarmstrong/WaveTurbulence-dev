/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Layered.RestrictionCalculus
public import WaveTurbulence.Foundations.Fourier.Norm00VBasic

/-!
# Telescoping products in the order-zero restriction norms (TARGET prooflayer1-1, L1241)

TARGET's proof of Prop 6.1 for `q > q'` factorizes the kernel along the same-layer blocks and compares with the
product of the single-layer leading terms. One factor at a time:

* `restr_step`: a factor `c(v)` constant in time, compared with `a(v)`:
  `W(cK − aA) = (c−a)·W(K−A) + (c−a)·WA + a·W(K−A)`;
* `restr_top`: a time-dependent factor `x`, compared with `y`, by the product estimate.

`restr_add_le`, `restr_congr`: sums and pointwise agreement on `ℬ × K`.
-/

@[expose] public section

open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Layered

variable {r : ℕ} {V : Type*}

/-- The restriction norm only sees `ℬ × K`. -/
theorem restr_congr (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V) {F G : (Fin r → ℝ) → V → ℂ}
    (h : ∀ t ∈ B, ∀ v ∈ K, F t v = G t v) :
    mixedRestrictionNorm00 θ B K (fun t v => F t v) = mixedRestrictionNorm00 θ B K (fun t v => G t v) := by
  have he : (fun (t : B) (v : K) => F t v) = (fun (t : B) (v : K) => G t v) :=
    funext fun t => funext fun v => h t t.2 v v.2
  rw [he]

end WaveTurbulence.Layered

/-! ### Traces carried to a target box -/

namespace WaveTurbulence.Layered

open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal

variable {r : ℕ} {V : Type*}

/-- The unit box `[0, 1]^r`. -/
def unitBox : Set (Fin r → ℝ) := {u | ∀ i, u i ∈ Icc (0 : ℝ) 1}

theorem traceConst_chiUnit_ne_top (θ : ℝ) : Regref.traceConst (r := r) θ chiUnit ≠ ⊤ := by
  unfold Regref.traceConst
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (timeFourierNorm_lt_top_of_smooth_compact θ (coordinateCutoff_hasCompactSupport chiUnit_hasCompactSupport)
      (coordinateCutoff_contDiff chiUnit_contDiff)).ne

/-- **A trace at `u_j = c` of the unit box, carried between boxes by translations**:
`‖h(update (t + b) j c + a)‖_{𝔛(T')} ≤ K_tr ‖h‖_{𝔛(ℬ)}`, when `t ↦ t + b` maps `T'` into the unit box and the
trace line `update u j c + a` (`u` in the unit box) lies in `closure (interior ℬ)`. -/
theorem restr_trace_transport {θ : ℝ} (hθ : 0 ≤ θ) {B T' : Set (Fin r → ℝ)} (K : Set V)
    (h : (Fin r → ℝ) → V → ℂ) (hh : ∀ v ∈ K, Continuous fun t => h t v) (a b : Fin r → ℝ)
    (j : Fin r) (c : ℝ) (hT' : ∀ t ∈ T', t + b ∈ unitBox)
    (hline : ∀ u ∈ (unitBox : Set (Fin r → ℝ)), Function.update u j c + a ∈ closure (interior B)) :
    mixedRestrictionNorm00 θ T' K (fun t v => h (Function.update ((t : Fin r → ℝ) + b) j c + a) v) ≤
      Regref.traceConst (r := r) θ chiUnit * mixedRestrictionNorm00 θ B K (fun t v => h t v) := by
  set B₀ : Set (Fin r → ℝ) := (fun t => t + a) ⁻¹' B with hB₀
  have h1 := mixedRestrictionNorm00_translate_le θ (B := T') (B' := unitBox) K
    (fun u v => h (Function.update u j c + a) v) b hT'
  have hcl : ∀ u ∈ (unitBox : Set (Fin r → ℝ)), Function.update u j c ∈ closure (interior B₀) := by
    intro u hu
    have e : closure (interior B₀) = (fun t => t + a) ⁻¹' closure (interior B) := by
      show closure (interior ((Homeomorph.addRight a) ⁻¹' B)) =
        (Homeomorph.addRight a) ⁻¹' closure (interior B)
      rw [← Homeomorph.preimage_interior, ← Homeomorph.preimage_closure]
    rw [e]
    exact hline u hu
  have hc' : ∀ v ∈ K, Continuous fun t => h (t + a) v := fun v hv =>
    (hh v hv).comp (continuous_id.add continuous_const)
  have h2 := Regref.mixedRestrictionNorm00_trace_le hθ chiUnit_contDiff chiUnit_hasCompactSupport
    (B := B₀) (T := unitBox) (K := K) (fun t v => h (t + a) v) hc' j c hcl
    (fun u hu => coordinateCutoff_chiUnit_eq_one hu)
  have h3 := mixedRestrictionNorm00_translate_le θ (B := B₀) (B' := B) K h a (fun t ht => ht)
  exact h1.trans (h2.trans (mul_le_mul_right h3 _))

end WaveTurbulence.Layered
