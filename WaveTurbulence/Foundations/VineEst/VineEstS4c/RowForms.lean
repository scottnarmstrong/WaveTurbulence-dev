/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.LeibnizPack
import Mathlib.Tactic

/-!
# V5 Step 4c, clause (b): the momentum-difference rows

For real momentum factors `M` (`conj (M k) = M k`) and `a = x - y` or `a = y - x` (`‖a‖ = |r|`), the four
(b)-products of (replaceterm1) are `±|a|` times the weights of `kq_IIa`, `kq_IIb`, `kt_IIa`, `kt_IIb`:

* couple, Vine II-a (`y = k₁`, `x = k₁ + a`): `conj(M_Q y - M_Q x) M_T x = -|a| (dq_a M_Q)(k₁) M_T(k₁+a)`;
* couple, Vine II-b (`x = k₁`, `y = k₁ + a`): `conj(M_Q y - M_Q x) M_T x = |a| (M_T · dq_a M_Q)(k₁)`;
* tree, Vine II-a (`y = k₁`, `x = k₁ + a`): `M_Q x conj(M_T x - M_T y) = |a| (dq_a M_T · M_Q(·+a))(k₁)`;
* tree, Vine II-b (`x = k₁`, `y = k₁ + a`): `M_Q x conj(M_T x - M_T y) = -|a| (dq_a M_T · M_Q)(k₁)`.
-/

@[expose] public section
set_option autoImplicit false

open scoped ComplexConjugate

namespace WaveTurbulence.VineEstS4c

variable {d : ℕ}

theorem shift_sub_eq_norm_mul_diffQuot (f : Mom d → ℂ) (a k : Mom d) :
    f (k + a) - f k = ((‖a‖ : ℝ) : ℂ) * diffQuot a f k := by
  unfold diffQuot
  by_cases h : ‖a‖ = 0
  · have ha : a = 0 := norm_eq_zero.mp h
    subst ha; simp
  · have h' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    field_simp

end WaveTurbulence.VineEstS4c
