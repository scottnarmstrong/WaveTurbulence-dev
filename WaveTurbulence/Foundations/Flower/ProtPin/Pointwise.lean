/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Restr
public import WaveTurbulence.Foundations.Regref.FourierAE

/-! # D3 PROT-PIN: a continuous function is bounded pointwise by its restricted norm

`enorm_le_rn`: for `θ ≥ 0`, a continuous `f`, a set `B ⊆ closure (interior B)` and `x ∈ B`, `‖f x‖ₑ ≤ rn θ B f`
(a near-optimal continuous extension agrees with `f` on `B`, `exists_cont_ext`, and is bounded by its Fourier norm,
main's `enorm_le_timeFourierNorm_at`). Used for the constant pieces `Q(s, s)`, `K(t, s)` of the configurations that pin
two linked nodes. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

variable {r : ℕ}

/-- **Pointwise bound by the restricted norm.** -/
theorem enorm_le_rn {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)} (hB : ∀ t ∈ B, t ∈ closure (interior B))
    {f : (Fin r → ℝ) → ℂ} (hf : Continuous f) {x : Fin r → ℝ} (hx : x ∈ B) : ‖f x‖ₑ ≤ rn θ B f := by
  by_cases htop : rn θ B f = ⊤
  · rw [htop]; exact le_top
  have hfin : rn θ B f < ⊤ := lt_top_iff_ne_top.mpr htop
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨g, hgc, hgag, -, hgle⟩ := exists_cont_ext hθ hB hf hfin (ε := (ε : ℝ≥0∞))
    (by exact_mod_cast hε) ENNReal.coe_ne_top
  rw [← hgag x hx]
  exact (Regref.enorm_le_timeFourierNorm_at hθ g x hgc.continuousAt).trans hgle

end WaveTurbulence.Flower.ProtPin
