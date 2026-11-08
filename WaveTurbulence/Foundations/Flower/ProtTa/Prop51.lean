/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.AtomSmall

/-! # PROT-TA: o73 Proposition 5.1 in the source's form

(5.1): `K_α(t,s) = e^{-πiαs} ∫_s^t e^{πiαu} du` (`= (e^{πiα(t-s)}-1)/(πiα)`, resp. `t-s` for `α = 0`) equals
`hz (α/2) (t-s)`; (5.2): `sup_α ‖Φ(·-q) K_α‖_{A^θ} ≤ B_θ`, uniformly in the layer index `q`, for `0 ≤ θ ≤ 1`
(`A^θ` is the weighted Fourier `L¹` norm with weight `max(⟨λ₁⟩,⟨λ₂⟩)^θ` in the `2π` convention; `K_α` is smooth
on all of `ℝ²`, so the extension agrees with it on the open triangle `q < s < t < q+1`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtTa

/-- The one-link kernel (5.1), as the source writes it. -/
def linkKernel (α : ℝ) (y : Fin 2 → ℝ) : ℂ :=
  Complex.exp (((-(Real.pi * α * y 1) : ℝ) : ℂ) * Complex.I) *
    ∫ u in y 1..y 0, Complex.exp (((Real.pi * α * u : ℝ) : ℂ) * Complex.I)

theorem linkKernel_eq (α : ℝ) (y : Fin 2 → ℝ) : linkKernel α y = hz (α / 2) (y 0 - y 1) := by
  have hsub := intervalIntegral.integral_comp_add_left (a := 0) (b := y 0 - y 1)
    (fun u : ℝ => Complex.exp (((Real.pi * α * u : ℝ) : ℂ) * Complex.I)) (y 1)
  simp only [add_zero, add_sub_cancel] at hsub
  unfold linkKernel hz
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun w _ => ?_)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **o73 Proposition 5.1** (uniform in `α` and in the layer index `q`). -/
theorem prop51 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ α q : ℝ,
      timeFourierNorm θ (fun y : Fin 2 → ℝ => Phi (fun i => y i - q) * linkKernel α y) ≤ B := by
  obtain ⟨B, hB, h⟩ := psi_uniform_translate hθ0 hθ1
  refine ⟨B, hB, fun α q => ?_⟩
  have : (fun y : Fin 2 → ℝ => Phi (fun i => y i - q) * linkKernel α y) =
      fun y => psi (α / 2) (y + fun _ => -q) := by
    funext y
    rw [linkKernel_eq, psi]
    simp only [Pi.add_apply]
    have e : (y 0 + -q) - (y 1 + -q) = y 0 - y 1 := by ring
    rw [e]
    congr 2
  rw [this]
  exact h _ _

end WaveTurbulence.Flower.ProtTa
