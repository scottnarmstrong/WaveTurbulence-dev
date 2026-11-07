/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm15a
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 15b: G8's right-hand sides in potential form.**
`finalRHS`/`damagedRHS` `= (∏_v (apFactor v)⁻¹) · L^{exponent}` with the exponent of `exa`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem alpha_prod_eq (hf : HSt V D₀) (atoms : Finset V) {L : ℝ} (hL : 0 < L) (γ η : ℝ) :
    (∏ v ∈ WaveTurbulence.FinalCountG8.alphaAtoms atoms (cl8 hf),
      (L ^ (-(γ + 3 * η) / 2 + ((cl8 hf v).kap : ℝ) * η) * ((cl8 hf v).lab)⁻¹)) =
    ∏ v ∈ atoms, (apFactor L γ η (hf.s.cls v))⁻¹ := by
  unfold WaveTurbulence.FinalCountG8.alphaAtoms
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold cl8
  cases hc : hf.s.cls v with
  | eps => simp [toCls, g8Cls, WaveTurbulence.FinalCountG8.Cls.IsAlpha, apFactor]
  | beta => simp [toCls, g8Cls, WaveTurbulence.FinalCountG8.Cls.IsAlpha, apFactor]
  | ghost => simp [toCls, g8Cls, WaveTurbulence.FinalCountG8.Cls.IsAlpha, apFactor]
  | alpha R kp =>
    simp only [toCls, g8Cls, WaveTurbulence.FinalCountG8.Cls.IsAlpha, if_true, WaveTurbulence.FinalCountG8.Cls.kap,
      WaveTurbulence.FinalCountG8.Cls.lab, apFactor]
    rw [mul_inv, ← Real.rpow_neg hL.le]
    refine (if_pos trivial).trans ?_
    congr 2; ring

theorem finalRHS_eq (hf : HSt V D₀) {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (odd : Prop) {L : ℝ}
    (hL : 0 < L) (γ η : ℝ) :
    WaveTurbulence.FinalCountG8.finalRHS M (cl8 hf) odd L γ η =
      (∏ v ∈ M.atoms, (apFactor L γ η (hf.s.cls v))⁻¹) *
        L ^ ((gam0 γ + 2 * η ^ 2) * ((WaveTurbulence.FinalCountG8.betaAtoms M.atoms (cl8 hf)).card : ℝ)
          - (if ¬ odd then eraseA γ η else 0) - η ^ 5 * (M.rho : ℝ)) := by
  unfold WaveTurbulence.FinalCountG8.finalRHS
  simp only
  rw [alpha_prod_eq hf M.atoms hL, mul_assoc, ← Real.rpow_add hL]
  congr 2
  by_cases ho : odd <;> simp [ho, gam0, eraseA] <;> ring

theorem damagedRHS_eq (hf : HSt V D₀) {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {L : ℝ}
    (hL : 0 < L) (γ η : ℝ) :
    WaveTurbulence.FinalCountG8.damagedRHS M (cl8 hf) L γ η =
      (∏ v ∈ M.atoms, (apFactor L γ η (hf.s.cls v))⁻¹) *
        L ^ ((gam0 γ + 2 * η ^ 2) * ((WaveTurbulence.FinalCountG8.betaAtoms M.atoms (cl8 hf)).card : ℝ)
          - η ^ 5 * (M.rho : ℝ) + η * (WaveTurbulence.FinalCountG8.epsDefect M (cl8 hf) : ℝ)) := by
  unfold WaveTurbulence.FinalCountG8.damagedRHS
  simp only
  rw [alpha_prod_eq hf M.atoms hL, mul_assoc, ← Real.rpow_add hL]
  unfold gam0
  congr 2
  ring

end WaveTurbulence.FinalCountAsm
