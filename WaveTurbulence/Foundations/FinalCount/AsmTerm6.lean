/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm5
public import WaveTurbulence.Foundations.FinalCount.AsmInputs
public import WaveTurbulence.Foundations.FinalCount.G3Op5c
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 6: the `α`-part of the component product is at most `1/apProd(hf)`.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- `apFactor ∈ (0, 1]` for a label in range (`L⁻¹ ≤ R ≤ L^{-γ+η}`, `γ ≥ 5η`, `L ≥ 1`). -/
theorem apFactor_pos_le_one {L γ η : ℝ} (hL : 1 ≤ L) (hγ : 5 * η ≤ γ) (hη : 0 ≤ η) {c : Cls}
    (hc : ∀ ρ kp, c = .alpha ρ kp → L⁻¹ ≤ ρ ∧ ρ ≤ L ^ (-γ + η) ∧ (kp = 0 ∨ kp = 50)) :
    0 < apFactor L γ η c ∧ apFactor L γ η c ≤ 1 := by
  have hL0 : 0 < L := by linarith
  cases c with
  | eps => simp [apFactor]
  | beta => simp [apFactor]
  | ghost => simp [apFactor]
  | alpha ρ kp =>
    obtain ⟨h1, h2, h3⟩ := hc ρ kp rfl
    have hρ : 0 < ρ := lt_of_lt_of_le (inv_pos.2 hL0) h1
    refine ⟨by unfold apFactor; positivity, ?_⟩
    unfold apFactor
    have e1 : L ^ ((γ + 3 * η) / 2 - (kp : ℝ) * η) * ρ ≤ L ^ ((γ + 3 * η) / 2 - (kp : ℝ) * η) * L ^ (-γ + η) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e2 : L ^ ((γ + 3 * η) / 2 - (kp : ℝ) * η) * L ^ (-γ + η) ≤ 1 := by
      rw [← Real.rpow_add hL0]
      have : (γ + 3 * η) / 2 - (kp : ℝ) * η + (-γ + η) ≤ 0 := by
        have : 0 ≤ (kp : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη
        linarith
      calc _ ≤ L ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL this
        _ = 1 := Real.rpow_zero L
    exact e1.trans e2

theorem alpha_part {hf : HSt V D₀} {Tm : V → Prop} {L γ η : ℝ} {Rs : Finset V}
    (hR : CompRep (hf.op5 Tm).s.M Rs)
    (hap : ∀ v ∈ hf.s.M.atoms, 0 < apFactor L γ η (hf.s.cls v) ∧ apFactor L γ η (hf.s.cls v) ≤ 1) :
    ∏ a ∈ Rs, ∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹ ≤ (apProd L γ η hf.s)⁻¹ := by
  rw [← hR.prod_atoms (fun v => (apFactor L γ η (hf.s.cls v))⁻¹)]
  unfold apProd
  refine le_trans ?_ (le_of_eq (Finset.prod_inv_distrib (s := hf.s.M.atoms) (f := fun v => apFactor L γ η (hf.s.cls v))))
  exact prod_filter_le_of_one_le _ _ (fun v hv => (Op5.atoms_sub hv).1) _ (fun v hv => by
    have := hap v hv
    exact (one_le_inv₀ this.1).2 this.2)

end WaveTurbulence.FinalCountAsm
