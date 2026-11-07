/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL13
public import WaveTurbulence.Foundations.FinalCount.G3Ex34
/-! **G3-LOWDEG (R48), part 14**: the uniform step `UStepD3` and its deviation (`excessprop1` for the degree-`2` cut).
The molecule and the inherited decorations are unchanged, so `𝔄_pre = 𝔄_pos` (deviation `1`).  In the TARGET-literal bookkeeping
(the isolated half counted: `ΔF = 1`, `ΔV_β = 2`, no new `α`-atom) `excessRHS ≥ 1`, so `StepDev … 1 [] 1 2` holds.  The TRUE
increments (`ΔF = 0`, `ΔV_β = 1`, the isolated half deleted) would give `excessRHS < 1`: the statement with true increments is
FALSE for this step; the assembly pays the difference with the index drop `R → R - 1` (`InvL.stepD3`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {M₀ : Molecule V D₀}

/-- **Step D3 for the class `Adm0`**. -/
inductive UStepD3 (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) :
    HSt V D₀ → HSt V D₀ → Prop
  | cut (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) (hv : v ∈ h.s.M.atoms) (hε : h.s.cls v = .eps)
      (hd : h.s.M.deg v = 2) (hx₁ : h.s.M.atom x₁ = v) (hx₂ : h.s.M.atom x₂ = v)
      (hne : x₂ ≠ h.s.M.mate x₁) (ho₁ : h.s.M.out x₁ = false) (ho₂ : h.s.M.out x₂ = true)
      (hnz : ∀ k0, Adm0 k0 → pgap L w k0 (h.s.pr x₁ x₂) ≠ 0)
      (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂)) :
      UStepD3 C L γ η w Adm0 h (h.betaPost v x₁ x₂)

theorem UStepD3.hstep {C : CollData M₀} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : UStepD3 C L γ η w Adm0 h h') (hk : Adm0 κ) : HStepD3 C L γ η w κ h h' := by
  cases hs with
  | cut v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ hnz hdes =>
    exact HStepD3.cut h v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ (hnz κ hk) hdes

/-- **The degree-`2` cut changes neither the molecule nor the inherited decorations: deviation `1`.** -/
theorem UStepD3.dev {C : CollData M₀} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀}
    (hs : UStepD3 C L γ η w Adm0 h h') (δ C₁ : ℝ) (P : Finset V → ℝ) :
    IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P) 1 := by
  cases hs with
  | cut v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ hnz hdes =>
    unfold IsDeviation
    rw [one_mul]
    exact le_of_eq rfl

theorem excessRHS_two_cut_ge_one (hL : 1 ≤ L) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    1 ≤ excessRHS L γ η [] 1 2 := by
  unfold excessRHS
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  simp only [List.map_nil, List.prod_nil, mul_one]
  rw [← Real.rpow_add hL0]
  refine Real.one_le_rpow hL ?_
  push_cast
  nlinarith [mul_nonneg (mul_nonneg hη hη) (sub_nonneg.2 hη1)]

/-- **excessprop1 for the degree-`2` cut, TARGET-literal bookkeeping** (`ΔF = 1`, `ΔV_β = 2`, no `α`-atom). -/
theorem UStepD3.excess {C : CollData M₀} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀}
    (hs : UStepD3 C L γ η w Adm0 h h') (δ C₁ : ℝ) (P : Finset V → ℝ) (hL : 1 ≤ L) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    StepDev L γ η δ C₁ w Adm0 P 1 [] 1 2 h h' := by
  unfold StepDev
  have h0 := excessRHS_two_cut_ge_one (γ := γ) hL hη hη1
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 * excessRHS L γ η [] 1 2) := by
    rw [one_mul]; exact ENNReal.one_le_ofReal.2 h0
  unfold IsDeviation at *
  exact (hs.dev δ C₁ P).trans (mul_le_mul_left h1 _)

end WaveTurbulence.FinalCountG3
