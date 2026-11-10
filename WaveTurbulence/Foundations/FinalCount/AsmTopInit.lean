/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmP1H
public import WaveTurbulence.Foundations.FinalCount.AsmTerm16a
public import WaveTurbulence.Foundations.FinalCount.AsmTopNum
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
/-! **FINALCOUNT-ASSEMBLY (top level): the initial state.**  `F = 1`, `V_β = 0`, `apProd = 1`, `critCount = #crit`, and the value of
the phase-1 potential `WPot (g1 …)` at `HSt.init M₀`. -/
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

theorem vBeta_init (M₀ : Molecule V D₀) : vBeta (St.init M₀) = 0 := by
  unfold vBeta
  simp [St.init]

theorem apProd_init (L γ η : ℝ) (M₀ : Molecule V D₀) : apProd L γ η (St.init M₀) = 1 := by
  unfold apProd
  simp [St.init, apFactor]

theorem critCount_init (crit : V → Prop) (M₀ : Molecule V D₀) :
    critCount crit (St.init M₀) = (M₀.atoms.filter crit).card := by
  unfold critCount
  simp [St.init]

theorem numComponents_init {Rn : ℕ} {M₀ : Molecule V D₀} (hS : SubHyp Rn M₀) : M₀.numComponents = 1 := by
  refine Mole.numComponents_eq_one M₀ ?_ hS.conn
  by_contra hne
  have h0 : M₀.atoms = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
  have := hS.count
  rw [h0] at this
  have h1 := hS.one_le
  simp at this
  omega


/-- The value of the phase-1 potential at the initial state, with `Y0 = L^(eraseA γ η R + 4η(R-1) - ε0)` and `Fmax = 2R-1`. -/
theorem WPot_init_eq {Rn : ℕ} {M₀ : Molecule V D₀} (hS : SubHyp Rn M₀) {L γ η ε0 : ℝ} (hL : 0 < L) (crit : V → Prop) :
    WPot L γ η (L ^ (eraseA γ η * (Rn : ℝ) + 4 * η * ((Rn : ℝ) - 1) - ε0)) (g1 γ η crit (2 * (Rn : ℝ) - 1)) (HSt.init M₀) =
      ENNReal.ofReal (L ^ ((Rn - 1 : ℝ) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - ε0 -
        4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ)))) := by
  unfold WPot potR g1 gExp
  have e1 : (HSt.init M₀).s.M.numComponents = 1 := numComponents_init hS
  have e2 : vBeta (HSt.init M₀).s = 0 := vBeta_init M₀
  have e3 : apProd L γ η (HSt.init M₀).s = 1 := apProd_init L γ η M₀
  have e4 : critCount crit (HSt.init M₀).s = (M₀.atoms.filter crit).card := critCount_init crit M₀
  have e5 : (HSt.init M₀).s.M.rho = M₀.rho := rfl
  rw [e1, e2, e3, e4, e5]
  congr 1
  simp only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, add_zero, div_one]
  rw [← Real.rpow_add hL, ← Real.rpow_add hL]
  congr 1
  unfold eraseA gam0
  ring

end WaveTurbulence.FinalCountAsm
