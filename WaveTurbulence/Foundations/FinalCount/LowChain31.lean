/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain30
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass
public import WaveTurbulence.Foundations.FinalCount.AsmTopInit
/-! **FINALCOUNT LOW-CHAIN, session 6 (5): the corrected index profile and the loop-weighted potential.**
`Yz L γ η ε₀ r = L^{a r + 4η max(r-1,0) - ε₀ [1 ≤ r]}` for an INTEGER index `r = RofS - k` (R79: `Y(0) = 1`); `Yz_drop`: `Yz r' L^{a j - ε₀} ≤ Yz r`
for `r' + j = r`.  `Ypk gk k R = gk⁻¹ Yz (R - k)`: the loop gain `gk = g^k` is moved into the potential, so the cover theorems about `QS` are reused
unchanged.  `WPot_init_eqL`: the initial value at the ORIGINAL index `R` with `SubHypL (R + k)` on `M.unloop`. -/
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

/-- The corrected `Y` of R79 at an integer index. -/
noncomputable def Yz (L γ η ε0 : ℝ) (r : ℤ) : ℝ :=
  L ^ (eraseA γ η * (r : ℝ) + 4 * η * ((max (r - 1) 0 : ℤ) : ℝ) - (if 1 ≤ r then ε0 else 0))

theorem Yz_nonneg {L : ℝ} (hL : 0 ≤ L) (γ η ε0 : ℝ) (r : ℤ) : 0 ≤ Yz L γ η ε0 r := by
  unfold Yz; exact Real.rpow_nonneg hL _

theorem Yz_drop {L γ η ε0 : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η) (hε : 0 ≤ ε0) {r r' : ℤ} {j : ℕ} (h : r' + j = r) :
    Yz L γ η ε0 r' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yz L γ η ε0 r := by
  have hL0 : 0 < L := by linarith
  unfold Yz
  rw [← Real.rpow_add hL0]
  apply Real.rpow_le_rpow_of_exponent_le hL
  have hr : (r : ℝ) = r' + j := by rw [← h]; push_cast; ring
  have hjn : (0 : ℤ) ≤ j := by positivity
  have hmax : ((max (r' - 1) 0 : ℤ) : ℝ) ≤ ((max (r - 1) 0 : ℤ) : ℝ) := by
    exact_mod_cast (by omega : max (r' - 1) 0 ≤ max (r - 1) 0)
  have hA : 0 ≤ 4 * η * (((max (r - 1) 0 : ℤ) : ℝ) - ((max (r' - 1) 0 : ℤ) : ℝ)) := by
    have := sub_nonneg.2 hmax; positivity
  rw [hr]
  by_cases h1 : 1 ≤ r' <;> by_cases h2 : 1 ≤ r
  · rw [if_pos h1, if_pos h2]; nlinarith
  · exfalso; omega
  · rw [if_neg h1, if_pos h2]; nlinarith
  · rw [if_neg h1, if_neg h2]; nlinarith

theorem Yz_nat {L γ η ε0 : ℝ} {R : ℕ} (hR : 1 ≤ R) :
    Yz L γ η ε0 (R : ℤ) = L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - ε0) := by
  unfold Yz
  have h1 : 1 ≤ (R : ℤ) := by exact_mod_cast hR
  rw [if_pos h1]
  congr 2
  have : max ((R : ℤ) - 1) 0 = (R : ℤ) - 1 := max_eq_left (by omega)
  rw [this]; push_cast; ring

/-- The loop-weighted index profile: `Ypk gk k R = gk⁻¹ · Yz (R - k)`. -/
noncomputable def Ypk (L γ η ε0 gk : ℝ) (k : ℕ) (R : ℕ) : ℝ := gk⁻¹ * Yz L γ η ε0 ((R : ℤ) - k)

theorem Ypk_nonneg {L : ℝ} (hL : 0 ≤ L) {gk : ℝ} (hg : 0 ≤ gk) (γ η ε0 : ℝ) (k R : ℕ) : 0 ≤ Ypk L γ η ε0 gk k R :=
  mul_nonneg (inv_nonneg.2 hg) (Yz_nonneg hL _ _ _ _)

theorem Ypk_drop {L γ η ε0 : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η) (hε : 0 ≤ ε0) {gk : ℝ} (hg : 0 ≤ gk) (k : ℕ) :
    ∀ R R' j : ℕ, R' + j = R → Ypk L γ η ε0 gk k R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Ypk L γ η ε0 gk k R := by
  intro R R' j h
  unfold Ypk
  have : ((R' : ℤ) - k) + j = (R : ℤ) - k := by rw [← h]; push_cast; ring
  have := Yz_drop (L := L) (γ := γ) (η := η) hL hη hε this
  calc gk⁻¹ * Yz L γ η ε0 ((R' : ℤ) - k) * L ^ (eraseA γ η * (j : ℝ) - ε0) =
      gk⁻¹ * (Yz L γ η ε0 ((R' : ℤ) - k) * L ^ (eraseA γ η * (j : ℝ) - ε0)) := by ring
    _ ≤ gk⁻¹ * Yz L γ η ε0 ((R : ℤ) - k) := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hg)

theorem WPot_smul {L γ η Y0 c : ℝ} (hc : 0 ≤ c) (g : HSt V D₀ → ℝ) (h : HSt V D₀) :
    WPot L γ η (c * Y0) g h = ENNReal.ofReal c * WPot L γ η Y0 g h := by
  unfold WPot potR
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  ring

theorem numComponents_initL' {Rn : ℕ} {M₀ : Molecule V D₀} (hS : SubHypL Rn M₀) : M₀.numComponents = 1 := by
  refine Mole.numComponents_eq_one M₀ ?_ hS.conn
  by_contra hne
  have h0 : M₀.atoms = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
  have := hS.count
  rw [h0] at this
  have h1 := hS.one_le
  simp at this
  omega

/-- The initial value of the phase-1 potential with an arbitrary constant factor and the ORIGINAL index `R`. -/
theorem WPot_init_eqL {Rn R : ℕ} {M₀ : Molecule V D₀} (hS : SubHypL Rn M₀) {L γ η ε0 c : ℝ} (hc : 0 ≤ c) (hL : 0 < L) (crit : V → Prop) :
    WPot L γ η (c * L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - ε0)) (g1 γ η crit (2 * (R : ℝ) - 1)) (HSt.init M₀) =
      ENNReal.ofReal c * ENNReal.ofReal (L ^ ((R - 1 : ℝ) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - ε0 -
        4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ)))) := by
  rw [WPot_smul hc]
  congr 1
  unfold WPot potR g1 gExp
  have e1 : (HSt.init M₀).s.M.numComponents = 1 := numComponents_initL' hS
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
