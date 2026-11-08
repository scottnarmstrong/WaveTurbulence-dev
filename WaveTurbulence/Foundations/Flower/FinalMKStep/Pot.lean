/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.FinalCount.LowChain28

/-! # C1a SURV-STEP (1): the potential inequality of the re-cut step with the survivor budget (`hW_RCp`)

o75 75-F2 on main's potential model (C0 SCOPE §7). The re-cut step removes a survivor one of whose joints is an
`α/β` remnant of degree `2` (an already cut shared joint); its isolated half is a ghost and is deleted
(`vinePostG`). Against main's per-step form `N · (CN · excessRHS2 [] 1 2) · W(h') ≤ W(h)`:

* the index drops by `j` (the number of `ε` joints of degree `2`, `j ≤ 1` here) and `Yp` pays `L^{eraseA·j - ε₀}`;
* `ΔF ≥ -j` (ghost deleted: the new component is the deleted isolated half) and `ΔV_β ≤ 1 - j`;
* the removed `α/β` joint can only lower `apProd` (`hApe`: the label refund `1/factor(J^o) ≥ 1`);
* the survivor budget `g1E = g1 - pendRC` gains `L^{-1}` (`hpend`).

The margin is `2γ₀ + 3η² + 8η⁶ + ε₀ - 1 ≤ 0`, i.e. `hmarg : 2 γ₀ + 4 η² ≤ 1`, which main's `h8 : 8η ≤ 2γ - 1`
gives for every `γ ∈ (1/2, 1)` (`hmarg_of_h8`). `pot_step_idx_le` is main's `pot_step_idx` (LowChain1) with the
`apProd` equality weakened to `apProd h ≤ apProd h'`; its proof is main's, with one added comparison step. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **`pot_step_idx` with a label refund**: as main's `pot_step_idx`, but `apProd` may grow along the step. -/
theorem pot_step_idx_le {L γ η : ℝ} (hL1 : 1 ≤ L) {h h' : HSt V D₀} (hAp : 0 < apProd L γ η h.s)
    (hApe : apProd L γ η h.s ≤ apProd L γ η h'.s) (hγ0 : 0 ≤ min γ (1 - γ)) {Y Y' A j : ℝ} (hY' : 0 ≤ Y')
    (hYY : Y' * L ^ (A * j) ≤ Y) {g : HSt V D₀ → ℝ} {δg : ℝ} (hg : g h - δg ≤ g h') (dF dV : ℝ)
    (hF : (h.s.M.numComponents : ℝ) + dF ≤ h'.s.M.numComponents) (hV : (vBeta h'.s : ℝ) ≤ vBeta h.s + dV)
    {Ilit : ℝ} (hI : 0 ≤ Ilit) (N : ℕ) {x : ℝ} (hNI : (N : ℝ) * Ilit ≤ L ^ x)
    (hx : x + δg + (-(2 * min γ (1 - γ) + 5 * η ^ 2) * dF + (min γ (1 - γ) + 2 * η ^ 2) * dV) - A * j ≤ 0) :
    (N : ℝ≥0∞) * (ENNReal.ofReal Ilit * WPot L γ η Y' g h') ≤ WPot L γ η Y g h := by
  have hL : 0 < L := by linarith
  unfold WPot potR
  rw [← ENNReal.ofReal_mul hI, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set a := 2 * min γ (1 - γ) + 5 * η ^ 2 with ha
  set b := min γ (1 - γ) + 2 * η ^ 2 with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  -- the refund: dividing by the larger `apProd h'` only helps
  have hnum : 0 ≤ Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)) :=
    mul_nonneg (mul_nonneg hY' (Real.rpow_nonneg hL.le _)) (Real.rpow_nonneg hL.le _)
  have hdiv : Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)) / apProd L γ η h'.s ≤
      Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)) / apProd L γ η h.s :=
    div_le_div_of_nonneg_left hnum hAp hApe
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiv hI) (Nat.cast_nonneg _)) ?_
  have hE : L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)) ≤
      L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) * L ^ (-a * dF + b * dV) := by
    rw [← Real.rpow_add hL]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    nlinarith
  have h1 : L ^ (-g h') ≤ L ^ (-g h) * L ^ δg := by
    rw [← Real.rpow_add hL]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hP : 0 ≤ L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) := by positivity
  have h2 : L ^ x * L ^ δg * L ^ (-a * dF + b * dV) ≤ L ^ (A * j) := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hpos1 : 0 ≤ L ^ (-g h) := by positivity
  have hpos2 : 0 ≤ L ^ δg := by positivity
  have hpos3 : 0 ≤ L ^ (-a * dF + b * dV) := by positivity
  have hpos4 : 0 ≤ L ^ x := by positivity
  rw [show (N : ℝ) * (Ilit * (Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)) /
      apProd L γ η h.s)) = ((N : ℝ) * Ilit) * (Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) +
      b * (vBeta h'.s : ℝ))) / apProd L γ η h.s by ring]
  rw [div_le_div_iff_of_pos_right hAp]
  calc (N : ℝ) * Ilit * (Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)))
      ≤ (N : ℝ) * Ilit * (Y' * L ^ (-g h') * (L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) *
          L ^ (-a * dF + b * dV))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hE (mul_nonneg hY' (by positivity))
    _ ≤ L ^ x * (Y' * (L ^ (-g h) * L ^ δg) * (L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) *
          L ^ (-a * dF + b * dV))) := by
        apply mul_le_mul hNI _ (mul_nonneg (mul_nonneg hY' (by positivity)) (by positivity)) hpos4
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h1 hY'
    _ = (Y' * (L ^ x * L ^ δg * L ^ (-a * dF + b * dV))) *
          (L ^ (-g h) * L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ))) := by
        ring
    _ ≤ (Y' * L ^ (A * j)) * (L ^ (-g h) * L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hY'
    _ ≤ Y * (L ^ (-g h) * L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ))) := by
        apply mul_le_mul_of_nonneg_right hYY (by positivity)
    _ = _ := by ring

/-- The re-cut margin from main's smallness hypothesis `h8` (`chain_coverLL`): `2γ₀ + 4η² ≤ 1`. -/
theorem hmarg_of_h8 {γ η : ℝ} (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (h8 : 8 * η ≤ 2 * γ - 1) :
    2 * min γ (1 - γ) + 4 * η ^ 2 ≤ 1 := by
  have h1 : min γ (1 - γ) ≤ 1 - γ := min_le_right _ _
  nlinarith

section hWRC
variable {L γ η : ℝ} {M₀ : Molecule V D₀} {m : ℕ}

/-- The survivor budget changes the exponent by the drop of `pendRC` (`g1E = g1 - pendRC`). -/
theorem g1E_step (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀) {h h' : HSt V D₀} {δ : ℝ}
    (hg : g1 γ η crit Fmax h - δ ≤ g1 γ η crit Fmax h') (hpend : pendRC E h' + 1 ≤ pendRC E h) :
    g1E γ η crit Fmax E h - (δ - 1) ≤ g1E γ η crit Fmax E h' := by
  unfold g1E
  have : (pendRC E h' : ℝ) + 1 ≤ pendRC E h := by exact_mod_cast hpend
  linarith

/-- **C1a: the potential inequality of the re-cut step** (o75 75-F2 with ghost deletion; C0 SCOPE §7), with the
survivor budget `g1E`. Increments: index drop `j` (the `ε` joints of degree `2`), `ΔF ≥ -j`, `ΔV_β ≤ 1 - j`, `apProd`
not decreasing (label refund), `ρ` and the critical count as in `hW_D1p`, and one pending re-cut paid (`hpend`).
The case `j = 1` is the whole-component removal (both joints of degree `2`: the re-cut `α/β` joint and an `ε` joint). -/
theorem hW_RCp (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ))
    (hmarg : 2 * min γ (1 - γ) + 4 * η ^ 2 ≤ 1) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀)
    {h h' : HSt V D₀} {R R' j : ℕ} (hRR : R' + j = R) (hI : Inv R h.s) (hI' : Inv R' h'.s)
    (hap : ApPos h.s) (hApe : apProd L γ η h.s ≤ apProd L γ η h'.s)
    (hF : (h.s.M.numComponents : ℝ) - j ≤ h'.s.M.numComponents) (hV : (vBeta h'.s : ℝ) + j ≤ vBeta h.s + 1)
    (hρ : h.s.M.rho ≤ h'.s.M.rho + 88) (hcr : critCount crit h.s ≤ critCount crit h'.s + 2)
    (hpend : pendRC E h' + 1 ≤ pendRC E h) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS h'.s)) (g1E γ η crit Fmax E) h') ≤
      WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  have hL : 0 < L := by linarith
  have hRs : RofS h.s = R := rofS_of_inv hI
  have hRs' : RofS h'.s = R' := rofS_of_inv hI'
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hdrop := hYpd R R' j hRR
  have hex : excessRHS2 L γ η [] 1 2 = L ^ min γ (1 - γ) * L ^ (-η ^ 3 + η ^ 2) := by
    rw [excessRHS2_eq _ _ _ _ _ _ hL, excessRHS_beta L γ η hL]
  have hgd := gExp_drop hη crit (h := h) (h' := h') (a := 88) (b := 2) hρ hcr
  have hg1 : g1 γ η crit Fmax h - (4 * η ^ 6 * (((88 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) + min γ (1 - γ) * (j : ℝ)) ≤
      g1 γ η crit Fmax h' := by
    unfold g1
    nlinarith [mul_nonneg hγ0 (show (0 : ℝ) ≤ (h'.s.M.numComponents : ℝ) - ((h.s.M.numComponents : ℝ) - j) by linarith)]
  have hgE := g1E_step crit Fmax E hg1 hpend
  rw [hRs, hRs']
  have hpow : 0 ≤ η ^ 6 := by positivity
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  refine pot_step_idx_le hL1 hAp hApe hγ0 (A := eraseA γ η * (j : ℝ) - ε0) (j := 1) (hYp0 _)
    (by simpa using hdrop) (g := g1E γ η crit Fmax E) hgE (-(j : ℝ)) (1 - j) (by linarith) (by linarith)
    (by rw [hex]; positivity) N
    (x := (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) + min γ (1 - γ) + (-η ^ 3 + η ^ 2)) ?_ ?_
  · rw [hex]
    calc (N : ℝ) * (CN * (L ^ min γ (1 - γ) * L ^ (-η ^ 3 + η ^ 2)))
        = ((N : ℝ) * CN) * (L ^ min γ (1 - γ) * L ^ (-η ^ 3 + η ^ 2)) := by ring
      _ ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) * (L ^ min γ (1 - γ) * L ^ (-η ^ 3 + η ^ 2)) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by rw [← Real.rpow_add hL, ← Real.rpow_add hL]; congr 1; ring
  · unfold eraseA gam0
    push_cast
    have h4 : η ^ 6 ≤ η ^ 2 / 4096 := by
      have : η ^ 4 ≤ (1 / 40) ^ 4 := pow_le_pow_left₀ hη hη40 4
      have e : η ^ 6 = η ^ 2 * η ^ 4 := by ring
      rw [e]; nlinarith [pow_nonneg hη 2]
    nlinarith [pow_nonneg hη 2, mul_nonneg (pow_nonneg hη 2) hj0]

/-- `hW_RCp` under main's smallness hypothesis `8η ≤ 2γ - 1` (`γ > 1/2`). -/
theorem hW_RCp_h8 (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ))
    (h8 : 8 * η ≤ 2 * γ - 1) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀)
    {h h' : HSt V D₀} {R R' j : ℕ} (hRR : R' + j = R) (hI : Inv R h.s) (hI' : Inv R' h'.s)
    (hap : ApPos h.s) (hApe : apProd L γ η h.s ≤ apProd L γ η h'.s)
    (hF : (h.s.M.numComponents : ℝ) - j ≤ h'.s.M.numComponents) (hV : (vBeta h'.s : ℝ) + j ≤ vBeta h.s + 1)
    (hρ : h.s.M.rho ≤ h'.s.M.rho + 88) (hcr : critCount crit h.s ≤ critCount crit h'.s + 2)
    (hpend : pendRC E h' + 1 ≤ pendRC E h) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS h'.s)) (g1E γ η crit Fmax E) h') ≤
      WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h :=
  hW_RCp hL1 hη hη40 hγ0 (hmarg_of_h8 hη hη40 h8) ε0 Yp hYp0 hYpd hε0 crit Fmax E hRR hI hI' hap hApe hF hV hρ hcr
    hpend hCN N hN

/-! ### Lifting main's phase-1 steps to the survivor budget

`W(Y, g1E) = W(Y·L^{pendRC}, g1)`. A Step-1 step that does not create a pending re-cut (`pendRC h' ≤ pendRC h`: every
step of main's phase 1, and the fresh survivor removals) keeps main's per-step inequality, applied with the constant
`Y·L^{pendRC h}` (main's `hW1_of`, `hW_D1'p`, `hW3_1` are stated for every `Y₀ ≥ 0` or every profile `Yp`). -/

/-- The survivor budget as a factor of `Y`. -/
theorem WPot_g1E (hL : 0 < L) (Y : ℝ) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀) (h : HSt V D₀) :
    WPot L γ η Y (g1E γ η crit Fmax E) h = WPot L γ η (Y * L ^ (pendRC E h : ℝ)) (g1 γ η crit Fmax) h := by
  have e : Y * L ^ (-(g1 γ η crit Fmax h - (pendRC E h : ℝ))) = Y * L ^ (pendRC E h : ℝ) * L ^ (-g1 γ η crit Fmax h) := by
    rw [mul_assoc, ← Real.rpow_add hL]; congr 2; ring
  show ENNReal.ofReal (potR L γ η (Y * L ^ (-(g1 γ η crit Fmax h - (pendRC E h : ℝ)))) h) =
    ENNReal.ofReal (potR L γ η (Y * L ^ (pendRC E h : ℝ) * L ^ (-g1 γ η crit Fmax h)) h)
  rw [e]

/-- `WPot` is monotone in its constant. -/
theorem WPot_mono_Y (hL : 0 < L) {Y Y' : ℝ} (hYY : Y ≤ Y') (g : HSt V D₀ → ℝ) {h : HSt V D₀}
    (hap : 0 < apProd L γ η h.s) : WPot L γ η Y g h ≤ WPot L γ η Y' g h := by
  unfold WPot potR
  refine ENNReal.ofReal_le_ofReal ?_
  apply div_le_div_of_nonneg_right _ hap.le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right hYY (by positivity)

/-- **Main's phase-1 step inequalities hold for `g1E`** when the step creates no pending re-cut: apply main's
inequality with the constant `Y·L^{pendRC h}`. -/
theorem g1E_lift (hL1 : 1 ≤ L) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀) {h h' : HSt V D₀}
    {Y Y' c : ℝ} (hY' : 0 ≤ Y') (hap' : 0 < apProd L γ η h'.s) (hpend : pendRC E h' ≤ pendRC E h) (N : ℕ)
    (hstep : (N : ℝ≥0∞) * (ENNReal.ofReal c * WPot L γ η (Y' * L ^ (pendRC E h : ℝ)) (g1 γ η crit Fmax) h') ≤
      WPot L γ η (Y * L ^ (pendRC E h : ℝ)) (g1 γ η crit Fmax) h) :
    (N : ℝ≥0∞) * (ENNReal.ofReal c * WPot L γ η Y' (g1E γ η crit Fmax E) h') ≤
      WPot L γ η Y (g1E γ η crit Fmax E) h := by
  have hL : 0 < L := by linarith
  rw [WPot_g1E hL, WPot_g1E hL]
  refine le_trans ?_ hstep
  have hp : L ^ (pendRC E h' : ℝ) ≤ L ^ (pendRC E h : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by exact_mod_cast hpend)
  have hmono := WPot_mono_Y (L := L) (γ := γ) (η := η) hL
    (mul_le_mul_of_nonneg_left hp hY') (g1 γ η crit Fmax) hap'
  gcongr

/-- At the end of Step 1 (no pending re-cut), the budget is main's potential. -/
theorem WPot_g1E_of_pend_zero (Y : ℝ) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀) {h : HSt V D₀}
    (h0 : pendRC E h = 0) : WPot L γ η Y (g1E γ η crit Fmax E) h = WPot L γ η Y (g1 γ η crit Fmax) h := by
  unfold WPot g1E
  rw [h0]; simp

/-- The initial cost of the budget: `W(Y, g1E) ≤ W(Y·L^m, g1)`. -/
theorem WPot_g1E_le (hL1 : 1 ≤ L) {Y : ℝ} (hY : 0 ≤ Y) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀)
    {h : HSt V D₀} (hap : 0 < apProd L γ η h.s) :
    WPot L γ η Y (g1E γ η crit Fmax E) h ≤ WPot L γ η (Y * L ^ (m : ℝ)) (g1 γ η crit Fmax) h := by
  have hL : 0 < L := by linarith
  rw [WPot_g1E hL]
  have hle : pendRC E h ≤ m := by
    unfold pendRC
    exact (Finset.card_filter_le _ _).trans (by simp)
  exact WPot_mono_Y hL
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by exact_mod_cast hle)) hY) _ hap

end hWRC

end WaveTurbulence.Flower.FinalMKStep
