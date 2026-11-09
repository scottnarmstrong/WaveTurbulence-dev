/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Flower.FinalMKStep.Pot

/-! # FLOWER-LOW (packet L8), item H (re-cut ledger): the survivor budget banks `L²` per pending re-cut

Main's re-cut step `FinalMKStep.hW_RCp` (o75 75-F2 on main's potential model) takes
`hmarg : 2·min γ (1−γ) + 4η² ≤ 1`, which is false at `γ = 1/2` for every `η > 0` (M3 §7.2; REF-M3 R3; AUDIT-V4 §7
watch item 1). Main banks `L¹` per pending re-cut (`g1E = g1 − pendRC`). Following M3 §7.2 as repaired by REF-M3 R3,
this module banks `L²` per pending re-cut:

  `g1E2 = g1 − 2·pendRCG`,

so the re-cut step gains `L²`, and its margin is `2γ₀ + 3η² + 8η⁶ + ε₀ − 2 ≤ 0`, which holds for every `γ ∈ (0,1)`
(`γ₀ = min γ (1−γ) ≤ 1/2`) once `η ≤ 1/40` and `ε₀ ≤ η²/2`: **`hW_RCp2` has no hypothesis on `γ`**. The initial cost
of the budget is `L^{2·pendRC₀} ≤ L^{2m}` (`WPot_g1E2_le`) instead of `L^{m}`; with `m = N_E ≤ 2b` the total survivor
charge is `L^{(2+γ₀)N_E} ≤ L^{5b}` (REF-M3 R3), absorbed by (10.4).

The survivors are over `𝒱_γ` (`Src.Object γ`, L6's carrier): `DartlessG`, `pendRCG` are main's `Dartless`
(`FinalCount/AsmPhase1.lean`) and `pendRC` (`Flower/FinalMKDefs/Count.lean`) with that carrier. Everything else
(`HSt`, `WPot`, `g1`, `apProd`, `Inv`, `eraseA`, `excessRHS2`, `pot_step_idx_le`, `WPot_mono_Y`) is main's and
family-free, by import. The proofs are main's (`FinalMKStep/Pot.lean`, sha256 in `COPIED-SHA256SUMS`) with the bank
changed from `1` to `2`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal

namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKStep

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- No dart of the `𝒱_γ` object `U` of `M₀` remains in the state `h` (main's `FinalCountAsm.Dartless`). -/
def DartlessG {γ : ℝ} {M₀ : Molecule V D₀} (U : FinalCount.Src.Object γ M₀) (h : HSt V D₀) : Prop :=
  ∀ x : h.s.D, ¬ U.ContainsDart (h.s.down x)

section hWRC
variable {γ L γ' η : ℝ} {M₀ : Molecule V D₀} {m : ℕ}

/-- The pending re-cuts of a state: survivors still present that share a joint with an earlier survivor (main's
`FinalMKDefs.pendRC` over `𝒱_γ`). -/
noncomputable def pendRCG (E : Fin m → FinalCount.Src.Object γ M₀) (h : HSt V D₀) : ℕ :=
  (Finset.univ.filter fun i : Fin m => ¬ DartlessG (E i) h ∧ ∃ j, j < i ∧ ¬ Disjoint (E j).atoms (E i).atoms).card

/-- **The survivor-budget exponent with the `L²` bank** (M3 §7.2, REF-M3 R3): main's `g1` minus two units per pending
re-cut. `WPot … (g1E2 …)` gains `L²` at each re-cut; initially it costs `L^{2·pendRC} ≤ L^{2m}`. -/
noncomputable def g1E2 (γ' η : ℝ) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → FinalCount.Src.Object γ M₀)
    (h : HSt V D₀) : ℝ :=
  g1 γ' η crit Fmax h - 2 * (pendRCG E h : ℝ)

/-- The re-cut margin with the `L²` bank, for every `γ'` (`γ₀ ≤ 1/2`). -/
theorem two_gam0_le_one (γ' : ℝ) : 2 * min γ' (1 - γ') ≤ 1 := by
  have h1 := min_le_left γ' (1 - γ')
  have h2 := min_le_right γ' (1 - γ')
  linarith

/-- The survivor budget changes the exponent by twice the drop of `pendRCG`. -/
theorem g1E2_step (crit : V → Prop) (Fmax : ℝ) (E : Fin m → FinalCount.Src.Object γ M₀) {h h' : HSt V D₀}
    {δ : ℝ} (hg : g1 γ' η crit Fmax h - δ ≤ g1 γ' η crit Fmax h') (hpend : pendRCG E h' + 1 ≤ pendRCG E h) :
    g1E2 γ' η crit Fmax E h - (δ - 2) ≤ g1E2 γ' η crit Fmax E h' := by
  unfold g1E2
  have : (pendRCG E h' : ℝ) + 1 ≤ pendRCG E h := by exact_mod_cast hpend
  linarith

/-- **C1a with the `L²` bank: the potential inequality of the re-cut step** (main's `hW_RCp` with `g1E2` in place of
`g1E`, and WITHOUT `hmarg`: the margin `2γ₀ + 3η² + 8η⁶ + ε₀ − 2 ≤ 0` holds for every `γ'`). Increments as main's:
index drop `j`, `ΔF ≥ -j`, `ΔV_β ≤ 1 - j`, `apProd` not decreasing, `ρ` and the critical count as in `hW_D1p`, one
pending re-cut paid (`hpend`). -/
theorem hW_RCp2 (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ' (1 - γ'))
    (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ' η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (crit : V → Prop) (Fmax : ℝ) (E : Fin m → FinalCount.Src.Object γ M₀)
    {h h' : HSt V D₀} {R R' j : ℕ} (hRR : R' + j = R) (hI : Inv R h.s) (hI' : Inv R' h'.s)
    (hap : ApPos h.s) (hApe : apProd L γ' η h.s ≤ apProd L γ' η h'.s)
    (hF : (h.s.M.numComponents : ℝ) - j ≤ h'.s.M.numComponents) (hV : (vBeta h'.s : ℝ) + j ≤ vBeta h.s + 1)
    (hρ : h.s.M.rho ≤ h'.s.M.rho + 88) (hcr : critCount crit h.s ≤ critCount crit h'.s + 2)
    (hpend : pendRCG E h' + 1 ≤ pendRCG E h) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ' η [] 1 2) *
      WPot L γ' η (Yp (RofS h'.s)) (g1E2 γ' η crit Fmax E) h') ≤
      WPot L γ' η (Yp (RofS h.s)) (g1E2 γ' η crit Fmax E) h := by
  have hL : 0 < L := by linarith
  have hRs : RofS h.s = R := rofS_of_inv hI
  have hRs' : RofS h'.s = R' := rofS_of_inv hI'
  have hAp := apProd_pos (L := L) (γ := γ') (η := η) hL hap
  have hdrop := hYpd R R' j hRR
  have hex : excessRHS2 L γ' η [] 1 2 = L ^ min γ' (1 - γ') * L ^ (-η ^ 3 + η ^ 2) := by
    rw [excessRHS2_eq _ _ _ _ _ _ hL, excessRHS_beta L γ' η hL]
  have hgd := gExp_drop hη crit (h := h) (h' := h') (a := 88) (b := 2) hρ hcr
  have hg1 : g1 γ' η crit Fmax h - (4 * η ^ 6 * (((88 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) + min γ' (1 - γ') * (j : ℝ)) ≤
      g1 γ' η crit Fmax h' := by
    unfold g1
    nlinarith [mul_nonneg hγ0 (show (0 : ℝ) ≤ (h'.s.M.numComponents : ℝ) - ((h.s.M.numComponents : ℝ) - j) by linarith)]
  have hgE := g1E2_step crit Fmax E hg1 hpend
  rw [hRs, hRs']
  have hpow : 0 ≤ η ^ 6 := by positivity
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hmarg2 := two_gam0_le_one γ'
  refine pot_step_idx_le hL1 hAp hApe hγ0 (A := eraseA γ' η * (j : ℝ) - ε0) (j := 1) (hYp0 _)
    (by simpa using hdrop) (g := g1E2 γ' η crit Fmax E) hgE (-(j : ℝ)) (1 - j) (by linarith) (by linarith)
    (by rw [hex]; positivity) N
    (x := (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) + min γ' (1 - γ') + (-η ^ 3 + η ^ 2)) ?_ ?_
  · rw [hex]
    calc (N : ℝ) * (CN * (L ^ min γ' (1 - γ') * L ^ (-η ^ 3 + η ^ 2)))
        = ((N : ℝ) * CN) * (L ^ min γ' (1 - γ') * L ^ (-η ^ 3 + η ^ 2)) := by ring
      _ ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) *
            (L ^ min γ' (1 - γ') * L ^ (-η ^ 3 + η ^ 2)) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by rw [← Real.rpow_add hL, ← Real.rpow_add hL]; congr 1; ring
  · unfold eraseA gam0
    push_cast
    have h4 : η ^ 6 ≤ η ^ 2 / 4096 := by
      have : η ^ 4 ≤ (1 / 40) ^ 4 := pow_le_pow_left₀ hη hη40 4
      have e : η ^ 6 = η ^ 2 * η ^ 4 := by ring
      rw [e]; nlinarith [pow_nonneg hη 2]
    have h2 : η ^ 2 ≤ 1 / 1600 := by nlinarith
    nlinarith [pow_nonneg hη 2, mul_nonneg (pow_nonneg hη 2) hj0]

/-! ### Lifting main's phase-1 steps to the `L²` survivor budget -/

/-- The survivor budget as a factor of `Y`: `W(Y, g1E2) = W(Y·L^{2·pendRC}, g1)`. -/
theorem WPot_g1E2 (hL : 0 < L) (Y : ℝ) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → FinalCount.Src.Object γ M₀)
    (h : HSt V D₀) :
    WPot L γ' η Y (g1E2 γ' η crit Fmax E) h =
      WPot L γ' η (Y * L ^ (2 * (pendRCG E h : ℝ))) (g1 γ' η crit Fmax) h := by
  have e : Y * L ^ (-(g1 γ' η crit Fmax h - 2 * (pendRCG E h : ℝ))) =
      Y * L ^ (2 * (pendRCG E h : ℝ)) * L ^ (-g1 γ' η crit Fmax h) := by
    rw [mul_assoc, ← Real.rpow_add hL]; congr 2; ring
  show ENNReal.ofReal (potR L γ' η (Y * L ^ (-(g1 γ' η crit Fmax h - 2 * (pendRCG E h : ℝ)))) h) =
    ENNReal.ofReal (potR L γ' η (Y * L ^ (2 * (pendRCG E h : ℝ)) * L ^ (-g1 γ' η crit Fmax h)) h)
  rw [e]

/-- **Main's phase-1 step inequalities hold for `g1E2`** when the step creates no pending re-cut: apply main's
inequality with the constant `Y·L^{2·pendRC h}`. -/
theorem g1E2_lift (hL1 : 1 ≤ L) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → FinalCount.Src.Object γ M₀)
    {h h' : HSt V D₀} {Y Y' c : ℝ} (hY' : 0 ≤ Y') (hap' : 0 < apProd L γ' η h'.s)
    (hpend : pendRCG E h' ≤ pendRCG E h) (N : ℕ)
    (hstep : (N : ℝ≥0∞) * (ENNReal.ofReal c *
        WPot L γ' η (Y' * L ^ (2 * (pendRCG E h : ℝ))) (g1 γ' η crit Fmax) h') ≤
      WPot L γ' η (Y * L ^ (2 * (pendRCG E h : ℝ))) (g1 γ' η crit Fmax) h) :
    (N : ℝ≥0∞) * (ENNReal.ofReal c * WPot L γ' η Y' (g1E2 γ' η crit Fmax E) h') ≤
      WPot L γ' η Y (g1E2 γ' η crit Fmax E) h := by
  have hL : 0 < L := by linarith
  rw [WPot_g1E2 hL, WPot_g1E2 hL]
  refine le_trans ?_ hstep
  have hpR : (pendRCG E h' : ℝ) ≤ pendRCG E h := by exact_mod_cast hpend
  have hp : L ^ (2 * (pendRCG E h' : ℝ)) ≤ L ^ (2 * (pendRCG E h : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hmono := WPot_mono_Y (L := L) (γ := γ') (η := η) hL
    (mul_le_mul_of_nonneg_left hp hY') (g1 γ' η crit Fmax) hap'
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono bot_le) bot_le

/-- At the end of Step 1 (no pending re-cut), the budget is main's potential. -/
theorem WPot_g1E2_of_pend_zero (Y : ℝ) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → FinalCount.Src.Object γ M₀)
    {h : HSt V D₀} (h0 : pendRCG E h = 0) :
    WPot L γ' η Y (g1E2 γ' η crit Fmax E) h = WPot L γ' η Y (g1 γ' η crit Fmax) h := by
  unfold WPot g1E2
  rw [h0]; simp

/-- **The initial cost of the `L²` budget**: `W(Y, g1E2) ≤ W(Y·L^{2m}, g1)` (REF-M3 R3: the survivor charge becomes
`L^{(2+γ₀)N_E}`). -/
theorem WPot_g1E2_le (hL1 : 1 ≤ L) {Y : ℝ} (hY : 0 ≤ Y) (crit : V → Prop) (Fmax : ℝ)
    (E : Fin m → FinalCount.Src.Object γ M₀) {h : HSt V D₀} (hap : 0 < apProd L γ' η h.s) :
    WPot L γ' η Y (g1E2 γ' η crit Fmax E) h ≤ WPot L γ' η (Y * L ^ (2 * (m : ℝ))) (g1 γ' η crit Fmax) h := by
  have hL : 0 < L := by linarith
  rw [WPot_g1E2 hL]
  have hle : pendRCG E h ≤ m := by
    unfold pendRCG
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hle' : 2 * (pendRCG E h : ℝ) ≤ 2 * (m : ℝ) := by
    have : (pendRCG E h : ℝ) ≤ m := by exact_mod_cast hle
    linarith
  exact WPot_mono_Y hL
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hle') hY) _ hap

end hWRC

end WaveTurbulence.GammaLow.Flower
