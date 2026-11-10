/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowIface
/-! **FINALCOUNT LOW-CHAIN, LC-1 (1): the index and the index-dependent potential factor.**
`RofS s` is the current index `R` of a state (`Inv R s`: `Σ base - |D| = 2R`).  `Y0f` is the REG factor `Y0` with the index a variable,
`Y0f R = L^{eraseA R + 4η (R-1)₊ - ε₀}`.  `pot_step_idx`: the per-step inequality of a step whose index drops by `j`
(the potential factor `Y0f R'` is smaller by at least `L^{a j}`), for a step constant given literally. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The current index of a state. -/
noncomputable def RofS (s : St.{u} V D₀) : ℕ := ((∑ a ∈ s.M.atoms, (s.cls a).base - (Fintype.card s.D : ℤ)) / 2).toNat

theorem rofS_of_inv {R : ℕ} {s : St.{u} V D₀} (hI : Inv R s) : RofS s = R := by
  unfold RofS
  have := hI.phi
  have h2 : ∑ a ∈ s.M.atoms, (s.cls a).base - (Fintype.card s.D : ℤ) = 2 * (R : ℤ) := by linarith
  rw [h2]; omega

/-- **The per-step inequality of a step with an index drop and a literal constant.**  `Ilit` is the literal step constant; `dF`, `dV` are
the true increments of the number of components and of the number of `β`-atoms, `apProd` is unchanged; `Y' L^{A j} ≤ Y` is the index
drop; the numerical hypothesis `hx` is the paper check of PROGRESS-LOWCHAIN.md. -/
theorem pot_step_idx {L γ η : ℝ} (hL1 : 1 ≤ L) {h h' : HSt V D₀} (hAp : 0 < apProd L γ η h.s)
    (hApe : apProd L γ η h'.s = apProd L γ η h.s) (hγ0 : 0 ≤ min γ (1 - γ)) {Y Y' A j : ℝ} (hY' : 0 ≤ Y')
    (hYY : Y' * L ^ (A * j) ≤ Y) {g : HSt V D₀ → ℝ} {δg : ℝ} (hg : g h - δg ≤ g h') (dF dV : ℝ)
    (hF : (h.s.M.numComponents : ℝ) + dF ≤ h'.s.M.numComponents) (hV : (vBeta h'.s : ℝ) ≤ vBeta h.s + dV)
    {Ilit : ℝ} (hI : 0 ≤ Ilit) (N : ℕ) {x : ℝ} (hNI : (N : ℝ) * Ilit ≤ L ^ x)
    (hx : x + δg + (-(2 * min γ (1 - γ) + 5 * η ^ 2) * dF + (min γ (1 - γ) + 2 * η ^ 2) * dV) - A * j ≤ 0) :
    (N : ℝ≥0∞) * (ENNReal.ofReal Ilit * WPot L γ η Y' g h') ≤ WPot L γ η Y g h := by
  have hL : 0 < L := by linarith
  unfold WPot potR
  rw [← ENNReal.ofReal_mul hI, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hApe]
  set a := 2 * min γ (1 - γ) + 5 * η ^ 2 with ha
  set b := min γ (1 - γ) + 2 * η ^ 2 with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hE : L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)) ≤
      L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) * L ^ (-a * dF + b * dV) := by
    rw [← Real.rpow_add hL]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    nlinarith
  have h1 : L ^ (-g h') ≤ L ^ (-g h) * L ^ δg := by
    rw [← Real.rpow_add hL]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hYpos : 0 ≤ Y := le_trans (by positivity) hYY
  have hP : 0 ≤ L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) := by positivity
  have h2 : L ^ x * L ^ δg * L ^ (-a * dF + b * dV) ≤ L ^ (A * j) := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hpos1 : 0 ≤ L ^ (-g h) := by positivity
  have hpos2 : 0 ≤ L ^ δg := by positivity
  have hpos3 : 0 ≤ L ^ (-a * dF + b * dV) := by positivity
  have hpos4 : 0 ≤ L ^ x := by positivity
  rw [show (N : ℝ) * (Ilit * (Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)) / apProd L γ η h.s)) =
      ((N : ℝ) * Ilit) * (Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ))) / apProd L γ η h.s by ring]
  rw [div_le_div_iff_of_pos_right hAp]
  calc (N : ℝ) * Ilit * (Y' * L ^ (-g h') * L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)))
      ≤ (N : ℝ) * Ilit * (Y' * L ^ (-g h') * (L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) * L ^ (-a * dF + b * dV))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ L ^ x * (Y' * (L ^ (-g h) * L ^ δg) * (L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) *
          L ^ (-a * dF + b * dV))) := by
        apply mul_le_mul hNI _ (by positivity) hpos4
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h1 hY'
    _ = (Y' * (L ^ x * L ^ δg * L ^ (-a * dF + b * dV))) * (L ^ (-g h) * L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ))) := by
        ring
    _ ≤ (Y' * L ^ (A * j)) * (L ^ (-g h) * L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hY'
    _ ≤ Y * (L ^ (-g h) * L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ))) := by
        apply mul_le_mul_of_nonneg_right hYY (by positivity)
    _ = _ := by ring

section D3
variable {L γ η : ℝ}

theorem vBeta_betaSt (s : St.{u} V D₀) {v : V} (hv : v ∈ s.M.atoms) (hε : s.cls v = .eps) :
    vBeta (s.betaSt v) = vBeta s + 1 := by
  unfold vBeta
  have : (s.betaSt v).M.atoms.filter (fun a => (s.betaSt v).cls a = .beta) =
      insert v (s.M.atoms.filter (fun a => s.cls a = .beta)) := by
    ext a
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
    by_cases e : a = v
    · subst e; simp [hv, St.betaSt_cls, St.betaSt_M]
    · simp [e, St.betaSt_cls, St.betaSt_M, Function.update_of_ne e]
  rw [this, Finset.card_insert_of_notMem]
  simp [hε]

theorem apProd_betaSt (L γ η : ℝ) (s : St.{u} V D₀) {v : V} (hε : s.cls v = .eps) :
    apProd L γ η (s.betaSt v) = apProd L γ η s := by
  unfold apProd
  refine Finset.prod_congr rfl fun a ha => ?_
  by_cases e : a = v
  · subst e; simp [St.betaSt_cls, hε, apFactor]
  · simp [St.betaSt_cls, Function.update_of_ne e]

theorem apPos_betaSt {s : St.{u} V D₀} (hap : ApPos s) (v : V) : ApPos (s.betaSt v) := by
  intro a ha R kp hc
  by_cases e : a = v
  · subst e; simp [St.betaSt_cls] at hc
  · rw [St.betaSt_cls, Function.update_of_ne e] at hc
    exact hap a ha R kp hc

theorem critCount_betaSt (crit : V → Prop) (s : St.{u} V D₀) (v : V) :
    critCount crit s ≤ critCount crit (s.betaSt v) + 1 := by
  unfold critCount
  have hsub : (s.M.atoms.filter fun a => s.cls a = .eps ∧ crit a).erase v ⊆
      (s.betaSt v).M.atoms.filter fun a => (s.betaSt v).cls a = .eps ∧ crit a := by
    intro a ha
    obtain ⟨hav, ha'⟩ := Finset.mem_erase.1 ha
    obtain ⟨ham, hε, hcr⟩ := Finset.mem_filter.1 ha'
    refine Finset.mem_filter.2 ⟨ham, ?_, hcr⟩
    rw [St.betaSt_cls, Function.update_of_ne hav]; exact hε
  have := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := s.M.atoms.filter fun a => s.cls a = .eps ∧ crit a) (a := v)
  omega

end D3

section D1
variable {L γ η : ℝ}

end D1

end WaveTurbulence.FinalCountAsm
