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

/-- The `Y₀` factor of the REG chain with the index as a variable. -/
noncomputable def Y0f (L γ η ε0 : ℝ) (R : ℕ) : ℝ :=
  L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R - 1 : ℕ) : ℝ) - ε0)

theorem Y0f_nonneg {L : ℝ} (hL : 0 ≤ L) (γ η ε0 : ℝ) (R : ℕ) : 0 ≤ Y0f L γ η ε0 R := by
  unfold Y0f; exact Real.rpow_nonneg hL _

/-- `Y0f` at an index `R ≥ 1` is the `Y₀` of `reg_class_bound`. -/
theorem Y0f_eq {L γ η ε0 : ℝ} {R : ℕ} (hR : 1 ≤ R) :
    Y0f L γ η ε0 R = L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - ε0) := by
  unfold Y0f
  congr 2
  rw [Nat.cast_sub hR]; simp

/-- Dropping the index by `j` divides `Y0f` by at least `L^{a j}`, `a = eraseA`. -/
theorem Y0f_drop {L γ η ε0 : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η) {R R' j : ℕ} (hj : R' + j = R) :
    Y0f L γ η ε0 R' * L ^ (eraseA γ η * (j : ℝ)) ≤ Y0f L γ η ε0 R := by
  unfold Y0f
  have hL0 : 0 < L := by linarith
  rw [← Real.rpow_add hL0]
  apply Real.rpow_le_rpow_of_exponent_le hL
  have h1 : ((R' - 1 : ℕ) : ℝ) ≤ ((R - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : R' - 1 ≤ R - 1)
  have h2 : (R : ℝ) = R' + j := by rw [← hj]; push_cast; ring
  rw [h2]
  nlinarith

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

/-- **LC-1: the potential inequality of Step D3** (index drop `1`, literal constant `excessRHS [] 1 2 = L^{-η³+η²}`, true increments
`ΔF = 0`, `Δ V_β = 1`; paper check 1 of PROGRESS-LOWCHAIN.md, margin `γ₀ + 2η²`). -/
theorem hW_D3 (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hγ0 : 0 ≤ min γ (1 - γ)) (ε0 : ℝ) (crit : V → Prop) {h : HSt V D₀} {v : V}
    {x₁ x₂ : h.s.D} {R : ℕ} (hg : Good R h.s) (hD : D3Data h v x₁ x₂) (hap : ApPos h.s) (N : ℕ)
    (hN : (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6)) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (excessRHS L γ η [] 1 2) *
      WPot L γ η (Y0f L γ η ε0 (RofS (h.betaPost v x₁ x₂).s)) (gExp η crit) (h.betaPost v x₁ x₂)) ≤
      WPot L γ η (Y0f L γ η ε0 (RofS h.s)) (gExp η crit) h := by
  have hL : 0 < L := by linarith
  obtain ⟨hR1, hg'⟩ := hg.betaSt hD.hv hD.hε hD.hd
  have hRs : RofS h.s = R := rofS_of_inv hg.1
  have hRs' : RofS (h.betaPost v x₁ x₂).s = R - 1 := rofS_of_inv hg'.1
  have hs : (h.betaPost v x₁ x₂).s = h.s.betaSt v := rfl
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hex : excessRHS L γ η [] 1 2 = L ^ (-η ^ 3 + η ^ 2) := excessRHS_beta L γ η hL
  have hdrop := Y0f_drop (L := L) (γ := γ) (η := η) (ε0 := ε0) hL1 hη (R := R) (R' := R - 1) (j := 1) (by omega)
  rw [hRs, hRs']
  have hgd := gExp_drop hη crit (h := h) (h' := h.betaPost v x₁ x₂) (a := 0) (b := 1) (by rw [hs]; show h.s.M.rho ≤ h.s.M.rho + 0; omega)
    (by rw [hs]; exact critCount_betaSt crit h.s v)
  refine pot_step_idx hL1 hAp (by rw [hs]; exact apProd_betaSt L γ η h.s hD.hε) hγ0 (A := eraseA γ η) (j := 1)
    (Y0f_nonneg hL.le _ _ _ _) (by simpa using hdrop) (g := gExp η crit) (δg := 4 * η ^ 6 * (((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)))
    (by linarith) 0 1 (by rw [hs]; show (h.s.M.numComponents : ℝ) + 0 ≤ ((h.s.M.numComponents : ℕ) : ℝ); simp) (by rw [hs, vBeta_betaSt _ hD.hv hD.hε]; push_cast; exact le_of_eq (by ring))
    (by rw [hex]; positivity) N (x := η ^ 2 - 4 * η ^ 6) ?_ ?_
  · rw [hex]
    calc (N : ℝ) * L ^ (-η ^ 3 + η ^ 2) ≤ L ^ (η ^ 3 - 4 * η ^ 6) * L ^ (-η ^ 3 + η ^ 2) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = L ^ (η ^ 2 - 4 * η ^ 6) := by rw [← Real.rpow_add hL]; congr 1; ring
  · unfold eraseA gam0
    simp only [Nat.cast_zero, Nat.cast_one]
    nlinarith [pow_nonneg hη 2, pow_nonneg hη 6]

end D3

section D1
variable {L γ η : ℝ}

/-- **LC-1: the potential inequality of Step D1** (an object with `j = jdeg2 K ∈ {1,2}` joints of degree `2`; index drop `j`; literal
constant `CN · excessRHS2 [] 1 2` of `UStepD1.excess_new`; phase-1 potential `g₁`).  The true increments after deleting the isolated halves
are `ΔF ≥ 1 - j` and `ΔV_β ≤ 2 - j` (hypotheses `hF`, `hV`, proved in LC-2 from `vineStG`); paper check 1 of PROGRESS-LOWCHAIN.md. -/
theorem hW_D1 (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (ε0 : ℝ) (crit : V → Prop) (Fmax : ℝ)
    {h h' : HSt V D₀} {R R' : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 2) (hRR : R' + j = R) (hI : Inv R h.s) (hI' : Inv R' h'.s)
    (hap : ApPos h.s) (hApe : apProd L γ η h'.s = apProd L γ η h.s)
    (hF : (h.s.M.numComponents : ℝ) + 1 - j ≤ h'.s.M.numComponents) (hV : (vBeta h'.s : ℝ) ≤ vBeta h.s + 2 - j)
    (hρ : h.s.M.rho ≤ h'.s.M.rho + 88) (hcr : critCount crit h.s ≤ critCount crit h'.s + 2) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Y0f L γ η ε0 (RofS h'.s)) (g1 γ η crit Fmax) h') ≤
      WPot L γ η (Y0f L γ η ε0 (RofS h.s)) (g1 γ η crit Fmax) h := by
  have hL : 0 < L := by linarith
  have hRs : RofS h.s = R := rofS_of_inv hI
  have hRs' : RofS h'.s = R' := rofS_of_inv hI'
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hdrop := Y0f_drop (L := L) (γ := γ) (η := η) (ε0 := ε0) hL1 hη (R := R) (R' := R') (j := j) hRR
  have hex : excessRHS2 L γ η [] 1 2 = L ^ min γ (1 - γ) * L ^ (-η ^ 3 + η ^ 2) := by
    rw [excessRHS2_eq _ _ _ _ _ _ hL, excessRHS_beta L γ η hL]
  have hgd := gExp_drop hη crit (h := h) (h' := h') (a := 88) (b := 2) hρ hcr
  have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hj2' : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
  rw [hRs, hRs']
  have hpow : 0 ≤ η ^ 6 := by positivity
  refine pot_step_idx hL1 hAp hApe hγ0 (A := eraseA γ η) (j := (j : ℝ)) (Y0f_nonneg hL.le _ _ _ _) hdrop
    (g := g1 γ η crit Fmax) (δg := 4 * η ^ 6 * (((88 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) - min γ (1 - γ) * (1 - j)) ?_ (1 - j) (2 - j)
    (by linarith) (by linarith) (by rw [hex]; positivity) N
    (x := (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) + min γ (1 - γ) + (-η ^ 3 + η ^ 2)) ?_ ?_
  · unfold g1
    have : (h.s.M.numComponents : ℝ) + (1 - j) ≤ h'.s.M.numComponents := by linarith
    nlinarith
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
    nlinarith [pow_nonneg hη 2]

end D1

end WaveTurbulence.FinalCountAsm
