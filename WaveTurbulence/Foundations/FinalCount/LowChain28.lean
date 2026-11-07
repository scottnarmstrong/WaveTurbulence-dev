/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain27
/-! **FINALCOUNT LOW-CHAIN, session 6 (R79), LC-B (2): the per-step potential inequalities for a general index profile `Yp : ℕ → ℝ`.**
`hW_D3p`, `hW_D1p`, `hW_D1'p` are `hW_D3`, `hW_D1`, `hW_D1'` (LowChain1, 2) with `Y0f L γ η ε0` replaced by a function `Yp` satisfying the
drop inequality `Yp R' · L^{a j - ε₀} ≤ Yp R` for `R' + j = R` (the corrected potential of R79 has this form, see `Yz_drop`); the margins have
room for `ε₀ ≤ η²/2` (D3: `γ₀ + 2η²`, D1: `2jη² - 8η⁶`). -/
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

section D3p
variable {L γ η : ℝ}

/-- **LC-1: the potential inequality of Step D3** (index drop `1`, literal constant `excessRHS [] 1 2 = L^{-η³+η²}`, true increments
`ΔF = 0`, `Δ V_β = 1`; paper check 1 of PROGRESS-LOWCHAIN.md, margin `γ₀ + 2η²`). -/
theorem hW_D3p (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hγ0 : 0 ≤ min γ (1 - γ)) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2) (crit : V → Prop) {h : HSt V D₀} {v : V}
    {x₁ x₂ : h.s.D} {R : ℕ} (hg : Good R h.s) (hD : D3Data h v x₁ x₂) (hap : ApPos h.s) (N : ℕ)
    (hN : (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6)) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (excessRHS L γ η [] 1 2) *
      WPot L γ η (Yp (RofS (h.betaPost v x₁ x₂).s)) (gExp η crit) (h.betaPost v x₁ x₂)) ≤
      WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
  have hL : 0 < L := by linarith
  obtain ⟨hR1, hg'⟩ := hg.betaSt hD.hv hD.hε hD.hd
  have hRs : RofS h.s = R := rofS_of_inv hg.1
  have hRs' : RofS (h.betaPost v x₁ x₂).s = R - 1 := rofS_of_inv hg'.1
  have hs : (h.betaPost v x₁ x₂).s = h.s.betaSt v := rfl
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hex : excessRHS L γ η [] 1 2 = L ^ (-η ^ 3 + η ^ 2) := excessRHS_beta L γ η hL
  have hdrop := hYpd R (R - 1) 1 (by omega)
  rw [hRs, hRs']
  have hgd := gExp_drop hη crit (h := h) (h' := h.betaPost v x₁ x₂) (a := 0) (b := 1) (by rw [hs]; show h.s.M.rho ≤ h.s.M.rho + 0; omega)
    (by rw [hs]; exact critCount_betaSt crit h.s v)
  refine pot_step_idx hL1 hAp (by rw [hs]; exact apProd_betaSt L γ η h.s hD.hε) hγ0 (A := eraseA γ η - ε0) (j := 1)
    (hYp0 _) (by simpa using hdrop) (g := gExp η crit) (δg := 4 * η ^ 6 * (((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)))
    (by linarith) 0 1 (by rw [hs]; show (h.s.M.numComponents : ℝ) + 0 ≤ ((h.s.M.numComponents : ℕ) : ℝ); simp) (by rw [hs, vBeta_betaSt _ hD.hv hD.hε]; push_cast; exact le_of_eq (by ring))
    (by rw [hex]; positivity) N (x := η ^ 2 - 4 * η ^ 6) ?_ ?_
  · rw [hex]
    calc (N : ℝ) * L ^ (-η ^ 3 + η ^ 2) ≤ L ^ (η ^ 3 - 4 * η ^ 6) * L ^ (-η ^ 3 + η ^ 2) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = L ^ (η ^ 2 - 4 * η ^ 6) := by rw [← Real.rpow_add hL]; congr 1; ring
  · unfold eraseA gam0
    simp only [Nat.cast_zero, Nat.cast_one]
    nlinarith [pow_nonneg hη 2, pow_nonneg hη 6]


end D3p

section D1p
variable {L γ η : ℝ}

/-- **LC-1: the potential inequality of Step D1** (an object with `j = jdeg2 K ∈ {1,2}` joints of degree `2`; index drop `j`; literal
constant `CN · excessRHS2 [] 1 2` of `UStepD1.excess_new`; phase-1 potential `g₁`).  The true increments after deleting the isolated halves
are `ΔF ≥ 1 - j` and `ΔV_β ≤ 2 - j` (hypotheses `hF`, `hV`, proved in LC-2 from `vineStG`); paper check 1 of PROGRESS-LOWCHAIN.md. -/
theorem hW_D1p (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2) (crit : V → Prop) (Fmax : ℝ)
    {h h' : HSt V D₀} {R R' : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 2) (hRR : R' + j = R) (hI : Inv R h.s) (hI' : Inv R' h'.s)
    (hap : ApPos h.s) (hApe : apProd L γ η h'.s = apProd L γ η h.s)
    (hF : (h.s.M.numComponents : ℝ) + 1 - j ≤ h'.s.M.numComponents) (hV : (vBeta h'.s : ℝ) ≤ vBeta h.s + 2 - j)
    (hρ : h.s.M.rho ≤ h'.s.M.rho + 88) (hcr : critCount crit h.s ≤ critCount crit h'.s + 2) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS h'.s)) (g1 γ η crit Fmax) h') ≤
      WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
  have hL : 0 < L := by linarith
  have hRs : RofS h.s = R := rofS_of_inv hI
  have hRs' : RofS h'.s = R' := rofS_of_inv hI'
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hdrop := hYpd R R' j hRR
  have hex : excessRHS2 L γ η [] 1 2 = L ^ min γ (1 - γ) * L ^ (-η ^ 3 + η ^ 2) := by
    rw [excessRHS2_eq _ _ _ _ _ _ hL, excessRHS_beta L γ η hL]
  have hgd := gExp_drop hη crit (h := h) (h' := h') (a := 88) (b := 2) hρ hcr
  have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hj2' : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
  rw [hRs, hRs']
  have hpow : 0 ≤ η ^ 6 := by positivity
  refine pot_step_idx hL1 hAp hApe hγ0 (A := eraseA γ η * (j : ℝ) - ε0) (j := 1) (hYp0 _) (by simpa using hdrop)
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


end D1p

section hwd1p
variable {L γ η : ℝ}

/-- **LC-1: the potential inequality of Step D1 from the object data** (no assumption on the true increments: `ΔF`, `ΔV_β`, `ρ`, the
critical count and the index of `vinePostG K` are computed). -/
theorem hW_D1'p (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2) (crit : V → Prop) (Fmax : ℝ)
    {h : HSt V D₀} (K : VineCut h.s.M) {R : ℕ} (hI : Inv R h.s) (hap : ApPos h.s)
    (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
    (hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2) (hnew : h.s.M.numComponents < K.post.numComponents)
    (hrem : ∀ a ∈ K.C.atoms, h.s.cls a = .eps) (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a)
    (hM : ∀ x ∈ h.s.M.atoms, h.s.M.deg x ≤ 4)
    (hloss : ladderLoss h.s.M (h.s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS (h.vinePostG K).s)) (g1 γ η crit Fmax) (h.vinePostG K)) ≤
      WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
  have hju : 3 ≤ h.s.M.deg K.C.upper ∨ h.s.M.deg K.C.upper = 2 := by
    have := two_le_deg_upper K; omega
  have hjl : 3 ≤ h.s.M.deg K.C.lower ∨ h.s.M.deg K.C.lower = 2 := by
    have := two_le_deg_lower K; omega
  obtain ⟨R', e, hI'⟩ := hI.vineStG K hu hl hju hjl
  have hs : (h.vinePostG K).s = vineStG h.s K := rfl
  have hF1 : K.post.numComponents = h.s.M.numComponents + 1 := by
    have := vine_F_le_succ K; omega
  have hFc := numComponents_vineStG K
  have hVc := vBeta_vineStG h.s K hrem
  have hj1 := jdeg2_pos K hd2
  have hj2 := jdeg2_le K
  have hρ := rho_vineStG_le K hM hloss
  refine hW_D1p hL1 hη hη40 hγ0 ε0 Yp hYp0 hYpd hε0 crit Fmax (j := jdeg2 K) hj1 hj2 (R := R) (R' := R') e hI (by rw [hs]; exact hI') hap ?_ ?_ ?_ ?_ ?_
    hCN N hN
  · rw [hs]; exact apProd_vineStG h.s K L γ η hrem
  · rw [hs]
    have : (h.s.M.numComponents : ℝ) + 1 = (vineStG h.s K).M.numComponents + jdeg2 K := by
      have : h.s.M.numComponents + 1 = (vineStG h.s K).M.numComponents + jdeg2 K := by omega
      exact_mod_cast this
    linarith
  · rw [hs]
    have : (vBeta (vineStG h.s K) : ℝ) + jdeg2 K = vBeta h.s + 2 := by exact_mod_cast hVc
    linarith
  · rw [hs]; omega
  · rw [hs]; exact critCount_vineStG h.s K crit hint


end hwd1p

end WaveTurbulence.FinalCountAsm
