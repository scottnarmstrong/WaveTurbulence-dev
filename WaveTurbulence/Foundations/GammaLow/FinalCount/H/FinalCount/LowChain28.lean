/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain28
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain27
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain28`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 6 (R79), LC-B (2): the per-step potential inequalities for a general index profile `Yp : ℕ → ℝ`.**
`hW_D3p`, `hW_D1p`, `hW_D1'p` are `hW_D3`, `hW_D1`, `hW_D1'` (LowChain1, 2) with `Y0f L γ η ε0` replaced by a function `Yp` satisfying the
drop inequality `Yp R' · L^{a j - ε₀} ≤ Yp R` for `R' + j = R` (the corrected potential of R79 has this form, see `Yz_drop`); the margins have
room for `ε₀ ≤ η²/2` (D3: `γ₀ + 2η²`, D1: `2jη² - 8η⁶`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section D3p
variable {L γ η : ℝ}

end D3p

section D1p
variable {L γ η : ℝ}

end D1p

section hwd1p
variable {L γ η : ℝ}

/-- **LC-1: the potential inequality of Step D1 from the object data** (no assumption on the true increments: `ΔF`, `ΔV_β`, `ρ`, the
critical count and the index of `vinePostG K` are computed). -/
theorem hW_D1'p (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2) (crit : V → Prop) (Fmax : ℝ)
    {h : HSt V D₀} (K : Step1.VineCut Src.γL h.s.M) {R : ℕ} (hI : Inv R h.s) (hap : ApPos h.s)
    (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
    (hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2) (hnew : h.s.M.numComponents < K.post.numComponents)
    (hrem : ∀ a ∈ K.C.atoms, h.s.cls a = .eps) (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a)
    (hM : ∀ x ∈ h.s.M.atoms, h.s.M.deg x ≤ 4)
    (hloss : ladderLoss h.s.M (h.s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS (h.vinePostGL K).s)) (g1 γ η crit Fmax) (h.vinePostGL K)) ≤
      WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
  have hju : 3 ≤ h.s.M.deg K.C.upper ∨ h.s.M.deg K.C.upper = 2 := by
    have := two_le_deg_upper K; omega
  have hjl : 3 ≤ h.s.M.deg K.C.lower ∨ h.s.M.deg K.C.lower = 2 := by
    have := two_le_deg_lower K; omega
  obtain ⟨R', e, hI'⟩ := hI.vineStGL K hu hl hju hjl
  have hs : (h.vinePostGL K).s = vineStG h.s K := rfl
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

end WaveTurbulence.GammaLow.FinalCount.H
