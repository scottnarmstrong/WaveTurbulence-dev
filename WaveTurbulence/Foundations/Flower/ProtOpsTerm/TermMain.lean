/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.TermNorm
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Sumint.TimeBridge

/-! # PROT-OPS-TERM: `TerminalOperatorBoundY` (o104 Lemma 7.1(1) with `r` spectator times) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtOpsTerm

theorem xnorm_eq_mixed {r d : ℕ} (θ : ℝ) (H : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ 0 0 H = mixedFourierNorm00 θ H := by
  rw [NormBridgeScratch.XNorm_zero_eq_XNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]

/-- **o104 Lemma 7.1(1)** with `r` spectators, in the pinned form of `ProtDefs`. -/
theorem terminalOperatorBoundY : ProtDefs.TerminalOperatorBoundY := by
  intro d r θ hθ0 hθ1
  obtain ⟨B0, hB0t, hB0⟩ := psi_uniform (le_refl (0 : ℝ)) zero_le_one
  obtain ⟨Bθ, hBθt, hBθ⟩ := psi_uniform hθ0 hθ1
  set C0 : ℝ≥0∞ := B0 + ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * Bθ with hC0
  have hC0t : C0 < ⊤ := ENNReal.add_lt_top.2 ⟨hB0t, ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hBθt⟩
  have hCpos : 0 < C0.toReal + 1 := by positivity
  refine ⟨C0.toReal + 1, hCpos.le, ?_⟩
  intro A H K
  by_cases hH : XNorm θ 0 0 H < ⊤
  · rw [xnorm_eq_mixed] at hH ⊢
    unfold XNormRestr
    refine (iInf₂_le (fun ts k => Gf A (fun t => H t k) ts) ?_).trans ?_
    · intro ts hts k _
      obtain ⟨h1, h2, h3⟩ := hts
      have hP : Phi (tl ts) = 1 :=
        Phi_one (h1.le.trans h2.le) h3.le h1.le (h2.le.trans h3.le)
      show Phi (tl ts) * Tf A (fun t => H t k) ts = _
      rw [hP, one_mul]
      rfl
    · rw [xnorm_eq_mixed]
      refine (term_norm_core hθ0 hB0 hBθ A H hH).trans ?_
      refine mul_le_mul_left ?_ _
      calc C0 = ENNReal.ofReal C0.toReal := (ENNReal.ofReal_toReal hC0t.ne).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  · rw [not_lt, top_le_iff] at hH
    rw [hH, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCpos).ne']
    exact le_top

end WaveTurbulence.Flower.ProtOpsTerm
