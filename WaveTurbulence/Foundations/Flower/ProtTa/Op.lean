/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.Synth
public import WaveTurbulence.Foundations.Flower.ProtTa.Statement

/-! # PROT-TA: o73 Lemma 12.1 (the consumed-modulation operator)

* `op_exists`: for `H` of finite `𝔛^{θ,0,0}` norm there is an ambient `G` agreeing with `T_A H` on the open unit
  triangle (for all `k ∈ K`) with `‖G‖ ≤ 2^θ·2^θ·B·‖H‖`, `B` the uniform bound of Prop 5.1;
* `terminalOperatorBound : TerminalOperatorBound`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtTa

variable {V : Type*}

theorem op_exists {θ : ℝ} (hθ0 : 0 ≤ θ) {B : ℝ≥0∞} (hB : ∀ z : ℝ, timeFourierNorm θ (psi z) ≤ B)
    (A : ℝ) (H : (Fin 3 → ℝ) → V → ℂ) (K : Set V) (hH : mixedFourierNorm00 θ H < ⊤) :
    ∃ G : (Fin 2 → ℝ) → V → ℂ,
      (∀ y ∈ {ts : Fin 2 → ℝ | 0 < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < 1}, ∀ k ∈ K,
        G y k = ∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
          H ![y 0, u, y 1] k) ∧
      mixedFourierNorm00 θ G ≤
        ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * B * mixedFourierNorm00 θ H := by
  classical
  have hk : ∀ k, Integrable (fun t => H t k) := integrable_of_mixedFourierNorm00_lt_top hH
  have hhat : ∀ k, Integrable (timeFourier fun t => H t k) := fun k =>
    integrable_timeFourier_of_norm_lt_top hθ0
      ((timeFourierNorm_slice_le_mixedFourierNorm00 θ H k).trans_lt hH)
  let S : Set (Fin 2 → ℝ) := {ts | 0 < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < 1}
  let G : (Fin 2 → ℝ) → V → ℂ := fun y k =>
    if y ∈ S ∧ k ∈ K then ∫ u in y 1..y 0,
      Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) * H ![y 0, u, y 1] k
    else G0 A H y k
  refine ⟨G, fun y hy k hkK => if_pos ⟨hy, hkK⟩, ?_⟩
  have hcongr : mixedFourierNorm00 θ G = mixedFourierNorm00 θ (G0 A H) := by
    refine mixedFourierNorm00_congr_ae fun k => ?_
    by_cases hkK : k ∈ K
    · filter_upwards [op_agree (hk k) (hhat k) A] with y hy
      by_cases hyS : y ∈ S
      · simp only [G, if_pos (And.intro hyS hkK)]
        rw [hy hyS.2.1]
        unfold G0
        refine integral_congr_ae (ae_of_all _ fun l => ?_)
        have hPhi : Phi y = 1 :=
          Phi_one (hyS.2.1.le.trans' hyS.1.le |>.trans' le_rfl) hyS.2.2.le hyS.1.le
            (hyS.2.1.le.trans hyS.2.2.le)
        simp only [atom_of_Phi hPhi]
      · simp only [G, if_neg (fun h : y ∈ S ∧ k ∈ K => hyS h.1)]
    · exact ae_of_all _ fun y => by simp only [G, if_neg (fun h : y ∈ S ∧ k ∈ K => hkK h.2)]
  rw [hcongr]
  exact G0_norm_le hθ0 hB hH

/-- **o73 Lemma 12.1** (the consumed terminal modulation), in the pinned form of S-MARKED §2.6. -/
theorem terminalOperatorBound : TerminalOperatorBound := by
  intro d θ hθ0 hθ1
  obtain ⟨B, hBtop, hB⟩ := psi_uniform hθ0 hθ1
  have hCpos : 0 < (2 : ℝ) ^ θ * 2 ^ θ * B.toReal + 1 := by positivity
  refine ⟨(2 : ℝ) ^ θ * 2 ^ θ * B.toReal + 1, hCpos.le, ?_⟩
  intro A H K
  by_cases hH : XNorm θ 0 0 H < ⊤
  · have hH' : mixedFourierNorm00 θ H < ⊤ := by
      rwa [NormBridgeScratch.XNorm_zero_eq_XNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00] at hH
    obtain ⟨G, hGag, hGn⟩ := op_exists hθ0 hB A H K hH'
    unfold XNormRestr
    refine (iInf₂_le G hGag).trans ?_
    rw [NormBridgeScratch.XNorm_zero_eq_XNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00,
      NormBridgeScratch.XNorm_zero_eq_XNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
    refine hGn.trans (mul_le_mul_left ?_ _)
    have hBr : B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBtop.ne).symm
    conv_lhs => rw [hBr]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [not_lt, top_le_iff] at hH
    rw [hH, ENNReal.mul_top (by simpa using hCpos)]
    exact le_top

end WaveTurbulence.Flower.ProtTa
