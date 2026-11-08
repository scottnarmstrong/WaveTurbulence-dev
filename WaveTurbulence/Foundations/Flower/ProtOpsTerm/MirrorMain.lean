/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.Reflect
public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.TermMain
public import WaveTurbulence.Foundations.Flower.ProtOps.LinSynth

/-! # PROT-OPS-TERM: `MirrorOperatorBoundY` from `TerminalOperatorBoundY`

`T'_A H(t,s) = ∫_s^t e^{πiA(t-u)} H(t,u,s) du` is `T_A` of `H' = H ∘ blk R3` after `u ↦ t+s-u`, and the reflection costs
a factor `2^θ` in the `𝔛^{θ,0,0}` norm. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa Matrix
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtOpsTerm

variable {r : ℕ}

theorem tail_mulVec_R3T (x : Fin 3 → ℝ) :
    R3ᵀ *ᵥ x = ![x 0 + x 1, -x 1, x 1 + x 2] := by
  ext i; fin_cases i <;> simp [R3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem tb_blkT (l : Fin (r + 3) → ℝ) : timeBracket (blk R3ᵀ l) ≤ 2 * timeBracket l := by
  have hT := one_le_timeBracket l
  apply timeBracket_le (by linarith)
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [blk, Fin.append_left, hd]
    have := bracket_le_timeBracket l (Fin.castAdd 3 i)
    linarith
  · simp only [blk, Fin.append_right, tail_mulVec_R3T]
    have hsq : ∀ i : Fin (r + 3), 1 + l i ^ 2 ≤ timeBracket l ^ 2 := fun i => by
      have h1 := bracket_le_timeBracket l i
      have h2 := Real.sqrt_le_iff.1 h1
      exact h2.2 |>.trans (le_of_eq (by ring))
    have ha := hsq (Fin.natAdd r 0)
    have hb := hsq (Fin.natAdd r 1)
    have hc := hsq (Fin.natAdd r 2)
    refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
    fin_cases i <;> simp [tl] <;> nlinarith [sq_nonneg (l (Fin.natAdd r 0) - l (Fin.natAdd r 1)),
      sq_nonneg (l (Fin.natAdd r 1) - l (Fin.natAdd r 2))]

theorem norm_blk_le {θ : ℝ} (hθ0 : 0 ≤ θ) {V : Type*} (H : (Fin (r + 3) → ℝ) → V → ℂ) :
    mixedFourierNorm00 θ (fun z k => H (blk R3 z) k) ≤
      ENNReal.ofReal (2 ^ θ) * mixedFourierNorm00 θ H := by
  have hE := blkE_mp (r := r) R3_mul R3_det
  have hET := blkE_mp (r := r) R3T_mul R3T_det
  by_cases hk : ∀ k, Integrable (fun t => H t k)
  · have hk' : ∀ k, Integrable (fun t => H (blk R3 t) k) := fun k =>
      (hE.integrable_comp_emb (blkE (r := r) R3_mul R3_det).measurableEmbedding (g := fun t => H t k)).2 (hk k)
    rw [mixedFourierNorm00_eq_lintegral hk', mixedFourierNorm00_eq_lintegral hk]
    have henv : ∀ l, mixedFourierEnvelope00 (fun z k => H (blk R3 z) k) l =
        mixedFourierEnvelope00 H (blk R3ᵀ l) := fun l => by
      simp only [mixedFourierEnvelope00]
      exact iSup_congr fun k => by rw [timeFourier_blk (h := fun t => H t k)]
    simp_rw [henv]
    calc ∫⁻ l, timeWeight θ l * mixedFourierEnvelope00 H (blk R3ᵀ l)
        ≤ ∫⁻ l, ENNReal.ofReal (2 ^ θ) *
            (timeWeight θ (blk R3ᵀ l) * mixedFourierEnvelope00 H (blk R3ᵀ l)) := by
          refine lintegral_mono fun l => ?_
          rw [← mul_assoc]
          refine mul_le_mul_left ?_ _
          refine ProtOps.timeWeight_le_of_bracket hθ0 ?_
          have := tb_blkT (blk R3ᵀ l)
          rwa [blk_blk R3T_mul] at this
      _ = ENNReal.ofReal (2 ^ θ) * ∫⁻ l, timeWeight θ (blk R3ᵀ l) * mixedFourierEnvelope00 H (blk R3ᵀ l) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by
          congr 1
          exact hET.lintegral_comp_emb (blkE (r := r) R3T_mul R3T_det).measurableEmbedding
            (fun l => timeWeight θ l * mixedFourierEnvelope00 H l)
  · have hk2 : ¬ ∀ k, Integrable (fun t => H t k) := hk
    rw [mixedFourierNorm00_of_not_integrable hk2, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top

theorem blk_R3_append (sp : Fin r → ℝ) (t u s : ℝ) :
    blk R3 (Fin.append sp ![t, u, s]) = Fin.append sp ![t, t - u + s, s] := by
  have : R3 *ᵥ ![t, u, s] = ![t, t - u + s, s] := by
    ext i; fin_cases i <;> simp [R3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  simp only [blk, hd_append, tl_append, this]

/-- **o104 Lemma 7.1(2)** with `r` spectators, in the pinned form of `ProtDefs`. -/
theorem mirrorOperatorBoundY : ProtDefs.MirrorOperatorBoundY := by
  intro d r θ hθ0 hθ1
  obtain ⟨C, hC0, hC⟩ := terminalOperatorBoundY d r θ hθ0 hθ1
  have hpos : 0 < C * 2 ^ θ + 1 := by positivity
  refine ⟨C * 2 ^ θ + 1, hpos.le, ?_⟩
  intro A H K
  set H' : (Fin (r + 3) → ℝ) → Mom d → ℂ := fun z k => H (blk R3 z) k with hH'
  have key : (fun (ts : Fin (r + 2) → ℝ) (k : Mom d) =>
      ∫ u in ts (Fin.natAdd r 1)..ts (Fin.natAdd r 0),
        Complex.exp (((Real.pi * A * (ts (Fin.natAdd r 0) - u)) : ℝ) * Complex.I) *
          H (Fin.append (fun i : Fin r => ts (Fin.castAdd 2 i))
            ![ts (Fin.natAdd r 0), u, ts (Fin.natAdd r 1)]) k) =
      (fun (ts : Fin (r + 2) → ℝ) (k : Mom d) =>
      ∫ u in ts (Fin.natAdd r 1)..ts (Fin.natAdd r 0),
        Complex.exp (((Real.pi * A * (u - ts (Fin.natAdd r 1)) : ℝ) : ℂ) * Complex.I) *
          H' (Fin.append (fun i : Fin r => ts (Fin.castAdd 2 i))
            ![ts (Fin.natAdd r 0), u, ts (Fin.natAdd r 1)]) k) := by
    funext ts k
    set t := ts (Fin.natAdd r 0)
    set s := ts (Fin.natAdd r 1)
    set sp : Fin r → ℝ := fun i => ts (Fin.castAdd 2 i)
    have hsub := intervalIntegral.integral_comp_sub_left (a := s) (b := t)
      (fun u : ℝ => Complex.exp (((Real.pi * A * (t - u)) : ℝ) * Complex.I) *
        H (Fin.append sp ![t, u, s]) k) (t + s)
    have e1 : t + s - t = s := by ring
    have e2 : t + s - s = t := by ring
    rw [e1, e2] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp only [hH', blk_R3_append]
    have e3 : t - (t + s - u) = u - s := by ring
    have e4 : t + s - u = t - u + s := by ring
    rw [e3, e4]
  rw [key]
  by_cases hH : XNorm θ 0 0 H < ⊤
  · calc XNormRestr θ 0 0 {ts : Fin (r + 2) → ℝ | 0 < ts (Fin.natAdd r 1) ∧
          ts (Fin.natAdd r 1) < ts (Fin.natAdd r 0) ∧ ts (Fin.natAdd r 0) < 1} K
          (fun (ts : Fin (r + 2) → ℝ) (k : Mom d) =>
      ∫ u in ts (Fin.natAdd r 1)..ts (Fin.natAdd r 0),
        Complex.exp (((Real.pi * A * (u - ts (Fin.natAdd r 1)) : ℝ) : ℂ) * Complex.I) *
          H' (Fin.append (fun i : Fin r => ts (Fin.castAdd 2 i))
            ![ts (Fin.natAdd r 0), u, ts (Fin.natAdd r 1)]) k)
        ≤ ENNReal.ofReal C * XNorm θ 0 0 H' := hC A H' K
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 ^ θ) * XNorm θ 0 0 H) := by
          refine mul_le_mul_right ?_ _
          rw [xnorm_eq_mixed, xnorm_eq_mixed]
          exact norm_blk_le hθ0 H
      _ = ENNReal.ofReal (C * 2 ^ θ) * XNorm θ 0 0 H := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC0]
      _ ≤ ENNReal.ofReal (C * 2 ^ θ + 1) * XNorm θ 0 0 H :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
  · rw [not_lt, top_le_iff] at hH
    rw [hH, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top

end WaveTurbulence.Flower.ProtOpsTerm
