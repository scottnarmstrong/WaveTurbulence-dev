/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOps.LocalNorm
public import WaveTurbulence.Frozen.Defs.XNorm00Restr
public import WaveTurbulence.Frozen.Defs.XNormRestr

/-! # PROT-OPS: o73 (13.4), the core: separated points -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence MeasureTheory WaveTurbulence.Fourier
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.ProtOps

variable {d : ℕ} {r : ℕ}

theorem superpose_apply_mem {L : ℝ} (hL : 1 ≤ L) {S : Finset (Mom d)}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 / L ≤ ‖a - b‖) (g : Mom d → (Fin r → ℝ) → ℂ) (t : Fin r → ℝ)
    {k₀ : Mom d} (hk : k₀ ∈ S) : superpose L S g t k₀ = g k₀ t := by
  unfold superpose
  rw [Finset.sum_eq_single k₀]
  · simp [psiT, psi_zero]
  · intro j hj hne
    have h := hsep k₀ hk j hj (Ne.symm hne)
    have h2 : 1 / 3 ≤ ‖L • (k₀ - j)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hL)]
      have : 1 ≤ L * ‖k₀ - j‖ := by
        have := mul_le_mul_of_nonneg_left h (zero_le_one.trans hL)
        rwa [mul_one_div_cancel (zero_lt_one.trans_le hL).ne'] at this
      linarith
    simp [psiT, psi_eq_zero_of_far d h2]
  · intro h; exact absurd hk h

/-- The core of o73 (13.4): extensions at `1/L`-separated points glue to an `X^{θ,N,0}` extension. -/
theorem localExt_core {N : ℕ} {B1 : ℝ} (hB : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ B1)
    (θ : ℝ) {L : ℝ} (hL : 1 ≤ L) (Bset : Set (Fin r → ℝ)) (F : (Fin r → ℝ) → Mom d → ℂ) (X : ℝ≥0∞)
    (hXt : X < ⊤) (S : Finset (Mom d)) (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 / L ≤ ‖a - b‖)
    (hX : ∀ k ∈ S, XNorm00Restr θ Bset {k} F ≤ X) :
    XNormRestr θ N 0 Bset (↑S : Set (Mom d)) F ≤ ENNReal.ofReal (L ^ N * B1 * S.card) * X := by
  have hB0 : 0 ≤ B1 := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hc0 : 0 ≤ L ^ N * B1 := by have := zero_le_one.trans hL; positivity
  set K : ℝ := L ^ N * B1 * S.card with hK
  have hK0 : 0 ≤ K := by positivity
  have key : ∀ ε : ℝ≥0∞, 0 < ε → ε < ⊤ →
      XNormRestr θ N 0 Bset (↑S : Set (Mom d)) F ≤ ENNReal.ofReal (L ^ N * B1) * (S.card * (X + ε)) := by
    intro ε hε0 hεt
    have hex : ∀ k ∈ S, ∃ G : (Fin r → ℝ) → Mom d → ℂ, (∀ t ∈ Bset, G t k = F t k) ∧ XNorm00 θ G < X + ε := by
      intro k hk
      have h := (hX k hk).trans_lt (ENNReal.lt_add_right hXt.ne hε0.ne')
      unfold XNorm00Restr at h
      rw [iInf_lt_iff] at h
      obtain ⟨G, hG⟩ := h
      rw [iInf_lt_iff] at hG
      obtain ⟨hag, hlt⟩ := hG
      exact ⟨G, fun t ht => hag t ht k (Set.mem_singleton k), hlt⟩
    choose! G hGag hGlt using hex
    let g : Mom d → (Fin r → ℝ) → ℂ := fun k t => G k t k
    have hGm : ∀ k ∈ S, mixedFourierNorm00 θ (G k) < X + ε := fun k hk => by
      rw [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]; exact hGlt k hk
    have hgi : ∀ k ∈ S, Integrable (g k) := fun k hk =>
      integrable_of_mixedFourierNorm00_lt_top ((hGm k hk).trans (ENNReal.add_lt_top.2 ⟨hXt, hεt⟩)) k
    have hgn : ∀ k ∈ S, timeFourierNorm θ (g k) ≤ X + ε := fun k hk =>
      (timeFourierNorm_slice_le_mixedFourierNorm00 θ (G k) k).trans (hGm k hk).le
    unfold XNormRestr
    refine (iInf₂_le (superpose L S g) (fun t ht k hk => ?_)).trans ?_
    · rw [superpose_apply_mem hL hsep g t hk]
      exact hGag k hk t ht
    · refine (XNorm_superpose_le hB hL S g hgi θ).trans ?_
      refine mul_le_mul_right ?_ _
      calc ∑ j ∈ S, timeFourierNorm θ (g j) ≤ ∑ j ∈ S, (X + ε) := Finset.sum_le_sum hgn
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hbt => ?_
  have hpos : (0 : ℝ) < (ε : ℝ) / (K + 1) := by positivity
  have h1 := key (ENNReal.ofReal ((ε : ℝ) / (K + 1))) (ENNReal.ofReal_pos.2 hpos) ENNReal.ofReal_lt_top
  refine h1.trans ?_
  have hcard : ENNReal.ofReal (L ^ N * B1) * (S.card * (X + ENNReal.ofReal ((ε : ℝ) / (K + 1)))) =
      ENNReal.ofReal K * X + ENNReal.ofReal K * ENNReal.ofReal ((ε : ℝ) / (K + 1)) := by
    have hKe : ENNReal.ofReal K = ENNReal.ofReal (L ^ N * B1) * S.card := by
      rw [hK, ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast]
    rw [hKe]; ring
  rw [hcard]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_mul hK0]
  calc ENNReal.ofReal (K * ((ε : ℝ) / (K + 1))) ≤ ENNReal.ofReal (ε : ℝ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [ε.2]
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

end WaveTurbulence.Flower.ProtOps
