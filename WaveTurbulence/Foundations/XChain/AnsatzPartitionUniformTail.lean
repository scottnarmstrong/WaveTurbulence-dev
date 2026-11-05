/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzLowerOrderSummedTail
public import WaveTurbulence.Foundations.XChain.PartitionEnvelopeBound
public import WaveTurbulence.Foundations.XChain.TopTimePrefactorBounds
public import WaveTurbulence.Foundations.XChain.AnsatzBlockKernelBound
public import WaveTurbulence.Foundations.XChain.AnsatzBlockResidual
public import WaveTurbulence.Foundations.XChain.TopPartitionBracketBound
public import WaveTurbulence.Foundations.XChain.InductDecayParameters
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
public import WaveTurbulence.Foundations.XChain.TopPartitionError
/-! Actual source input errors give the externally weighted decoration-summed cmattr error. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem ansatz_partition_tail_uniform_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (n : Fin w → (Fin Q.d → ℤ)) (hd : 1 ≤ Q.d) (hp : p < Q.D)
    (J Ntop : ℕ) (htop : ∀ j, (top j).order ≤ Ntop)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) :
    ‖lowerOrderTail Q.L Q.γ Q.δ (inputsF Q R) sig top P p (Q.N p) J t n‖ ≤
      ((Q.δ ^ (Q.ν / 2)) ^ J *
        (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4))) *
          ((2 * C) ^ (w * (2 * Ntop + 1)) *
            (2 ^ (w * (2 * Ntop + 1)) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
              (max 1 (∑' m : Fin Q.d → ℤ,
                jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ (w * (2 * Ntop + 1))) := by
  classical
  let H := w * (2 * Ntop + 1)
  let b : ℝ := (Q.Lambda p : ℝ) / 4
  let S : ℝ := ∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-b)
  let ε : ℝ := (Q.δ ^ (Q.ν / 2)) ^ J
  let W : ℝ := (∏ j, jbr (latticePoint Q.L (n j))) ^ (-b)
  let V : ℝ := ∏ j, SysAPI.boxVol (top j) p t
  let E0 : ℝ := 2 ^ P.parts.card * C ^ P.parts.card *
    (2 ^ Fintype.card (GLeaf top) : ℝ) ^ b * S ^ Fintype.card (GLeaf top)
  have hS : 0 ≤ S := tsum_nonneg (fun m => Real.rpow_nonneg (jbr_pos _).le _)
  have hV0 : 0 ≤ V := prod_nonneg (fun j _ => SysAPI.boxVol_nonneg (top j) p t)
  have hV : V ≤ 1 := prod_le_one₀ (fun j _ => SysAPI.boxVol_nonneg (top j) p t)
    (fun j _ => boxVol_le_one (top j) hpt htp)
  have hεW : 0 ≤ ε * W := mul_nonneg (pow_nonneg (Real.rpow_nonneg hδ.le _) _)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _)
  have hleaf : Fintype.card (GLeaf top) ≤ H := forest_card_leaves_le top htop
  have hparts : P.parts.card ≤ H := by
    have h := P.card_parts_le_card
    simpa only [card_univ] using h.trans (by simpa only [card_univ] using hleaf)
  have hE := partition_envelope_le hparts hleaf (by linarith : 1 ≤ C)
    (show 0 ≤ b from div_nonneg (Nat.cast_nonneg _) (by norm_num)) hS
  have hE0 : 0 ≤ E0 := by
    dsimp [E0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
      (Real.rpow_nonneg (by positivity) _)) (pow_nonneg hS _)
  have he := ansatz_lower_order_tail_bound Q μ g a Fev R E Et p ha hδ hsmall hLone
    C hC hF sig top P n hd hp t J hR
  have heq : ((∏ j, SysAPI.boxVol (top j) p t) * C ^ P.parts.card *
      ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) *
        ((2 ^ Fintype.card (GLeaf top) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
          (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) *
            (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4))) ^ Fintype.card (GLeaf top)) =
      (V * (ε * W)) * E0 := by dsimp [V, ε, W, E0, S, b]; ring
  rw [heq] at he
  have hVW : V * (ε * W) ≤ ε * W := by nlinarith
  exact he.trans (mul_le_mul hVW hE hE0 hεW)

end WaveTurbulence.Induct
