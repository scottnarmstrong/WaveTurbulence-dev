/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.RemAe

/-! # P4-W2 (R78): Fourier modes of a remainder, EVERYWHERE on a continuity set

`fs_expansion_C`: as `P2.fs_expansion_ae`, but the remainder `f` need only be `ContinuousOn Bc` (`Bc ⊆ B`, `Bc ⊆ closure (interior Bc)`; `XNormRestr ... B < b` on the whole window `B`), and the expansion holds at EVERY
point of `Bc` (the upgrade `hasSum_of_ae_contOn` of the a.e. expansion of the extension, which agrees with `f` on `B`).  This is the remainder analogue of `AuxRows.sepRowWS` (F-AUX-CONT).
`rowModes3_of_restr_C`: the three-clock version (zero third mode). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.NormBridgeScratch MeasureTheory Set
open scoped ENNReal

variable {r d : ℕ}

theorem fs_expansion_C {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B Bc : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ) (b : ℝ≥0∞),
      B ⊆ cell q → B ⊆ closure (interior B) → Bc ⊆ B → Bc ⊆ closure (interior Bc) →
      (∀ k, ContinuousOn (fun t => f t k) Bc) →
      XNormRestr θ Λ₁ Λ₂ B Set.univ f < b →
      ∃ c : (Fin r → ℤ) → Mom d → ℂ,
        (∀ t ∈ Bc, ∀ k, HasSum (fun m : Fin r → ℤ => c m k * fsPhase m t) (f t k)) ∧
        ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) ≤ C * b := by
  obtain ⟨C, hC, hCb⟩ := sum_SNorm_coeff_le (r := r) (d := d) hθ hΛ
  obtain ⟨C0, hC0, hC0b⟩ := hcoef_sum_le (r := r) hθ
  refine ⟨C, hC, fun q B Bc f b hBc hBi hBcB hBci hfc hb => ?_⟩
  unfold XNormRestr at hb
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 hb
  obtain ⟨hGK, hGb⟩ := iInf_lt_iff.1 hG
  have hGtop : XNorm θ Λ₁ Λ₂ G < ⊤ := lt_of_lt_of_le hGb le_top
  refine ⟨coeff q G, fun t htBc k => ?_, ?_⟩
  · have hG0 := (VineEstS3.XNorm00_le_XNorm θ Λ₁ Λ₂ G).trans_lt hGtop
    have hgn : timeFourierNorm θ (fun s => G s k) < ⊤ := by
      refine lt_of_le_of_lt ((timeFourierNorm_slice_le_mixedFourierNorm00 θ G k).trans_eq ?_) hG0
      exact (NormBridgeScratch.XNorm00_eq_mixedFourierNorm00 θ G).symm
    have hae := scalar_fs_hasSum_ae hθ q hBc hBi hgn
    have hae' : ∀ᵐ t : Fin r → ℝ, t ∈ B → HasSum (fun m : Fin r → ℤ => hcoef q (fun s => G s k) m * fsPhase m t) (f t k) := by
      filter_upwards [hae] with t ht htB
      have := ht htB
      rwa [hGK t htB k (Set.mem_univ k)] at this
    have hsum : Summable fun m => ‖hcoef q (fun s => G s k) m‖ := by
      refine summable_of_bracket hθ (b := C0 * timeFourierNorm θ (fun s => G s k)) ?_ (hC0b q _)
      exact ENNReal.mul_ne_top hC0 hgn.ne
    have hall := hasSum_of_ae_contOn hsum hBcB hBci (hfc k) hae' t htBc
    simpa only [coeff, NormBridgeScratch.timeFT_eq_timeFourier, hcoef] using hall
  · exact (hCb q G hGtop).trans (mul_le_mul_right hGb.le _)

theorem rowModes3_of_restr_C {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin 2 → ℝ) (B Bc : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → Mom d → ℂ) (b : ℝ≥0∞),
      B ⊆ cell q → B ⊆ closure (interior B) → Bc ⊆ B → Bc ⊆ closure (interior Bc) →
      (∀ k, ContinuousOn (fun t => f t k) Bc) → XNormRestr θ Λ₁ Λ₂ B Set.univ f < b →
      ∃ c : (Fin 3 → ℤ) → Mom d → ℂ,
        (∀ t3 : Fin 3 → ℝ, ![t3 0, t3 1] ∈ Bc → ∀ k, HasSum (fun m : Fin 3 → ℤ => c m k * fsPhase m t3)
          (f ![t3 0, t3 1] k)) ∧
        ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) ≤ C * b := by
  obtain ⟨C, hC, hf⟩ := fs_expansion_C (r := 2) (d := d) hθ hΛ (Λ₂ := Λ₂)
  refine ⟨C, hC, fun q B Bc f b hBc hBi hBcB hBci hfc hb => ?_⟩
  obtain ⟨c2, h1, h2⟩ := hf q B Bc f b hBc hBi hBcB hBci hfc hb
  refine ⟨fun m k => embed2 (fun n => c2 n k) m, fun t3 ht3 k => ?_, ?_⟩
  · exact hasSum_embed2 (fun n => c2 n k) t3 (h1 _ ht3 k)
  · refine le_trans (le_of_eq ?_) h2
    rw [← embedMode_injective.tsum_eq (f := fun m : Fin 3 → ℤ => maxBracketPow θ (half m) *
      SNorm Λ₁ Λ₂ (fun k => embed2 (fun n => c2 n k) m))]
    · refine tsum_congr fun n => ?_
      rw [maxBracketPow_embedMode]
      congr 2
      funext k
      rw [embed2_embedMode]
    · intro m hm
      by_contra hnr
      apply hm
      have : (fun k => embed2 (fun n => c2 n k) m) = fun _ => 0 := funext fun k => embed2_eq_zero _ m hnr
      simp [this, SNorm_zero_fun]

end WaveTurbulence.VineEstS5C.P4.W2
