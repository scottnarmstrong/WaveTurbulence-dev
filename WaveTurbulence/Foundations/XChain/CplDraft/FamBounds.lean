/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.FamKernel
public import WaveTurbulence.Foundations.XChain.CmattrFiniteErrorBound
public import WaveTurbulence.Foundations.XChain.CoupleFiniteTailBound
public import WaveTurbulence.Foundations.XChain.GraftEnvelope

/-!
# CPL-2, step 5: envelope bounds for a family

**Statements.** For `𝒮 ⊆ truncatedTrees M` with `2(2M+1) ≤ 2R_p`, under `AnsatzAt` and rapid data, with
`W = (⟨n₁⟩⟨n₂⟩)^{-Λ_p/4}`:
1. `famError_envelope_bound`: `|famError| ≤ graftEnvelope d 2 M L (Λ_p/4) C · e^{-N_p} · W`;
2. `famTail_envelope_bound`: the order tail `> Ncut` (CPL step 3) is
   `≤ graftEnvelope d 2 M L (Λ_p/4) C · (δ^{ν/2})^{(Ncut+1) − 2M} · W`.

These are INDUCT's `ansatz_cmattr_error_bound` and the couple tail bound (`CoupleFiniteTailBound`) with the
forests restricted to `𝒮`.
- Each forest term is bounded by INDUCT's uniform per-partition bounds (`ansatz_partition_error_uniform_bound`,
  `ansatz_partition_tail_uniform_bound`).
- The number of partitions is bounded by `card_leafPartitions_le`, and the forest count by
  `card_topForests_le`.
- The indicator of `𝒮` only removes terms.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Induct
open scoped Classical

/-- A sum over the forests of `𝒮`, bounded term by term. -/
theorem norm_sum_forests_le {M : ℕ} (𝒮 : Finset TTree) (A : (Fin 2 → TrTree M) → ℂ) {K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (h : ∀ top, (∀ j, (top j).1 ∈ 𝒮) → ‖A top‖ ≤ K * B) :
    ‖∑ top : Fin 2 → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then A top else 0‖ ≤
      ((3 ^ (3 * M + 1) : ℝ) ^ 2) * (K * B) := by
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ top : Fin 2 → TrTree M,
      ‖if ∀ j, (top j).1 ∈ 𝒮 then A top else 0‖ ≤ K * B := by
    intro top
    split_ifs with ht
    · exact h top ht
    · rw [norm_zero]
      exact mul_nonneg hK hB
  refine (sum_le_sum fun top _ => hterm top).trans ?_
  rw [sum_const, card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Fin 2 → TrTree M) : ℝ) ≤ (3 ^ (3 * M + 1) : ℝ) ^ 2 := by
    exact_mod_cast card_topForests_le 2 M
  exact mul_le_mul_of_nonneg_right hc (mul_nonneg hK hB)

/-- One forest: the prefactor has norm `≤ 1` and there are `≤ K` partitions. -/
theorem norm_forest_term_le {d : ℕ} (L γ δ : ℝ) (hc : |coupling d L γ δ| ≤ 1) {M : ℕ}
    (sig : Fin 2 → ℤˣ) (top : Fin 2 → TrTree M)
    (X : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
      TopPartitionIrreducible (fun j => (top j).1) P} → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ P, ‖X P‖ ≤ B) :
    ‖(∏ j, zpowSign (sig j) (SysAPI.treePrefactor L γ δ d (top j).1)) * ∑ P, X P‖ ≤
      (((2 ^ (2 * (2 * M + 1))) ^ (2 * (2 * M + 1)) : ℕ) : ℝ) * B := by
  have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
  have hcard : Fintype.card {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
      TopPartitionIrreducible (fun j => (top j).1) P} ≤ (2 ^ (2 * (2 * M + 1))) ^ (2 * (2 * M + 1)) := by
    have hi := Nat.card_le_card_of_injective
      (fun P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
        TopPartitionIrreducible (fun j => (top j).1) P} => P.1) Subtype.val_injective
    have hcl := card_leafPartitions_le (fun j => (top j).1) hT
    simp only [Nat.card_eq_fintype_card] at hi hcl
    exact hi.trans hcl
  have hs : ‖∑ P, X P‖ ≤ (((2 ^ (2 * (2 * M + 1))) ^ (2 * (2 * M + 1)) : ℕ) : ℝ) * B := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun P _ => hX P).trans ?_)
    rw [sum_const, card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  have hpref : ‖∏ j, zpowSign (sig j) (SysAPI.treePrefactor L γ δ d (top j).1)‖ ≤ 1 := by
    rw [norm_prod]
    apply prod_le_one₀ (fun j _ => norm_nonneg _)
    intro j _
    rw [SysAPI.norm_zpowSign]
    exact norm_treePrefactor_le_one L γ δ (top j).1 hc
  rw [norm_mul]
  exact (mul_le_mul hpref hs (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

section

variable (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin Q.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom Q.d → ℝ)
    (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    (hδ : 0 < Q.δ) (hLone : 1 ≤ Q.L) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    (hd : 1 ≤ Q.d) (hp : p < Q.D) (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)

include hG ha hrapid hδ hLone hC hF hd hp hγ hδ1 in
/-- **The family error envelope.** -/
theorem famError_envelope_bound (hsmall : Q.δ ^ Q.ν ≤ 1 / 2) (M : ℕ) (𝒮 : Finset TTree)
    (sig : Fin 2 → ℤˣ) (n : Fin 2 → (Fin Q.d → ℤ)) (hNR : 2 * (2 * M + 1) ≤ 2 * Q.R p)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) :
    ‖famError Q.L Q.γ Q.δ (μ.restrict (Fev p)) (inputsF Q R) sig (fun ω => a ω p) p M (Q.N p) 𝒮 t n‖ ≤
      graftEnvelope Q.d 2 M Q.L ((Q.Lambda p : ℝ) / 4) C * Real.exp (-(Q.N p : ℝ)) *
        (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) := by
  let H := 2 * (2 * M + 1)
  let B : ℝ := (Real.exp (-(Q.N p : ℝ)) *
    (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4))) *
      ((2 * C) ^ H * (2 ^ H : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
        (max 1 (∑' m : Fin Q.d → ℤ,
          jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ H)
  have hB : 0 ≤ B := by
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _)
    · exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
        (Real.rpow_nonneg (by positivity) _)) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hcoupling := abs_coupling_le_one hLone hγ hδ.le hδ1
  have h := norm_sum_forests_le (M := M) 𝒮 _ (Nat.cast_nonneg _) hB fun top _ =>
    norm_forest_term_le Q.L Q.γ Q.δ hcoupling sig top _ hB fun P => by
      have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
      exact ansatz_partition_error_uniform_bound Q μ g hG a Fev R E Et p ha hrapid hδ hsmall hLone
        C hC hF sig (fun j => (top j).1) P.1 n hd hp M hT t hpt htp
        (fun B => (topBlock_card_le _ hT P.1 B).trans hNR)
  unfold famError
  refine h.trans_eq ?_
  unfold graftEnvelope
  simp only [B, H, Nat.cast_pow, Nat.cast_ofNat]
  ring

include ha hδ hLone hC hF hd hp hγ hδ1 in
/-- **The family tail envelope.** -/
theorem famTail_envelope_bound (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (M : ℕ) (𝒮 : Finset TTree)
    (n : Fin 2 → (Fin Q.d → ℤ)) (hNR : 2 * (2 * M + 1) ≤ 2 * Q.R p)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (Ncut : ℕ) :
    ‖∑ top : Fin 2 → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then
        (∏ j, zpowSign (![1, -1] j) (SysAPI.treePrefactor Q.L Q.γ Q.δ Q.d (top j).1)) *
          ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
              TopPartitionIrreducible (fun j => (top j).1) P},
            lowerOrderTail Q.L Q.γ Q.δ (inputsF Q R) ![1, -1] (fun j => (top j).1) P.1 p (Q.N p)
              ((Ncut + 1) - ∑ j, (top j).1.order) t n
        else 0‖ ≤
      graftEnvelope Q.d 2 M Q.L ((Q.Lambda p : ℝ) / 4) C *
        (Q.δ ^ (Q.ν / 2)) ^ ((Ncut + 1) - 2 * M) *
          (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) := by
  let H := 2 * (2 * M + 1)
  let B : ℝ := ((Q.δ ^ (Q.ν / 2)) ^ ((Ncut + 1) - 2 * M) *
    (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4))) *
      ((2 * C) ^ H * (2 ^ H : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
        (max 1 (∑' m : Fin Q.d → ℤ,
          jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ H)
  let Z : ℝ := (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) *
    ((2 * C) ^ H * (2 ^ H : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
      (max 1 (∑' m : Fin Q.d → ℤ,
        jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ H)
  have hZ : 0 ≤ Z := mul_nonneg
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _)
    (mul_nonneg (mul_nonneg (pow_nonneg (by linarith : 0 ≤ 2 * C) _)
      (Real.rpow_nonneg (by positivity) _))
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  have hB : 0 ≤ B := by
    have : B = (Q.δ ^ (Q.ν / 2)) ^ ((Ncut + 1) - 2 * M) * Z := by simp only [B, Z]; ring
    rw [this]
    exact mul_nonneg (pow_nonneg (Real.rpow_nonneg hδ.le _) _) hZ
  have hcoupling := abs_coupling_le_one hLone hγ hδ.le hδ1
  have h := norm_sum_forests_le (M := M) 𝒮 _ (Nat.cast_nonneg _) hB fun top _ =>
    norm_forest_term_le Q.L Q.γ Q.δ hcoupling ![1, -1] top _ hB fun P => by
      have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
      have he := ansatz_partition_tail_uniform_bound Q μ g a Fev R E Et p ha hδ hsmall hLone
        C hC hF ![1, -1] (fun j => (top j).1) P.1 n hd hp ((Ncut + 1) - ∑ j, (top j).1.order) M hT
        t hpt htp (fun B => (topBlock_card_le _ hT P.1 B).trans hNR)
      have hsum : (∑ j, (top j).1.order) ≤ 2 * M := by
        simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] using
          sum_le_sum (s := (univ : Finset (Fin 2))) (fun j _ => hT j)
      have hJ : (Ncut + 1) - 2 * M ≤ (Ncut + 1) - ∑ j, (top j).1.order := by omega
      have hq := pow_le_pow_of_le_one (Real.rpow_nonneg hδ.le _)
        (hsmall.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)) hJ
      have he' := mul_le_mul_of_nonneg_right hq hZ
      exact he.trans (by simpa only [B, H, Z, mul_assoc] using he')
  refine h.trans_eq ?_
  unfold graftEnvelope
  simp only [B, H, Nat.cast_pow, Nat.cast_ofNat]
  ring

end

end WaveTurbulence.Cpl
