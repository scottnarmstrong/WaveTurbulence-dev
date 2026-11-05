/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.DtTail
public import WaveTurbulence.Foundations.XChain.CplDraft.FamBounds
public import WaveTurbulence.Foundations.XChain.AnsatzLowerOrderTail
public import WaveTurbulence.Foundations.XChain.ForestWeightedNormSum
public import WaveTurbulence.Foundations.XChain.PartitionEnvelopeBound

/-!
# CPL-3, step 9: envelope bounds for a family with general coefficients

**Statements.** Let the coefficients have norm `≤ 1`. Let `𝒮 ⊆ truncatedTrees M` with `2(2M+1) ≤ 2R_p`, under
`AnsatzAt` and rapid data, and let `W = (⟨n₁⟩⟨n₂⟩)^{-Λ_p/4}`.
1. `genOrderTail_bound`, `genOrderTail_uniform_bound`: INDUCT's `ansatz_lower_order_tail_bound` and
   `ansatz_partition_tail_uniform_bound` for the generic order tail. The top factor has norm `≤ 1` in place of
   the time volume `∏_j boxVol ≤ 1`.
2. `famGenError_envelope_bound`: `|famGenError| ≤ graftEnvelope d 2 M L (Λ_p/4) C · e^{-N_p} · W`.
3. `famGenTail_envelope_bound`: the tail of order `> Ncut` (`famGenGarden_dt_tail_eq`) is
   `≤ graftEnvelope d 2 M L (Λ_p/4) C · (δ^{ν/2})^{(Ncut+1) − 2M} · W`.

These are `famError_envelope_bound` and `famTail_envelope_bound` (FamBounds) without the tree prefactors; the
per-partition bounds are `genError_uniform_bound` and `genOrderTail_uniform_bound`.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Induct
open scoped Classical

/-- A sum over the irreducible partitions of a forest, bounded term by term. -/
theorem norm_sum_partitions_le {M : ℕ} (top : Fin 2 → TrTree M)
    (X : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
      TopPartitionIrreducible (fun j => (top j).1) P} → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ P, ‖X P‖ ≤ B) :
    ‖∑ P, X P‖ ≤ (((2 ^ (2 * (2 * M + 1))) ^ (2 * (2 * M + 1)) : ℕ) : ℝ) * B := by
  have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
  have hcard : Fintype.card {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
      TopPartitionIrreducible (fun j => (top j).1) P} ≤ (2 ^ (2 * (2 * M + 1))) ^ (2 * (2 * M + 1)) := by
    have hi := Nat.card_le_card_of_injective
      (fun P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
        TopPartitionIrreducible (fun j => (top j).1) P} => P.1) Subtype.val_injective
    have hcl := card_leafPartitions_le (fun j => (top j).1) hT
    simp only [Nat.card_eq_fintype_card] at hi hcl
    exact hi.trans hcl
  refine (norm_sum_le _ _).trans ((sum_le_sum fun P _ => hX P).trans ?_)
  rw [sum_const, card_univ, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

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
    (hd : 1 ≤ Q.d) (hp : p < Q.D)

omit [IsProbabilityMeasure μ] in
include ha hδ hLone hC hF hd hp in
/-- **The generic order tail** after decoration summation. -/
theorem genOrderTail_bound (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (coef : (j : Fin w) → TreeCoef Q.d (top j)) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (univ : Finset (GLeaf top))) (n : Fin w → (Fin Q.d → ℤ)) (J : ℕ)
    (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) :
    ‖genOrderTail Q.L Q.γ Q.δ (inputsF Q R) sig top coef P p (Q.N p) J n‖ ≤
      (C ^ P.parts.card * ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) *
        ((2 ^ Fintype.card (GLeaf top) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
          (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) *
            (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4))) ^
              Fintype.card (GLeaf top)) := by
  have hC0 : 0 ≤ C := by linarith
  have htail : 0 ≤ (Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card :=
    mul_nonneg (pow_nonneg (Real.rpow_nonneg hδ.le _) _) (by positivity)
  apply norm_tsum_le_of_forest_bracket_bound top n Q.L ((Q.Lambda p : ℝ) / 4)
    (C ^ P.parts.card * ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) hLone
    (lambda_quarter_ge_dimension Q hd hp) (mul_nonneg (pow_nonneg hC0 _) htail)
    (genOrderTailIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig top coef P p (Q.N p) J n)
  intro κ
  have he := ansatz_lower_order_product_tail_bound Q μ g a Fev R E Et p ha hδ hsmall hLone
    C hC hF sig top P κ J hR
  have hc := norm_prod_genTopCoef_le top sig coef (fun _ => 1) hcoef κ
  rw [prod_const_one] at hc
  unfold genOrderTailIntegrand
  rw [norm_mul]
  have h := mul_le_mul hc he (norm_nonneg _) zero_le_one
  refine h.trans_eq ?_
  have hexp : -(2 * ((Q.Lambda p : ℝ) / 4)) = -(Q.Lambda p : ℝ) / 2 := by ring
  rw [hexp]
  ring

omit [IsProbabilityMeasure μ] in
include ha hδ hLone hC hF hd hp in
/-- **The uniform generic order-tail bound** (orders `≤ Ntop`). -/
theorem genOrderTail_uniform_bound (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (coef : (j : Fin w) → TreeCoef Q.d (top j)) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (univ : Finset (GLeaf top))) (n : Fin w → (Fin Q.d → ℤ)) (J Ntop : ℕ)
    (htop : ∀ j, (top j).order ≤ Ntop) (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) :
    ‖genOrderTail Q.L Q.γ Q.δ (inputsF Q R) sig top coef P p (Q.N p) J n‖ ≤
      ((Q.δ ^ (Q.ν / 2)) ^ J *
        (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4))) *
          ((2 * C) ^ (w * (2 * Ntop + 1)) *
            (2 ^ (w * (2 * Ntop + 1)) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
              (max 1 (∑' m : Fin Q.d → ℤ,
                jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ (w * (2 * Ntop + 1))) := by
  let H := w * (2 * Ntop + 1)
  let b : ℝ := (Q.Lambda p : ℝ) / 4
  let S : ℝ := ∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-b)
  let ε : ℝ := (Q.δ ^ (Q.ν / 2)) ^ J
  let W : ℝ := (∏ j, jbr (latticePoint Q.L (n j))) ^ (-b)
  let E0 : ℝ := 2 ^ P.parts.card * C ^ P.parts.card *
    (2 ^ Fintype.card (GLeaf top) : ℝ) ^ b * S ^ Fintype.card (GLeaf top)
  have hS : 0 ≤ S := tsum_nonneg (fun m => Real.rpow_nonneg (jbr_pos _).le _)
  have hεW : 0 ≤ ε * W := mul_nonneg (pow_nonneg (Real.rpow_nonneg hδ.le _) _)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _)
  have hleaf : Fintype.card (GLeaf top) ≤ H := forest_card_leaves_le top htop
  have hparts : P.parts.card ≤ H := by
    have h := P.card_parts_le_card
    simpa only [card_univ] using h.trans (by simpa only [card_univ] using hleaf)
  have hE := partition_envelope_le hparts hleaf (by linarith : 1 ≤ C)
    (show 0 ≤ b from div_nonneg (Nat.cast_nonneg _) (by norm_num)) hS
  have he := genOrderTail_bound Q μ g a Fev R E Et p ha hδ hLone C hC hF hd hp hsmall sig top coef hcoef P n J hR
  have heq : (C ^ P.parts.card * ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) *
        ((2 ^ Fintype.card (GLeaf top) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
          (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) *
            (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4))) ^
              Fintype.card (GLeaf top)) = (ε * W) * E0 := by
    dsimp [ε, W, E0, S, b]
    ring
  rw [heq] at he
  exact he.trans (mul_le_mul_of_nonneg_left hE hεW)

include hG ha hrapid hδ hLone hC hF hd hp in
/-- **The family error envelope** for general coefficients. -/
theorem famGenError_envelope_bound (hsmall : Q.δ ^ Q.ν ≤ 1 / 2) (M : ℕ) (𝒮 : Finset TTree)
    (coefOf : (T : TTree) → TreeCoef Q.d T) (hcoef : ∀ T κ, ‖coefOf T κ‖ ≤ 1)
    (sig : Fin 2 → ℤˣ) (n : Fin 2 → (Fin Q.d → ℤ)) (hNR : 2 * (2 * M + 1) ≤ 2 * Q.R p) :
    ‖famGenError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig (fun ω => a ω p) p M (Q.N p) 𝒮 coefOf n‖ ≤
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
  have h := norm_sum_forests_le (M := M) 𝒮 _ (Nat.cast_nonneg _) hB fun top _ =>
    norm_sum_partitions_le top _ hB fun P => by
      have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
      exact genError_uniform_bound Q μ g hG a Fev R E Et p ha hrapid hLone hδ hsmall C hC hF hd hp sig
        (fun j => (top j).1) (fun j => coefOf (top j).1) (fun j => hcoef _) P.1 n M hT
        (fun B => (topBlock_card_le _ hT P.1 B).trans hNR)
  unfold famGenError
  refine h.trans_eq ?_
  unfold graftEnvelope
  simp only [B, H, Nat.cast_pow, Nat.cast_ofNat]
  ring

omit [IsProbabilityMeasure μ] in
include ha hδ hLone hC hF hd hp in
/-- **The family tail envelope** for general coefficients. -/
theorem famGenTail_envelope_bound (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (M : ℕ) (𝒮 : Finset TTree)
    (coefOf : (T : TTree) → TreeCoef Q.d T) (hcoef : ∀ T κ, ‖coefOf T κ‖ ≤ 1)
    (n : Fin 2 → (Fin Q.d → ℤ)) (hNR : 2 * (2 * M + 1) ≤ 2 * Q.R p) (Ncut : ℕ) :
    ‖∑ top : Fin 2 → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then
        ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
            TopPartitionIrreducible (fun j => (top j).1) P},
          genOrderTail Q.L Q.γ Q.δ (inputsF Q R) ![1, -1] (fun j => (top j).1) (fun j => coefOf (top j).1) P.1
            p (Q.N p) ((Ncut + 1) - ∑ j, (top j).1.order) n
        else 0‖ ≤
      graftEnvelope Q.d 2 M Q.L ((Q.Lambda p : ℝ) / 4) C *
        (Q.δ ^ (Q.ν / 2)) ^ ((Ncut + 1) - 2 * M) *
          (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) := by
  let H := 2 * (2 * M + 1)
  let Z : ℝ := (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) *
    ((2 * C) ^ H * (2 ^ H : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
      (max 1 (∑' m : Fin Q.d → ℤ,
        jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ H)
  let B : ℝ := (Q.δ ^ (Q.ν / 2)) ^ ((Ncut + 1) - 2 * M) * Z
  have hZ : 0 ≤ Z := mul_nonneg
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _)
    (mul_nonneg (mul_nonneg (pow_nonneg (by linarith : 0 ≤ 2 * C) _)
      (Real.rpow_nonneg (by positivity) _))
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg (Real.rpow_nonneg hδ.le _) _) hZ
  have h := norm_sum_forests_le (M := M) 𝒮 _ (Nat.cast_nonneg _) hB fun top _ =>
    norm_sum_partitions_le top _ hB fun P => by
      have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
      have he := genOrderTail_uniform_bound Q μ g a Fev R E Et p ha hδ hLone C hC hF hd hp hsmall ![1, -1]
        (fun j => (top j).1) (fun j => coefOf (top j).1) (fun j => hcoef _) P.1 n
        ((Ncut + 1) - ∑ j, (top j).1.order) M hT (fun B => (topBlock_card_le _ hT P.1 B).trans hNR)
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
  simp only [B, H, Z, Nat.cast_pow, Nat.cast_ofNat]
  ring

end

end WaveTurbulence.Cpl
