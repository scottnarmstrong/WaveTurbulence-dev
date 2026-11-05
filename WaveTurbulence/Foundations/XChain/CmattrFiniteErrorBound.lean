/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzPartitionUniformError
public import WaveTurbulence.Foundations.XChain.CmattrError
public import WaveTurbulence.Foundations.XChain.TopExpansionCardBounds
public import WaveTurbulence.Foundations.XChain.AnsatzPartitionSummedError
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
open Finset MeasureTheory Set SysAPI

theorem ansatz_cmattr_error_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ Q.ν ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    {w : ℕ} (sig : Fin w → ℤˣ) (n : Fin w → (Fin Q.d → ℤ))
    (hd : 1 ≤ Q.d) (hp : p < Q.D) (Ntop : ℕ)
    (hwidth : w * (2 * Ntop + 1) ≤ 2 * Q.R p)
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) :
    ‖cmattrError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig
      (fun ω => a ω p) p Ntop (Q.N p) t n‖ ≤
      ((3 ^ (3 * Ntop + 1) : ℝ) ^ w *
        ((2 ^ (w * (2 * Ntop + 1)) : ℝ) ^ (w * (2 * Ntop + 1)))) *
          ((Real.exp (-(Q.N p : ℝ)) *
            (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4))) *
              ((2 * C) ^ (w * (2 * Ntop + 1)) *
                (2 ^ (w * (2 * Ntop + 1)) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
                  (max 1 (∑' m : Fin Q.d → ℤ,
                    jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ (w * (2 * Ntop + 1)))) := by
  classical
  let H := w * (2 * Ntop + 1)
  let B : ℝ := (Real.exp (-(Q.N p : ℝ)) *
    (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4))) *
      ((2 * C) ^ H * (2 ^ H : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
        (max 1 (∑' m : Fin Q.d → ℤ,
          jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ H)
  have hB : 0 ≤ B := by
    dsimp [B]
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _)
    · exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
        (Real.rpow_nonneg (by positivity) _)) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  let K : ℕ := (2 ^ H) ^ H
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
  have hcoupling := abs_coupling_le_one hLone hγ hδ.le hδ1
  have htop (top : Fin w → TrTree Ntop) :
      ‖(∏ j, zpowSign (sig j) (SysAPI.treePrefactor Q.L Q.γ Q.δ Q.d (top j).1)) *
        ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
          TopPartitionIrreducible (fun j => (top j).1) P},
          topPartitionError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig
            (fun j => (top j).1) P.1 (fun ω => a ω p) p (Q.N p) t n‖ ≤ (K : ℝ) * B := by
    let T := fun j => (top j).1
    let Parts := {P : Finpartition (univ : Finset (GLeaf T)) // TopPartitionIrreducible T P}
    have hT (j) : (T j).order ≤ Ntop := mem_truncatedTrees.mp (top j).2
    have hP (P : Parts) :
        ‖topPartitionError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig T P.1
          (fun ω => a ω p) p (Q.N p) t n‖ ≤ B :=
      ansatz_partition_error_uniform_bound Q μ g hG a Fev R E Et p ha hrapid hδ hsmall hLone
        C hC hF sig T P.1 n hd hp Ntop hT t hpt htp
        (fun B => (topBlock_card_le T hT P.1 B).trans hwidth)
    have hcard : Fintype.card Parts ≤ K := by
      have hi := Nat.card_le_card_of_injective (fun P : Parts => P.1) Subtype.val_injective
      have hc := card_leafPartitions_le T hT
      have hi' : Fintype.card Parts ≤ Fintype.card (Finpartition (univ : Finset (GLeaf T))) := by
        simpa only [Nat.card_eq_fintype_card] using hi
      apply hi'.trans
      simpa only [Nat.card_eq_fintype_card] using hc
    have hs : ‖∑ P : Parts, topPartitionError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R)
        sig T P.1 (fun ω => a ω p) p (Q.N p) t n‖ ≤ (K : ℝ) * B := by
      have h := (norm_sum_le (univ : Finset Parts) _).trans (sum_le_sum (fun P _ => hP P))
      simp only [sum_const, card_univ, nsmul_eq_mul] at h
      exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB)
    rw [norm_mul]
    have hpref : ‖∏ j, zpowSign (sig j) (SysAPI.treePrefactor Q.L Q.γ Q.δ Q.d (top j).1)‖ ≤ 1 := by
      rw [norm_prod]
      apply prod_le_one₀ (fun j _ => norm_nonneg _)
      intro j _
      rw [norm_zpowSign]
      exact norm_treePrefactor_le_one Q.L Q.γ Q.δ (top j).1 hcoupling
    exact (mul_le_mul hpref hs (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  unfold cmattrError
  have hs := (norm_sum_le (univ : Finset (Fin w → TrTree Ntop)) _).trans
    (sum_le_sum (fun top _ => htop top))
  simp only [sum_const, card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card (Fin w → TrTree Ntop) : ℝ) ≤ (3 ^ (3 * Ntop + 1) : ℝ) ^ w := by
    exact_mod_cast card_topForests_le w Ntop
  have h := hs.trans (mul_le_mul_of_nonneg_right hc (mul_nonneg hK hB))
  simpa only [K, H, B, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using h

end WaveTurbulence.Induct
