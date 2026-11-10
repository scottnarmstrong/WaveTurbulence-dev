/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerTail
public import WaveTurbulence.Foundations.XChain.InductDecayParameters

/-!
# X2E-4, step 3: the tail and the input error at fixed flower trees

Under `AnsatzAt`, with `b = Λ_p/4` and the flower forest bracket weight
`BR = 2^{b·#} (∏_j ⟨n − ζ n'⟩)^{−b} S_b^{#}` (`#` the number of non-flower leaves):
- `norm_tail_mk_le`: the order tail at a partition with the pair blocks is `≤ C^{|P|} (δ^{ν/2})^J 2^{|P|} BR`;
- `norm_flowerError_le`: X2E-1's input error at a partition `Q` is `≤ 2^{|Q|} e^{−N_p} C^{|Q|} BR`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped Classical

/-- The flower forest bracket weight. -/
noncomputable def flowerBR (L b : ℝ) {d Pm : ℕ} (tops : Fin (2 * Pm) → FTree) (ζ : ℤˣ) (n n' : Fin d → ℤ) : ℝ :=
  (2 ^ (nfLeaves tops).card : ℝ) ^ b * (∏ _j : Fin (2 * Pm), jbr (latticePoint L (n - (ζ : ℤ) • n'))) ^ (-b) *
    (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ^ (nfLeaves tops).card

theorem flowerBR_nonneg (L b : ℝ) {d Pm : ℕ} (tops : Fin (2 * Pm) → FTree) (ζ : ℤˣ) (n n' : Fin d → ℤ) :
    0 ≤ flowerBR L b tops ζ n n' :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (prod_nonneg fun _ _ => (jbr_pos _).le) _))
    (pow_nonneg (tsum_nonneg fun _ => Real.rpow_nonneg (jbr_pos _).le _) _)

section Bounds

variable (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin Q.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom Q.d → ℝ)
    (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    (hL : 1 ≤ Q.L) (hδ : 0 < Q.δ) (hsmall : Q.δ ^ Q.ν ≤ 1 / 2) (hsmall' : Q.δ ^ (Q.ν / 2) ≤ 1 / 2)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤ C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    (hd : 1 ≤ Q.d) (hp : p < Q.D) (hc : |coupling Q.d Q.L Q.γ Q.δ| ≤ 1)
    {Pm : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hFl : ∀ j, tops j ≠ FTree.flower)
    (hsign : ∀ j, (tops j).sign = ζ) (hR : (nfLeaves tops).card ≤ 2 * Q.R p)

omit [IsProbabilityMeasure μ] in
include ha hL hδ hsmall' hC hF hFl hsign hR in
/-- **The order tail at a partition with the pair blocks**, for a coefficient weight `‖c‖ W^{−Λ/2} ≤ K W^{−2b}`. -/
theorem norm_tail_mk_le (b K : ℝ) (hb : (Q.d : ℝ) + 1 ≤ b) (hK : 0 ≤ K)
    (P : Finpartition (univ : Finset (GLeaf (ftop tops))))
    (hP : ∀ j, pbF tops j ∈ P.parts)
    (hsumF : ∀ q, Summable fun m : Fin Q.d → ℤ => |inputsF Q R q (latticePoint Q.L m)|)
    (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (dagger : Option (Fin 3 → Mom Q.d)) (cut1 cut2 : Option ℕ)
    (hcut : ∀ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p (Q.N p),
      CutWeightsOK Q.L (d := Q.d) hFl (mkFlowerAt P hP fam) hsign cut1 cut2)
    {t s : ℝ} (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin Q.d → ℤ) (J : ℕ)
    (hcw : ∀ κ : GNode (ftop tops) → (Fin Q.d → ℤ),
      ‖topCoefK Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s tops κ‖ *
          (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) ≤
        K * (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ l.toNode))) ^ (-(2 * b))) :
    ‖∑ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p (Q.N p),
        (if J ≤ ∑ B, (fam B).low.garden.order then
          gateSummand Q.L Q.γ Q.δ (inputsF Q R) p pat dagger cut1 cut2 t s n n'
            ((mkFlowerAt P hP fam).toData hsign).flowerGraft
        else 0)‖ ≤
      (C ^ P.parts.card * ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) *
        (K * flowerBR Q.L b tops ζ n n') := by
  set Λ := (Q.Lambda p : ℝ)
  rw [sum_gateSummand_mk_tail Q.L Q.γ Q.δ (Q.N p) hFl hsign P hP (inputsF Q R) hsumF pat hpat dagger cut1 cut2 hcut
    hpt hps n n' J]
  set inner := fun κ : GNode (ftop tops) → (Fin Q.d → ℤ) =>
    ∑ orders : P.parts → Fin (Q.N p + 1), if J ≤ ∑ B, (orders B).1 then
      ∏ B : P.parts, ∑ D : LowerGraftData (sigP tops P B) p (Q.N p),
        (if lowOrd D = orders B then blockG Q.L Q.γ Q.δ (inputsF Q R) p (Q.N p) n' tops P B D κ else 0)
    else 0 with hinner
  have hib (κ : GNode (ftop tops) → (Fin Q.d → ℤ)) := norm_inner_tail_le Q μ g a Fev R E Et p ha hL hδ hsmall'
    C hC hF hsign hR P hP n' κ J
  let S : Set (ForestDecoration (ftop tops) Q.d (fun _ => n)) := {kt | ∀ j, kt.1 (flowerAt tops j).toNode = n'}
  have hsupp : Function.support (fun kt : ForestDecoration (ftop tops) Q.d (fun _ => n) =>
      topCoefK Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s tops kt.1 * inner kt.1) ⊆ S := by
    intro kt hkt
    by_contra hS
    apply hkt
    have h0 := hib kt.1
    rw [ite_eq_right (show ¬ ∀ j, kt.1 (flowerAt tops j).toNode = n' from hS), zero_mul] at h0
    have hz : inner kt.1 = 0 := norm_le_zero_iff.mp h0
    change topCoefK Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s tops kt.1 * inner kt.1 = 0
    rw [hz, mul_zero]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  let M : ℝ := C ^ P.parts.card * ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg (by linarith) _)
    (mul_nonneg (pow_nonneg (Real.rpow_nonneg hδ.le _) _) (by positivity))
  let f : FlowerForestDec tops Q.d (fun _ => n) (fun _ => n') → ℂ :=
    fun κ => topCoefK Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s tops κ.1.1 * inner κ.1.1
  have hf : ∀ κ, ‖f κ‖ ≤ (M * K) * (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(2 * b)) := by
    intro κ
    have h2 := hib κ.1.1
    rw [ite_eq_left (fun j => κ.2 j), one_mul] at h2
    have h1 := hcw κ.1.1
    calc ‖f κ‖ = ‖topCoefK Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s tops κ.1.1‖ * ‖inner κ.1.1‖ := norm_mul _ _
      _ ≤ ‖topCoefK Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s tops κ.1.1‖ *
          ((C ^ P.parts.card * (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-Λ / 2)) *
            ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = M * (‖topCoefK Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s tops κ.1.1‖ *
          (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-Λ / 2)) := by ring
      _ ≤ M * (K * (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(2 * b))) :=
          mul_le_mul_of_nonneg_left h1 hM
      _ = _ := by ring
  have h := norm_tsum_le_of_flower_bracket_bound tops hsign Q.L b (M * K) hL hb (mul_nonneg hM hK) f hf
  refine h.trans (le_of_eq ?_)
  unfold flowerBR
  ring

include hG ha hrapid hL hδ hsmall hC hF in
/-- X2E-1's pointwise input error, keeping the top coefficients. -/
theorem norm_flowerMom_sub_flowerKer_le' {w : ℕ} (sig : Fin w → ℤˣ) (tops' : Fin w → FTree)
    (coef : (j : Fin w) → TreeCoef Q.d (tops' j).toTree)
    (P : Finpartition (nfLeaves tops')) (hRP : ∀ B ∈ P.parts, B.card ≤ 2 * Q.R p)
    {n n' : Fin w → (Fin Q.d → ℤ)} (κ : FlowerForestDec tops' Q.d n n') :
    ‖flowerMomIntegrand (μ.restrict (Fev p)) sig tops' coef P (fun ω => a ω p) κ -
        flowerKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig tops' coef P p (Q.N p) κ‖ ≤
      ‖∏ j, flowerTopCoef tops' sig coef κ j‖ * (2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card *
        (∏ l ∈ nfLeaves tops', jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2)) := by
  set Λ := (Q.Lambda p : ℝ)
  have hexp1 : Real.exp (-(Q.N p : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hd := norm_prod_difference_le P.parts
    (fun B => cumulant (μ.restrict (Fev p)) (flowerLeafInputs tops' sig (fun ω => a ω p) κ) B)
    (fun B => flowerBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig tops' p (Q.N p) κ B)
    (fun B => C * (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-Λ / 2))
    (Real.exp_pos _).le hexp1
    (fun B _ => mul_nonneg (by linarith) (Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _))
    (fun B hB => ansatz_flowerBlock_kernel_bound Q μ g a Fev R E Et p ha hL hδ hsmall C hC hF sig tops' κ B
      (P.nonempty_of_mem_parts hB) (hRP B hB))
    (fun B hB => by
      have he := ansatz_flowerBlock_residual_bound Q μ g hG a Fev R E Et p ha hrapid hL sig tops' κ B
        (P.nonempty_of_mem_parts hB) (hRP B hB)
      have hW : 0 ≤ (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-Λ / 2) :=
        Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _
      calc _ ≤ _ := he
        _ ≤ Real.exp (-(Q.N p : ℝ)) * (C * (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^
            (-Λ / 2)) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos _).le)
  rw [prod_parts_weight tops' P (fun l => jbr (latticePoint Q.L (κ.1.1 l.toNode))) (fun l => (jbr_pos _).le)
    C (-Λ / 2)] at hd
  unfold flowerMomIntegrand flowerKerIntegrand
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (hd.trans_eq (by ring)) (norm_nonneg _)

include hG ha hrapid hL hδ hsmall hC hF hsign in
/-- **X2E-1's input error at a partition**, for a coefficient weight `‖c‖ W^{−Λ/2} ≤ K W^{−2b}`. -/
theorem norm_flowerError_le (b K : ℝ) (hb : (Q.d : ℝ) + 1 ≤ b) (hK : 0 ≤ K)
    (coef : (j : Fin (2 * Pm)) → TreeCoef Q.d (tops j).toTree) (P : Finpartition (nfLeaves tops))
    (hRP : ∀ B ∈ P.parts, B.card ≤ 2 * Q.R p) (n n' : Fin Q.d → ℤ)
    (hcw : ∀ κ : FlowerForestDec tops Q.d (fun _ => n) (fun _ => n'),
      ‖∏ j, flowerTopCoef tops (altFlowerSig Pm) coef κ j‖ *
          (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) ≤
        K * (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(2 * b))) :
    ‖flowerError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) (altFlowerSig Pm) tops coef P (fun ω => a ω p) p
        (Q.N p) (fun _ => n) (fun _ => n')‖ ≤
      (2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card) * (K * flowerBR Q.L b tops ζ n n') := by
  set M := 2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (pow_nonneg (by linarith) _)
  unfold flowerError
  refine (norm_tsum_le_of_flower_bracket_bound tops hsign Q.L b (M * K) hL hb (mul_nonneg hM hK) _
    fun κ => ?_).trans (le_of_eq (by unfold flowerBR; ring))
  have h := norm_flowerMom_sub_flowerKer_le' Q μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF (altFlowerSig Pm)
    tops coef P hRP κ
  refine h.trans ?_
  calc _ = M * (‖∏ j, flowerTopCoef tops (altFlowerSig Pm) coef κ j‖ *
        (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2)) := by ring
    _ ≤ M * (K * (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(2 * b))) :=
        mul_le_mul_of_nonneg_left (hcw κ) hM
    _ = _ := by ring

end Bounds

end WaveTurbulence.X2E
