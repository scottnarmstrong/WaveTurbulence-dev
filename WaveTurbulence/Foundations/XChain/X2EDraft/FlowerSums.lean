/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerBounds
public import WaveTurbulence.Foundations.XChain.TopExpansionCardBounds
public import WaveTurbulence.Foundations.XChain.GraftEnvelope
public import WaveTurbulence.Foundations.XChain.TreeLeafCard

/-!
# X2E-4, step 4: the tail and the input error, summed

With `N = N_{p+1}`, `b = Λ_p/4`, `q = δ^{ν/2}` and INDUCT's envelope `graftEnvelope d (12P) N L b C`:
- `card_kernelTrees_le`: the kernel family has at most `(3^{3N+1})^6` trees;
- `flowerTail_eq`: the tail is the sum over flower trees and partitions of the order tails at `J = M + 1 − ∑ orders`;
- `norm_flowerTail_le`: `‖flowerTail_M‖ ≤ graftEnvelope · q^{M + 1 − 2P(3N+1)} · (∏_j ⟨n − ζ n'⟩)^{−b}`;
- `norm_flowerErr_le`: `‖flowerErr‖ ≤ graftEnvelope · e^{−N_p} · (∏_j ⟨n − ζ n'⟩)^{−b}`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped Classical

/-! ## Counting -/

theorem card_treesLE_le (M : ℕ) : (treesLE M).card ≤ 3 ^ (3 * M + 1) := by
  have e : ↥(treesLE M) ≃ {T : TTree // T.order ≤ M} := Equiv.subtypeEquivRight fun _ => mem_treesLE
  have h := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h
  exact h.trans_le (card_bounded_trees_le M)

theorem card_ftreesLE_le (M : ℕ) : (ftreesLE M).card ≤ 3 ^ (3 * M + 1) * (2 * M + 1) := by
  have hmaps : ∀ F ∈ ftreesLE M, (⟨F.toTree, F.flowerPath⟩ : Σ _ : TTree, TTree.Path) ∈
      (treesLE M).sigma fun T => T.leaves := by
    intro F hF
    refine mem_sigma.mpr ⟨mem_treesLE.mpr ?_, F.flowerPath_mem_leaves⟩
    rw [order_toTree]
    exact mem_ftreesLE.mp hF
  have hinj : Set.InjOn (fun F : FTree => (⟨F.toTree, F.flowerPath⟩ : Σ _ : TTree, TTree.Path))
      (ftreesLE M : Set FTree) := by
    intro F _ G _ h
    have h' := Sigma.mk.inj_iff.mp h
    exact eq_of_toTree_flowerPath h'.1 (eq_of_heq h'.2)
  refine (card_le_card_of_injOn _ hmaps hinj).trans ?_
  rw [card_sigma]
  calc ∑ T ∈ treesLE M, T.leaves.card ≤ ∑ _T ∈ treesLE M, (2 * M + 1) := sum_le_sum fun T hT => by
        rw [tree_card_leaves_eq]
        have := mem_treesLE.mp hT
        omega
    _ = (treesLE M).card * (2 * M + 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ 3 ^ (3 * M + 1) * (2 * M + 1) := Nat.mul_le_mul_right _ (card_treesLE_le M)

theorem card_kernelTrees_le (pat : FixPat) (N : ℕ) (kind : FlowerKind) (ζ : ℤˣ) :
    (kernelTrees pat N kind ζ).card ≤ (3 ^ (3 * N + 1)) ^ 6 := by
  have hsub : kernelTrees pat N kind ζ ⊆ ftreesLE (3 * N + 1) := fun F hF =>
    mem_ftreesLE.mpr (order_le_of_mem_kindTrees (mem_filter.mp hF).1)
  refine (card_le_card hsub).trans ((card_ftreesLE_le _).trans ?_)
  have h1 : 2 * (3 * N + 1) + 1 ≤ 3 ^ (9 * N + 2) := by
    have := Nat.lt_pow_self (by norm_num : 1 < 3) (n := 9 * N + 2)
    omega
  calc 3 ^ (3 * (3 * N + 1) + 1) * (2 * (3 * N + 1) + 1) ≤ 3 ^ (9 * N + 4) * 3 ^ (9 * N + 2) := by
        rw [show 3 * (3 * N + 1) + 1 = 9 * N + 4 by ring]
        exact Nat.mul_le_mul_left _ h1
    _ = (3 ^ (3 * N + 1)) ^ 6 := by
        rw [← pow_add, ← pow_mul]
        ring_nf

theorem norm_sum_le_card_mul {ι : Type*} [Fintype ι] (f : ι → ℂ) (B : ℝ) (h : ∀ i, ‖f i‖ ≤ B) :
    ‖∑ i, f i‖ ≤ Fintype.card ι * B := by
  refine (norm_sum_le _ _).trans ?_
  have := Finset.sum_le_card_nsmul univ (fun i => ‖f i‖) B (fun i _ => h i)
  simpa only [card_univ, nsmul_eq_mul] using this

/-! ## The tail and the error -/

section Sums

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
    (hsumF : ∀ q, Summable fun m : Fin Q.d → ℤ => |inputsF Q R q (latticePoint Q.L m)|)
    (kind : FlowerKind) (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot)
    (dagger : Option (Fin 3 → Mom Q.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin Q.d → ℤ) (Pm : ℕ)
    (hNR : (2 * Pm) * (2 * (3 * Q.N (p + 1) + 1) + 1) ≤ 2 * Q.R p)
    (hcut : ∀ x : FlIdx (Q.N p) (Q.N (p + 1)) pat kind ζ Pm p, CutWeightsOK Q.L (d := Q.d)
      (fun j => ne_flower_of_mem_kernelTrees pat (x.1 j).2) (mkFlowerAt x.2.1.1 x.2.1.2 x.2.2)
      (fun j => kernelTrees_sign (Q.N (p + 1)) pat kind ζ (x.1 j).2) cut1 cut2)

/-- The leaves of a tuple of kernel trees. -/
theorem card_leaves_tops (tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ)) :
    Fintype.card (GLeaf (ftop fun j => (tops j).1)) ≤ 12 * Pm * (2 * Q.N (p + 1) + 1) := by
  have h := forest_card_leaves_le (ftop fun j => (tops j).1)
    (fun j => order_toTree_le_of_mem_kernelTrees (tops j).2)
  refine h.trans ?_
  nlinarith

include hNR in
theorem card_nfLeaves_tops (tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ)) :
    (nfLeaves fun j => (tops j).1).card ≤ 2 * Q.R p := by
  have h := forest_card_leaves_le (ftop fun j => (tops j).1)
    (fun j => order_toTree_le_of_mem_kernelTrees (tops j).2)
  exact (card_le_univ _).trans (h.trans hNR)

/-- The orders and the order threshold. -/
theorem ite_order_eq {T S M : ℕ} (x : ℂ) : (if T + S ≤ M then 0 else x) = if (M + 1) - T ≤ S then x else 0 := by
  by_cases h : T + S ≤ M
  · rw [ite_eq_left h, ite_eq_right (by omega)]
  · rw [ite_eq_right h, ite_eq_left (by omega)]

/-- **The tail by flower trees and partitions.** -/
theorem flowerTail_eq (M : ℕ) :
    flowerTail Q (inputsF Q R) p kind pat dagger cut1 cut2 ζ t s n n' Pm M =
      ∑ tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ),
        ∑ P : {P : Finpartition (univ : Finset (GLeaf (ftop fun j => (tops j).1))) //
            ∀ j, pbF (fun j => (tops j).1) j ∈ P.parts},
          ∑ fam : (B : P.1.parts) → LowerGraftData (sigP (fun j => (tops j).1) P.1 B) p (Q.N p),
            (if (M + 1) - ∑ j, ((tops j).1.toTree).order ≤ ∑ B, (fam B).low.garden.order then
              gateSummand Q.L Q.γ Q.δ (inputsF Q R) p pat dagger cut1 cut2 t s n n'
                ((mkFlowerAt P.1 P.2 fam).toData fun j =>
                  kernelTrees_sign (Q.N (p + 1)) pat kind ζ (tops j).2).flowerGraft
            else 0) := by
  unfold flowerTail
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun tops _ => ?_
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun P _ => sum_congr rfl fun fam _ => ?_
  have ho := FlowerGraftData.order_flowerGraft
    ((mkFlowerAt P.1 P.2 fam).toData fun j => kernelTrees_sign (Q.N (p + 1)) pat kind ζ (tops j).2)
  change (if ((mkFlowerAt P.1 P.2 fam).toData _).flowerGraft.garden.order ≤ M then 0 else _) = _
  rw [ho]
  exact ite_order_eq _

/-- The per-term envelope factor. -/
noncomputable def envU (C b : ℝ) : ℝ :=
  (2 * C) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) * (2 ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) : ℝ) ^ b *
    (max 1 (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-b))) ^ (12 * Pm * (2 * Q.N (p + 1) + 1))

/-- The bracket factor `(∏_j ⟨n − ζ n'⟩)^{−b}`. -/
noncomputable def bracketW (b : ℝ) : ℝ :=
  (∏ _j : Fin (2 * Pm), jbr (latticePoint Q.L (n - (ζ : ℤ) • n'))) ^ (-b)

theorem envU_nonneg (b : ℝ) (hC1 : 1 ≤ C) : 0 ≤ envU Q p Pm C b :=
  mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

theorem bracketW_nonneg (b : ℝ) : 0 ≤ bracketW Q ζ n n' Pm b :=
  Real.rpow_nonneg (prod_nonneg fun _ _ => (jbr_pos _).le) _

theorem graftEnvelope_split (b : ℝ) :
    graftEnvelope Q.d (12 * Pm) (Q.N (p + 1)) Q.L b C =
      (3 ^ (3 * Q.N (p + 1) + 1) : ℝ) ^ (12 * Pm) *
        ((2 ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) : ℝ) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) * envU Q p Pm C b) := by
  unfold graftEnvelope envU
  ring

/-- The envelope part of a term. -/
theorem term_le_envelope (b : ℝ) (hb : 0 ≤ b) (tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ))
    (k : ℕ) (hk : k ≤ Fintype.card (GLeaf (ftop fun j => (tops j).1))) (hC1 : 1 ≤ C) :
    (2 * C) ^ k * flowerBR Q.L b (fun j => (tops j).1) ζ n n' ≤ envU Q p Pm C b * bracketW Q ζ n n' Pm b := by
  have hleaf := card_leaves_tops Q p kind pat ζ Pm tops
  have hnf : (nfLeaves fun j => (tops j).1).card ≤ 12 * Pm * (2 * Q.N (p + 1) + 1) := (card_le_univ _).trans hleaf
  have hkH : k ≤ 12 * Pm * (2 * Q.N (p + 1) + 1) := hk.trans hleaf
  have hS0 : 0 ≤ ∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-b) :=
    tsum_nonneg fun _ => Real.rpow_nonneg (jbr_pos _).le _
  have h1 : (2 * C) ^ k ≤ (2 * C) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) := pow_le_pow_right₀ (by linarith) hkH
  have h2 : (2 ^ (nfLeaves fun j => (tops j).1).card : ℝ) ^ b ≤ (2 ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) : ℝ) ^ b :=
    Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) hnf) hb
  have h3 : (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-b)) ^ (nfLeaves fun j => (tops j).1).card ≤
      (max 1 (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-b))) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) :=
    (pow_le_pow_left₀ hS0 (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) hnf)
  have hA : 0 ≤ (2 ^ (nfLeaves fun j => (tops j).1).card : ℝ) ^ b := Real.rpow_nonneg (by positivity) _
  have hW0 := bracketW_nonneg Q ζ n n' Pm b
  unfold flowerBR envU
  change (2 * C) ^ k * ((2 ^ (nfLeaves fun j => (tops j).1).card : ℝ) ^ b * bracketW Q ζ n n' Pm b * _) ≤ _
  calc _ = ((2 * C) ^ k * (2 ^ (nfLeaves fun j => (tops j).1).card : ℝ) ^ b *
        (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-b)) ^ (nfLeaves fun j => (tops j).1).card) *
          bracketW Q ζ n n' Pm b := by ring
    _ ≤ _ := by gcongr

theorem card_partitions_tops (tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ)) :
    (Fintype.card {P : Finpartition (univ : Finset (GLeaf (ftop fun j => (tops j).1))) //
      ∀ j, pbF (fun j => (tops j).1) j ∈ P.parts} : ℝ) ≤
      (2 ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) : ℝ) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) := by
  have hleaf := card_leaves_tops Q p kind pat ζ Pm tops
  have h1 := Fintype.card_subtype_le (fun P : Finpartition (univ : Finset (GLeaf (ftop fun j => (tops j).1))) =>
    ∀ j, pbF (fun j => (tops j).1) j ∈ P.parts)
  have h2 := card_finpartitions_le (α := GLeaf (ftop fun j => (tops j).1))
  rw [Nat.card_eq_fintype_card] at h2
  have h3 : (2 ^ Fintype.card (GLeaf (ftop fun j => (tops j).1))) ^ Fintype.card (GLeaf (ftop fun j => (tops j).1)) ≤
      (2 ^ (12 * Pm * (2 * Q.N (p + 1) + 1))) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) :=
    (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hleaf) _).trans
      (Nat.pow_le_pow_right (by positivity) hleaf)
  exact_mod_cast h1.trans (h2.trans h3)

theorem card_tops_le :
    (Fintype.card (Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ)) : ℝ) ≤
      ((3 ^ (3 * Q.N (p + 1) + 1) : ℝ) ^ (12 * Pm)) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have h := Nat.pow_le_pow_left (card_kernelTrees_le pat (Q.N (p + 1)) kind ζ) (2 * Pm)
  have h' : (kernelTrees pat (Q.N (p + 1)) kind ζ).card ^ (2 * Pm) ≤ (3 ^ (3 * Q.N (p + 1) + 1)) ^ (12 * Pm) := by
    refine h.trans (le_of_eq ?_)
    rw [← pow_mul]
    ring_nf
  exact_mod_cast h'

theorem sum_orders_tops_le (tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ)) :
    ∑ j, ((tops j).1.toTree).order ≤ 2 * Pm * (3 * Q.N (p + 1) + 1) := by
  have := sum_le_sum (s := (univ : Finset (Fin (2 * Pm)))) fun j _ => order_toTree_le_of_mem_kernelTrees (tops j).2
  simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] using this

/-- The coefficient weight hypothesis over all tuples of kernel trees. -/
def CoefW (b K : ℝ) : Prop :=
  ∀ (tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ))
    (κ : GNode (ftop fun j => (tops j).1) → (Fin Q.d → ℤ)),
    ‖topCoefK Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s (fun j => (tops j).1) κ‖ *
        (∏ l ∈ nfLeaves (fun j => (tops j).1), jbr (latticePoint Q.L (κ l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) ≤
      K * (∏ l ∈ nfLeaves (fun j => (tops j).1), jbr (latticePoint Q.L (κ l.toNode))) ^ (-(2 * b))

omit [IsProbabilityMeasure μ] in
include ha hL hδ hsmall' hC hF hsumF hpat hpt hps hNR hcut in
/-- The order tail at fixed flower trees. -/
theorem norm_tail_tops_le (b K : ℝ) (hb : (Q.d : ℝ) + 1 ≤ b) (hK : 0 ≤ K)
    (hcw : CoefW Q p kind pat dagger cut1 cut2 ζ t s Pm b K) (M : ℕ)
    (tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ)) :
    ‖∑ P : {P : Finpartition (univ : Finset (GLeaf (ftop fun j => (tops j).1))) //
          ∀ j, pbF (fun j => (tops j).1) j ∈ P.parts},
        ∑ fam : (B : P.1.parts) → LowerGraftData (sigP (fun j => (tops j).1) P.1 B) p (Q.N p),
          (if (M + 1) - ∑ j, ((tops j).1.toTree).order ≤ ∑ B, (fam B).low.garden.order then
            gateSummand Q.L Q.γ Q.δ (inputsF Q R) p pat dagger cut1 cut2 t s n n'
              ((mkFlowerAt P.1 P.2 fam).toData fun j =>
                kernelTrees_sign (Q.N (p + 1)) pat kind ζ (tops j).2).flowerGraft
          else 0)‖ ≤
      (2 ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) : ℝ) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) *
        ((Q.δ ^ (Q.ν / 2)) ^ ((M + 1) - 2 * Pm * (3 * Q.N (p + 1) + 1)) *
          (K * (envU Q p Pm C b * bracketW Q ζ n n' Pm b))) := by
  have hb0 : 0 ≤ b := by have : (0 : ℝ) ≤ Q.d := Nat.cast_nonneg _; linarith
  have hq0 : 0 ≤ Q.δ ^ (Q.ν / 2) := Real.rpow_nonneg hδ.le _
  have hq1 : Q.δ ^ (Q.ν / 2) ≤ 1 := hsmall'.trans (by norm_num)
  have hEW : 0 ≤ K * (envU Q p Pm C b * bracketW Q ζ n n' Pm b) :=
    mul_nonneg hK (mul_nonneg (envU_nonneg Q p C Pm b (by linarith)) (bracketW_nonneg Q ζ n n' Pm b))
  have hFl : ∀ j, (tops j).1 ≠ FTree.flower := fun j => ne_flower_of_mem_kernelTrees pat (tops j).2
  have hsign : ∀ j, ((tops j).1).sign = ζ := fun j => kernelTrees_sign (Q.N (p + 1)) pat kind ζ (tops j).2
  have hR := card_nfLeaves_tops Q p kind pat ζ Pm hNR tops
  have hJ : (M + 1) - 2 * Pm * (3 * Q.N (p + 1) + 1) ≤ (M + 1) - ∑ j, ((tops j).1.toTree).order := by
    have := sum_orders_tops_le Q p kind pat ζ Pm tops
    omega
  have hqJ := pow_le_pow_of_le_one hq0 hq1 hJ
  refine (norm_sum_le_card_mul _ _ fun P => ?_).trans
    (mul_le_mul_of_nonneg_right (card_partitions_tops Q p kind pat ζ Pm tops)
      (mul_nonneg (pow_nonneg hq0 _) hEW))
  have h := norm_tail_mk_le Q μ g a Fev R E Et p ha hL hδ hsmall' C hC hF hFl hsign hR b K hb hK P.1 P.2 hsumF
    pat hpat dagger cut1 cut2 (fun fam => hcut ⟨tops, ⟨P.1, P.2⟩, fam⟩) hpt hps n n'
    ((M + 1) - ∑ j, ((tops j).1.toTree).order) (hcw tops)
  refine h.trans ?_
  have hk : P.1.parts.card ≤ Fintype.card (GLeaf (ftop fun j => (tops j).1)) := by
    have := P.1.card_parts_le_card
    rwa [card_univ] at this
  have he := term_le_envelope Q p C kind pat ζ n n' Pm b hb0 tops P.1.parts.card hk (by linarith)
  have hBR := flowerBR_nonneg Q.L b (fun j => (tops j).1) ζ n n'
  calc (C ^ P.1.parts.card * ((Q.δ ^ (Q.ν / 2)) ^ ((M + 1) - ∑ j, ((tops j).1.toTree).order) *
        2 ^ P.1.parts.card)) * (K * flowerBR Q.L b (fun j => (tops j).1) ζ n n') =
      (Q.δ ^ (Q.ν / 2)) ^ ((M + 1) - ∑ j, ((tops j).1.toTree).order) *
        (K * ((2 * C) ^ P.1.parts.card * flowerBR Q.L b (fun j => (tops j).1) ζ n n')) := by
        rw [mul_pow]
        ring
    _ ≤ _ := mul_le_mul hqJ (mul_le_mul_of_nonneg_left he hK)
        (mul_nonneg hK (mul_nonneg (pow_nonneg (by linarith) _) hBR)) (pow_nonneg hq0 _)

omit [IsProbabilityMeasure μ] in
include ha hL hδ hsmall' hC hF hsumF hpat hpt hps hNR hcut in
/-- **The order tail.** -/
theorem norm_flowerTail_le (b K : ℝ) (hb : (Q.d : ℝ) + 1 ≤ b) (hK : 0 ≤ K)
    (hcw : CoefW Q p kind pat dagger cut1 cut2 ζ t s Pm b K) (M : ℕ) :
    ‖flowerTail Q (inputsF Q R) p kind pat dagger cut1 cut2 ζ t s n n' Pm M‖ ≤
      graftEnvelope Q.d (12 * Pm) (Q.N (p + 1)) Q.L b C *
        (Q.δ ^ (Q.ν / 2)) ^ ((M + 1) - 2 * Pm * (3 * Q.N (p + 1) + 1)) * (K * bracketW Q ζ n n' Pm b) := by
  rw [flowerTail_eq]
  refine (norm_sum_le_card_mul _ _ (norm_tail_tops_le Q μ g a Fev R E Et p ha hL hδ hsmall' C hC hF
    hsumF kind pat hpat dagger cut1 cut2 ζ t s hpt hps n n' Pm hNR hcut b K hb hK hcw M)).trans ?_
  have hq0 : 0 ≤ Q.δ ^ (Q.ν / 2) := Real.rpow_nonneg hδ.le _
  have hEW : 0 ≤ K * (envU Q p Pm C b * bracketW Q ζ n n' Pm b) :=
    mul_nonneg hK (mul_nonneg (envU_nonneg Q p C Pm b (by linarith)) (bracketW_nonneg Q ζ n n' Pm b))
  refine (mul_le_mul_of_nonneg_right (card_tops_le Q p kind pat ζ Pm)
    (mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hq0 _) hEW))).trans (le_of_eq ?_)
  rw [graftEnvelope_split]
  ring

include hG ha hrapid hL hδ hsmall hC hF hNR in
/-- The input error at fixed flower trees. -/
theorem norm_err_tops_le (b K : ℝ) (hb : (Q.d : ℝ) + 1 ≤ b) (hK : 0 ≤ K)
    (hcw : CoefW Q p kind pat dagger cut1 cut2 ζ t s Pm b K)
    (tops : Fin (2 * Pm) → ↥(kernelTrees pat (Q.N (p + 1)) kind ζ)) :
    ‖∑ Qp : Finpartition (nfLeaves fun j => (tops j).1),
      flowerError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) (altFlowerSig Pm) (fun j => (tops j).1)
        (fun j => fkCoef Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s (tops j).1) Qp (fun ω => a ω p) p (Q.N p)
        (fun _ => n) (fun _ => n')‖ ≤
      (2 ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) : ℝ) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) *
        (Real.exp (-(Q.N p : ℝ)) * (K * (envU Q p Pm C b * bracketW Q ζ n n' Pm b))) := by
  have hb0 : 0 ≤ b := by have : (0 : ℝ) ≤ Q.d := Nat.cast_nonneg _; linarith
  have he0 : 0 ≤ Real.exp (-(Q.N p : ℝ)) := (Real.exp_pos _).le
  have hEW : 0 ≤ K * (envU Q p Pm C b * bracketW Q ζ n n' Pm b) :=
    mul_nonneg hK (mul_nonneg (envU_nonneg Q p C Pm b (by linarith)) (bracketW_nonneg Q ζ n n' Pm b))
  have hsign : ∀ j, ((tops j).1).sign = ζ := fun j => kernelTrees_sign (Q.N (p + 1)) pat kind ζ (tops j).2
  have hR := card_nfLeaves_tops Q p kind pat ζ Pm hNR tops
  have hcard : (Fintype.card (Finpartition (nfLeaves fun j => (tops j).1)) : ℝ) ≤
      (2 ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) : ℝ) ^ (12 * Pm * (2 * Q.N (p + 1) + 1)) := by
    rw [Fintype.card_congr (pairPartitionEquiv fun j => (tops j).1)]
    exact card_partitions_tops Q p kind pat ζ Pm tops
  refine (norm_sum_le_card_mul _ _ fun Qp => ?_).trans (mul_le_mul_of_nonneg_right hcard (mul_nonneg he0 hEW))
  have hRP : ∀ B ∈ Qp.parts, B.card ≤ 2 * Q.R p := fun B hB => (card_le_card (Qp.le hB)).trans hR
  have h := norm_flowerError_le Q μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hsign b K hb hK
    (fun j => fkCoef Q.L Q.γ Q.δ p pat dagger cut1 cut2 t s (tops j).1) Qp hRP n n' (fun κ => hcw tops κ.1.1)
  refine h.trans ?_
  have hk : Qp.parts.card ≤ Fintype.card (GLeaf (ftop fun j => (tops j).1)) :=
    Qp.card_parts_le_card.trans (card_le_univ _)
  have he' := term_le_envelope Q p C kind pat ζ n n' Pm b hb0 tops Qp.parts.card hk (by linarith)
  calc (2 ^ Qp.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ Qp.parts.card) *
        (K * flowerBR Q.L b (fun j => (tops j).1) ζ n n') =
      Real.exp (-(Q.N p : ℝ)) * (K * ((2 * C) ^ Qp.parts.card * flowerBR Q.L b (fun j => (tops j).1) ζ n n')) := by
        rw [mul_pow]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he' hK) he0

include hG ha hrapid hL hδ hsmall hC hF hNR in
/-- **The input error.** -/
theorem norm_flowerErr_le (b K : ℝ) (hb : (Q.d : ℝ) + 1 ≤ b) (hK : 0 ≤ K)
    (hcw : CoefW Q p kind pat dagger cut1 cut2 ζ t s Pm b K) :
    ‖flowerErr Q μ a Fev R p kind pat dagger cut1 cut2 ζ t s n n' Pm‖ ≤
      graftEnvelope Q.d (12 * Pm) (Q.N (p + 1)) Q.L b C * Real.exp (-(Q.N p : ℝ)) *
        (K * bracketW Q ζ n n' Pm b) := by
  unfold flowerErr
  refine (norm_sum_le_card_mul _ _ (norm_err_tops_le Q μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF
    kind pat dagger cut1 cut2 ζ t s n n' Pm hNR b K hb hK hcw)).trans ?_
  have he0 : 0 ≤ Real.exp (-(Q.N p : ℝ)) := (Real.exp_pos _).le
  have hEW : 0 ≤ K * (envU Q p Pm C b * bracketW Q ζ n n' Pm b) :=
    mul_nonneg hK (mul_nonneg (envU_nonneg Q p C Pm b (by linarith)) (bracketW_nonneg Q ζ n n' Pm b))
  refine (mul_le_mul_of_nonneg_right (card_tops_le Q p kind pat ζ Pm)
    (mul_nonneg (by positivity) (mul_nonneg he0 hEW))).trans (le_of_eq ?_)
  rw [graftEnvelope_split]
  ring

end Sums

end WaveTurbulence.X2E
