/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerTail
public import WaveTurbulence.Foundations.XChain.X2EDraft.CutSupport

/-!
# X2E-5, step 3: the coefficient weight

`m2Tree`: the per-tree `M₂` bound (`8/(πδL^{2γ}2^{j₂}L)` for plain with `cut2 = j₂ ≥ 1`, else `1`).
`m1Gain`: the `M₁` gain (`(2^{j₁}L/4)^{−80dP}` for `cut1 = j₁ ≥ 1`, else `1`).

**Statement** (`coef_weight_le`, `|coupling| ≤ 1`, `p < s < t ≤ p + 1`, `L ≥ 4`): with `W = ∏_{ℓ ∉ 𝔣} ⟨k_ℓ⟩`,
`‖∏_j σ_j fkCoef_j‖ W^{−Λ/2} ≤ m2Tree^{2P} m1Gain · W^{−(Λ/2 − 40d)}`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI Cpl
open scoped Classical

variable (L γ δ : ℝ) {d : ℕ}

/-- The per-tree `M₂` bound. -/
noncomputable def m2Tree (pat : FixPat) (cut2 : Option ℕ) : ℝ :=
  cut2.elim 1 fun j₂ => if pat = .plain ∧ 1 ≤ j₂ then 8 / (Real.pi * δ * L ^ (2 * γ) * (2 ^ j₂ * L)) else 1

/-- The `M₁` gain. -/
noncomputable def m1Gain (d Pm : ℕ) (cut1 : Option ℕ) : ℝ :=
  cut1.elim 1 fun j₁ => if 1 ≤ j₁ then (2 ^ j₁ * L / 4) ^ (-(80 * d * Pm : ℝ)) else 1

theorem m2Tree_nonneg (hδ : 0 < δ) (hL : 0 < L) (pat : FixPat) (cut2 : Option ℕ) : 0 ≤ m2Tree L γ δ pat cut2 := by
  have hLγ : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL _
  cases cut2 with
  | none => exact zero_le_one
  | some j₂ =>
    change 0 ≤ if pat = .plain ∧ 1 ≤ j₂ then 8 / (Real.pi * δ * L ^ (2 * γ) * (2 ^ j₂ * L)) else 1
    split_ifs
    · positivity
    · exact zero_le_one

theorem m1Gain_nonneg (hL : 0 < L) (d Pm : ℕ) (cut1 : Option ℕ) : 0 ≤ m1Gain L d Pm cut1 := by
  cases cut1 with
  | none => exact zero_le_one
  | some j₁ =>
    change 0 ≤ if 1 ≤ j₁ then (2 ^ j₁ * L / 4) ^ (-(80 * d * Pm : ℝ)) else 1
    split_ifs
    · exact Real.rpow_nonneg (by positivity) _
    · exact zero_le_one

section Bound

variable (p : ℕ) (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (t s : ℝ)

theorem norm_fkCoef_le_m2Tree (hc : |coupling d L γ δ| ≤ 1) (hδ : 0 < δ) (hL : 0 < L) (hps : (p : ℝ) < s)
    (hst : s < t) (ht : t ≤ p + 1) (F : FTree) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    ‖fkCoef L γ δ p pat dagger cut1 cut2 t s F κ‖ ≤ m2Tree L γ δ pat cut2 := by
  cases cut2 with
  | none => exact norm_fkCoef_le L γ δ p pat dagger cut1 none t s hc F κ
  | some j₂ =>
    change _ ≤ if pat = .plain ∧ 1 ≤ j₂ then 8 / (Real.pi * δ * L ^ (2 * γ) * (2 ^ j₂ * L)) else 1
    by_cases h : pat = .plain ∧ 1 ≤ j₂
    · rw [ite_eq_left h]
      obtain ⟨rfl, hj⟩ := h
      exact norm_fkCoef_plain_cut2_le L γ δ p dagger t s cut1 hc hδ hL hj hps hst ht F κ
    · rw [ite_eq_right h]
      exact norm_fkCoef_le L γ δ p pat dagger cut1 (some j₂) t s hc F κ

theorem one_le_prod_jbr {ι : Type*} (S : Finset ι) (f : ι → Mom d) : 1 ≤ ∏ l ∈ S, jbr (f l) :=
  (prod_const_one).symm.le.trans (prod_le_prod₀ (fun _ _ => zero_le_one) fun _ _ => one_le_jbr _)

theorem norm_topCoefK_le_m2 {Pm : ℕ} (hc : |coupling d L γ δ| ≤ 1) (hδ : 0 < δ) (hL : 0 < L) (hps : (p : ℝ) < s)
    (hst : s < t) (ht : t ≤ p + 1) (tops : Fin (2 * Pm) → FTree) (κ : GNode (ftop tops) → (Fin d → ℤ)) :
    ‖topCoefK L γ δ p pat dagger cut1 cut2 t s tops κ‖ ≤ m2Tree L γ δ pat cut2 ^ (2 * Pm) := by
  unfold topCoefK
  rw [norm_prod]
  have h := prod_le_prod₀ (s := (univ : Finset (Fin (2 * Pm)))) (fun j _ => norm_nonneg _)
    (fun j _ => (le_of_eq (norm_zpowSign (altFlowerSig Pm j) _)).trans
      (norm_fkCoef_le_m2Tree L γ δ p pat dagger cut1 cut2 t s hc hδ hL hps hst ht (tops j)
        (fun a => κ (singleNodeToForest (ftop tops) j a))))
  simpa only [prod_const, card_univ, Fintype.card_fin] using h

theorem topCoefK_eq_zero {Pm : ℕ} (tops : Fin (2 * Pm) → FTree) (κ : GNode (ftop tops) → (Fin d → ℤ)) (j : Fin (2 * Pm))
    (hj : fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j) (fun a => κ (singleNodeToForest (ftop tops) j a)) = 0) :
    topCoefK L γ δ p pat dagger cut1 cut2 t s tops κ = 0 := by
  unfold topCoefK
  exact prod_eq_zero (mem_univ j) (by rw [hj, zpowSign_zero])

end Bound

theorem norm_le_jbr {d : ℕ} (x : Mom d) : ‖x‖ ≤ jbr x :=
  Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg x])

/-- One large non-flower leaf per tree bounds the leaf product below. -/
theorem pow_le_prod_nf {Pm : ℕ} (tops : Fin (2 * Pm) → FTree) (f : GLeaf (ftop tops) → ℝ) (hf : ∀ l, 1 ≤ f l) {a : ℝ}
    (ha : 0 ≤ a) (Lf : Fin (2 * Pm) → GLeaf (ftop tops)) (hinj : Function.Injective Lf)
    (hmem : ∀ j, Lf j ∈ nfLeaves tops) (hbig : ∀ j, a ≤ f (Lf j)) :
    a ^ (2 * Pm) ≤ ∏ l ∈ nfLeaves tops, f l := by
  have hsub : univ.image Lf ⊆ nfLeaves tops := by
    intro l hl
    obtain ⟨j, -, rfl⟩ := mem_image.mp hl
    exact hmem j
  have h1 : a ^ (2 * Pm) ≤ ∏ j, f (Lf j) := by
    have h := prod_le_prod₀ (s := (univ : Finset (Fin (2 * Pm)))) (fun _ _ => ha) fun j _ => hbig j
    rwa [prod_const, card_univ, Fintype.card_fin] at h
  have h2 : ∏ j, f (Lf j) = ∏ l ∈ univ.image Lf, f l := (prod_image fun i _ j _ h => hinj h).symm
  have h3 : ∏ l ∈ univ.image Lf, f l ≤ ∏ l ∈ nfLeaves tops, f l :=
    prod_le_prod_of_subset_of_one_le₀ hsub (fun l _ => zero_le_one.trans (hf l)) fun l _ _ => hf l
  exact h1.trans (h2.le.trans h3)

theorem rpow_neg_le_of_pow_le {W a : ℝ} (ha : 0 < a) {Pm : ℕ} (h : a ^ (2 * Pm) ≤ W) (e : ℝ) (he : 0 ≤ e) :
    W ^ (-e) ≤ a ^ (-(2 * Pm * e)) := by
  have h' := Real.rpow_le_rpow_of_nonpos (pow_pos ha _) h (neg_nonpos.mpr he)
  refine h'.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  congr 1
  push_cast
  ring

section Weight

variable (p : ℕ) (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (t s : ℝ)

/-- The `M₁` part. -/
theorem coef_m1_le {Pm : ℕ} (hc : |coupling d L γ δ| ≤ 1) (hδ : 0 < δ) (hL4 : 4 ≤ L) (hps : (p : ℝ) < s)
    (hst : s < t) (ht : t ≤ p + 1) (tops : Fin (2 * Pm) → FTree) (κ : GNode (ftop tops) → (Fin d → ℤ)) :
    ‖topCoefK L γ δ p pat dagger cut1 cut2 t s tops κ‖ *
        (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode))) ^ (-(40 * d : ℝ)) ≤
      m2Tree L γ δ pat cut2 ^ (2 * Pm) * m1Gain L d Pm cut1 := by
  have hL : 0 < L := by linarith
  have hd0 : (0 : ℝ) ≤ 40 * d := by positivity
  have hW1 := one_le_prod_jbr (nfLeaves tops) fun l => latticePoint L (κ l.toNode)
  have hm2 := m2Tree_nonneg L γ δ hδ hL pat cut2
  have hc2 := norm_topCoefK_le_m2 L γ δ p pat dagger cut1 cut2 t s hc hδ hL hps hst ht tops κ
  have hW40 : (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode))) ^ (-(40 * d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (neg_nonpos.mpr hd0)
  have hWnn : 0 ≤ (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode))) ^ (-(40 * d : ℝ)) :=
    Real.rpow_nonneg (zero_le_one.trans hW1) _
  have hdef := mul_le_mul hc2 hW40 hWnn (pow_nonneg hm2 _)
  cases cut1 with
  | none => exact hdef
  | some j₁ =>
    change _ ≤ _ * if 1 ≤ j₁ then (2 ^ j₁ * L / 4) ^ (-(80 * d * Pm : ℝ)) else 1
    by_cases hj : 1 ≤ j₁
    · rw [ite_eq_left hj]
      by_cases hall : ∀ j, fkCoef L γ δ p pat dagger (some j₁) cut2 t s (tops j)
          (fun a => κ (singleNodeToForest (ftop tops) j a)) ≠ 0
      · have hbig := fun j => exists_big_leaf_of_fkCoef_ne L γ δ p dagger t s pat cut2 hL hj (tops j)
          (fun a => κ (singleNodeToForest (ftop tops) j a)) (hall j)
        choose ℓ hℓmem hℓbig using hbig
        have ha : (0 : ℝ) < 2 ^ j₁ * L / 4 := by positivity
        have hge := pow_le_prod_nf tops (fun l => jbr (latticePoint L (κ l.toNode))) (fun l => one_le_jbr _) ha.le
          (fun j => singleLeafToForest (ftop tops) j (ℓ j))
          (fun i j h => congrArg (fun l : GLeaf (ftop tops) => l.1.1) h)
          (fun j => (singleLeafToForest_mem_nfLeaves_iff tops j (ℓ j)).mpr (mem_erase.mp (hℓmem j)).1)
          (fun j => (hℓbig j).le.trans (norm_le_jbr _))
        have hpow := rpow_neg_le_of_pow_le ha hge (40 * d) hd0
        have he : -(2 * (Pm : ℝ) * (40 * d)) = -(80 * d * Pm : ℝ) := by ring
        rw [he] at hpow
        exact mul_le_mul hc2 hpow hWnn (pow_nonneg hm2 _)
      · push Not at hall
        obtain ⟨j, hj0⟩ := hall
        rw [topCoefK_eq_zero L γ δ p pat dagger (some j₁) cut2 t s tops κ j hj0, norm_zero, zero_mul]
        exact mul_nonneg (pow_nonneg hm2 _) (Real.rpow_nonneg (by positivity) _)
    · rw [ite_eq_right hj]
      exact hdef

/-- **The coefficient weight.** -/
theorem coef_weight_le {Pm : ℕ} (hc : |coupling d L γ δ| ≤ 1) (hδ : 0 < δ) (hL4 : 4 ≤ L) (hps : (p : ℝ) < s)
    (hst : s < t) (ht : t ≤ p + 1) (tops : Fin (2 * Pm) → FTree) (κ : GNode (ftop tops) → (Fin d → ℤ)) (Λ : ℝ) :
    ‖topCoefK L γ δ p pat dagger cut1 cut2 t s tops κ‖ *
        (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode))) ^ (-Λ / 2) ≤
      (m2Tree L γ δ pat cut2 ^ (2 * Pm) * m1Gain L d Pm cut1) *
        (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode))) ^ (-(Λ / 2 - 40 * d)) := by
  have hW1 := one_le_prod_jbr (nfLeaves tops) fun l => latticePoint L (κ l.toNode)
  have hW0 : 0 < ∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode)) := zero_lt_one.trans_le hW1
  have hsplit : (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode))) ^ (-Λ / 2) =
      (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode))) ^ (-(40 * d : ℝ)) *
        (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ l.toNode))) ^ (-(Λ / 2 - 40 * d)) := by
    rw [← Real.rpow_add hW0]
    ring_nf
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (coef_m1_le L γ δ p pat dagger cut1 cut2 t s hc hδ hL4 hps hst ht tops κ)
    (Real.rpow_nonneg hW0.le _)

end Weight


end WaveTurbulence.X2E
