/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SameLayer
public import WaveTurbulence.Foundations.Spine.PL234Draft.Bodies

/-!
# Single-layer leading terms: inputs, constants and the separated form (TARGET (regref1-3))

* `kernelK_congr_inputs`: the kernel depends on the inputs only at the input leaves;
* `regBound_mono`, `sourceSeparated_mono`: the bounds are monotone in `C₁`;
* `XNorm00_const_mul_le`, `XNorm00Restr_const_mul_le`: scalars come out of the order-zero norms;
* `norm_app_coeff_le`: the coefficient `2^{-n(𝒬)} ζ(𝒬) ∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1}` has modulus at most `1`;
* `sourceSeparated_app_couple`, `sourceSeparated_app_tree`: B2's single-layer leading term is a sum of at
  most `2^n` terms `δ^n 𝒥(t,s) ℳ(k)` (TARGET (layerregest4)), with the factor bounds of B2.1 (3).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

/-! ### Inputs -/

/-- The one kernel depends on the input family only at the layers of the input leaves. -/
theorem kernelK_congr_inputs (L γ δ : ℝ) {d w : ℕ} (F F' : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ)
    (h : ∀ ℓ ∈ inputLeaves LG.garden, F (LG.layer ℓ.toNode) = F' (LG.layer ℓ.toNode)) :
    kernelK L γ δ F LG up s k₀ nroot nfl = kernelK L γ δ F' LG up s k₀ nroot nfl := by
  unfold kernelK
  congr 1
  refine tsum_congr fun κ => ?_
  congr 1
  refine Finset.prod_congr rfl fun ℓ hℓ => ?_
  rw [h ℓ hℓ]

/-! ### Monotonicity in `C₁` -/

/-! ### Scalars in the order-zero norms -/

/-! ### The coefficient of a leading term -/

theorem norm_zetaOfTrees {w : ℕ} (σ : Fin w → ℤˣ) (T : Fin w → TTree) :
    ‖zetaOfTrees σ T‖ = 1 := by
  unfold zetaOfTrees
  rw [norm_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [norm_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  rcases Int.units_eq_one_or (pathSign (σ j) p) with h | h <;> simp [h]

theorem norm_specialWeight_le {w : ℕ} (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) :
    ‖specialWeight σ Z‖ ≤ 1 := by
  unfold specialWeight
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun z _ => ?_
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [norm_inv, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
  rcases Int.units_eq_one_or (nodeSign σ z) with h | h <;>
    simp [h, Complex.norm_real, abs_of_pos Real.pi_pos, inv_le_one_of_one_le₀ hpi]

/-! ### Counting special subsets -/

theorem card_specialSets_couple_le {Q : RegCpl} {n : ℕ} (hsize : Q.size = 2 * n) :
    (specialSets Q.links).card ≤ 2 ^ n := by
  have hc := card_chosenSet Q
  have hn : (chosenSet Q.links).card = n := by omega
  unfold specialSets
  refine (card_filter_le _ _).trans ?_
  rw [card_powerset, hn]

theorem card_specialSets_tree_le {X : RegChain} {n : ℕ} (hsize : X.size = 2 * n) (ζ : ℤˣ) :
    (specialSets (X.treeLinks ζ)).card ≤ 2 ^ n := by
  have hl := chain_linksAt_length X ζ ((0 : Fin 1), ([] : Path))
  have hlen : (X.treeLinks ζ).length = n := by
    unfold RegChain.treeLinks
    omega
  have hc : (chosenSet (X.treeLinks ζ)).card ≤ n := by
    unfold chosenSet
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, hlen]
  unfold specialSets
  refine (card_filter_le _ _).trans ?_
  rw [card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) hc

/-! ### The separated form of a single-layer leading term -/

end WaveTurbulence.PL234
