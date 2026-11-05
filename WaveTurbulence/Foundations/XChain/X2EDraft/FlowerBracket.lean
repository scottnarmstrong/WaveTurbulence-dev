/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerExp
public import WaveTurbulence.Foundations.XChain.ForestRootWeights
public import WaveTurbulence.Foundations.XChain.BracketWeightSplit
public import WaveTurbulence.Foundations.XChain.ForestBracketWeightSum

/-!
# X2E-4, step 1: the flower forest bracket bound

For flower trees `tops` of flower sign `ζ`, root labels `n` and flower labels `n'`, momentum conservation gives
`n_j − ζ n'_j = ∑_{ℓ ≠ 𝔣, ℓ ∈ 𝒯_j} ±k_ℓ`, hence `⟨n_j − ζ n'_j⟩ ≤ 2^{#} ∏ ⟨k_ℓ⟩` (`flower_root_jbr_le`).

**Statements.**
- `tsum_flower_bracket_weight_le`: `∑_κ (∏_{ℓ ∉ 𝔣} ⟨k_ℓ⟩)^{−2b} ≤ 2^{b #} (∏_j ⟨n_j − ζ n'_j⟩)^{−b} S_b^{#}`;
- `norm_tsum_le_of_flower_bracket_bound`: the same for a series dominated by that weight.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI
open scoped Classical

section Bracket

variable {w d : ℕ} (tops : Fin w → FTree)

/-- The non-flower leaves of tree `j`. -/
noncomputable def nfOf (j : Fin w) : Finset (GLeaf (ftop tops)) := (nfLeaves tops).filter fun l => l.1.1 = j

theorem flowerAt_notMem_nfOf (j : Fin w) : flowerAt tops j ∉ nfOf tops j := fun h =>
  flowerAt_notMem_nfLeaves tops j (mem_filter.mp h).1

theorem leavesBelow_root_eq (j : Fin w) :
    (GNode.root (ftop tops) j).leavesBelow = insert (flowerAt tops j) (nfOf tops j) := by
  rw [root_leavesBelow_eq_filter]
  ext l
  rw [mem_filter, mem_insert, nfOf, mem_filter]
  constructor
  · rintro ⟨-, hl⟩
    by_cases hn : l ∈ nfLeaves tops
    · exact Or.inr ⟨hn, hl⟩
    · left
      rw [eq_flowerAt_of_notMem_nfLeaves tops hn, hl]
  · rintro (rfl | ⟨-, hl⟩)
    · exact ⟨mem_univ _, rfl⟩
    · exact ⟨mem_univ _, hl⟩

variable {ζ : ℤˣ} (hsgn : ∀ j, (tops j).sign = ζ)

include hsgn in
theorem nodeSign_one_flowerAt (j : Fin w) : nodeSign (fun _ : Fin w => (1 : ℤˣ)) (flowerAt tops j).1 = ζ := by
  rw [flowerAt_val]
  change TTree.pathSign 1 (tops j).flowerPath = ζ
  rw [← sign_eq_pathSign, hsgn j]

include hsgn in
/-- **Momentum conservation in a flower tree.** -/
theorem flower_root_jbr_le {n n' : Fin w → (Fin d → ℤ)} (κ : FlowerForestDec tops d n n') (L : ℝ) (j : Fin w) :
    jbr (latticePoint L (n j - (ζ : ℤ) • n' j)) ≤
      2 ^ (nfOf tops j).card * ∏ l ∈ nfOf tops j, jbr (latticePoint L (κ.1.1 l.toNode)) := by
  have h := sum_rule (fun _ : Fin w => (1 : ℤˣ)) κ.1.1 κ.1.2.1 (GNode.root (ftop tops) j)
  have hs : nodeSign (fun _ : Fin w => (1 : ℤˣ)) (GNode.root (ftop tops) j).1 = 1 := by
    simp [nodeSign, GNode.root, TTree.pathSign]
  rw [hs, Units.val_one, one_smul, κ.1.2.2 j, leavesBelow_root_eq, sum_insert (flowerAt_notMem_nfOf tops j),
    nodeSign_one_flowerAt tops hsgn j, κ.2 j] at h
  have hr : n j - (ζ : ℤ) • n' j =
      ∑ l ∈ nfOf tops j, ((nodeSign (fun _ : Fin w => (1 : ℤˣ)) l.1 : ℤˣ) : ℤ) • κ.1.1 l.toNode := by
    rw [h]
    abel
  rw [hr]
  have hm : latticePoint L (∑ l ∈ nfOf tops j, ((nodeSign (fun _ : Fin w => (1 : ℤˣ)) l.1 : ℤˣ) : ℤ) •
      κ.1.1 l.toNode) = ∑ l ∈ nfOf tops j,
        latticePoint L (((nodeSign (fun _ : Fin w => (1 : ℤˣ)) l.1 : ℤˣ) : ℤ) • κ.1.1 l.toNode) :=
    map_sum (latticePointAddHom L) _ _
  rw [hm]
  have hb := jbr_finset_sum_le (nfOf tops j)
    (fun l => latticePoint L (((nodeSign (fun _ : Fin w => (1 : ℤˣ)) l.1 : ℤˣ) : ℤ) • κ.1.1 l.toNode))
  simpa only [latticePoint_units_smul, jbr_units_smul] using hb

include hsgn in
theorem flower_roots_jbr_le {n n' : Fin w → (Fin d → ℤ)} (κ : FlowerForestDec tops d n n') (L : ℝ) :
    (∏ j, jbr (latticePoint L (n j - (ζ : ℤ) • n' j))) ≤
      2 ^ (nfLeaves tops).card * ∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode)) := by
  have h := prod_le_prod₀ (s := (univ : Finset (Fin w))) (fun j _ => (jbr_pos _).le)
    (fun j _ => flower_root_jbr_le tops hsgn κ L j)
  have hc : ∑ j, (nfOf tops j).card = (nfLeaves tops).card :=
    (card_eq_sum_card_fiberwise (f := fun l : GLeaf (ftop tops) => l.1.1) fun _ _ => mem_univ _).symm
  have hp : ∏ j, ∏ l ∈ nfOf tops j, jbr (latticePoint L (κ.1.1 l.toNode)) =
      ∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode)) :=
    prod_fiberwise_of_maps_to (g := fun l : GLeaf (ftop tops) => l.1.1) (fun _ _ => mem_univ _) _
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, hc, hp] at h
  exact h

include hsgn in
/-- **The flower forest bracket bound.** -/
theorem tsum_flower_bracket_weight_le {n n' : Fin w → (Fin d → ℤ)} (L b : ℝ) (hL : 1 ≤ L)
    (hb : (d : ℝ) + 1 ≤ b) :
    (∑' κ : FlowerForestDec tops d n n',
      (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode))) ^ (-(2 * b))) ≤
      (2 ^ (nfLeaves tops).card : ℝ) ^ b * (∏ j, jbr (latticePoint L (n j - (ζ : ℤ) • n' j))) ^ (-b) *
        (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ^ (nfLeaves tops).card := by
  have hb0 : 0 ≤ b := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  let v : (Fin d → ℤ) → ℝ := fun m => jbr (latticePoint L m) ^ (-b)
  let A : ℝ := (2 ^ (nfLeaves tops).card : ℝ) ^ b * (∏ j, jbr (latticePoint L (n j - (ζ : ℤ) • n' j))) ^ (-b)
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (prod_nonneg fun j _ => (jbr_pos _).le) _)
  have hv : Summable v := summable_lattice_bracket_weight L b hL hb
  have hn : ∀ m, 0 ≤ v m := fun m => Real.rpow_nonneg (jbr_pos _).le _
  let e : FlowerForestDec tops d n n' → ((l : ↥(nfLeaves tops)) → (Fin d → ℤ)) := fun κ l => κ.1.1 l.1.toNode
  have he : Function.Injective e := fun a c hac =>
    flowerForestDec_eq_of_nf tops a c (fun l hl => congrFun hac ⟨l, hl⟩)
  have hpi := summable_independent_prod_real (fun (_ : ↥(nfLeaves tops)) m => v m) (fun _ => hv)
  have hcomp (κ : FlowerForestDec tops d n n') :
      ∏ l ∈ nfLeaves tops, v (κ.1.1 l.toNode) = ∏ l : ↥(nfLeaves tops), v (e κ l) :=
    (prod_coe_sort (nfLeaves tops) (fun l => v (κ.1.1 l.toNode))).symm
  have hsv : Summable fun κ : FlowerForestDec tops d n n' => ∏ l ∈ nfLeaves tops, v (κ.1.1 l.toNode) :=
    (hpi.comp_injective he).congr fun κ => (hcomp κ).symm
  have hbound (κ : FlowerForestDec tops d n n') :
      (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode))) ^ (-(2 * b)) ≤
        A * ∏ l ∈ nfLeaves tops, v (κ.1.1 l.toNode) := by
    have hX : 0 < ∏ j, jbr (latticePoint L (n j - (ζ : ℤ) • n' j)) := prod_pos fun j _ => jbr_pos _
    have hY : 0 < ∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode)) := prod_pos fun l _ => jbr_pos _
    have h := rpow_neg_split_le hX hY (by positivity) hb0 (flower_roots_jbr_le tops hsgn κ L)
    have hr := Real.finsetProd_rpow (nfLeaves tops) (fun l => jbr (latticePoint L (κ.1.1 l.toNode)))
      (fun l _ => (jbr_pos _).le) (-b)
    rw [← hr] at h
    exact h
  have hsum : Summable fun κ : FlowerForestDec tops d n n' =>
      (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode))) ^ (-(2 * b)) :=
    Summable.of_nonneg_of_le (fun κ => Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _) hbound
      (hsv.mul_left A)
  have htot : (∑' κ : FlowerForestDec tops d n n', ∏ l ∈ nfLeaves tops, v (κ.1.1 l.toNode)) ≤
      (∑' m, v m) ^ (nfLeaves tops).card := by
    have hle := tsum_comp_le_tsum_of_inj hpi (fun x => prod_nonneg fun l _ => hn (x l)) he
    rw [tsum_independent_prod_real] at hle
    simp only [prod_const, card_univ, Fintype.card_coe] at hle
    refine (tsum_congr fun κ => hcomp κ).trans_le ?_
    exact hle
  calc _ ≤ ∑' κ : FlowerForestDec tops d n n', A * ∏ l ∈ nfLeaves tops, v (κ.1.1 l.toNode) :=
        hsum.tsum_le_tsum hbound (hsv.mul_left A)
    _ = A * ∑' κ : FlowerForestDec tops d n n', ∏ l ∈ nfLeaves tops, v (κ.1.1 l.toNode) := tsum_mul_left
    _ ≤ A * (∑' m, v m) ^ (nfLeaves tops).card := mul_le_mul_of_nonneg_left htot hA

include hsgn in
/-- **A series dominated by the flower forest weight.** -/
theorem norm_tsum_le_of_flower_bracket_bound {n n' : Fin w → (Fin d → ℤ)} (L b M : ℝ) (hL : 1 ≤ L)
    (hb : (d : ℝ) + 1 ≤ b) (hM : 0 ≤ M) (f : FlowerForestDec tops d n n' → ℂ)
    (hf : ∀ κ, ‖f κ‖ ≤ M * (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode))) ^ (-(2 * b))) :
    ‖∑' κ, f κ‖ ≤ M * ((2 ^ (nfLeaves tops).card : ℝ) ^ b *
      (∏ j, jbr (latticePoint L (n j - (ζ : ℤ) • n' j))) ^ (-b) *
        (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ^ (nfLeaves tops).card) := by
  have hb2 : (d : ℝ) + 1 ≤ 2 * b := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hs : Summable fun κ : FlowerForestDec tops d n n' =>
      M * (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode))) ^ (-(2 * b)) := by
    let v : (Fin d → ℤ) → ℝ := fun m => jbr (latticePoint L m) ^ (-(2 * b))
    have hv : Summable v := summable_lattice_bracket_weight L (2 * b) hL hb2
    let e : FlowerForestDec tops d n n' → ((l : ↥(nfLeaves tops)) → (Fin d → ℤ)) := fun κ l => κ.1.1 l.1.toNode
    have he : Function.Injective e := fun a c hac =>
      flowerForestDec_eq_of_nf tops a c (fun l hl => congrFun hac ⟨l, hl⟩)
    have hpi := summable_independent_prod_real (fun (_ : ↥(nfLeaves tops)) m => v m) (fun _ => hv)
    refine ((hpi.comp_injective he).mul_left M).congr fun κ => ?_
    simp only [Function.comp_apply, e, v]
    rw [prod_coe_sort (nfLeaves tops) (fun l => jbr (latticePoint L (κ.1.1 l.toNode)) ^ (-(2 * b))),
      ← Real.finsetProd_rpow _ _ (fun l _ => (jbr_pos _).le)]
  have hnrm : Summable fun κ => ‖f κ‖ := Summable.of_nonneg_of_le (fun κ => norm_nonneg _) hf hs
  calc ‖∑' κ, f κ‖ ≤ ∑' κ, ‖f κ‖ := norm_tsum_le_tsum_norm hnrm
    _ ≤ ∑' κ : FlowerForestDec tops d n n',
        M * (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode))) ^ (-(2 * b)) :=
      hnrm.tsum_le_tsum hf hs
    _ = M * ∑' κ : FlowerForestDec tops d n n',
        (∏ l ∈ nfLeaves tops, jbr (latticePoint L (κ.1.1 l.toNode))) ^ (-(2 * b)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_flower_bracket_weight_le tops hsgn L b hL hb) hM

end Bracket

end WaveTurbulence.X2E
