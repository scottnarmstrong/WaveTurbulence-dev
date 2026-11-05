/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AllMomentProducts
public import WaveTurbulence.Foundations.XChain.TreeNormBounds
/-! Actual decoration summands retain finite moments and admit an absolute lattice envelope. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal

theorem memLp_treeSummand {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {d : ℕ} (L γ δ : ℝ) (p : ℕ) (S : TTree) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (t : ℝ) (n : Fin d → ℤ) (κ : TreeDecoration S d n) (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => treeSummand L γ δ p S (c ω) t n κ) (q : ℝ≥0∞) μ := by
  simp only [treeSummand_eq]
  apply MemLp.const_mul
  unfold leafProd
  apply memLp_prod_of_all_memLp
  intro l _ r hr
  unfold zpowSign
  split_ifs
  · exact hc _ r hr
  · exact (hc _ r hr).star
  exact hq

theorem sum_norm_treeSummand_le_l1 {d : ℕ} (L γ δ : ℝ) (p : ℕ) (S : TTree)
    {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) (t : ℝ) (n : Fin d → ℤ)
    (u : Finset (TreeDecoration S d n)) :
    (∑ κ ∈ u, ‖treeSummand L γ δ p S c t n κ‖) ≤
      boxVol S p t * (∑' m, ‖c m‖) ^ Fintype.card (GLeaf (single S)) := by
  classical
  let f : (GLeaf (single S) → (Fin d → ℤ)) → ℝ := fun z => ∏ l, ‖c (z l)‖
  let e : TreeDecoration S d n → (GLeaf (single S) → (Fin d → ℤ)) := fun κ l => κ.1 l.toNode
  have he : Function.Injective e := fun a b h =>
    Subtype.ext (treeDecoration_eq_of_leaves a b (fun l => congrFun h l))
  have hf := summable_pi_prod (fun (_ : GLeaf (single S)) m => ‖c m‖)
    (fun _ _ => norm_nonneg _) (fun _ => hc)
  have hsum : (∑ κ ∈ u, f (e κ)) ≤ (∑' z, f z) :=
    ((hf.comp_injective he).sum_le_tsum u (fun _ _ => prod_nonneg (fun _ _ => norm_nonneg _))).trans
      (tsum_comp_le_tsum_of_inj hf (fun _ => prod_nonneg (fun _ _ => norm_nonneg _)) he)
  have hpow : (∑' z, f z) ≤ (∑' m, ‖c m‖) ^ Fintype.card (GLeaf (single S)) := by
    simpa only [prod_const, card_univ] using tsum_pi_product_le
      (fun (_ : GLeaf (single S)) m => ‖c m‖) (fun _ _ => norm_nonneg _) (fun _ => hc)
  calc
    _ ≤ ∑ κ ∈ u, boxVol S p t * f (e κ) :=
      sum_le_sum (fun κ _ => norm_treeSummand_le L γ δ p S c t n κ)
    _ = boxVol S p t * ∑ κ ∈ u, f (e κ) := (mul_sum _ _ _).symm
    _ ≤ boxVol S p t * (∑' m, ‖c m‖) ^ Fintype.card (GLeaf (single S)) :=
      mul_le_mul_of_nonneg_left (hsum.trans hpow) (boxVol_nonneg _ _ _)

end WaveTurbulence.Induct
