/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
/-! Absolute tree terms are bounded by a fixed power of the initial absolute lattice sum. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open SysAPI

theorem tsum_pi_product_le {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (f : ι → β → ℝ) (hf0 : ∀ i b, 0 ≤ f i b) (hf : ∀ i, Summable (f i)) :
    (∑' z : ι → β, ∏ i, f i (z i)) ≤ ∏ i, ∑' b, f i b := by
  apply (summable_pi_prod f hf0 hf).tsum_le_of_sum_le
  intro u
  calc
    _ ≤ ∑ z ∈ Fintype.piFinset (fun i => u.image fun z => z i), ∏ i, f i (z i) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
        (fun z _ _ => Finset.prod_nonneg fun i _ => hf0 i (z i))
      exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image_of_mem _ hz)
    _ = ∏ i, ∑ b ∈ u.image (fun z => z i), f i b := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun b _ => hf0 i b)
      (fun i _ => (hf i).sum_le_tsum _ (fun b _ => hf0 i b))

/-- A deterministic coefficient-space bound for any literal tree, with its exact leaf degree. -/
theorem norm_treeTerm_le_l1 {d : ℕ} (L γ δ : ℝ) (p : ℕ) (S : TTree)
    {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) (t : ℝ) (n : Fin d → ℤ) :
    ‖treeTerm L γ δ p S c t n‖ ≤ (‖treePrefactor L γ δ d S‖ * boxVol S p t) *
      (∑' m, ‖c m‖) ^ Fintype.card (GLeaf (single S)) := by
  classical
  have hleaf : (∑' z : GLeaf (single S) → (Fin d → ℤ), ∏ ℓ : GLeaf (single S), ‖c (z ℓ)‖) ≤
      (∑' m, ‖c m‖) ^ Fintype.card (GLeaf (single S)) := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      tsum_pi_product_le (fun (_ : GLeaf (single S)) m => ‖c m‖)
        (fun _ _ => norm_nonneg _) (fun _ => hc)
  calc
    _ ≤ ∑' m, ‖treeTerm L γ δ p S c t m‖ :=
      norm_le_tsum_norm (summable_norm_treeTerm L γ δ p S hc t) n
    _ ≤ ‖treePrefactor L γ δ d S‖ * (boxVol S p t *
        ∑' z : GLeaf (single S) → (Fin d → ℤ), ∏ ℓ : GLeaf (single S), ‖c (z ℓ)‖) :=
      tsum_norm_treeTerm_le L γ δ p S hc le_rfl
    _ ≤ ‖treePrefactor L γ δ d S‖ * (boxVol S p t *
        (∑' m, ‖c m‖) ^ Fintype.card (GLeaf (single S))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hleaf (boxVol_nonneg _ _ _)) (norm_nonneg _)
    _ = _ := by ring

end WaveTurbulence.Induct
