/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestLeafLabels
public import WaveTurbulence.Foundations.XChain.IndependentSummability
/-! Absolute decoration weights are bounded by independent top-leaf sums. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem summable_independent_prod_real {ι β : Type*} [Fintype ι] [Countable β]
    (f : ι → β → ℝ) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : ι → β => ∏ i, f i (x i)) := by
  have hc := summable_independent_prod (fun i x => (f i x : ℂ))
    (fun i => Complex.summable_ofReal.mpr (hf i))
  apply Complex.summable_ofReal.mp
  simpa only [← Complex.ofReal_prod] using hc

theorem tsum_independent_prod_real {ι β : Type*} [Fintype ι] [Countable β]
    (f : ι → β → ℝ) :
    (∑' x : ι → β, ∏ i, f i (x i)) = ∏ i, ∑' x, f i x := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_tsum, Complex.ofReal_prod] using
    tsum_independent_prod (fun i x => (f i x : ℂ))

theorem forest_weight_summable {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (v : (Fin d → ℤ) → ℝ) (hv : Summable v) :
    Summable (fun κ : ForestDecoration top d n => ∏ l : GLeaf top, v (κ.1 l.toNode)) := by
  have h := summable_independent_prod_real (fun (_ : GLeaf top) m => v m) (fun _ => hv)
  exact h.comp_injective (forestLeafLabelsEmbedding top n).injective

theorem tsum_forest_weight_le {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (v : (Fin d → ℤ) → ℝ)
    (hv : Summable v) (hn : ∀ m, 0 ≤ v m) :
    (∑' κ : ForestDecoration top d n, ∏ l : GLeaf top, v (κ.1 l.toNode)) ≤
      (∑' m, v m) ^ Fintype.card (GLeaf top) := by
  have h := summable_independent_prod_real (fun (_ : GLeaf top) m => v m) (fun _ => hv)
  have he := tsum_comp_le_tsum_of_inj h (fun x => prod_nonneg (fun l _ => hn (x l)))
    (forestLeafLabelsEmbedding top n).injective
  have ht := tsum_independent_prod_real (fun (_ : GLeaf top) m => v m)
  change (∑' κ : ForestDecoration top d n, ∏ l : GLeaf top, v (κ.1 l.toNode)) ≤
    ∑' x : GLeaf top → (Fin d → ℤ), ∏ l, v (x l) at he
  rw [ht] at he
  simpa only [prod_const, card_univ] using he

end WaveTurbulence.Induct
