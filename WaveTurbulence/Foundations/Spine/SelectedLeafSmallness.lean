/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafSelectionBounds
/-! Every nonempty remainder subset retains the original smallness factor in real source costs. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

 theorem leafSizeProduct_selected_le_marked {w : ℕ} (LG : LayeredGarden w)
    (S : Finset (GLeaf LG.garden.tree)) (hSI : S ⊆ inputLeaves LG.garden) (hne : S.Nonempty)
    (B₀ B₁ : (Fin w × TTree.Path) → NNReal) (ε : NNReal)
    (hB : ∀ l ∈ inputLeaves LG.garden, B₁ l.1 ≤ B₀ l.1)
    (hsmall : ∀ l ∈ S, B₁ l.1 ≤ ε * B₀ l.1) :
    leafSizeProduct LG (selectLeafBounds LG.garden S B₀ B₁) ≤
      (ε : ℝ) * leafSizeProduct LG B₀ := by
  have hh := selected_leaf_product_le_marked LG.garden S hSI hne B₀ B₁ ε hB hsmall
  unfold leafSizeProduct
  exact_mod_cast hh

/-- The standard phi/R baseline: a nonempty selected subset costs at most epsilon
 times the common phi bound to the number of actual positive leaves. -/
theorem leafSizeProduct_selected_constant_le {w : ℕ} (LG : LayeredGarden w)
    (S : Finset (GLeaf LG.garden.tree)) (hSI : S ⊆ inputLeaves LG.garden) (hne : S.Nonempty)
    (C ε : NNReal) (hC : 1 ≤ C) (hε : ε ≤ C) :
    leafSizeProduct LG (selectLeafBounds LG.garden S (fun _ => C) (fun _ => ε)) ≤
      (ε : ℝ) * (C : ℝ) ^ (inputLeaves LG.garden).card := by
  have hh := leafSizeProduct_selected_le_marked LG S hSI hne (fun _ => C) (fun _ => ε) ε
    (fun _ _ => hε) (fun _ _ => by simpa only [mul_one] using mul_le_mul_of_nonneg_left hC (show 0 ≤ ε by positivity))
  simpa only [leafSizeProduct, prod_const] using hh

end WaveTurbulence.LGSpine
