/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeafGardenKernel
public import WaveTurbulence.Foundations.XChain.LeafPairRootFacts
/-! The zero-order pair kernel is exactly the diagonal two-point input. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem kernelK_leafPair {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2)
    (ht : ∀ j, LG.garden.tree j = TTree.leaf) (hplain : LG.garden.IsPlain)
    (p : ℕ) (hl : ∀ a, LG.layer a = p) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (k₀ : Mom d) (n : Fin 2 → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelK L γ δ F LG up s k₀ n nfl = if n 0 = n 1 then (F p (k₀ + latticePoint L (n 0)) : ℂ) else 0 := by
  classical
  rw [kernelK_leafGarden L γ δ F LG ht hplain]
  by_cases h : n 0 = n 1
  · rw [ite_eq_left ((leafPair_matched_iff LG.garden ht hplain n).mpr h), ite_eq_left h]
    apply leafPair_input_prod_const LG.garden ht hplain
    intro l
    have hn : ∀ j, n j = n 0 := by
      intro j
      fin_cases j
      · rfl
      · exact h.symm
    rw [hl, hn l.1.1]
  · rw [ite_eq_right (fun hm => h ((leafPair_matched_iff LG.garden ht hplain n).mp hm)), ite_eq_right h]

theorem KG_leafPair {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2)
    (ht : ∀ j, LG.garden.tree j = TTree.leaf) (hplain : LG.garden.IsPlain)
    (p : ℕ) (hl : ∀ a, LG.layer a = p) (t : ℝ) (n : Fin 2 → (Fin d → ℤ)) :
    KG L γ δ F LG t n = if n 0 = n 1 then (F p (latticePoint L (n 0)) : ℂ) else 0 := by
  simpa only [zero_add, KG] using kernelK_leafPair L γ δ F LG ht hplain p hl (fun _ => t) 0 0 n 0

end WaveTurbulence.Induct
