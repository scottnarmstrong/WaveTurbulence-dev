/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeafForestRoots
public import WaveTurbulence.Foundations.XChain.LeafGardenDecoration
/-! A plain two-root leaf garden pairs the two roots and has exactly one positive input. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem leafPair_pair_root_zero (G : Garden 2) (ht : ∀ j, G.tree j = TTree.leaf) (hplain : G.IsPlain) :
    (G.pair (leafRoot G.tree ht 0)).1.1 = 1 := by
  have hn : (G.pair (leafRoot G.tree ht 0)).1.1 ≠ 0 := by
    intro hr
    have he : G.pair (leafRoot G.tree ht 0) = leafRoot G.tree ht 0 :=
      (leafForestLeafEquiv G.tree ht).injective hr
    exact ((G.pair_eq_iff _).mp he) (hplain _)
  apply Fin.ext
  have hb := (G.pair (leafRoot G.tree ht 0)).1.1.isLt
  have hn' : (G.pair (leafRoot G.tree ht 0)).1.1.val ≠ 0 := fun h => hn (Fin.ext h)
  omega

theorem leafPair_sig_one (G : Garden 2) (ht : ∀ j, G.tree j = TTree.leaf) (hplain : G.IsPlain) :
    G.sig 1 = -G.sig 0 := by
  let l := leafRoot G.tree ht 0
  have he : G.pair l = leafRoot G.tree ht 1 :=
    (leafForestLeafEquiv G.tree ht).injective (leafPair_pair_root_zero G ht hplain)
  have hs := G.pair_sign l (fun h => ((G.pair_eq_iff l).mp h) (hplain l))
  rw [he] at hs
  simpa only [l, leafRoot, nodeSign, TTree.pathSign, List.count_nil, pow_zero, mul_one] using hs

theorem leafPair_matched_iff {d : ℕ} (G : Garden 2) (ht : ∀ j, G.tree j = TTree.leaf)
    (hplain : G.IsPlain) (n : Fin 2 → (Fin d → ℤ)) : LeafRootMatched G n ↔ n 0 = n 1 := by
  constructor
  · intro h
    have he := h (leafRoot G.tree ht 0)
    exact he.trans (congrArg n (leafPair_pair_root_zero G ht hplain))
  · intro h
    have hn : ∀ j, n j = n 0 := by
      intro j
      fin_cases j
      · rfl
      · exact h.symm
    intro l
    exact (hn l.1.1).trans (hn (G.pair l).1.1).symm

theorem leafPair_input_prod_const (G : Garden 2) (ht : ∀ j, G.tree j = TTree.leaf)
    (hplain : G.IsPlain) (f : GLeaf G.tree → ℂ) (z : ℂ) (hf : ∀ l, f l = z) :
    (∏ l ∈ inputLeaves G, f l) = z := by
  classical
  unfold inputLeaves
  rw [prod_filter]
  have he := Fintype.prod_equiv (leafForestLeafEquiv G.tree ht)
    (fun l => if G.sign l.toNode = 1 ∧ G.mark l = none then f l else 1)
    (fun j => if G.sig j = 1 then z else 1) (fun l => by
      rw [leafForest_sign G ht l, hplain l, hf l]
      simp only [and_true]
      rfl)
  rw [he, Fin.prod_univ_two, leafPair_sig_one G ht hplain]
  rcases Int.units_eq_one_or (G.sig 0) with h | h <;> simp [h]

end WaveTurbulence.Induct
