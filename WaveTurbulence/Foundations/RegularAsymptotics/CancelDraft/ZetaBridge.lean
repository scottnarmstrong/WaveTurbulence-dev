/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.NetSign

/-!
# The net sign `ζ*`: B1's `Garden.zeta` and B2's `zetaOfTrees`

DH21 (defzetaq) (L900) and TARGET Def `defgarden`: `ζ*(𝒬) = ζ(𝒢) = ∏_{𝔫 ∈ 𝒩} (i ζ_𝔫)` over the branching
nodes. B1 defines it on gardens (`Garden.zeta`, a product over `GBranch`). The Wave B2 draft uses it on codes in
`RegCpl.app` / `RegChain.app` as `zetaOfTrees σ T` (a product over the branching paths of each tree).

* `garden_zeta_eq_zetaOfTrees`: `G.zeta = zetaOfTrees G.sig G.tree` for every garden.
* `zeta_eq_zetaOfTrees_of_decodes` / `zeta_eq_zetaOfTrees_of_decodesTree`: on a decoded couple (tree)
  carrier this is the B2 expression of `RegCpl.app` (`RegChain.app`).
* `zetaOfTrees_eq_links_prod` / `zetaOfTrees_tree_eq_links_prod`: code level, link by link (each branching
  node lies in exactly one link, LINKS `couple_links_flat_nodup`).
* `zetaOfTrees_eq_netSign` / `zetaOfTrees_tree_eq_netSign`: for dominant codes, the net sign of the
  enhanced-couple shape (ENHANCED `linksAt_prod`): `(−1)^{#(𝚌 ≠ 1)}`-type products.
-/

@[expose] public section

namespace WaveTurbulence.Cancel

open TTree WaveTurbulence.Reg WaveTurbulence.Links Finset

/-- The factor `i ζ_𝔫` of a branching node. -/
noncomputable def nodeFactor {w : ℕ} (σ : Fin w → ℤˣ) (z : Fin w × Path) : ℂ :=
  Complex.I * (((nodeSign σ z : ℤˣ) : ℤ) : ℂ)

/-- A product over the endpoints of a pair list without repetitions, pair by pair. -/
theorem prod_pairEndpoints {α M : Type*} [DecidableEq α] [CommMonoid M] {L : List (α × α)}
    (h : (flatPairs L).Nodup) (f : α → M) :
    ∏ z ∈ pairEndpoints L, f z = (L.map fun l => f l.1 * f l.2).prod := by
  rw [← flatPairs_toFinset, List.prod_toFinset _ h]
  clear h
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [flatPairs, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one] at ih ⊢
    rw [ih, mul_assoc]

/-- `zetaOfTrees` of a single tree placed at `(j, [])`: the product over its branching addresses. -/
theorem prod_branching_eq {w : ℕ} (σ : Fin w → ℤˣ) (j : Fin w) {ζ : ℤˣ} (hj : σ j = ζ) (T : TTree) :
    ∏ p ∈ T.branching, Complex.I * (((pathSign ζ p : ℤˣ) : ℤ) : ℂ) =
      ∏ z ∈ branchAddresses T ((j, []) : Fin w × Path), nodeFactor σ z := by
  rw [branchAddresses, Finset.prod_image (fun p _ q _ h => by simpa [addrExt] using h)]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [nodeFactor, nodeSign, addrExt, hj]

/-- **Code level: `zetaOfTrees` of a couple code is the product of its link factors.** -/
theorem zetaOfTrees_eq_links_prod (Q : RegCpl) :
    zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2] = (Q.links.map (linkFactor ![1, -1])).prod := by
  classical
  have hdisj : Disjoint (branchAddresses Q.trees.1 (((0 : Fin 2), []) : Fin 2 × Path))
      (branchAddresses Q.trees.2 (((1 : Fin 2), []) : Fin 2 × Path)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [branchAddresses, Finset.mem_image, addrExt] at hx hx'
    obtain ⟨p, -, rfl⟩ := hx
    obtain ⟨q, -, h⟩ := hx'
    simp at h
  unfold zetaOfTrees
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [prod_branching_eq (![1, -1] : Fin 2 → ℤˣ) 0 (ζ := 1) rfl,
    prod_branching_eq (![1, -1] : Fin 2 → ℤˣ) 1 (ζ := -1) rfl,
    ← Finset.prod_union hdisj, couple_branchAddresses, ← RegCpl.links,
    prod_pairEndpoints (couple_links_flat_nodup Q)]
  rfl

/-- **Code level: `zetaOfTrees` of a tree code is the product of its link factors.** -/
theorem zetaOfTrees_tree_eq_links_prod (X : RegChain) (ζ : ℤˣ) :
    zetaOfTrees ![ζ] ![X.plug ζ .leaf] = ((X.treeLinks ζ).map (linkFactor ![ζ])).prod := by
  classical
  have hb := chain_branchAddresses X ζ .leaf ((0 : Fin 1), ([] : Path))
  rw [branchAddresses_leaf, Finset.union_empty] at hb
  unfold zetaOfTrees
  rw [Fin.prod_univ_one]
  simp only [Matrix.cons_val_zero]
  rw [prod_branching_eq (![ζ] : Fin 1 → ℤˣ) 0 (ζ := ζ) rfl, hb, ← RegChain.treeLinks,
    prod_pairEndpoints (tree_links_flat_nodup X ζ)]
  rfl

/-- **The net sign of a dominant couple code** (DH21 (defzetaq); B2 `RegCpl.app` meets ENHANCED). -/
theorem zetaOfTrees_eq_netSign (Q : RegCpl) (hdom : Q.dominant = true) :
    zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2] = ((cplShape0 Q).netSign : ℂ) := by
  rw [zetaOfTrees_eq_links_prod, RegCpl.links]
  exact linksAt_prod ![1, -1] Q hdom _ _ (by simp [nodeSign, pathSign])
    (by simp [nodeSign, pathSign])

/-- **The net sign of a dominant tree code.** -/
theorem zetaOfTrees_tree_eq_netSign (X : RegChain) (hdom : X.dominant = true) (ζ : ℤˣ) :
    zetaOfTrees ![ζ] ![X.plug ζ .leaf] = ((chainTuples0 X).netSign : ℂ) := by
  rw [zetaOfTrees_tree_eq_links_prod, RegChain.treeLinks]
  exact chain_linksAt_prod ![ζ] X hdom ζ _ (by simp [nodeSign, pathSign])

end WaveTurbulence.Cancel
