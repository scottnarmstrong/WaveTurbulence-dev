/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Omega

/-!
# Links of regular trees (packet C2)

TARGET Prop `deflink` for a paired-tree carrier `G` (B1 `Garden 1`) decoded by a chain code `X`
(B2 draft `RegChain.DecodesTree`), with links `X.treeLinks (G.sig 0)`:

* the link endpoints are exactly the branching nodes, each in one link (`tree_links_flat_nodup`,
  `tree_exists_unique_link`); `𝒩^ch` has `n(𝒯)/2` elements;
* every decoration `κ` satisfies the link relation (`tree_linkRel_of_decoration`), hence
  `ζ_{𝔫'} Ω_{𝔫'} = -ζ_𝔫 Ω_𝔫` and `{x_{𝔫'}, y_{𝔫'}} = {ζ₁ x_𝔫, ζ₂ y_𝔫}` (`tree_zeta_omega_link`,
  `tree_xy_link`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg Finset

/-! ### The pairs of a chain cover every leaf except the lone leaf, once -/

theorem card_leafAddresses {w : ℕ} (t : TTree) (a : Fin w × Path) :
    (leafAddresses t a).card = 2 * t.order + 1 := by
  rw [leafAddresses, Finset.card_image_of_injective _ (fun p q h => by
    simpa [addrExt] using h), Comb.card_leaves]

theorem pairEndpoints_card_le {α : Type*} [DecidableEq α] (P : List (α × α)) :
    (pairEndpoints P).card ≤ 2 * P.length := by
  rw [← flatPairs_toFinset, ← flatPairs_length]
  exact List.toFinset_card_le _

/-- **The pair list of a decoded chain has no repeated endpoint and avoids the lone leaf.** -/
theorem chain_pairs_flat_nodup {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (flatPairs (X.pairsAt ζ a)).Nodup ∧ addrExt a X.lonePath ∉ pairEndpoints (X.pairsAt ζ a) := by
  have hl := chain_leafAddresses X ζ .leaf a
  simp only [leafAddresses_leaf] at hl
  have hc := card_leafAddresses (X.plug ζ .leaf) a
  rw [code_plug_order, TTree.order, add_zero, hl] at hc
  have hlen := chain_pairsAt_length X ζ a
  have hle := pairEndpoints_card_le (X.pairsAt ζ a)
  have hu := Finset.card_union_le (pairEndpoints (X.pairsAt ζ a)) {addrExt a X.lonePath}
  rw [Finset.card_singleton] at hu
  have heq : (pairEndpoints (X.pairsAt ζ a)).card = 2 * (X.pairsAt ζ a).length := by omega
  refine ⟨nodup_of_card (by rw [flatPairs_toFinset, flatPairs_length, heq]), fun hm => ?_⟩
  rw [Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hm)] at hc
  omega

theorem functional_of_flat_nodup {α : Type*} {P : List (α × α)} (h : (flatPairs P).Nodup)
    {x y z : α} (hy : (x, y) ∈ symmPairs P) (hz : (x, z) ∈ symmPairs P) : y = z := by
  have get : ∀ {y : α}, (x, y) ∈ symmPairs P → ∃ p ∈ P, (x = p.1 ∧ y = p.2) ∨ (x = p.2 ∧ y = p.1) :=
    fun {y} hy => by
      rcases List.mem_append.mp hy with hy | hy
      · exact ⟨(x, y), hy, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hy
        obtain ⟨q1, q2⟩ := q
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hqe
        exact ⟨(q1, q2), hq, Or.inr ⟨hqe.1.symm, hqe.2.symm⟩⟩
  obtain ⟨p, hp, hpy⟩ := get hy
  obtain ⟨p', hp', hpz⟩ := get hz
  have e : p = p' := eq_of_flat_nodup h hp hp' (hpy.imp And.left And.left) (hpz.imp And.left And.left)
  subst e
  have hne := fst_ne_snd_of_flat_nodup h hp
  rcases hpy with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases hpz with ⟨h2, rfl⟩ | ⟨h2, rfl⟩
  · rfl
  · exact absurd (h1.symm.trans h2) hne
  · exact absurd (h2.symm.trans h1) hne
  · rfl

/-! ### Tree carriers -/

variable {V : Type*} [AddCommGroup V] {G : Garden 1} {X : RegChain}

theorem tree_eq_plug (hX : X.DecodesTree G) : G.tree 0 = X.plug (G.sig 0) .leaf := hX.1

/-- On a decoded tree carrier, every decoded pair is a pair of the carrier. -/
theorem tree_pair_of_decoded (hX : X.DecodesTree G) {p : (Fin 1 × Path) × (Fin 1 × Path)}
    (hp : p ∈ X.pairsAt (G.sig 0) (0, [])) :
    ∃ ℓ : GLeaf G.tree, ℓ.1 = p.1 ∧ (G.pair ℓ).1 = p.2 := by
  obtain ⟨hnd, hlone⟩ := chain_pairs_flat_nodup X (G.sig 0) ((0 : Fin 1), ([] : Path))
  have hleaf : p.1 ∈ leafAddresses (X.plug (G.sig 0) .leaf) ((0 : Fin 1), ([] : Path)) := by
    rw [chain_leafAddresses]
    exact Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).2 ⟨p, hp, Or.inl rfl⟩)
  have hv : p.1.2 ∈ (G.tree p.1.1).leaves := by
    have hj : p.1.1 = 0 := Subsingleton.elim _ _
    rw [hj, tree_eq_plug hX]
    simp only [leafAddresses, Finset.mem_image, addrExt] at hleaf
    obtain ⟨q, hq, hqe⟩ := hleaf
    rw [← hqe]; simpa using hq
  refine ⟨⟨p.1, hv⟩, rfl, ?_⟩
  have hne : p.1.2 ≠ X.lonePath := fun h => hlone ((mem_pairEndpoints_iff _ _).2 ⟨p, hp, Or.inl (by
    have hj : p.1.1 = 0 := Subsingleton.elim _ _
    exact Prod.ext (by simp [addrExt, hj]) (by simp [addrExt, h]))⟩)
  have h1 := hX.2.2 ⟨p.1, hv⟩ hne
  exact functional_of_flat_nodup hnd h1 (List.mem_append_left _ hp)

theorem tree_mem_pairEndpoints_links_iff (hX : X.DecodesTree G) (x : Fin 1 × Path) :
    x ∈ pairEndpoints (X.treeLinks (G.sig 0)) ↔ x.2 ∈ (G.tree x.1).branching := by
  have := chain_branchAddresses X (G.sig 0) .leaf ((0 : Fin 1), ([] : Path))
  rw [branchAddresses_leaf, Finset.union_empty] at this
  rw [RegChain.treeLinks, ← this]
  have hj : x.1 = 0 := Subsingleton.elim _ _
  rw [hj, tree_eq_plug hX]
  obtain ⟨j, p⟩ := x
  simp only at hj; subst hj
  simp [branchAddresses, addrExt]

/-- **A decoration of a decoded tree carrier decorates the chain code.** -/
theorem chainDec_of_decoration (hX : X.DecodesTree G) {κ : GNode G.tree → V}
    (hκ : IsDecoration G κ) : ChainDec (extend κ) X (G.sig 0) (0, []) := by
  refine chainDec_of_lists _ X _ _ (fun x hx => ?_) (fun p hp => ?_)
  · exact nodeRel_extend hκ ⟨x, (tree_mem_pairEndpoints_links_iff hX x).1 hx⟩
  · obtain ⟨ℓ, h1, h2⟩ := tree_pair_of_decoded hX hp
    rw [← h1, ← h2]
    show extend κ ℓ.toNode.1 = extend κ (G.pair ℓ).toNode.1
    rw [extend_node, extend_node]
    exact hκ.2 ℓ

/-- **Links of regular trees on carriers** (TARGET Prop `deflink`). -/
theorem tree_linkRel_of_decoration (hX : X.DecodesTree G) {κ : GNode G.tree → V}
    (hκ : IsDecoration G κ) : ∀ l ∈ X.treeLinks (G.sig 0), LinkRel (extend κ) G.sig l.1 l.2 :=
  linkRel_of_chainDec _ _ X _ _ (chainDec_of_decoration hX hκ) (by simp [nodeSign, pathSign])

/-- Every branching node of a decoded tree lies in exactly one link. -/
theorem tree_links_flat_nodup (X : RegChain) (ζ : ℤˣ) : (flatPairs (X.treeLinks ζ)).Nodup := by
  apply nodup_of_card
  have := chain_branchAddresses X ζ .leaf ((0 : Fin 1), ([] : Path))
  rw [branchAddresses_leaf, Finset.union_empty] at this
  rw [flatPairs_toFinset, flatPairs_length, RegChain.treeLinks, ← this, card_branchAddresses,
    code_plug_order, TTree.order, add_zero]
  have := chain_linksAt_length X ζ ((0 : Fin 1), ([] : Path))
  omega

theorem tree_exists_unique_link (hX : X.DecodesTree G) (b : GBranch G.tree) :
    ∃! l, l ∈ X.treeLinks (G.sig 0) ∧ (b.1 = l.1 ∨ b.1 = l.2) := by
  have hx : b.1 ∈ pairEndpoints (X.treeLinks (G.sig 0)) :=
    (tree_mem_pairEndpoints_links_iff hX b.1).2 b.2
  obtain ⟨l, hl, hxl⟩ := (mem_pairEndpoints_iff _ _).1 hx
  exact ⟨l, ⟨hl, hxl⟩, fun l' ⟨hl', hxl'⟩ =>
    (eq_of_flat_nodup (tree_links_flat_nodup X _) hl hl' hxl hxl').symm⟩

/-- **The `(x,y)` relation of a link of a regular tree.** -/
theorem tree_xy_link (hX : X.DecodesTree G) {κ : GNode G.tree → V} (hκ : IsDecoration G κ)
    {l : (Fin 1 × Path) × (Fin 1 × Path)} (hl : l ∈ X.treeLinks (G.sig 0))
    (b b' : GBranch G.tree) (hb : b.1 = l.1) (hb' : b'.1 = l.2) :
    ∃ s₁ s₂ : ℤˣ,
      ((xNode κ b' = (s₁ : ℤ) • xNode κ b ∧ yNode κ b' = (s₂ : ℤ) • yNode κ b) ∨
        (xNode κ b' = (s₁ : ℤ) • yNode κ b ∧ yNode κ b' = (s₂ : ℤ) • xNode κ b)) ∧
      G.sign b'.toNode = -(s₁ * s₂) * G.sign b.toNode := by
  obtain ⟨s₁, s₂, hxy, hs⟩ := tree_linkRel_of_decoration hX hκ l hl
  rw [← hb, ← hb', xv_extend, xv_extend, yv_extend, yv_extend] at hxy
  rw [← hb, ← hb'] at hs
  exact ⟨s₁, s₂, hxy, hs⟩

/-- **`ζ_{𝔫'} Ω_{𝔫'} = -ζ_𝔫 Ω_𝔫` for the links of a regular tree.** -/
theorem tree_zeta_omega_link {d : ℕ} (hX : X.DecodesTree G) {κ : GNode G.tree → Mom d}
    (hκ : IsDecoration G κ) {l : (Fin 1 × Path) × (Fin 1 × Path)}
    (hl : l ∈ X.treeLinks (G.sig 0)) (b b' : GBranch G.tree) (hb : b.1 = l.1) (hb' : b'.1 = l.2) :
    ((G.sign b'.toNode : ℤ) : ℝ) * omegaNode G κ b' =
      -(((G.sign b.toNode : ℤ) : ℝ) * omegaNode G κ b) := by
  obtain ⟨s₁, s₂, hxy, hs⟩ := tree_xy_link hX hκ hl b b' hb hb'
  rw [omegaNode_eq hκ, omegaNode_eq hκ, hs]
  have h12 : ((s₁ : ℤ) : ℝ) * ((s₂ : ℤ) : ℝ) * (((s₁ : ℤ) : ℝ) * ((s₂ : ℤ) : ℝ)) = 1 := by
    rcases Int.units_eq_one_or s₁ with rfl | rfl <;> rcases Int.units_eq_one_or s₂ with rfl | rfl <;>
      norm_num
  have key : inner ℝ (xNode κ b') (yNode κ b') =
      ((s₁ : ℤ) : ℝ) * ((s₂ : ℤ) : ℝ) * inner ℝ (xNode κ b) (yNode κ b) := by
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy, inner_smul_units, real_inner_comm,
      inner_smul_units]
    · rw [real_inner_comm]; ring
    · ring
  rw [key]
  simp only [Units.val_mul, Units.val_neg, Int.cast_mul, Int.cast_neg]
  linear_combination (-(((G.sign b.toNode : ℤ) : ℝ) * (2 * inner ℝ (xNode κ b) (yNode κ b)))) * h12

end WaveTurbulence.Links
