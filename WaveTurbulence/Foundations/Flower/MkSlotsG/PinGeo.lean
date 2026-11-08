/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Data

/-! # B3s-HELPER6 G2: the geometry of the pins and of the lower bounds

* Copied by source (see `COPIED-SHA256SUMS`; the source files import modules that construct `PieceRestB3s`, which
  ruling R187 extended): `rootLeaf`, `eq_rootLeaf` (B3s `MkSlots/IntCount.lean`), and β's pin geometry
  (`MkSlotsB/PatGeo.lean`): `fixCap_cases`, `fixCap_value`, `capPair_not_cap`, `exists_capFlower_of_card`,
  `exists_capFlower_of_capGeo`, `branch_not_cap`, `fixCap_layer`, `fixCap_val` (every pinned branch is in layer `p`;
  pinned values are `s` or `t` in `(p, p+1)`).
* New (ruling R187, the lower bounds of the general piece): `fixCap_parent_of_cfp_dParent` (in a `dParent` tree the
  parent of a capped flower parent is pinned), **`layer_parent_of_pinned_dParent`** (a free branch with a pinned child
  in a `dParent` tree lies on the capped stem, hence in layer `p`), **`mem_protI_of_child_pinned`** (the parent of a
  pinned branch is protected: `N[u] ⊆ Π`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs
open WaveTurbulence.Flower.MkSlots (layer_capFlowerParent)

namespace WaveTurbulence.Flower.MkSlotsG

variable {w : ℕ}

-- [copied] world MkSlots/IntCount.lean (sha256 in COPIED-SHA256SUMS) L33-42: `rootLeaf`, `eq_rootLeaf`.
/-- The leaf of a single-leaf tree. -/
def rootLeaf (G : Garden w) (j : Fin w) (hj : G.tree j = TTree.leaf) : GLeaf G.tree :=
  ⟨(j, []), by rw [hj]; simp [TTree.leaves]⟩

theorem eq_rootLeaf {G : Garden w} {j : Fin w} (hj : G.tree j = TTree.leaf) (ℓ : GLeaf G.tree) (hℓ : ℓ.1.1 = j) :
    ℓ = rootLeaf G j hj := by
  have hl := ℓ.2
  rw [hℓ, hj] at hl
  have hp : ℓ.1.2 = [] := by simpa [TTree.leaves] using hl
  exact Subtype.ext (Prod.ext hℓ hp)
-- [end copied]

-- [copied] world MkSlotsB/PatGeo.lean (β, sha256 in COPIED-SHA256SUMS) L42-207 (verbatim; `layer_capFlowerParent`
-- is B3s's `MkSlots.layer_capFlowerParent`).

/-! ## The four kinds of pins -/

/-- **The pins of a pattern**: a capped flower parent at `s`; otherwise the pattern's pin — a `dRoot` root at `t`, a
`dParent` parent of a capped flower parent at `s`, a `dChild i` child `i` of a capped flower parent at `s`. -/
theorem fixCap_cases {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) :
    (IsCapFlowerParent LG J b ∧ v = s) ∨
    (¬ IsCapFlowerParent LG J b ∧ pat b.1.1 = FixPat.dRoot ∧ b.1.2 = [] ∧ v = t) ∨
    (¬ IsCapFlowerParent LG J b ∧ pat b.1.1 = FixPat.dParent ∧
      (∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.IsChildOf b) ∧ v = s) ∨
    (∃ i : Fin 3, ¬ IsCapFlowerParent LG J b ∧ pat b.1.1 = FixPat.dChild i ∧
      (∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i]) ∧ v = s) := by
  unfold fixCap at h
  by_cases hc : IsCapFlowerParent LG J b
  · simp only [hc, ↓reduceIte] at h
    exact Or.inl ⟨hc, (Option.some.inj h).symm⟩
  · simp only [hc, ↓reduceIte] at h
    right
    cases hp : pat b.1.1 with
    | plain => rw [hp] at h; exact absurd h (by simp)
    | dRoot =>
      rw [hp] at h
      simp only at h
      split_ifs at h with h0
      exact Or.inl ⟨hc, rfl, h0, (Option.some.inj h).symm⟩
    | dParent =>
      rw [hp] at h
      simp only at h
      split_ifs at h with h0
      exact Or.inr (Or.inl ⟨hc, rfl, h0, (Option.some.inj h).symm⟩)
    | dChild i =>
      rw [hp] at h
      simp only at h
      split_ifs at h with h0
      exact Or.inr (Or.inr ⟨i, hc, rfl, h0, (Option.some.inj h).symm⟩)

/-- The pinned values: `s`, or `t` at a root. -/
theorem fixCap_value {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) :
    v = s ∨ (v = t ∧ b.1.2 = [] ∧ pat b.1.1 = FixPat.dRoot) := by
  rcases fixCap_cases h with ⟨-, hv⟩ | ⟨-, hp, h0, hv⟩ | ⟨-, -, -, hv⟩ | ⟨i, -, -, -, hv⟩
  · exact Or.inl hv
  · exact Or.inr ⟨hv, h0, hp⟩
  · exact Or.inl hv
  · exact Or.inl hv

/-! ## Every non-cap tree carries a capped flower (`2·|J| = w`) -/

/-- **No two cap roots are paired** in an irreducible plain garden with `2·|J| = w` and single-leaf cap trees. -/
theorem capPair_not_cap (G : Garden w) (hp : G.IsPlain) (hirr : G.Irreducible) (J : Finset (Fin w))
    (hJ : 2 * J.card = w) (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) :
    ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J := by
  intro ℓ h1 h2
  let A : Finset (Fin w) := {ℓ.1.1, (G.pair ℓ).1.1}
  have hAJ : A ⊆ J := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h1
    · rw [Finset.mem_singleton.mp hj]; exact h2
  refine hirr A ⟨ℓ.1.1, Finset.mem_insert_self _ _⟩ ?_ ?_
  · intro hA
    have hJu : J = Finset.univ := Finset.eq_univ_of_forall fun j => hAJ (hA ▸ Finset.mem_univ j)
    have hc : J.card = w := by rw [hJu, Finset.card_univ, Fintype.card_fin]
    have h0 : J.card = 0 := by omega
    exact absurd h1 (by rw [Finset.card_eq_zero.mp h0]; exact Finset.notMem_empty _)
  · intro ℓ' hℓ'
    have hne : G.pair ℓ' ≠ ℓ' := fun he => ((G.pair_eq_iff ℓ').mp he) (hp ℓ')
    refine ⟨hne, ?_⟩
    have hA' : ℓ'.1.1 ∈ A := (Finset.mem_filter.mp hℓ').2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hA' with he | he
    · have e1 := eq_rootLeaf (hcap _ h1) ℓ' he
      have e2 := eq_rootLeaf (hcap _ h1) ℓ rfl
      rw [e1, ← e2]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · have he' : ℓ'.1.1 = (G.pair ℓ).1.1 := Finset.mem_singleton.mp he
      have e1 := eq_rootLeaf (hcap _ h2) ℓ' he'
      have e2 := eq_rootLeaf (hcap _ h2) (G.pair ℓ) rfl
      rw [e1, ← e2, G.pair_pair]
      exact Finset.mem_insert_self _ _

/-- **Every non-cap tree carries a capped flower** (`2·|J| = w`, single-leaf cap trees, no two cap roots paired, at
most one capped flower per tree): the trees of the partners of the `|J|` cap roots are pairwise distinct non-cap
trees, hence all of them. -/
theorem exists_capFlower_of_card (G : Garden w) (J : Finset (Fin w)) (hJ : 2 * J.card = w)
    (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) (hcc : ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J)
    (hone : ∀ ℓ ℓ' : GLeaf G.tree, ℓ.1.1 ∉ J → (G.pair ℓ).1.1 ∈ J → ℓ'.1.1 ∉ J → (G.pair ℓ').1.1 ∈ J →
      ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ') :
    ∀ j ∉ J, ∃ ℓ : GLeaf G.tree, ℓ.1.1 ∉ J ∧ (G.pair ℓ).1.1 ∈ J ∧ ℓ.1.1 = j := by
  intro j hj
  let f : ∀ j' ∈ J, Fin w := fun j' hj' => (G.pair (rootLeaf G j' (hcap j' hj'))).1.1
  have hf : ∀ j' (hj' : j' ∈ J), f j' hj' ∈ Finset.univ \ J := fun j' hj' =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcc _ hj'⟩
  have hfl : ∀ j' (hj' : j' ∈ J), (G.pair (G.pair (rootLeaf G j' (hcap j' hj')))).1.1 ∈ J := by
    intro j' hj'
    rw [G.pair_pair]
    exact hj'
  have hinj : ∀ j₁ j₂ (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J), f j₁ h₁ = f j₂ h₂ → j₁ = j₂ := by
    intro j₁ j₂ h₁ h₂ he
    have hl := hone _ _ (hcc _ h₁) (hfl j₁ h₁) (hcc _ h₂) (hfl j₂ h₂) he
    have hr := congrArg G.pair hl
    rw [G.pair_pair, G.pair_pair] at hr
    exact congrArg (fun ℓ : GLeaf G.tree => ℓ.1.1) hr
  have hcard : (Finset.univ \ J).card ≤ J.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j', hj', he⟩ := Finset.surj_on_of_inj_on_of_card_le f hf hinj hcard j
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)
  exact ⟨G.pair (rootLeaf G j' (hcap j' hj')), hcc _ hj', hfl j' hj', he.symm⟩

/-- The capped-flower form of `exists_capFlower_of_card` on a capped component (`CapGeo`, irreducible, plain,
`2·|J| = w`). -/
theorem exists_capFlower_of_capGeo {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} (hG : CapGeo LG J p)
    (hp : LG.garden.IsPlain) (hirr : LG.garden.Irreducible) (hJ : 2 * J.card = w) :
    ∀ j ∉ J, ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j := by
  intro j hj
  obtain ⟨ℓ, h1, h2, h3⟩ := exists_capFlower_of_card LG.garden J hJ hG.cap_leaf
    (capPair_not_cap LG.garden hp hirr J hJ hG.cap_leaf)
    (fun ℓ ℓ' a1 a2 a3 a4 he => hG.one_flower ℓ ℓ' ⟨a1, a2⟩ ⟨a3, a4⟩ he) j hj
  exact ⟨ℓ, ⟨h1, h2⟩, h3⟩

/-! ## Layers and values -/

/-- A branch never lies in a cap tree. -/
theorem branch_not_cap {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} (hG : CapGeo LG J p)
    (b : GBranch LG.garden.tree) : b.1.1 ∉ J := by
  intro hb
  have h := b.2
  rw [hG.cap_leaf _ hb] at h
  simp [TTree.branching] at h

/-- **Every pinned branch is in layer `p`.** `hroot`: every non-cap tree carries a capped flower
(`exists_capFlower_of_capGeo`). -/
theorem fixCap_layer {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {pat : Fin w → FixPat} {t s : ℝ}
    (hG : CapGeo LG J p) (hpat : CapPatValid LG J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j)
    {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) :
    LG.layer b.toNode = p := by
  rcases fixCap_cases h with ⟨hc, -⟩ | ⟨-, -, h0, -⟩ | ⟨-, -, ⟨c, hc, hcb⟩, -⟩ | ⟨i, -, hpi, ⟨c, hc, h1, h2⟩, -⟩
  · exact layer_capFlowerParent hG hc
  · obtain ⟨ℓ, hℓ, hℓj⟩ := hroot b.1.1 (branch_not_cap hG b)
    refine hG.stem_layer _ ⟨ℓ, hℓ, hℓj.symm, ?_⟩
    show b.1.2 <+: ℓ.1.2
    rw [h0]
    exact List.nil_prefix
  · obtain ⟨ℓ, hℓ, hℓt, i, hℓp⟩ := hc
    obtain ⟨hcb1, i', hcb2⟩ := hcb
    refine hG.stem_layer _ ⟨ℓ, hℓ, (hℓt.trans hcb1).symm, ?_⟩
    show b.1.2 <+: ℓ.1.2
    rw [hℓp, hcb2, List.append_assoc]
    exact List.prefix_append _ _
  · refine hpat b c i hc ?_ (Prod.ext h1 h2)
    rw [← h1]
    exact hpi

/-- **`val` for the member pins**: a pinned value lies in the layer window of its branch and below the top time. -/
theorem fixCap_val {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {pat : Fin w → FixPat} {t s : ℝ}
    (hG : CapGeo LG J p) (hpat : CapPatValid LG J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j)
    (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1)
    {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) :
    (LG.layer b.toNode : ℝ) < v ∧ v ≤ LG.layer b.toNode + 1 ∧ v ≤ t := by
  rw [fixCap_layer hG hpat hroot h]
  rcases fixCap_value h with rfl | ⟨rfl, -, -⟩
  · exact ⟨hs.1, by linarith [hs.2], hs.2.le⟩
  · exact ⟨hs.1.trans hs.2, ht.le, le_rfl⟩
-- [end copied]

/-! ## The lower bounds (ruling R187) -/

/-- In a `dParent` tree, the parent of a capped flower parent is pinned. -/
theorem fixCap_parent_of_cfp_dParent {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {π u : GBranch LG.garden.tree} (hpat : pat π.1.1 = FixPat.dParent) (hu : IsCapFlowerParent LG J u)
    (huπ : u.IsChildOf π) : fixCap LG J pat t s π = some s := by
  unfold fixCap
  by_cases hπ : IsCapFlowerParent LG J π
  · simp only [hπ, ↓reduceIte]
  · simp only [hπ, ↓reduceIte, hpat]
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨u, hu, huπ⟩)

/-- **A free branch with a pinned child, in a `dParent` tree, lies in layer `p`**: the pinned child is the `dParent`
pin (the parent of a capped flower parent; a capped flower parent child would pin the branch itself, a `dRoot` pin is
a root, a `dChild` pin lies in another pattern), so the branch is an ancestor of the flower (`CapGeo.stem_layer`). -/
theorem layer_parent_of_pinned_dParent {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {pat : Fin w → FixPat}
    {t s : ℝ} (hG : CapGeo LG J p) {π u : GBranch LG.garden.tree} (hpat : pat π.1.1 = FixPat.dParent)
    (hfree : fixCap LG J pat t s π = none) (hu : (fixCap LG J pat t s u).isSome) (huπ : u.IsChildOf π) :
    LG.layer π.toNode = p := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hu
  have hπu : u.1.1 = π.1.1 := huπ.1
  rcases fixCap_cases hv with ⟨hc, -⟩ | ⟨-, -, h0, -⟩ | ⟨-, -, ⟨c₀, hc₀, hc₀u⟩, -⟩ | ⟨i, -, hpi, -, -⟩
  · rw [fixCap_parent_of_cfp_dParent hpat hc huπ] at hfree
    cases hfree
  · exfalso
    obtain ⟨-, i, hi⟩ := huπ
    rw [hi] at h0
    simp at h0
  · obtain ⟨ℓ, hℓ, hℓt, i, hℓp⟩ := hc₀
    obtain ⟨h1, i', h2⟩ := hc₀u
    obtain ⟨h3, i'', h4⟩ := huπ
    refine hG.stem_layer _ ⟨ℓ, hℓ, (hℓt.trans (h1.trans h3)).symm, ?_⟩
    show π.1.2 <+: ℓ.1.2
    rw [hℓp, h2, h4, List.append_assoc, List.append_assoc]
    exact List.prefix_append _ _
  · exfalso
    rw [hπu, hpat] at hpi
    cases hpi

/-- **The parent of a pinned branch is protected** (`N[u] ⊆ Π`, the parent case of `NearNode`). -/
theorem mem_protI_of_child_pinned {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {kSel : Fin w → Option ℕ} {π u : GBranch LG.garden.tree} (hu : (fixCap LG J pat t s u).isSome)
    (huπ : u.IsChildOf π) : π.toNode ∈ protI LG J pat t s kSel := by
  obtain ⟨h1, i, h2⟩ := huπ
  unfold protI protectedSet
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, u.toNode, ⟨h1.symm, Or.inr (Or.inl ⟨?_, ?_⟩)⟩,
    Or.inr ⟨u, rfl, Or.inl hu⟩⟩
  · show u.1.2 ≠ []
    rw [h2]
    simp
  · show π.1.2 = u.1.2.dropLast
    rw [h2, List.dropLast_concat]

end WaveTurbulence.Flower.MkSlotsG
