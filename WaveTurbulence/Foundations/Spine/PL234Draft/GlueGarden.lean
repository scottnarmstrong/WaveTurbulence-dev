/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueDec
public import WaveTurbulence.Foundations.RegStruct.ChainSpines

/-!
# Gluing a paired tree on top of a garden (garden level)

The situation of TARGET L1236–L1241: a garden `G` whose tree `0` is the tree of a chain `X` (the top
same-layer block) with the tree `0` of a garden `G₂` plugged at its lone position, the other trees of
`G` being those of `G₂`; `G₁` is a paired tree decoded by `X`.

* `topAddr`, `botAddr`: the address maps of the two pieces (both commute with `addrExt`);
* `GlueData.ι₁`, `GlueData.ι₂`: the corresponding node maps (`ι₁` of the lone leaf is `ι₂` of the root
  `0`);
* `GlueData.branchEquiv`: the branching nodes of `G` are those of `G₁` and of `G₂`.
-/

@[expose] public section

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg

variable {w : ℕ} [NeZero w]

/-- The address map of the top chain. -/
def topAddr (x : Fin 1 × Path) : Fin w × Path := (0, x.2)

/-- The address map of the bottom garden: its tree `0` sits at the lone position `lp`. -/
def botAddr (lp : Path) (x : Fin w × Path) : Fin w × Path := if x.1 = 0 then (0, lp ++ x.2) else x

theorem topAddr_hom (x : Fin 1 × Path) (q : Path) :
    topAddr (w := w) (addrExt x q) = addrExt (topAddr x) q := rfl

theorem botAddr_hom (lp : Path) (x : Fin w × Path) (q : Path) :
    botAddr lp (addrExt x q) = addrExt (botAddr lp x) q := by
  unfold botAddr addrExt
  split_ifs with h <;> simp [List.append_assoc]

/-- **Gluing data**: `G.tree 0 = X.plug ζ (G₂.tree 0)`, the other trees of `G` are those of `G₂`, and
`G₁` is a paired tree decoded by `X` with the sign of `G`'s tree `0`. -/
structure GlueData (G : Garden w) (G₁ : Garden 1) (G₂ : Garden w) (X : RegChain) : Prop where
  tree0 : G.tree 0 = X.plug (G.sig 0) (G₂.tree 0)
  treej : ∀ j, j ≠ 0 → G.tree j = G₂.tree j
  sig : G.sig = G₂.sig
  sig1 : G₁.sig 0 = G.sig 0
  dec1 : X.DecodesTree G₁

namespace GlueData

variable {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
variable (h : GlueData G G₁ G₂ X)
include h

theorem tree1 : G₁.tree 0 = X.plug (G.sig 0) .leaf := by
  rw [h.dec1.1, h.sig1]

/-! ### Membership in the two regions -/

theorem top_node {p : Path} (hp : p ∈ (G₁.tree 0).nodes) : p ∈ (G.tree 0).nodes := by
  rw [h.tree1] at hp
  rw [h.tree0]
  by_cases hpre : X.lonePath <+: p
  · rw [plug_leaf_prefix X _ hp hpre]
    exact lonePath_mem_plug X _ _
  · exact (plug_mem_off X _ _ _ p hpre).1.mpr hp

theorem top_branch_iff (p : Path) :
    p ∈ (G₁.tree 0).branching ↔ p ∈ (G.tree 0).branching ∧ ¬ X.lonePath <+: p := by
  rw [h.tree1, h.tree0]
  constructor
  · intro hp
    have hpre : ¬ X.lonePath <+: p := by
      intro hpre
      have := plug_leaf_prefix X (G.sig 0) (TTree.branching_subset_nodes _ hp) hpre
      subst this
      exact TTree.not_mem_branching_of_mem_leaves _ (lonePath_mem_leaves X _) hp
    exact ⟨(plug_mem_off X _ _ _ p hpre).2.2.mpr hp, hpre⟩
  · rintro ⟨hp, hpre⟩
    exact (plug_mem_off X _ _ _ p hpre).2.2.mp hp

theorem top_leaf_iff (p : Path) :
    (p ∈ (G₁.tree 0).leaves ∧ p ≠ X.lonePath) ↔ p ∈ (G.tree 0).leaves ∧ ¬ X.lonePath <+: p := by
  rw [h.tree1, h.tree0]
  constructor
  · rintro ⟨hp, hne⟩
    have hpre : ¬ X.lonePath <+: p := fun hpre =>
      hne (plug_leaf_prefix X (G.sig 0) (TTree.leaves_subset_nodes _ hp) hpre)
    exact ⟨(plug_mem_off X _ _ _ p hpre).2.1.mpr hp, hpre⟩
  · rintro ⟨hp, hpre⟩
    exact ⟨(plug_mem_off X _ _ _ p hpre).2.1.mp hp, fun he => hpre (he ▸ List.prefix_refl _)⟩

theorem top_node_iff (p : Path) (hpre : ¬ X.lonePath <+: p) :
    p ∈ (G₁.tree 0).nodes ↔ p ∈ (G.tree 0).nodes := by
  rw [h.tree1, h.tree0]
  exact (plug_mem_off X _ _ _ p hpre).1.symm

theorem bot_iff (y : Fin w × Path) :
    ((botAddr X.lonePath y).2 ∈ (G.tree (botAddr X.lonePath y).1).nodes ↔ y.2 ∈ (G₂.tree y.1).nodes) ∧
    ((botAddr X.lonePath y).2 ∈ (G.tree (botAddr X.lonePath y).1).leaves ↔
      y.2 ∈ (G₂.tree y.1).leaves) ∧
    ((botAddr X.lonePath y).2 ∈ (G.tree (botAddr X.lonePath y).1).branching ↔
      y.2 ∈ (G₂.tree y.1).branching) := by
  obtain ⟨j, q⟩ := y
  unfold botAddr
  by_cases hj : j = 0
  · subst hj
    simp only [ite_true]
    rw [h.tree0]
    exact plug_mem_on X _ _ q
  · simp only [hj, ite_false]
    rw [h.treej j hj]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ### Node maps -/

/-- The node map of the top paired tree. -/
def ι₁ (x : GNode G₁.tree) : GNode G.tree :=
  ⟨topAddr x.1, h.top_node (by
    have hx : x.1.1 = 0 := Subsingleton.elim _ _
    have := x.2
    rw [hx] at this
    exact this)⟩

/-- The node map of the bottom garden. -/
def ι₂ (y : GNode G₂.tree) : GNode G.tree := ⟨botAddr X.lonePath y.1, (h.bot_iff y.1).1.mpr y.2⟩

theorem ι₁_val (x : GNode G₁.tree) : (h.ι₁ x).1 = ((0 : Fin w), x.1.2) := rfl

theorem ι₂_val (y : GNode G₂.tree) : (h.ι₂ y).1 = botAddr X.lonePath y.1 := rfl

/-- Unplugging an address of the bottom region. -/
def unbot (lp : Path) (z : Fin w × Path) : Fin w × Path :=
  if z.1 = 0 then (0, z.2.drop lp.length) else z

omit h in
theorem botAddr_unbot {lp : Path} {z : Fin w × Path} (hz : z.1 = 0 → lp <+: z.2) :
    botAddr lp (unbot lp z) = z := by
  obtain ⟨j, p⟩ := z
  unfold unbot botAddr
  by_cases hj : j = 0
  · subst hj
    obtain ⟨q, rfl⟩ := hz rfl
    simp
  · simp [hj]

omit h in
theorem unbot_botAddr (lp : Path) (y : Fin w × Path) : unbot lp (botAddr lp y) = y := by
  obtain ⟨j, p⟩ := y
  unfold unbot botAddr
  by_cases hj : j = 0
  · subst hj
    simp
  · simp [hj]

omit h in
/-- An address of the bottom region is never in the top region. -/
theorem botAddr_not_top (lp : Path) (y : Fin w × Path) :
    ¬ ((botAddr lp y).1 = 0 ∧ ¬ lp <+: (botAddr lp y).2) := by
  obtain ⟨j, p⟩ := y
  unfold botAddr
  by_cases hj : j = 0
  · subst hj
    simp [List.prefix_append]
  · simp [hj]

/-! ### Branching nodes -/

theorem branch_top {b : GBranch G.tree} (hb : b.1.1 = 0 ∧ ¬ X.lonePath <+: b.1.2) :
    b.1.2 ∈ (G₁.tree ((0 : Fin 1), b.1.2).1).branching := by
  have hm := b.2
  rw [hb.1] at hm
  exact (h.top_branch_iff _).mpr ⟨hm, hb.2⟩

theorem branch_bot {b : GBranch G.tree} (hb : ¬ (b.1.1 = 0 ∧ ¬ X.lonePath <+: b.1.2)) :
    (unbot X.lonePath b.1).2 ∈ (G₂.tree (unbot X.lonePath b.1).1).branching := by
  have he : botAddr X.lonePath (unbot X.lonePath b.1) = b.1 :=
    botAddr_unbot fun h0 => by
      by_contra hne
      exact hb ⟨h0, hne⟩
  have := (h.bot_iff (unbot X.lonePath b.1)).2.2
  rw [he] at this
  exact this.mp b.2

theorem branch_ofTop (x : GBranch G₁.tree) : (topAddr (w := w) x.1).2 ∈
    (G.tree (topAddr (w := w) x.1).1).branching := by
  have hx : x.1.1 = 0 := Subsingleton.elim _ _
  have hm := x.2
  rw [hx] at hm
  exact ((h.top_branch_iff _).mp hm).1

theorem branch_ofBot (y : GBranch G₂.tree) : (botAddr X.lonePath y.1).2 ∈
    (G.tree (botAddr X.lonePath y.1).1).branching :=
  (h.bot_iff y.1).2.2.mpr y.2

/-- The branching nodes of `G`, sorted into the two pieces. -/
noncomputable def toSum (b : GBranch G.tree) : GBranch G₁.tree ⊕ GBranch G₂.tree := by
  classical
  exact if hb : b.1.1 = 0 ∧ ¬ X.lonePath <+: b.1.2 then .inl ⟨((0 : Fin 1), b.1.2), h.branch_top hb⟩
    else .inr ⟨unbot X.lonePath b.1, h.branch_bot hb⟩

/-- The branching nodes of the two pieces, placed in `G`. -/
def ofSum : GBranch G₁.tree ⊕ GBranch G₂.tree → GBranch G.tree
  | .inl x => ⟨topAddr x.1, h.branch_ofTop x⟩
  | .inr y => ⟨botAddr X.lonePath y.1, h.branch_ofBot y⟩

theorem ofSum_toSum (b : GBranch G.tree) : h.ofSum (h.toSum b) = b := by
  classical
  unfold toSum
  by_cases hb : b.1.1 = 0 ∧ ¬ X.lonePath <+: b.1.2
  · rw [dite_eq_left hb]
    apply Subtype.ext
    obtain ⟨⟨j, p⟩, _⟩ := b
    simp only at hb
    show ((0 : Fin w), p) = (j, p)
    rw [hb.1]
  · rw [dite_eq_right hb]
    apply Subtype.ext
    exact botAddr_unbot fun h0 => by
      by_contra hne
      exact hb ⟨h0, hne⟩

theorem toSum_ofSum (z : GBranch G₁.tree ⊕ GBranch G₂.tree) : h.toSum (h.ofSum z) = z := by
  classical
  rcases z with x | y
  · have hx : ¬ X.lonePath <+: x.1.2 := by
      have hx0 : x.1.1 = 0 := Subsingleton.elim _ _
      have hm := x.2
      rw [hx0] at hm
      exact ((h.top_branch_iff _).mp hm).2
    have hc : (h.ofSum (.inl x)).1.1 = 0 ∧ ¬ X.lonePath <+: (h.ofSum (.inl x)).1.2 := ⟨rfl, hx⟩
    unfold toSum
    rw [dite_eq_left hc]
    congr 1
    apply Subtype.ext
    obtain ⟨⟨j, p⟩, _⟩ := x
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rfl
  · have hc : ¬ ((h.ofSum (.inr y)).1.1 = 0 ∧ ¬ X.lonePath <+: (h.ofSum (.inr y)).1.2) :=
      botAddr_not_top _ _
    unfold toSum
    rw [dite_eq_right hc]
    congr 1
    exact Subtype.ext (unbot_botAddr _ _)

/-- **The branching nodes of `G` are those of `G₁` and of `G₂`.** -/
noncomputable def branchEquiv : GBranch G.tree ≃ GBranch G₁.tree ⊕ GBranch G₂.tree where
  toFun := h.toSum
  invFun := h.ofSum
  left_inv := h.ofSum_toSum
  right_inv := h.toSum_ofSum

@[simp] theorem branchEquiv_symm_inl (x : GBranch G₁.tree) :
    (h.branchEquiv.symm (.inl x)).1 = topAddr x.1 := rfl

@[simp] theorem branchEquiv_symm_inr (y : GBranch G₂.tree) :
    (h.branchEquiv.symm (.inr y)).1 = botAddr X.lonePath y.1 := rfl

end GlueData

end WaveTurbulence.PL234
