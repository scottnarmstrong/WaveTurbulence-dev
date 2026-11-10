/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntWeight
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.FwNode
public import WaveTurbulence.Foundations.Molecule.CLBoundaryRoots
public import WaveTurbulence.Foundations.Molecule.LFTwist.LFConstruction

/-! # B3s MK-SLOTS (integration): the pinned cap-slot kernel depends only on the native couple

For a cap pair `q` of a skeleton (`IsCapPair`) of a reconstruction `LG = layeredReconstruction D hS layer hLayer`
satisfying the capped geometry `CapGeo LG J p`, the pinned weighted slot kernel
`slotFnNWF … (anchProfiles …) (capNodeW …) … (fixCap … plain) (.inl q)` is a function of the layered native couple
`N = nativeCoupleLayered D hS layer hLayer q`, of the tree indices `(coupleRoot D hS q i).1` of its two roots and of
the last letters `(coupleRoot D hS q i).2.getLast?` of their addresses only (**`capSlot_transfer`**).

Every ingredient of the slot kernel at a couple node `a` (embedded by address prefixing, `capT_emb`) is read on `N`:
* the anchored profile (`capT_prof_eq`): the pair trees of `emb a` are the root indices of the sides of `a` and of its
  partner in `N` (the induced pairing is the ambient one, `inducedGarden_pair`), the layer of `emb a` is the `N`-layer;
* the plain pins (`capT_fix_eq`): `emb b` is a capped flower parent iff `b` is one in `N` read through the root
  indices (`capT_cfp_iff`);
* the frontier weight (`capT_fw_eq`): at a non-root couple node the parent is in the couple (`fwNode_embed`); at a
  couple root it is `1`, since a cap root is a garden root (cap trees are single leaves) and a non-garden root is an
  ancestor of the capped flower of the couple (the partner of the cap leaf, `capT_root_flower`), hence in layer `p`
  (`CapGeo.stem_layer`);
* the dagger weight (`capT_par_eq`, `capT_ch_nonroot`, `capT_ch_root`): the parent factor and the child factor at a
  non-root node are read on `N` (signs: `subforest_node_sign`); at a couple root `r` that is not a garden root, the
  ambient parent `B₀` is outside the couple: it is a capped flower parent iff `emb r` is the capped flower (otherwise
  `B₀` would have a second capped flower in the tree of the flower inside the couple, `CapGeo.one_flower`), and then
  the factor is `exp(-i θ_{B₀} ε_i ‖x‖²)` with `i` the last letter of the root address and `sign B₀` determined by
  `sign (emb r)` and `i` (`Mole.child_sign_formula`).

Hence `slotFnNWF … (.inl q) = capT_kernel … N ri rl` (`capT_slot_eq`), a kernel defined from `N`, the root indices `ri`
and the last letters `rl` alone, and the transfer follows by rewriting with `N₁ = N₂`.

* `capT_IsFl`, `capT_IsFP`, `capT_pt`, `capT_prof`, `capT_par`, `capT_ch`, `capT_dag`, `capT_fw`, `capT_nodeW`,
  `capT_kernel`: the couple-intrinsic objects;
* `capT_prof_eq`, `capT_fix_eq`, `capT_nodeW_eq`: the identification on an arbitrary completely paired rooted
  subforest with two roots (`rootedLayeredGarden`);
* `capT_slot_eq`, **`capSlot_transfer`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlots.IntCapT

open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

variable {w d : ℕ}

/-- The angle `π σ δ L^{2γ} s` of the removed phase of a branch of sign `σ` (`capTheta` is its value at the
sign of the branch). -/
def capT_theta (L γ δ s : ℝ) (σ : ℤˣ) : ℝ := Real.pi * ((σ : ℤ) : ℝ) * δ * L ^ (2 * γ) * s

/-- A capped flower of a couple `N` read through the root indices `ri`: its side is not a cap tree, the side of its
partner is. -/
def capT_IsFl (N : LayeredGarden 2) (ri : Fin 2 → Fin w) (J : Finset (Fin w)) (l : GLeaf N.garden.tree) : Prop :=
  ri l.1.1 ∉ J ∧ ri (N.garden.pair l).1.1 ∈ J

/-- A capped flower parent of a couple `N` read through the root indices `ri`. -/
def capT_IsFP (N : LayeredGarden 2) (ri : Fin 2 → Fin w) (J : Finset (Fin w)) (c : GBranch N.garden.tree) : Prop :=
  ∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ c.IsParentOf l

/-- The parent factor of the removed phase at a couple node. -/
def capT_par (L γ δ s : ℝ) (J : Finset (Fin w)) (N : LayeredGarden 2) (ri : Fin 2 → Fin w)
    (a : GNode N.garden.tree) (x : Mom d) : ℂ :=
  if ∃ c : GBranch N.garden.tree, c.toNode = a ∧ capT_IsFP N ri J c then
    Complex.exp (((capT_theta L γ δ s (N.garden.sign a) * ‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I)
  else 1

/-- The child factor of the removed phase at a couple node. -/
def capT_ch (L γ δ s : ℝ) (J : Finset (Fin w)) (cc : Fin w → Fin 3 → Mom d) (N : LayeredGarden 2)
    (ri : Fin 2 → Fin w) (rl : Fin 2 → Option (Fin 3)) (a : GNode N.garden.tree) (x : Mom d) : ℂ :=
  if ha : a.1.2 = [] then
    (rl a.1.1).elim 1 fun i =>
      if ∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ l.toNode = a then
        Complex.exp (((-(capT_theta L γ δ s (if i = 1 then -N.garden.sign a else N.garden.sign a) *
          childSign i * ‖x‖ ^ 2) : ℝ) : ℂ) * Complex.I)
      else 1
  else
    if capT_IsFP N ri J (a.parent ha) then
      Complex.exp (((-(capT_theta L γ δ s (N.garden.sign (a.parent ha).toNode) * childSign (a.1.2.getLast ha) *
          ‖x‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
        (if ∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ l.toNode = a then 1 else
          if x = cc (ri a.1.1) (a.1.2.getLast ha) then 1 else 0)
    else 1

/-- The dagger node weight at a couple node. -/
def capT_dag (L γ δ s : ℝ) (J : Finset (Fin w)) (dag : Option (Fin w → Fin 3 → Mom d)) (N : LayeredGarden 2)
    (ri : Fin 2 → Fin w) (rl : Fin 2 → Option (Fin 3)) (a : GNode N.garden.tree) (x : Mom d) : ℂ :=
  dag.elim 1 fun cc => capT_par L γ δ s J N ri a x * capT_ch L γ δ s J cc N ri rl a x

/-- The frontier node weight at a couple node. -/
def capT_fw (p : ℕ) (Rf : Fin w → Option ℝ) (N : LayeredGarden 2) (ri : Fin 2 → Fin w)
    (a : GNode N.garden.tree) (x : Mom d) : ℂ :=
  if a.1.2 ≠ [] then topPsi p (frontierG (Rf (ri a.1.1))) (N.layer a) (N.parentLayer 0 a) x else 1

/-- The cap node weight at a couple node. -/
def capT_nodeW (L γ δ : ℝ) (p : ℕ) (s : ℝ) (J : Finset (Fin w)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (N : LayeredGarden 2) (ri : Fin 2 → Fin w)
    (rl : Fin 2 → Option (Fin 3)) (a : GNode N.garden.tree) (x : Mom d) : ℂ :=
  capT_fw p Rf N ri a x * capT_dag L γ δ s J dag N ri rl a x

/-- The pair trees `(tree of a, tree of its partner)` of a couple node, read through the root indices. -/
def capT_pt (N : LayeredGarden 2) (ri : Fin 2 → Fin w) (a : GNode N.garden.tree) : Fin w × Fin w :=
  if hl : a.1.2 ∈ (N.garden.tree a.1.1).leaves then (ri a.1.1, ri (N.garden.pair ⟨a.1, hl⟩).1.1)
  else (ri a.1.1, ri a.1.1)

/-- The anchored profile at a couple node. -/
def capT_prof (J : Finset (Fin w)) (N : LayeredGarden 2) (ri : Fin 2 → Fin w) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (L : ℝ) (roots : Fin w → (Fin d → ℤ)) (a : GNode N.garden.tree) : Mom d → ℝ :=
  if (capT_pt N ri a).1 ∈ J then (fun x => if x = latticePoint L (roots (capT_pt N ri a).1) then 1 else 0)
  else if (capT_pt N ri a).2 ∈ J then (fun x => if x = latticePoint L (roots (capT_pt N ri a).2) then 1 else 0)
  else h (N.layer a) (capT_pt N ri a).1 (capT_pt N ri a).2

section Generic

variable (LG : LayeredGarden w) (E : Comb.RootedSubforest LG.garden.tree 2)
  (hc : LG.garden.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (J : Finset (Fin w))
  (ri : Fin 2 → Fin w) (hri : ∀ c, (E.root c).1.1 = ri c)

include hri in
/-- A leaf of the couple is a capped flower of the ambient garden iff it is one of the couple. -/
theorem capT_isCapFlower_iffE (l : GLeaf E.shape) :
    IsCapFlower LG J (E.leafEmbedding l) ↔ capT_IsFl (rootedLayeredGarden LG E hc) ri J l := by
  unfold IsCapFlower capT_IsFl
  rw [← Comb.RootedSubforest.inducedGarden_pair E hc l]
  show (E.root l.1.1).1.1 ∉ J ∧ (E.root _).1.1 ∈ J ↔ _
  rw [hri, hri]
  rfl

include hri in
/-- A branch of the couple is a capped flower parent of the ambient garden iff it is one of the couple. -/
theorem capT_cfp_iffE (c : GBranch E.shape) :
    IsCapFlowerParent LG J (subforestBranchEmbedding E c) ↔ capT_IsFP (rootedLayeredGarden LG E hc) ri J c := by
  constructor
  · rintro ⟨ℓ, hℓ, h1, i, h2⟩
    have hl : c.1.2 ++ [i] ∈ (E.shape c.1.1).leaves := by
      rw [Comb.subtree_leaves_iff (E.subtree_eq c.1.1), ← List.append_assoc]
      have h := ℓ.2
      rw [h1, h2] at h
      exact h
    have hle : E.leafEmbedding ⟨(c.1.1, c.1.2 ++ [i]), hl⟩ = ℓ := by
      apply Subtype.ext
      refine Prod.ext h1.symm ?_
      rw [h2]
      exact (List.append_assoc _ _ _).symm
    refine ⟨⟨(c.1.1, c.1.2 ++ [i]), hl⟩, ?_, rfl, i, rfl⟩
    exact (capT_isCapFlower_iffE LG E hc J ri hri _).mp (Eq.mpr (congrArg (IsCapFlower LG J) hle) hℓ)
  · rintro ⟨l, hl, h1, i, h2⟩
    refine ⟨E.leafEmbedding l, (capT_isCapFlower_iffE LG E hc J ri hri l).mpr hl, ?_, i, ?_⟩
    · show (E.root l.1.1).1.1 = (E.root c.1.1).1.1
      rw [h1]
    · show (E.root l.1.1).1.2 ++ l.1.2 = ((E.root c.1.1).1.2 ++ c.1.2) ++ [i]
      rw [h1, h2, List.append_assoc]

include hri in
/-- A couple node is a capped flower of the ambient garden iff it is one of the couple. -/
theorem capT_exists_flower_iffE (a : GNode E.shape) :
    (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = E.nodeEmbedding a) ↔
      ∃ l : GLeaf E.shape, capT_IsFl (rootedLayeredGarden LG E hc) ri J l ∧ l.toNode = a := by
  constructor
  · rintro ⟨ℓ, hℓ, he⟩
    have hv : ℓ.1 = ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ a.1.2) := congrArg Subtype.val he
    have hl : a.1.2 ∈ (E.shape a.1.1).leaves := by
      rw [Comb.subtree_leaves_iff (E.subtree_eq a.1.1)]
      have h := ℓ.2
      rw [hv] at h
      exact h
    have hle : E.leafEmbedding ⟨a.1, hl⟩ = ℓ := Subtype.ext hv.symm
    refine ⟨⟨a.1, hl⟩, ?_, Subtype.ext rfl⟩
    exact (capT_isCapFlower_iffE LG E hc J ri hri _).mp (Eq.mpr (congrArg (IsCapFlower LG J) hle) hℓ)
  · rintro ⟨l, hl, he⟩
    refine ⟨E.leafEmbedding l, (capT_isCapFlower_iffE LG E hc J ri hri l).mpr hl, ?_⟩
    subst he
    rfl

include hri in
/-- A couple node is a capped flower parent of the ambient garden iff it is one of the couple. -/
theorem capT_exists_cfp_iffE (a : GNode E.shape) :
    (∃ b : GBranch LG.garden.tree, b.toNode = E.nodeEmbedding a ∧ IsCapFlowerParent LG J b) ↔
      ∃ c : GBranch E.shape, c.toNode = a ∧ capT_IsFP (rootedLayeredGarden LG E hc) ri J c := by
  constructor
  · rintro ⟨b, hb, hcfp⟩
    have hv : b.1 = ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ a.1.2) := congrArg Subtype.val hb
    have hbr : a.1.2 ∈ (E.shape a.1.1).branching := by
      rw [Comb.subtree_branching_iff (E.subtree_eq a.1.1)]
      have h := b.2
      rw [hv] at h
      exact h
    have hbe : subforestBranchEmbedding E ⟨a.1, hbr⟩ = b := Subtype.ext hv.symm
    refine ⟨⟨a.1, hbr⟩, Subtype.ext rfl, ?_⟩
    exact (capT_cfp_iffE LG E hc J ri hri _).mp (Eq.mpr (congrArg (IsCapFlowerParent LG J) hbe) hcfp)
  · rintro ⟨c, hca, hcfp⟩
    refine ⟨subforestBranchEmbedding E c, ?_, (capT_cfp_iffE LG E hc J ri hri c).mpr hcfp⟩
    rw [← hca]
    exact (subforest_branch_node E c).symm

/-- The ambient sign of an embedded couple node is its sign in the couple. -/
theorem capT_signE (a : GNode E.shape) :
    LG.garden.sign (E.nodeEmbedding a) = (rootedLayeredGarden LG E hc).garden.sign a :=
  (subforest_node_sign E LG.garden.sig a).symm

/-- The couple nodes inside the ambient garden (address prefixing). -/
def capT_emb (a : GNode (rootedLayeredGarden LG E hc).garden.tree) : GNode LG.garden.tree := E.nodeEmbedding a

/-- The couple branches inside the ambient garden. -/
def capT_bemb (b : GBranch (rootedLayeredGarden LG E hc).garden.tree) : GBranch LG.garden.tree :=
  subforestBranchEmbedding E b

/-- The couple leaves inside the ambient garden. -/
def capT_lemb (l : GLeaf (rootedLayeredGarden LG E hc).garden.tree) : GLeaf LG.garden.tree := E.leafEmbedding l

include hri in
/-- `capT_isCapFlower_iffE` on the nodes of `rootedLayeredGarden`. -/
theorem capT_isCapFlower_iff (l : GLeaf (rootedLayeredGarden LG E hc).garden.tree) :
    IsCapFlower LG J (capT_lemb LG E hc l) ↔ capT_IsFl (rootedLayeredGarden LG E hc) ri J l :=
  capT_isCapFlower_iffE LG E hc J ri hri l

include hri in
/-- `capT_cfp_iffE` on the nodes of `rootedLayeredGarden`. -/
theorem capT_cfp_iff (c : GBranch (rootedLayeredGarden LG E hc).garden.tree) :
    IsCapFlowerParent LG J (capT_bemb LG E hc c) ↔ capT_IsFP (rootedLayeredGarden LG E hc) ri J c :=
  capT_cfp_iffE LG E hc J ri hri c

include hri in
/-- `capT_exists_flower_iffE` on the nodes of `rootedLayeredGarden`. -/
theorem capT_exists_flower_iff (a : GNode (rootedLayeredGarden LG E hc).garden.tree) :
    (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = capT_emb LG E hc a) ↔
      ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree, capT_IsFl (rootedLayeredGarden LG E hc) ri J l ∧
        l.toNode = a :=
  capT_exists_flower_iffE LG E hc J ri hri a

include hri in
/-- `capT_exists_cfp_iffE` on the nodes of `rootedLayeredGarden`. -/
theorem capT_exists_cfp_iff (a : GNode (rootedLayeredGarden LG E hc).garden.tree) :
    (∃ b : GBranch LG.garden.tree, b.toNode = capT_emb LG E hc a ∧ IsCapFlowerParent LG J b) ↔
      ∃ c : GBranch (rootedLayeredGarden LG E hc).garden.tree, c.toNode = a ∧
        capT_IsFP (rootedLayeredGarden LG E hc) ri J c :=
  capT_exists_cfp_iffE LG E hc J ri hri a

/-- `capT_signE` on the nodes of `rootedLayeredGarden`. -/
theorem capT_sign (a : GNode (rootedLayeredGarden LG E hc).garden.tree) :
    LG.garden.sign (capT_emb LG E hc a) = (rootedLayeredGarden LG E hc).garden.sign a :=
  capT_signE LG E hc a

/-- Children of embedded branches. -/
theorem capT_emb_child (b : GBranch (rootedLayeredGarden LG E hc).garden.tree) (i : Fin 3) :
    capT_emb LG E hc (b.child i) = (capT_bemb LG E hc b).child i :=
  subforest_node_child E b i

/-- Embedded branches as nodes. -/
theorem capT_emb_toNode (b : GBranch (rootedLayeredGarden LG E hc).garden.tree) :
    capT_emb LG E hc b.toNode = (capT_bemb LG E hc b).toNode :=
  subforest_branch_node E b

include hri in
/-- **The parent factor of the dagger weight at a couple node.** -/
theorem capT_par_eq (L γ δ s : ℝ) (a : GNode (rootedLayeredGarden LG E hc).garden.tree) (x : Mom d) :
    (if hb : ∃ b : GBranch LG.garden.tree, b.toNode = capT_emb LG E hc a ∧ IsCapFlowerParent LG J b then
      Complex.exp (((capTheta L γ δ s LG.garden hb.choose * ‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I) else 1) =
      capT_par L γ δ s J (rootedLayeredGarden LG E hc) ri a x := by
  have hiff := capT_exists_cfp_iff LG E hc J ri hri a
  unfold capT_par
  split_ifs with hb h h'
  · have e : capTheta L γ δ s LG.garden hb.choose =
        capT_theta L γ δ s ((rootedLayeredGarden LG E hc).garden.sign a) := by
      show capT_theta L γ δ s (LG.garden.sign hb.choose.toNode) = _
      rw [hb.choose_spec.1, capT_sign LG E hc a]
    rw [e]
  · exact absurd (hiff.mp hb) h
  · exact absurd (hiff.mpr h') hb
  · rfl

include hri in
/-- **The child factor of the dagger weight at a non-root couple node**: its parent is in the couple. -/
theorem capT_ch_nonroot (L γ δ s : ℝ) (cc : Fin w → Fin 3 → Mom d) (rl : Fin 2 → Option (Fin 3))
    (a : GNode (rootedLayeredGarden LG E hc).garden.tree) (ha : a.1.2 ≠ []) (x : Mom d) :
    (if hc' : ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = capT_emb LG E hc a ∧
        IsCapFlowerParent LG J b then
      Complex.exp (((-(capTheta L γ δ s LG.garden hc'.choose * childSign hc'.choose_spec.choose * ‖x‖ ^ 2) : ℝ) : ℂ) *
          Complex.I) *
        (if (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = capT_emb LG E hc a) then 1 else
          if x = cc hc'.choose.1.1 hc'.choose_spec.choose then 1 else 0)
    else 1) = capT_ch L γ δ s J cc (rootedLayeredGarden LG E hc) ri rl a x := by
  unfold capT_ch
  rw [dite_eq_right ha]
  have hemb : capT_emb LG E hc a = (capT_bemb LG E hc (a.parent ha)).child (a.1.2.getLast ha) := by
    rw [← capT_emb_child, Reg.Skeleton.child_parent a ha]
  have e5 := capT_exists_flower_iff LG E hc J ri hri a
  by_cases hP : capT_IsFP (rootedLayeredGarden LG E hc) ri J (a.parent ha)
  · have hB₀ := (capT_cfp_iff LG E hc J ri hri (a.parent ha)).mpr hP
    have hc' : ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = capT_emb LG E hc a ∧
        IsCapFlowerParent LG J b := ⟨_, _, hemb.symm, hB₀⟩
    rw [dite_eq_left hc', ite_eq_left hP]
    obtain ⟨e1, e2⟩ := IntWeight.child_inj (hc'.choose_spec.choose_spec.1.trans hemb)
    rw [e2, e1]
    have e3 : capTheta L γ δ s LG.garden (capT_bemb LG E hc (a.parent ha)) =
        capT_theta L γ δ s ((rootedLayeredGarden LG E hc).garden.sign (a.parent ha).toNode) := by
      show capT_theta L γ δ s (LG.garden.sign (capT_bemb LG E hc (a.parent ha)).toNode) = _
      rw [← capT_emb_toNode, capT_sign LG E hc]
    have e4 : (capT_bemb LG E hc (a.parent ha)).1.1 = ri a.1.1 := hri _
    rw [e3, e4]
    by_cases hf : ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree,
        capT_IsFl (rootedLayeredGarden LG E hc) ri J l ∧ l.toNode = a
    · rw [ite_eq_left (e5.mpr hf), ite_eq_left hf]
    · rw [ite_eq_right (mt e5.mp hf), ite_eq_right hf]
  · have hn : ¬ ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = capT_emb LG E hc a ∧
        IsCapFlowerParent LG J b := by
      rintro ⟨B, i, hB, hcfp⟩
      obtain ⟨rfl, rfl⟩ := IntWeight.child_inj (hB.trans hemb)
      exact hP ((capT_cfp_iff LG E hc J ri hri _).mp hcfp)
    rw [dite_eq_right hn, ite_eq_right hP]

/-! ### The roots of a cap couple -/

section Roots

variable {p : ℕ} (hG : CapGeo LG J p) (hcp : ∃ c₀, ri c₀ ∈ J)

include hri in
/-- A cap side of the couple is a garden root carrying a single leaf. -/
theorem capT_cap_root (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (c₀ : Fin 2) (hc₀ : ri c₀ ∈ J) :
    (E.root c₀).1.2 = [] ∧ E.shape c₀ = TTree.leaf := by
  have h2 := (E.root c₀).2
  rw [hri, hleaf _ hc₀] at h2
  have h2' : (E.root c₀).1.2 = [] := by simpa [TTree.nodes] using h2
  have h3 := E.subtree_eq c₀
  rw [hri, hleaf _ hc₀, h2'] at h3
  exact ⟨h2', by simpa [Comb.subtree] using h3.symm⟩

/-- Two elements of `Fin 2` different from a third one are equal. -/
theorem capT_fin2 : ∀ x y z : Fin 2, x ≠ y → y ≠ z → x = z := by decide

include hri in
/-- The partner of the cap leaf is a capped flower on the other side. -/
theorem capT_flower_in (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (c₀ c : Fin 2) (hc₀ : ri c₀ ∈ J)
    (hcc : c ≠ c₀) (hcJ : ri c ∉ J) :
    ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree, l.1.1 = c ∧
      capT_IsFl (rootedLayeredGarden LG E hc) ri J l := by
  obtain ⟨-, hsh⟩ := capT_cap_root LG E J ri hri hleaf c₀ hc₀
  have hl₀ : ([] : Path) ∈ ((rootedLayeredGarden LG E hc).garden.tree c₀).leaves := by
    change ([] : Path) ∈ (E.shape c₀).leaves
    rw [hsh]
    simp [TTree.leaves]
  obtain ⟨l₀, hl₀v⟩ : ∃ l₀ : GLeaf (rootedLayeredGarden LG E hc).garden.tree, l₀.1 = (c₀, []) :=
    ⟨⟨(c₀, []), hl₀⟩, rfl⟩
  have h1 : ((rootedLayeredGarden LG E hc).garden.pair l₀).1.1 = c := by
    by_contra hne
    have h1' := capT_fin2 _ _ _ hne hcc
    have h2 := ((rootedLayeredGarden LG E hc).garden.pair l₀).2
    rw [h1'] at h2
    change _ ∈ (E.shape c₀).leaves at h2
    rw [hsh] at h2
    have h2' : ((rootedLayeredGarden LG E hc).garden.pair l₀).1.2 = [] := by simpa [TTree.leaves] using h2
    have he : (rootedLayeredGarden LG E hc).garden.pair l₀ = l₀ :=
      Subtype.ext (Prod.ext (h1'.trans (congrArg Prod.fst hl₀v).symm) (h2'.trans (congrArg Prod.snd hl₀v).symm))
    exact ((rootedLayeredGarden LG E hc).garden.pair_eq_iff l₀).mp he
      (Comb.RootedSubforest.inducedGarden_plain E hc l₀)
  refine ⟨(rootedLayeredGarden LG E hc).garden.pair l₀, h1, ?_, ?_⟩
  · rw [h1]
    exact hcJ
  · rw [(rootedLayeredGarden LG E hc).garden.pair_pair, hl₀v]
    exact hc₀

include hri hcp in
/-- At a couple root that is not a garden root, the couple contains a capped flower of the root's side. -/
theorem capT_root_flower (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf)
    (a : GNode (rootedLayeredGarden LG E hc).garden.tree) (hne : (E.root a.1.1).1.2 ≠ []) :
    ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree, l.1.1 = a.1.1 ∧
      capT_IsFl (rootedLayeredGarden LG E hc) ri J l := by
  obtain ⟨c₀, hc₀⟩ := hcp
  have hne' : a.1.1 ≠ c₀ := by
    intro h
    rw [h] at hne
    exact hne (capT_cap_root LG E J ri hri hleaf c₀ hc₀).1
  have hJ : ri a.1.1 ∉ J := fun h => hne (capT_cap_root LG E J ri hri hleaf _ h).1
  exact capT_flower_in LG E hc J ri hri hleaf c₀ a.1.1 hc₀ hne' hJ

include hri hcp in
/-- A couple root that is not a garden root lies on the capped stem. -/
theorem capT_onCapStem (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf)
    (a : GNode (rootedLayeredGarden LG E hc).garden.tree) (ha : a.1.2 = []) (hne : (E.root a.1.1).1.2 ≠ []) :
    OnCapStem LG J (capT_emb LG E hc a) := by
  obtain ⟨l, hl1, hl⟩ := capT_root_flower LG E hc J ri hri hcp hleaf a hne
  refine ⟨capT_lemb LG E hc l, (capT_isCapFlower_iff LG E hc J ri hri l).mpr hl, ?_, ?_⟩
  · show (E.root a.1.1).1.1 = (E.root l.1.1).1.1
    rw [hl1]
  · show (E.root a.1.1).1.2 ++ a.1.2 <+: (E.root l.1.1).1.2 ++ l.1.2
    rw [hl1, ha, List.append_nil]
    exact List.prefix_append _ _

include hri hG hcp in
/-- **The frontier node weight at a couple node.** -/
theorem capT_fw_eq (Rf : Fin w → Option ℝ) (a : GNode (rootedLayeredGarden LG E hc).garden.tree) (x : Mom d) :
    fwNode LG p (fun j => frontierG (Rf j)) (capT_emb LG E hc a) x =
      capT_fw p Rf (rootedLayeredGarden LG E hc) ri a x := by
  unfold capT_fw
  by_cases ha : a.1.2 = []
  · rw [ite_eq_right (not_not.mpr ha)]
    unfold fwNode
    split_ifs with hp
    · have hne : (E.root a.1.1).1.2 ≠ [] := by
        intro h
        apply hp
        show (E.root a.1.1).1.2 ++ a.1.2 = []
        rw [h, ha]
        rfl
      have hl := hG.stem_layer _ (capT_onCapStem LG E hc J ri hri hcp hG.cap_leaf a ha hne)
      unfold topPsi
      rw [ite_eq_right]
      rw [hl]
      exact fun h => lt_irrefl _ h.1
    · rfl
  · rw [ite_eq_left ha]
    rw [fwNode_embed LG (rootedLayeredGarden LG E hc) (capT_emb LG E hc) (fun j => (E.root j).1)
      (fun _ => rfl) (fun _ => rfl) p (fun j => frontierG (Rf j)) a x]
    simp only [rowParentLayer, ha, ite_false, hri]

include hri hG hcp in
/-- **The child factor at a couple root**: only a capped flower root that is not a garden root carries one. -/
theorem capT_ch_root (L γ δ s : ℝ) (cc : Fin w → Fin 3 → Mom d) (rl : Fin 2 → Option (Fin 3))
    (hrl : ∀ c, (E.root c).1.2.getLast? = rl c)
    (a : GNode (rootedLayeredGarden LG E hc).garden.tree) (ha : a.1.2 = []) (x : Mom d) :
    (if hc' : ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = capT_emb LG E hc a ∧
        IsCapFlowerParent LG J b then
      Complex.exp (((-(capTheta L γ δ s LG.garden hc'.choose * childSign hc'.choose_spec.choose * ‖x‖ ^ 2) : ℝ) : ℂ) *
          Complex.I) *
        (if (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = capT_emb LG E hc a) then 1 else
          if x = cc hc'.choose.1.1 hc'.choose_spec.choose then 1 else 0)
    else 1) = capT_ch L γ δ s J cc (rootedLayeredGarden LG E hc) ri rl a x := by
  unfold capT_ch
  rw [dite_eq_left ha]
  have hea : capT_emb LG E hc a = E.root a.1.1 := by
    apply Subtype.ext
    show ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ a.1.2) = (E.root a.1.1).1
    rw [ha, List.append_nil]
  by_cases hne : (E.root a.1.1).1.2 = []
  · have hrl' : rl a.1.1 = none := by rw [← hrl, hne]; rfl
    rw [hrl']
    have hn : ¬ ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = capT_emb LG E hc a ∧
        IsCapFlowerParent LG J b := by
      rintro ⟨B, i, hB, -⟩
      have h := congrArg (fun z : GNode LG.garden.tree => z.1.2) (hB.trans hea)
      simp only [GBranch.child, hne] at h
      simp at h
    rw [dite_eq_right hn]
    rfl
  · obtain ⟨B₀, i₀, hB₀c⟩ : ∃ (B : GBranch LG.garden.tree) (i : Fin 3), B.child i = capT_emb LG E hc a :=
      ⟨_, _, (Reg.Skeleton.child_parent _ hne).trans hea.symm⟩
    have hv : (B₀.1.1, B₀.1.2 ++ [i₀]) = (E.root a.1.1).1 := congrArg Subtype.val (hB₀c.trans hea)
    have hrl' : rl a.1.1 = some i₀ := by
      rw [← hrl, ← congrArg Prod.snd hv]
      simp
    rw [hrl']
    show _ = if ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree,
        capT_IsFl (rootedLayeredGarden LG E hc) ri J l ∧ l.toNode = a then _ else _
    by_cases hf : ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree,
        capT_IsFl (rootedLayeredGarden LG E hc) ri J l ∧ l.toNode = a
    · have hf' := (capT_exists_flower_iff LG E hc J ri hri a).mpr hf
      obtain ⟨ℓ, hℓ, hℓa⟩ := hf'
      have hℓv : ℓ.1 = (B₀.1.1, B₀.1.2 ++ [i₀]) := congrArg Subtype.val (hℓa.trans hB₀c.symm)
      have hB₀ : IsCapFlowerParent LG J B₀ := by
        refine ⟨ℓ, hℓ, ?_, i₀, ?_⟩
        · have h := congrArg Prod.fst hℓv
          exact h
        · have h := congrArg Prod.snd hℓv
          exact h
      have hc' : ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = capT_emb LG E hc a ∧
          IsCapFlowerParent LG J b := ⟨B₀, i₀, hB₀c, hB₀⟩
      rw [dite_eq_left hc', ite_eq_left hf]
      obtain ⟨e1, e2⟩ := IntWeight.child_inj (hc'.choose_spec.choose_spec.1.trans hB₀c.symm)
      rw [e2, e1, ite_eq_left ⟨ℓ, hℓ, hℓa⟩, mul_one]
      have hs : LG.garden.sign B₀.toNode = if i₀ = 1 then -(rootedLayeredGarden LG E hc).garden.sign a else
          (rootedLayeredGarden LG E hc).garden.sign a := by
        have h1 := Mole.child_sign_formula B₀ i₀
        rw [hB₀c, capT_sign] at h1
        rw [h1]
        split_ifs <;> simp
      have e : capTheta L γ δ s LG.garden B₀ = capT_theta L γ δ s (if i₀ = 1 then
          -(rootedLayeredGarden LG E hc).garden.sign a else (rootedLayeredGarden LG E hc).garden.sign a) := by
        show capT_theta L γ δ s (LG.garden.sign B₀.toNode) = _
        rw [hs]
      rw [e]
    · rw [ite_eq_right hf]
      have hn : ¬ ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = capT_emb LG E hc a ∧
          IsCapFlowerParent LG J b := by
        rintro ⟨B, i, hB, ℓ', hℓ', h1', i', h2'⟩
        obtain ⟨l, hl1, hl⟩ := capT_root_flower LG E hc J ri hri hcp hG.cap_leaf a hne
        have hfl := (capT_isCapFlower_iff LG E hc J ri hri l).mpr hl
        have hBv : (B.1.1, B.1.2 ++ [i]) = (E.root a.1.1).1 := congrArg Subtype.val (hB.trans hea)
        have hlv : (capT_lemb LG E hc l).1 = ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ l.1.2) := by
          show ((E.root l.1.1).1.1, (E.root l.1.1).1.2 ++ l.1.2) = _
          rw [hl1]
        have heq : ℓ' = capT_lemb LG E hc l := hG.one_flower ℓ' _ hℓ' hfl (by
          rw [h1', hlv, ← congrArg Prod.fst hBv])
        subst heq
        rw [hlv, ← congrArg Prod.snd hBv, List.append_assoc] at h2'
        have hlen := congrArg List.length h2'
        simp only [List.length_append, List.length_singleton] at hlen
        have hl0 : l.1.2 = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact hf ⟨l, hl, Subtype.ext (Prod.ext hl1 (hl0.trans ha.symm))⟩
      rw [dite_eq_right hn]

end Roots

/-! ### Profiles, pins and node weights of a cap couple -/

include hri in
/-- The pair trees of an embedded couple node. -/
theorem capT_pairTrees_eq (a : GNode (rootedLayeredGarden LG E hc).garden.tree) :
    pairTrees LG.garden (capT_emb LG E hc a).1 = capT_pt (rootedLayeredGarden LG E hc) ri a := by
  unfold pairTrees capT_pt
  by_cases hl : a.1.2 ∈ ((rootedLayeredGarden LG E hc).garden.tree a.1.1).leaves
  · have hex : ∃ ℓ : GLeaf LG.garden.tree, ℓ.1 = (capT_emb LG E hc a).1 := ⟨capT_lemb LG E hc ⟨a.1, hl⟩, rfl⟩
    rw [dite_eq_left hex, dite_eq_left hl]
    have hch : hex.choose = capT_lemb LG E hc ⟨a.1, hl⟩ := Subtype.ext hex.choose_spec
    have hp : LG.garden.pair (capT_lemb LG E hc ⟨a.1, hl⟩) =
        capT_lemb LG E hc ((rootedLayeredGarden LG E hc).garden.pair ⟨a.1, hl⟩) :=
      (Comb.RootedSubforest.inducedGarden_pair E hc _).symm
    rw [hch, hp]
    exact Prod.ext (hri a.1.1) (hri _)
  · have hex : ¬ ∃ ℓ : GLeaf LG.garden.tree, ℓ.1 = (capT_emb LG E hc a).1 := by
      rintro ⟨ℓ, hℓ⟩
      apply hl
      change a.1.2 ∈ (E.shape a.1.1).leaves
      rw [Comb.subtree_leaves_iff (E.subtree_eq a.1.1)]
      have h := ℓ.2
      rw [hℓ] at h
      exact h
    rw [dite_eq_right hex, dite_eq_right hl]
    exact Prod.ext (hri a.1.1) (hri a.1.1)

include hri in
/-- **The anchored profile at a couple node.** -/
theorem capT_prof_eq (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ) (roots : Fin w → (Fin d → ℤ))
    (a : GNode (rootedLayeredGarden LG E hc).garden.tree) :
    anchProfiles J LG h L roots (capT_emb LG E hc a).1 = capT_prof J (rootedLayeredGarden LG E hc) ri h L roots a := by
  unfold anchProfiles capT_prof typeProfiles
  rw [capT_pairTrees_eq LG E hc ri hri a, dite_eq_left (capT_emb LG E hc a).2]
  rfl

include hri in
/-- **The cap node weight at a couple node.** -/
theorem capT_nodeW_eq {p : ℕ} (hG : CapGeo LG J p) (hcp : ∃ c₀, ri c₀ ∈ J) (L γ δ s : ℝ)
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (rl : Fin 2 → Option (Fin 3))
    (hrl : ∀ c, (E.root c).1.2.getLast? = rl c) (a : GNode (rootedLayeredGarden LG E hc).garden.tree) (x : Mom d) :
    capNodeW L γ δ p s LG J Rf dag (capT_emb LG E hc a) x =
      capT_nodeW L γ δ p s J Rf dag (rootedLayeredGarden LG E hc) ri rl a x := by
  unfold capNodeW capT_nodeW
  rw [capT_fw_eq LG E hc J ri hri hG hcp Rf a x]
  congr 1
  cases dag with
  | none => rfl
  | some cc =>
    by_cases ha : a.1.2 = []
    · exact congrArg₂ (· * ·) (capT_par_eq LG E hc J ri hri L γ δ s a x)
        (capT_ch_root LG E hc J ri hri hG hcp L γ δ s cc rl hrl a ha x)
    · exact congrArg₂ (· * ·) (capT_par_eq LG E hc J ri hri L γ δ s a x)
        (capT_ch_nonroot LG E hc J ri hri L γ δ s cc rl a ha x)

end Generic
/-! ### The reconstruction side -/

/-- The root addresses of a native couple are `coupleRoot`. -/
theorem capT_root_val {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S) (c : Fin 2) :
    ((nativeCoupleForest D hS q).root c).1 = coupleRoot D hS q c := by
  fin_cases c <;> rfl

/-- A cap pair has a root index in `J`. -/
theorem capT_exists_cap {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (J : Finset (Fin w))
    (q : SourcePair S) (hq : IsCapPair S hS J q) : ∃ c, (coupleRoot D hS q c).1 ∈ J := by
  rcases hq with h0 | h1
  · refine ⟨0, ?_⟩
    show (inflatedPosition S D.tree (q.firstLeaf hS).toNode).1 ∈ J
    rw [inflatedPosition_index]
    exact h0
  · refine ⟨1, ?_⟩
    show (inflatedPosition S D.tree (q.secondLeaf hS).toNode).1 ∈ J
    rw [inflatedPosition_index]
    exact h1

end WaveTurbulence.Flower.MkSlots.IntCapT

namespace WaveTurbulence.Flower.MkSlots

end WaveTurbulence.Flower.MkSlots

end
