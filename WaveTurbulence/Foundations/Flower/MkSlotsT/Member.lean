/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.ShapeDesc
public import WaveTurbulence.Foundations.Vine.B.Hdata

/-! # B3s-HELPER5 (γ) T1, transport step 3: retention is common to two shapes with the same hinge data

Two reconstructions (skeletons `S₁`, `S₂`, data `D₁`, `D₂`) with splice shapes `Φ₁ : SpliceShape blk₁ Gsb`,
`Φ₂ : SpliceShape blk₂ Gsb` onto the SAME `Gsb`, the same unit index, the same hinge boundary data
(`Φ₂.hmom = Φ₁.hmom`, B3's `memShape_hmom` for the members of a run class), and single-leaf cap trees.

* `flower_owner`: every capped flower is owned by the image `Φ.leaf (Gsb.pair m)` of the `Gsb` partner of a cap root
  `m` (a `Gsb` leaf at `(j', [])`, `j' ∈ J`) — `Gsb` data, the same for both reconstructions;
* `flower_exists`: conversely every such `m` (partner off the cap trees) carries a capped flower owned by
  `Φ.leaf (Gsb.pair m)`;
* **`stemRet_transport`**: retention (`StemRet`, T1) of the first reconstruction implies retention of the second. A
  non-upper atom `β` of a unit on the second stem lies strictly between the upper joint and a crown node `x`; then
  `x` is a lower crown node (`hmom j 2` or `hmom j 3`), the SAME `Gsb` child of the hinge on the `Gsb` path to the
  flower's leaf in the first reconstruction, whose lower joint is then on the first stem — against retention there.
  A stem address owned by a leaf is owned by the (retained) flower leaf itself. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.VineB (SpliceShape Ret Disj crownSet regionOf)
open WaveTurbulence.RedSplice (CLBlock)
open WaveTurbulence.Flower.MkMark (owner CapFlowerAt LeafAt)
open WaveTurbulence.Flower.MkDefs (IsCapFlowerParent)

namespace WaveTurbulence.Flower.MkSlotsT

variable {w : ℕ}

/-- A leaf has no proper descendant. -/
theorem eq_of_leaf_isDesc {T : Fin w → TTree} (l : GLeaf T) {y : GNode T} (h : l.toNode.IsDesc y) :
    y = l.toNode := by
  obtain ⟨h1, s, hs⟩ := h
  have hs0 : s = [] := MkMark.eq_nil_of_leaf_append (T l.1.1) l.2 (by
    have e1 : l.1.2 ++ s = y.1.2 := hs
    have e2 : l.1.1 = y.1.1 := h1
    show l.1.2 ++ s ∈ (T l.1.1).nodes
    rw [e1, e2]; exact y.2)
  subst hs0
  exact Subtype.ext (Prod.ext h1.symm (by simpa using hs.symm))

section Shape
variable {S Gsb : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι] {blk : ι → CLBlock S}
  (Φ : SpliceShape blk Gsb)

omit [Fintype ι] [DecidableEq ι] in
/-- Node ancestry through a shape. -/
theorem shape_node_isDesc {y y' : GNode Gsb.tree} (h : y.IsDesc y') : (Φ.node y).IsDesc (Φ.node y') := by
  rcases VineB.SpliceShape.node_cases y with ⟨c, rfl⟩ | ⟨l, rfl⟩
  · rw [← Φ.br_node]
    exact shape_isDesc_of_isDesc Φ c y' h
  · rw [eq_of_leaf_isDesc l h]
    exact GNode.isDesc_refl _

omit [Fintype ι] [DecidableEq ι] in
/-- The `Gsb` root leaf of a single-leaf tree is mapped to the skeleton root leaf. -/
theorem leaf_root_node (m : GLeaf Gsb.tree) (hm : m.1.2 = []) :
    (Φ.leaf m).toNode = GNode.root S.tree m.1.1 := by
  rw [Φ.leaf_node]
  have : m.toNode = GNode.root Gsb.tree m.1.1 := Subtype.ext (Prod.ext rfl hm)
  rw [this, Φ.root]

variable (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) {J : Finset (Fin w)}
  (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)

include hcap in
/-- **Capped flowers are owned by the images of the `Gsb` partners of cap roots.** -/
theorem flower_owner {ℓ : Address w} (hℓ : CapFlowerAt (layeredReconstruction D hS layer hLayer) J ℓ) :
    ∃ m : GLeaf Gsb.tree, m.1.1 ∈ J ∧ m.1.2 = [] ∧ owner S D.tree ℓ = (Φ.leaf (Gsb.pair m)).toNode := by
  obtain ⟨hl, hj, hp⟩ := hℓ
  set f : GLeaf (D.garden hS).tree := ⟨ℓ, hl⟩
  set g : GLeaf (D.garden hS).tree := (D.garden hS).pair f with hg
  set j' := g.1.1
  have hj' : j' ∈ J := hp
  have hgnil : g.1.2 = [] := by
    have := g.2
    rw [show (D.garden hS).tree g.1.1 = TTree.leaf from hcap j' hj'] at this
    simpa [TTree.leaves] using this
  -- the skeleton root leaf of tree `j'` and its `Gsb` preimage
  have hrootS : ([] : TTree.Path) ∈ (S.tree j').leaves :=
    MkSlots.IntGeo.root_mem_leaves (D := D) (hS := hS) (hcap j' hj')
  set r : GLeaf S.tree := ⟨(j', []), hrootS⟩
  have hret : Ret blk r.toNode := by
    intro k
    left
    rw [leaf_mem_clRealizationNodes]
    rintro ⟨-, hn, -, -⟩
    exact hn rfl
  obtain ⟨m, hm⟩ := Φ.exists_leaf hret
  have hm1 : m.1.1 = j' := by
    have := Φ.tree_eq m.toNode
    rw [← Φ.leaf_node, hm] at this
    exact this.symm
  have hm2 : m.1.2 = [] := by
    have h := (Φ.root_iff m.toNode).mp (by rw [← Φ.leaf_node, hm]; rfl)
    exact h
  refine ⟨m, hm1 ▸ hj', hm2, ?_⟩
  -- owners of the pair `(f, g)`
  have hog : owner S D.tree g.1 = r.toNode := by
    refine MkMark.owner_eq_leaf S D.tree ?_
    show MkDefs.AddrBelow (inflatedPosition S D.tree (GNode.root S.tree j')) g.1
    rw [inflatedPosition_root]
    exact ⟨rfl, by rw [hgnil]⟩
  have hpo := MkMark.owner_pair (ReconstructionData.garden_decodes D hS) f
  rcases hpo with he | ⟨l, hl1, hl2⟩
  · exfalso
    have h1 := MkMark.owner_fst S D.tree f.1
    have h2 := MkMark.owner_fst S D.tree g.1
    rw [← hg] at he
    rw [he] at h1
    exact hj (h1.symm.trans h2 ▸ hj')
  · rw [← hg, hog] at hl2
    have hlr : S.pair l = r := Mole.leaf_toNode_injective hl2
    have hl' : l = S.pair r := by rw [← hlr, S.pair_pair]
    show owner S D.tree f.1 = _
    rw [← hl1, hl', ← hm, Φ.pair]

include hcap in
/-- **Every cap root whose `Gsb` partner is off the cap trees carries a capped flower** owned by the image of the
partner. -/
theorem flower_exists (m : GLeaf Gsb.tree) (hmJ : m.1.1 ∈ J) (hm2 : m.1.2 = []) (hpm : (Gsb.pair m).1.1 ∉ J) :
    ∃ ℓ, CapFlowerAt (layeredReconstruction D hS layer hLayer) J ℓ ∧
      owner S D.tree ℓ = (Φ.leaf (Gsb.pair m)).toNode := by
  have hleafT : (D.garden hS).tree m.1.1 = TTree.leaf := hcap _ hmJ
  have hc0 : ([] : TTree.Path) ∈ ((D.garden hS).tree m.1.1).leaves := by rw [hleafT]; simp [TTree.leaves]
  set c0 : GLeaf (D.garden hS).tree := ⟨(m.1.1, []), hc0⟩
  set f : GLeaf (D.garden hS).tree := (D.garden hS).pair c0 with hf
  have hoc : owner S D.tree c0.1 = (Φ.leaf m).toNode := by
    refine MkMark.owner_eq_leaf S D.tree ?_
    rw [leaf_root_node Φ m hm2, inflatedPosition_root]
    exact ⟨rfl, List.prefix_refl _⟩
  have hof : owner S D.tree f.1 = (Φ.leaf (Gsb.pair m)).toNode := by
    rcases MkMark.owner_pair (ReconstructionData.garden_decodes D hS) c0 with he | ⟨l, hl1, hl2⟩
    · exfalso
      have h1 := MkMark.owner_fst S D.tree c0.1
      have h2 := MkMark.owner_fst S D.tree f.1
      rw [← hf] at he
      rw [he] at h1
      have htr : f.1.1 = m.1.1 := h2.symm.trans h1
      have hfnil : f.1.2 = [] := by
        have := f.2
        rw [htr, hleafT] at this
        simpa [TTree.leaves] using this
      have hfc : f = c0 := Subtype.ext (Prod.ext htr hfnil)
      have hfix : (D.garden hS).pair c0 = c0 := hf ▸ hfc
      exact ((D.garden hS).pair_eq_iff c0).mp hfix (ReconstructionData.garden_plain D hS c0)
    · rw [hoc] at hl1
      have hl : l = Φ.leaf m := Mole.leaf_toNode_injective hl1
      have hl2' : (S.pair l).toNode = owner S D.tree f.1 := hl2
      rw [← hl2', hl, ← Φ.pair]
  refine ⟨f.1, ⟨f.2, ?_, ?_⟩, hof⟩
  · have h1 := MkMark.owner_fst S D.tree f.1
    rw [hof] at h1
    have h2 := Φ.tree_eq (Gsb.pair m).toNode
    rw [← Φ.leaf_node] at h2
    intro hfJ
    exact hpm (h2 ▸ h1 ▸ hfJ)
  · show ((D.garden hS).pair f).1.1 ∈ J
    rw [hf, (D.garden hS).pair_pair]
    exact hmJ

include hcap in
/-- **The core of `Φ.br c` is on the capped stem iff `c` is a `Gsb` ancestor of the partner of a cap root.** -/
theorem onStem_core_iff (c : GBranch Gsb.tree) :
    OnStemAddr (layeredReconstruction D hS layer hLayer) J (D.corePosition (Φ.br c)) ↔
      ∃ m : GLeaf Gsb.tree, m.1.1 ∈ J ∧ m.1.2 = [] ∧ (Gsb.pair m).1.1 ∉ J ∧ c.toNode.IsDesc (Gsb.pair m).toNode := by
  rw [core_onStem_iff_gsb Φ D (fun ℓ hℓ => by
    obtain ⟨m, -, -, h⟩ := flower_owner Φ D hS layer hLayer hcap hℓ
    exact ⟨Gsb.pair m, h⟩) c]
  constructor
  · rintro ⟨ℓ, hℓ, lf, hlf, hd⟩
    obtain ⟨m, hmJ, hm2, hown⟩ := flower_owner Φ D hS layer hLayer hcap hℓ
    have hlfm : lf = Gsb.pair m := Φ.leaf_inj (Mole.leaf_toNode_injective (hlf.symm.trans hown))
    subst hlfm
    refine ⟨m, hmJ, hm2, ?_, hd⟩
    have h1 := MkMark.owner_fst S D.tree ℓ
    rw [hown] at h1
    have h2 := Φ.tree_eq (Gsb.pair m).toNode
    rw [← Φ.leaf_node] at h2
    intro hJ
    exact hℓ.2.1 (h1 ▸ h2.symm ▸ hJ)
  · rintro ⟨m, hmJ, hm2, hpm, hd⟩
    obtain ⟨ℓ, hℓ, hown⟩ := flower_exists Φ D hS layer hLayer hcap m hmJ hm2 hpm
    exact ⟨ℓ, hℓ, Gsb.pair m, hown, hd⟩

/-- `StemB` at a core branch: on the capped stem and not a capped flower parent. -/
theorem stemB_core_iff (β : GBranch S.tree) :
    StemB D hS layer hLayer J (coreLG D hS layer hLayer β) ↔
      OnStemAddr (layeredReconstruction D hS layer hLayer) J (D.corePosition β) ∧
        ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (coreLG D hS layer hLayer β) := by
  unfold StemB
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨-, hst, hcfp⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨(MkMark.onCapStem_iff _ J _).mp hst, hcfp⟩
  · rintro ⟨hst, hcfp⟩
    refine ⟨(coreLG D hS layer hLayer β).1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, ?_, hcfp⟩⟩
    exact (MkMark.onCapStem_iff _ J _).mpr hst

end Shape

/-! ## Retention is common to two shapes with the same hinge data -/

section Transport
variable {S₁ S₂ Gsb : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι] {blk₁ : ι → CLBlock S₁}
  {blk₂ : ι → CLBlock S₂} (Φ₁ : SpliceShape blk₁ Gsb) (Φ₂ : SpliceShape blk₂ Gsb) (hd₁ : Disj blk₁)
  (hd₂ : Disj blk₂) (hm : ∀ j i, Φ₂.hmom hd₂ j i = Φ₁.hmom hd₁ j i)
  (D₁ : ReconstructionData S₁) (hS₁ : S₁.IsPlain) (layer₁ : GNode (D₁.forest hS₁) → ℕ)
  (hLayer₁ : IsLayering (D₁.garden hS₁) layer₁)
  (D₂ : ReconstructionData S₂) (hS₂ : S₂.IsPlain) (layer₂ : GNode (D₂.forest hS₂) → ℕ)
  (hLayer₂ : IsLayering (D₂.garden hS₂) layer₂) {J : Finset (Fin w)}
  (hcap₁ : ∀ j ∈ J, (D₁.garden hS₁).tree j = TTree.leaf) (hcap₂ : ∀ j ∈ J, (D₂.garden hS₂).tree j = TTree.leaf)

include hm in
/-- Equal hinge data gives equal hinges. -/
theorem hinge_eq_of_hmom (j : ι) : Φ₂.hinge hd₂ j = Φ₁.hinge hd₁ j := by
  have h0 : ∀ {S : Garden w} {blk : ι → CLBlock S} (Φ : SpliceShape blk Gsb) (hd : Disj blk),
      Φ.hmom hd j 0 = (Φ.hinge hd j).toNode := by
    intro S blk Φ hd
    apply Φ.inj
    rw [Φ.node_hmom, ← Φ.br_node, Φ.br_hinge]
    rfl
  have := (h0 Φ₂ hd₂).symm.trans ((hm j 0).trans (h0 Φ₁ hd₁))
  exact Mole.branch_toNode_injective this

include hm hcap₁ hcap₂ in
/-- **Retention is common to two shapes with the same hinge data** (T1, class-common). -/
theorem stemRet_transport (hR₁ : StemRet S₁ D₁.tree blk₁ (layeredReconstruction D₁ hS₁ layer₁ hLayer₁) J) :
    StemRet S₂ D₂.tree blk₂ (layeredReconstruction D₂ hS₂ layer₂ hLayer₂) J where
  upper := by
    intro j z hz β hβ hβU
    by_contra hne
    obtain ⟨ℓ, hℓ, hzℓ⟩ := hz
    obtain ⟨m, hmJ, hm2, hown⟩ := flower_owner Φ₂ D₂ hS₂ layer₂ hLayer₂ hcap₂ hℓ
    have hβσ : β.toNode.IsDesc (Φ₂.leaf (Gsb.pair m)).toNode := by
      have := MkMark.owner_isDesc_of_addrBelow S₂ D₂.tree hzℓ
      rwa [hβ, hown] at this
    have hβreal := (VineB.real_iff (blk₂ j) β.toNode).mp ((VineB.branch_real_iff (blk₂ j) β).mpr hβU)
    have hupσ := hβreal.1.trans hβσ
    have hh : (Φ₂.hinge hd₂ j).toNode.IsDesc (Gsb.pair m).toNode := by
      rw [← shape_isDesc_iff Φ₂, Φ₂.br_hinge, ← Φ₂.leaf_node]
      exact hupσ
    obtain ⟨i, hi⟩ := VineB.exists_child_isDesc (Φ₂.hinge hd₂ j) hh (Mole.branch_toNode_ne_leaf _ _)
    have hx₂ := Φ₂.crown (Φ₂.hinge hd₂ j) j (Φ₂.br_hinge hd₂ j) i
    have hx₂σ : (Φ₂.node ((Φ₂.hinge hd₂ j).child i)).IsDesc (Φ₂.leaf (Gsb.pair m)).toNode := by
      rw [Φ₂.leaf_node]
      exact shape_node_isDesc Φ₂ hi
    rcases MkMark.isDesc_total_of_common _ _ hβσ hx₂σ with h1 | h1
    · -- `β` lies above the crown node: the crown node is a lower crown node
      have hlow : (Φ₂.hinge hd₂ j).child i = Φ₂.hmom hd₂ j 2 ∨ (Φ₂.hinge hd₂ j).child i = Φ₂.hmom hd₂ j 3 := by
        rcases hx₂ with hx | hx | hx
        · exfalso
          rw [hx] at h1
          rcases (VineB.isDesc_child_iff _ _).mp h1 with h2 | h2
          · exact hβreal.2.1 (h2 ▸ GNode.isDesc_refl _)
          · exact hne (Mole.branch_toNode_injective (VineB.isDesc_antisymm' h2 hβreal.1))
        · left
          apply Φ₂.inj
          rw [Φ₂.node_hmom, hx]
          rfl
        · right
          apply Φ₂.inj
          rw [Φ₂.node_hmom, hx]
          rfl
      -- the same `Gsb` child at the first reconstruction
      have hpm : (Gsb.pair m).1.1 ∉ J := by
        have h1' := MkMark.owner_fst S₂ D₂.tree ℓ
        rw [hown] at h1'
        have h2' := Φ₂.tree_eq (Gsb.pair m).toNode
        rw [← Φ₂.leaf_node] at h2'
        intro hJ
        exact hℓ.2.1 (h1' ▸ h2'.symm ▸ hJ)
      obtain ⟨ℓ₁, hℓ₁, hown₁⟩ := flower_exists Φ₁ D₁ hS₁ layer₁ hLayer₁ hcap₁ m hmJ hm2 hpm
      have hhinge := hinge_eq_of_hmom Φ₁ Φ₂ hd₁ hd₂ hm j
      rw [hhinge] at hi hlow
      have hlow₁ : (blk₁ j).lower.toNode.IsDesc (Φ₁.node ((Φ₁.hinge hd₁ j).child i)) := by
        rcases hlow with hl | hl
        · rw [hl, hm, Φ₁.node_hmom]
          exact GBranch.isDesc_child _ _
        · rw [hl, hm, Φ₁.node_hmom]
          exact GBranch.isDesc_child _ _
      have hdesc₁ : (blk₁ j).lower.toNode.IsDesc (Φ₁.leaf (Gsb.pair m)).toNode := by
        rw [Φ₁.leaf_node]
        exact hlow₁.trans (shape_node_isDesc Φ₁ hi)
      have hst := onStem_of_desc D₁ hℓ₁ hown₁ hdesc₁
      have heq := hR₁.upper j (D₁.corePosition (blk₁ j).lower) hst (blk₁ j).lower (owner_corePosition D₁ _)
        (VineB.lower_mem _)
      exact (blk₁ j).isBlock.2.2.2.1 heq.symm
    · -- the crown node is above `β`, impossible for an atom of the unit
      rcases hx₂ with hx | hx | hx <;> rw [hx] at h1
      · exact hβreal.2.1 h1
      · exact hβreal.2.2.1 h1
      · exact hβreal.2.2.2 h1
  leaf := by
    intro j z hz l hl hint
    obtain ⟨ℓ, hℓ, hzℓ⟩ := hz
    obtain ⟨m, -, -, hown⟩ := flower_owner Φ₂ D₂ hS₂ layer₂ hLayer₂ hcap₂ hℓ
    have hlσ : l.toNode.IsDesc (Φ₂.leaf (Gsb.pair m)).toNode := by
      have := MkMark.owner_isDesc_of_addrBelow S₂ D₂.tree hzℓ
      rwa [hl, hown] at this
    have he := eq_of_leaf_isDesc l hlσ
    have hlm : l = Φ₂.leaf (Gsb.pair m) := (Mole.leaf_toNode_injective he).symm
    rcases Φ₂.ret_leaf (Gsb.pair m) j with h | h
    · rw [← hlm, leaf_mem_clRealizationNodes] at h
      exact h hint
    · exact Mole.branch_toNode_ne_leaf (blk₂ j).upper (Φ₂.leaf (Gsb.pair m)) h.symm

end Transport

end WaveTurbulence.Flower.MkSlotsT
