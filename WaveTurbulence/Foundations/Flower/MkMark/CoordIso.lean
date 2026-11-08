/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.Coord

/-! # B2b MK-MARK: correspondences of decoded gardens from skeleton maps

Two decoded gardens `dec(S, D)` and `dec(S', D')` and a map `ν` of skeleton nodes that preserves tree indices,
roots, the local trees and holes, ordered children and parents, off a set `Rsk` of skeleton nodes (the replaced
objects of an LF operation), give an `OutIso` off the regions owned by `Rsk` and `Rsk'` (`CoordData.toOutIso`):
the address map is `IP(o) ++ q ↦ IP'(ν o) ++ q` in skeleton coordinates (owner `o`, local path `q`). The partner-tree
field is a hypothesis here, discharged per instance by pair naturality. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-! ## Coordinates -/

section Coords
variable (S : Garden w) (X : GBranch S.tree → RegChain)

/-- The local path of an address inside the region of its owner. -/
def localPath (z : Address w) : TTree.Path := z.2.drop (inflatedPosition S X (owner S X z)).2.length

theorem coord_eq (z : Address w) : z = addrExt (inflatedPosition S X (owner S X z)) (localPath S X z) := by
  have h := (mem_ownRegion_owner S X z).1
  obtain ⟨h1, t, ht⟩ := h
  refine Prod.ext h1.symm ?_
  show z.2 = (inflatedPosition S X (owner S X z)).2 ++ z.2.drop (inflatedPosition S X (owner S X z)).2.length
  conv_rhs => rw [← ht]
  simp only [List.drop_left]
  exact ht.symm

theorem localPath_addrExt (o : GNode S.tree) (q : TTree.Path) (h : owner S X (addrExt (inflatedPosition S X o) q) = o) :
    localPath S X (addrExt (inflatedPosition S X o) q) = q := by
  unfold localPath
  rw [h]
  simp [addrExt]

/-- Roots are exactly the nodes with an empty inflated position. -/
theorem inflatedPosition_nil_iff (o : GNode S.tree) : (inflatedPosition S X o).2 = [] ↔ o.1.2 = [] := by
  induction o using node_induction with
  | hroot j => simp; rfl
  | hchild b i ih =>
    rw [inflatedPosition_snd_child]
    simp [GBranch.child]

/-- The parent address of a non-root inflated position is the core position of the skeleton parent. -/
theorem inflatedPosition_parent (o : GNode S.tree) (h : o.1.2 ≠ []) :
    ((inflatedPosition S X o).1, (inflatedPosition S X o).2.dropLast) =
      addrExt (inflatedPosition S X (o.parent h).toNode) (X (o.parent h)).lonePath := by
  conv_lhs => rw [← parent_child_self o h]
  rw [inflatedPosition_child]
  simp only [addrExt]
  refine Prod.ext rfl ?_
  show ((inflatedPosition S X (o.parent h).toNode).2 ++ ((X (o.parent h)).lonePath ++ [o.1.2.getLast h])).dropLast = _
  rw [← List.append_assoc, List.dropLast_concat]

end Coords

/-- The hole of a skeleton node: the lone path of its regular tree if it is a branch. -/
def holeOf {S : Garden w} (D : ReconstructionData S) (o : GNode S.tree) : Option TTree.Path :=
  if h : o.1.2 ∈ (S.tree o.1.1).branching then some (D.tree ⟨o.1, h⟩).lonePath else none

theorem holeOf_branch {S : Garden w} (D : ReconstructionData S) (b : GBranch S.tree) :
    holeOf D b.toNode = some (D.tree b).lonePath := by
  unfold holeOf
  exact dif_pos b.2

theorem holeOf_some {S : Garden w} (D : ReconstructionData S) {o : GNode S.tree} {q : TTree.Path}
    (h : holeOf D o = some q) : ∃ b : GBranch S.tree, b.toNode = o ∧ (D.tree b).lonePath = q := by
  unfold holeOf at h
  by_cases hb : o.1.2 ∈ (S.tree o.1.1).branching
  · rw [dif_pos hb] at h
    exact ⟨⟨o.1, hb⟩, rfl, Option.some.inj h⟩
  · rw [dif_neg hb] at h
    exact absurd h (by simp)

/-! ## Children in coordinates -/

section ChildCoord
variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
include hd

theorem nodeAt_inflatedPosition (c : GNode S.tree) :
    (inflatedPosition S D.tree c).2 ∈ (G.tree (inflatedPosition S D.tree c).1).nodes := by
  have := ((node_coord_iff D hS hd c []).mpr (TTree.nil_mem_nodes _)).1
  simpa [addrExt] using this

/-- A node in coordinates. -/
theorem node_local (z : Address w) (hz : z.2 ∈ (G.tree z.1).nodes) :
    localPath S D.tree z ∈ (localTree D hS (owner S D.tree z)).nodes := by
  apply (node_coord_iff D hS hd _ _).mp
  rw [← coord_eq]
  exact ⟨hz, rfl⟩

/-- **Children in coordinates.** For a node `z` with owner `o` and local path `q`, `z ++ [i]` is a node iff
`q ++ [i]` is a local node or `q` is the hole of `o`. -/
theorem node_child_iff (z : Address w) (hz : z.2 ∈ (G.tree z.1).nodes) (i : Fin 3) :
    (addrExt z [i]).2 ∈ (G.tree (addrExt z [i]).1).nodes ↔
      (localPath S D.tree z ++ [i] ∈ (localTree D hS (owner S D.tree z)).nodes ∨
        holeOf D (owner S D.tree z) = some (localPath S D.tree z)) := by
  have hz' := coord_eq S D.tree z
  constructor
  · intro hc
    rcases owner_child S D.tree z i with h1 | ⟨b, hb, hzb, -, -⟩
    · left
      apply (node_coord_iff D hS hd _ _).mp
      refine ⟨?_, ?_⟩
      · rw [show addrExt (inflatedPosition S D.tree (owner S D.tree z)) (localPath S D.tree z ++ [i]) =
          addrExt z [i] by conv_rhs => rw [hz']
                           simp [addrExt]]
        exact hc
      · rw [show addrExt (inflatedPosition S D.tree (owner S D.tree z)) (localPath S D.tree z ++ [i]) =
          addrExt z [i] by conv_rhs => rw [hz']
                           simp [addrExt]]
        exact h1
    · right
      rw [hb, holeOf_branch]
      congr 1
      have e := localPath_addrExt S D.tree b.toNode (D.tree b).lonePath (by rw [← hzb]; exact hb)
      rw [← hzb] at e
      exact e.symm
  · rintro (h | h)
    · have := ((node_coord_iff D hS hd _ _).mpr h).1
      rwa [show addrExt (inflatedPosition S D.tree (owner S D.tree z)) (localPath S D.tree z ++ [i]) =
          addrExt z [i] by conv_rhs => rw [hz']
                           simp [addrExt]] at this
    · obtain ⟨b, hb, hl⟩ := holeOf_some D h
      have e : addrExt z [i] = inflatedPosition S D.tree (b.child i) := by
        rw [inflatedPosition_child, hb, hl]
        conv_lhs => rw [hz']
        simp [addrExt]
      rw [e]
      exact nodeAt_inflatedPosition D hS hd _

end ChildCoord

/-! ## The coordinate correspondence -/

theorem nodeParent_eq_of_eq {F : Fin w → TTree} {n m : GNode F} {hn : n.1.2 ≠ []} {hm : m.1.2 ≠ []}
    (he : n = m) : GNode.parent n hn = GNode.parent m hm := by
  subst he
  rfl

/-- Skeleton data of a correspondence off replaced skeleton nodes. -/
structure CoordData {S S' : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (D' : ReconstructionData S')
    (hS' : S'.IsPlain) where
  ν : GNode S.tree ≃ GNode S'.tree
  Rsk : Set (GNode S.tree)
  Rsk' : Set (GNode S'.tree)
  tree : ∀ o, (ν o).1.1 = o.1.1
  root : ∀ o, (ν o).1.2 = [] ↔ o.1.2 = []
  rsk : ∀ o, ν o ∈ Rsk' ↔ o ∈ Rsk
  loc : ∀ o, o ∉ Rsk → localTree D' hS' (ν o) = localTree D hS o
  hole : ∀ o, o ∉ Rsk → holeOf D' (ν o) = holeOf D o
  child : ∀ (b : GBranch S.tree) (b' : GBranch S'.tree), b.toNode ∉ Rsk → b'.toNode = ν b.toNode → ∀ i : Fin 3,
    (b.child i ∈ Rsk ↔ b'.child i ∈ Rsk') ∧ (b.child i ∉ Rsk → ν (b.child i) = b'.child i)
  parent : ∀ o (h : o.1.2 ≠ []) (h' : (ν o).1.2 ≠ []), o ∉ Rsk →
    ((o.parent h).toNode ∈ Rsk ↔ ((ν o).parent h').toNode ∈ Rsk')

/-- The region of addresses owned by a set of skeleton nodes. -/
def ownedBy (S : Garden w) (X : GBranch S.tree → RegChain) (Q : Set (GNode S.tree)) : Set (Address w) :=
  {y | owner S X y ∈ Q}

namespace CoordData
variable {S S' : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {D' : ReconstructionData S'}
  {hS' : S'.IsPlain} (C : CoordData D hS D' hS')

/-- The reverse skeleton data. -/
def symm : CoordData D' hS' D hS where
  ν := C.ν.symm
  Rsk := C.Rsk'
  Rsk' := C.Rsk
  tree o' := by
    have := C.tree (C.ν.symm o')
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  root o' := by
    have := C.root (C.ν.symm o')
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  rsk o' := by
    have := C.rsk (C.ν.symm o')
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  loc o' ho' := by
    have h : C.ν.symm o' ∉ C.Rsk := fun h => ho' (by have := (C.rsk _).mpr h; rwa [Equiv.apply_symm_apply] at this)
    have := C.loc _ h
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  hole o' ho' := by
    have h : C.ν.symm o' ∉ C.Rsk := fun h => ho' (by have := (C.rsk _).mpr h; rwa [Equiv.apply_symm_apply] at this)
    have := C.hole _ h
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  child b' b hb' hbb i := by
    have hbb' : b'.toNode = C.ν b.toNode := by rw [hbb, Equiv.apply_symm_apply]
    have hb : b.toNode ∉ C.Rsk := by
      intro h
      apply hb'
      rw [hbb']
      exact (C.rsk _).mpr h
    obtain ⟨h1, h2⟩ := C.child b b' hb hbb' i
    refine ⟨h1.symm, fun hn => ?_⟩
    have hn' : b.child i ∉ C.Rsk := fun h => hn (h1.mp h)
    rw [← h2 hn', Equiv.symm_apply_apply]
  parent o' h h' ho' := by
    have hR : C.ν.symm o' ∉ C.Rsk := fun hh => ho' (by have := (C.rsk _).mpr hh; rwa [Equiv.apply_symm_apply] at this)
    have h'' : (C.ν (C.ν.symm o')).1.2 ≠ [] := by rw [Equiv.apply_symm_apply]; exact h
    have := C.parent (C.ν.symm o') h' h'' hR
    have e : ((C.ν (C.ν.symm o')).parent h'').toNode = (o'.parent h).toNode := by
      congr 1
      exact nodeParent_eq_of_eq (Equiv.apply_symm_apply _ _)
    rw [e] at this
    exact this.symm

/-- The address map in skeleton coordinates. -/
def map (z : Address w) : Address w :=
  addrExt (inflatedPosition S' D'.tree (C.ν (owner S D.tree z))) (localPath S D.tree z)

variable {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden) (hd' : D'.Decodes hS' LG'.garden)
include hd hd'

theorem map_node (z : Address w) (hz : NodeAt LG z) (hR : z ∉ ownedBy S D.tree C.Rsk) :
    NodeAt LG' (C.map z) ∧ owner S' D'.tree (C.map z) = C.ν (owner S D.tree z) := by
  have hl := node_local D hS hd z hz
  rw [← C.loc _ hR] at hl
  exact (node_coord_iff D' hS' hd' _ _).mpr hl

theorem map_localPath (z : Address w) (hz : NodeAt LG z) (hR : z ∉ ownedBy S D.tree C.Rsk) :
    localPath S' D'.tree (C.map z) = localPath S D.tree z :=
  localPath_addrExt S' D'.tree _ _ (C.map_node hd hd' z hz hR).2

theorem map_owner_not (z : Address w) (hz : NodeAt LG z) (hR : z ∉ ownedBy S D.tree C.Rsk) :
    C.map z ∉ ownedBy S' D'.tree C.Rsk' := by
  intro h
  change owner S' D'.tree (C.map z) ∈ C.Rsk' at h
  rw [(C.map_node hd hd' z hz hR).2, C.rsk] at h
  exact hR h

theorem map_child (z : Address w) (hz : NodeAt LG z) (hR : z ∉ ownedBy S D.tree C.Rsk) (i : Fin 3) :
    (NodeAt LG (addrExt z [i]) ↔ NodeAt LG' (addrExt (C.map z) [i])) := by
  have hn' := (C.map_node hd hd' z hz hR)
  unfold NodeAt
  rw [node_child_iff D hS hd z hz i, node_child_iff D' hS' hd' (C.map z) hn'.1 i, hn'.2,
    C.map_localPath hd hd' z hz hR, C.loc _ hR, C.hole _ hR]

end CoordData

theorem leafAt_iff_not_child {LG : LayeredGarden w} {z : Address w} (hz : NodeAt LG z) :
    LeafAt LG z ↔ ¬ NodeAt LG (addrExt z [0]) := by
  constructor
  · intro hl hc
    exact not_branchAt_of_leafAt hl (branchAt_of_child hc)
  · intro hc
    rcases (TTree.mem_nodes_iff _ _).mp hz with h | h
    · exact h
    · exact absurd (nodeAt_child h 0) hc

namespace CoordData
variable {S S' : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {D' : ReconstructionData S'}
  {hS' : S'.IsPlain} (C : CoordData D hS D' hS')
variable {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden) (hd' : D'.Decodes hS' LG'.garden)
include hd hd'

/-- The hole case of a child step: the address is the hole of the branch `b`, and `ν b` is a branch `b'` with the
same lone path. -/
theorem hole_case (z : Address w) (hz : NodeAt LG z) (hR : z ∉ ownedBy S D.tree C.Rsk) (b : GBranch S.tree)
    (hb : owner S D.tree z = b.toNode) (hzb : z = addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath) :
    ∃ b' : GBranch S'.tree, b'.toNode = C.ν b.toNode ∧ (D'.tree b').lonePath = (D.tree b).lonePath ∧
      localPath S D.tree z = (D.tree b).lonePath := by
  have hbR : b.toNode ∉ C.Rsk := by rw [← hb]; exact hR
  have hh := C.hole _ hbR
  rw [holeOf_branch] at hh
  obtain ⟨b', hb', hl⟩ := holeOf_some D' hh
  refine ⟨b', hb', hl, ?_⟩
  have e := localPath_addrExt S D.tree b.toNode (D.tree b).lonePath (by rw [← hzb]; exact hb)
  rwa [← hzb] at e

/-- **The coordinate correspondence.** -/
def toOutIso (hpair : ∀ z (h : LeafAt LG z) (h' : LeafAt LG' (C.map z)), z ∉ ownedBy S D.tree C.Rsk →
      (LG'.garden.pair ⟨C.map z, h'⟩).1.1 = (LG.garden.pair ⟨z, h⟩).1.1) :
    OutIso LG LG' (ownedBy S D.tree C.Rsk) (ownedBy S' D'.tree C.Rsk') where
  f := C.map
  node z hz hR := ⟨(C.map_node hd hd' z hz hR).1, C.map_owner_not hd hd' z hz hR⟩
  tree z hz hR := by
    show (inflatedPosition S' D'.tree (C.ν (owner S D.tree z))).1 = z.1
    rw [inflatedPosition_fst, C.tree, owner_fst]
  root z hz hR := by
    show (inflatedPosition S' D'.tree (C.ν (owner S D.tree z))).2 ++ localPath S D.tree z = [] ↔ z.2 = []
    conv_rhs => rw [coord_eq S D.tree z]
    show _ ↔ (inflatedPosition S D.tree (owner S D.tree z)).2 ++ localPath S D.tree z = []
    rw [List.append_eq_nil_iff, List.append_eq_nil_iff, inflatedPosition_nil_iff, inflatedPosition_nil_iff, C.root]
  leaf z hz hR := by
    have hn' := (C.map_node hd hd' z hz hR).1
    rw [leafAt_iff_not_child hn', leafAt_iff_not_child hz, C.map_child hd hd' z hz hR 0]
  child z i hz hR hc hcR := by
    rcases owner_child S D.tree z i with h1 | ⟨b, hb, hzb, hci, hco⟩
    · show addrExt (inflatedPosition S' D'.tree (C.ν (owner S D.tree (addrExt z [i])))) (localPath S D.tree (addrExt z [i])) =
        addrExt (addrExt (inflatedPosition S' D'.tree (C.ν (owner S D.tree z))) (localPath S D.tree z)) [i]
      have e : addrExt z [i] = addrExt (inflatedPosition S D.tree (owner S D.tree z)) (localPath S D.tree z ++ [i]) := by
        conv_lhs => rw [coord_eq S D.tree z]
        simp [addrExt]
      have hl : localPath S D.tree (addrExt z [i]) = localPath S D.tree z ++ [i] := by
        rw [e]
        exact localPath_addrExt S D.tree _ _ (by rw [← e]; exact h1)
      rw [h1, hl]
      simp [addrExt]
    · obtain ⟨b', hb', hl', hq⟩ := C.hole_case hd hd' z hz hR b hb hzb
      have hcR' : b.child i ∉ C.Rsk := by
        intro h
        apply hcR
        change owner S D.tree (addrExt z [i]) ∈ C.Rsk
        rw [hco]
        exact h
      have hbR : b.toNode ∉ C.Rsk := by rw [← hb]; exact hR
      have hν := (C.child b b' hbR hb' i).2 hcR'
      show addrExt (inflatedPosition S' D'.tree (C.ν (owner S D.tree (addrExt z [i])))) (localPath S D.tree (addrExt z [i])) =
        addrExt (addrExt (inflatedPosition S' D'.tree (C.ν (owner S D.tree z))) (localPath S D.tree z)) [i]
      have hl0 : localPath S D.tree (addrExt z [i]) = [] := by
        rw [hci]
        exact localPath_addrExt S D.tree _ [] (by rw [← hci]; simpa [addrExt] using hco) |>.trans rfl
          |> fun h => by simpa [addrExt] using h
      rw [hco, hν, hl0, hb, ← hb', hq, inflatedPosition_child, ← hl']
      simp [addrExt]
  childR z i hz hR := by
    constructor
    · rintro ⟨hc, hcR⟩
      rcases owner_child S D.tree z i with h1 | ⟨b, hb, hzb, hci, hco⟩
      · exfalso
        change owner S D.tree (addrExt z [i]) ∈ C.Rsk at hcR
        rw [h1] at hcR
        exact hR hcR
      · obtain ⟨b', hb', hl', hq⟩ := C.hole_case hd hd' z hz hR b hb hzb
        have hbR : b.toNode ∉ C.Rsk := by rw [← hb]; exact hR
        have hin : b.child i ∈ C.Rsk := by
          change owner S D.tree (addrExt z [i]) ∈ C.Rsk at hcR
          rwa [hco] at hcR
        have hin' := (C.child b b' hbR hb' i).1.mp hin
        have e : addrExt (C.map z) [i] = inflatedPosition S' D'.tree (b'.child i) := by
          rw [inflatedPosition_child, hb']
          show addrExt (addrExt (inflatedPosition S' D'.tree (C.ν (owner S D.tree z))) (localPath S D.tree z)) [i] = _
          rw [hb, hq, ← hl']
          simp [addrExt]
        rw [e]
        refine ⟨nodeAt_inflatedPosition D' hS' hd' _, ?_⟩
        change owner S' D'.tree _ ∈ C.Rsk'
        rw [owner_inflatedPosition]
        exact hin'
    · rintro ⟨hc', hcR'⟩
      have hn' := C.map_node hd hd' z hz hR
      rcases owner_child S' D'.tree (C.map z) i with h1 | ⟨b', hb', hzb', hci', hco'⟩
      · exfalso
        change owner S' D'.tree (addrExt (C.map z) [i]) ∈ C.Rsk' at hcR'
        rw [h1, hn'.2, C.rsk] at hcR'
        exact hR hcR'
      · -- `C.map z` is the hole of `b' = ν o`, so `z` is the hole of `o`
        have hoR : owner S D.tree z ∉ C.Rsk := hR
        have hh := C.hole _ hoR
        rw [← hn'.2, hb', holeOf_branch] at hh
        obtain ⟨b, hb, hl⟩ := holeOf_some D hh.symm
        have hq' : localPath S' D'.tree (C.map z) = (D'.tree b').lonePath := by
          have e := localPath_addrExt S' D'.tree b'.toNode (D'.tree b').lonePath (by rw [← hzb']; exact hb')
          rwa [← hzb'] at e
        rw [C.map_localPath hd hd' z hz hR] at hq'
        have hzb : z = addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath := by
          conv_lhs => rw [coord_eq S D.tree z]
          rw [hb, hq', hl]
        have hbR : b.toNode ∉ C.Rsk := by rw [hb]; exact hR
        have hbb' : b'.toNode = C.ν b.toNode := by rw [hb, ← hn'.2]; exact hb'.symm
        have hin' : b'.child i ∈ C.Rsk' := by
          change owner S' D'.tree (addrExt (C.map z) [i]) ∈ C.Rsk' at hcR'
          rwa [hco'] at hcR'
        have hin := (C.child b b' hbR hbb' i).1.mpr hin'
        have e : addrExt z [i] = inflatedPosition S D.tree (b.child i) := by
          rw [inflatedPosition_child, hzb]
          simp [addrExt]
        rw [e]
        refine ⟨nodeAt_inflatedPosition D hS hd _, ?_⟩
        change owner S D.tree _ ∈ C.Rsk
        rw [owner_inflatedPosition]
        exact hin
  parentR z hz hR hne := by
    have hn' := C.map_node hd hd' z hz hR
    by_cases hq : localPath S D.tree z = []
    · -- `z` is the inflated position of a non-root owner
      set o := owner S D.tree z
      have hzo : z = inflatedPosition S D.tree o := by
        conv_lhs => rw [coord_eq S D.tree z]
        rw [hq]
        simp [addrExt]
        rfl
      have hon : o.1.2 ≠ [] := fun h => hne (by
        have := (inflatedPosition_nil_iff S D.tree o).mpr h
        rw [← hzo] at this
        exact this)
      have hon' : (C.ν o).1.2 ≠ [] := fun h => hon ((C.root o).mp h)
      have hfz : C.map z = inflatedPosition S' D'.tree (C.ν o) := by
        show addrExt _ (localPath S D.tree z) = _
        rw [hq]
        simp [addrExt]
        rfl
      rw [hfz]
      conv_lhs => rw [hzo]
      rw [inflatedPosition_parent S D.tree o hon, inflatedPosition_parent S' D'.tree (C.ν o) hon']
      have e1 : owner S D.tree (addrExt (inflatedPosition S D.tree (o.parent hon).toNode) (D.tree (o.parent hon)).lonePath) =
          (o.parent hon).toNode :=
        ((node_coord_iff D hS hd _ _).mpr (by
          rw [localTree_branch]
          exact (TTree.mem_nodes_iff _ _).mpr (Or.inl (lonePath_mem_leaves _ _)))).2
      have e2 : owner S' D'.tree (addrExt (inflatedPosition S' D'.tree ((C.ν o).parent hon').toNode)
          (D'.tree ((C.ν o).parent hon')).lonePath) = ((C.ν o).parent hon').toNode :=
        ((node_coord_iff D' hS' hd' _ _).mpr (by
          rw [localTree_branch]
          exact (TTree.mem_nodes_iff _ _).mpr (Or.inl (lonePath_mem_leaves _ _)))).2
      change owner S D.tree _ ∈ C.Rsk ↔ owner S' D'.tree _ ∈ C.Rsk'
      rw [e1, e2]
      exact C.parent o hon hon' hR
    · -- the parent stays in the owner's region on both sides
      have hl := node_local D hS hd z hz
      have hpz : ((z.1, z.2.dropLast) : Address w) =
          addrExt (inflatedPosition S D.tree (owner S D.tree z)) (localPath S D.tree z).dropLast := by
        conv_lhs => rw [coord_eq S D.tree z]
        simp only [addrExt]
        refine Prod.ext rfl ?_
        show ((inflatedPosition S D.tree (owner S D.tree z)).2 ++ localPath S D.tree z).dropLast = _
        rw [List.dropLast_append_of_ne_nil hq]
      have hpz' : (((C.map z).1, (C.map z).2.dropLast) : Address w) =
          addrExt (inflatedPosition S' D'.tree (C.ν (owner S D.tree z))) (localPath S D.tree z).dropLast := by
        show (((inflatedPosition S' D'.tree (C.ν (owner S D.tree z))).1,
          ((inflatedPosition S' D'.tree (C.ν (owner S D.tree z))).2 ++ localPath S D.tree z).dropLast) : Address w) = _
        rw [List.dropLast_append_of_ne_nil hq]
        rfl
      have hmem : (localPath S D.tree z).dropLast ∈ (localTree D hS (owner S D.tree z)).nodes := by
        have := prefix_mem_nodes _ (s := [(localPath S D.tree z).getLast hq]) (by
          rw [List.dropLast_append_getLast hq]
          exact hl)
        exact this
      have o1 := ((node_coord_iff D hS hd _ _).mpr hmem).2
      have hmem' : (localPath S D.tree z).dropLast ∈ (localTree D' hS' (C.ν (owner S D.tree z))).nodes := by
        rw [C.loc _ hR]
        exact hmem
      have o2 := ((node_coord_iff D' hS' hd' _ _).mpr hmem').2
      change owner S D.tree _ ∈ C.Rsk ↔ owner S' D'.tree _ ∈ C.Rsk'
      rw [hpz, hpz', o1, o2, C.rsk]
  pairTree := hpair

theorem symm_map_map (z : Address w) (hz : NodeAt LG z) (hR : z ∉ ownedBy S D.tree C.Rsk) :
    C.symm.map (C.map z) = z := by
  have hn := C.map_node hd hd' z hz hR
  show addrExt (inflatedPosition S D.tree (C.ν.symm (owner S' D'.tree (C.map z)))) (localPath S' D'.tree (C.map z)) = z
  rw [hn.2, Equiv.symm_apply_apply, C.map_localPath hd hd' z hz hR]
  exact (coord_eq S D.tree z).symm

end CoordData

end WaveTurbulence.Flower.MkMark
