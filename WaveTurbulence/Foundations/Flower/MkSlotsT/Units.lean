/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntAdm
public import WaveTurbulence.Foundations.Flower.MkMark.StepSel
public import WaveTurbulence.Foundations.Flower.ProtGeo.Vine
public import WaveTurbulence.Foundations.Flower.MkSlots.IntGeo

/-! # B3s-HELPER5 (γ) T1, part 1: capped stems do not enter spliced units

Generic facts about a CL block `U` (upper joint `a`) with a chain assembly whose pieces carry the atoms of vines of a
set `V`, when the capped stem of a garden avoids the twist-active set `𝐀(c)` of every `c ∈ V` (`StemAvoid`, B2b's
address form of `StemCleanAt`).

* chain assemblies (`CLChainAssembly`): every piece lies in the region (`piece_atoms_sub`), the upper joint `a` is the
  upper joint of a piece (`exists_piece_upper`), and every other atom of the region is a non-upper atom of a piece
  (`exists_piece_nonUpper`);
* a dart at a joint `a` of two blocks `P ⊆ U` that is internal to `U` is internal to `P` (`inGroup_of_joint`: both
  have internal out- and in-degree `1` at `a`);
* owners of the native addresses of a slot (`owner_of_mem_nodeBlock_inr`, `owner_of_mem_nodeBlock_inl`,
  `owner_corePosition`);
* **`owner_eq_upper_of_stem`**: an address on a capped stem owned by an atom `β ∈ U` is owned by the upper joint
  (`β = a`): otherwise `β` is a non-upper atom of a vine `c ∈ V` (IntAdm's `ne_upper_of_piece`), so the address is
  in `𝐀(c)`;
* **`not_internalLeaf_of_stem`**: an address on a capped stem owned by a skeleton leaf `ℓ` is not below an internal
  leaf-pair bond of `U`: the parent `x` of `ℓ` is on the stem (its core address is above), so `x = a`; an LP dart at
  the joint `a` internal to `U` is internal to the first piece, a vine `c ∈ V`, and the address lies in `𝐀(c)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.VineEstS2 (CLChainAssembly assemblyPieceAt)
open WaveTurbulence.Flower.MkMark (owner activeSet StemAvoid CapFlowerAt mem_ownRegion_iff owner_eq_leaf
  owner_eq_branch)
open WaveTurbulence.Flower.MkSlots (slotOf)

namespace WaveTurbulence.Flower.MkSlotsT

variable {w : ℕ}

/-! ## Chain assemblies -/

section Chain
variable {G : Garden w}

/-- Every piece of a chain assembly lies in its region. -/
theorem piece_atoms_sub {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (i : Fin n) : (assemblyPieceAt B i).atoms ⊆ U := by
  induction B with
  | single hV R => exact fun x hx => hx
  | append B hT hi hU R ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exact Finset.subset_union_right
    · exact (ih k).trans Finset.subset_union_left

/-- The upper joint of the region is the upper joint of a piece. -/
theorem exists_piece_upper {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : ∃ i, (assemblyPieceAt B i).upper = a := by
  induction B with
  | single hV R => exact ⟨0, rfl⟩
  | append B hT hi hU R ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k.succ, hk⟩

/-- Every atom of the region other than its upper joint is a non-upper atom of a piece. -/
theorem exists_piece_nonUpper {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (B : CLChainAssembly G R n) :
    ∀ v ∈ U, v ≠ a → ∃ i, v ∈ (assemblyPieceAt B i).atoms ∧ v ≠ (assemblyPieceAt B i).upper := by
  induction B with
  | single hV R => exact fun v hv hva => ⟨0, hv, hva⟩
  | @append S T a' b' c' n' RP B X hT hi hU R ih =>
    intro v hv hva
    by_cases hS : v ∈ S
    · obtain ⟨k, hk⟩ := ih v hS hva
      exact ⟨k.succ, hk⟩
    · have hvT : v ∈ T := (Finset.mem_union.mp hv).resolve_left hS
      refine ⟨0, hvT, ?_⟩
      intro hvb
      apply hS
      have hb : b' ∈ S ∩ T := by rw [hi]; exact Finset.mem_singleton_self _
      rw [hvb]
      exact (Finset.mem_inter.mp hb).1

end Chain

/-! ## Darts at a joint -/

section Joint
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem inGroup_mono {P U : Finset V} (hPU : P ⊆ U) {x : D} (h : M.InGroup P x) : M.InGroup U x :=
  ⟨hPU h.1, hPU h.2⟩

/-- **A dart at a common joint of two nested blocks.** If `a` is a joint of the blocks `P ⊆ U`, every dart at `a`
internal to `U` is internal to `P` (both have internal out-degree and in-degree `1` at `a`). -/
theorem inGroup_of_joint {P U : Finset V} {a b b' : V} (hP : M.IsBlock P a b) (hU : M.IsBlock U a b')
    (hPU : P ⊆ U) {x : D} (hx : M.atom x = a) (hxU : M.InGroup U x) : M.InGroup P x := by
  have hxa : x ∈ M.dartsAt a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  cases hout : M.out x
  · have hsub : ((M.dartsAt a).filter fun y => M.InGroup P y ∧ M.out y = false) ⊆
        ((M.dartsAt a).filter fun y => M.InGroup U y ∧ M.out y = false) := by
      intro y hy
      obtain ⟨hy1, hy2, hy3⟩ := by simpa only [Finset.mem_filter] using hy
      exact Finset.mem_filter.mpr ⟨hy1, inGroup_mono M hPU hy2, hy3⟩
    have hcard : ((M.dartsAt a).filter fun y => M.InGroup U y ∧ M.out y = false).card ≤
        ((M.dartsAt a).filter fun y => M.InGroup P y ∧ M.out y = false).card := by
      have h1 : M.inIn U a = 1 := hU.2.2.2.2.2.1
      have h2 : M.inIn P a = 1 := hP.2.2.2.2.2.1
      unfold Molecule.inIn at h1 h2
      rw [h1, h2]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : x ∈ ((M.dartsAt a).filter fun y => M.InGroup U y ∧ M.out y = false) :=
      Finset.mem_filter.mpr ⟨hxa, hxU, hout⟩
    rw [← heq] at hmem
    exact (Finset.mem_filter.mp hmem).2.1
  · have hsub : ((M.dartsAt a).filter fun y => M.InGroup P y ∧ M.out y = true) ⊆
        ((M.dartsAt a).filter fun y => M.InGroup U y ∧ M.out y = true) := by
      intro y hy
      obtain ⟨hy1, hy2, hy3⟩ := by simpa only [Finset.mem_filter] using hy
      exact Finset.mem_filter.mpr ⟨hy1, inGroup_mono M hPU hy2, hy3⟩
    have hcard : ((M.dartsAt a).filter fun y => M.InGroup U y ∧ M.out y = true).card ≤
        ((M.dartsAt a).filter fun y => M.InGroup P y ∧ M.out y = true).card := by
      have h1 : M.outIn U a = 1 := hU.2.2.2.2.1
      have h2 : M.outIn P a = 1 := hP.2.2.2.2.1
      unfold Molecule.outIn at h1 h2
      rw [h1, h2]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : x ∈ ((M.dartsAt a).filter fun y => M.InGroup U y ∧ M.out y = true) :=
      Finset.mem_filter.mpr ⟨hxa, hxU, hout⟩
    rw [← heq] at hmem
    exact (Finset.mem_filter.mp hmem).2.1

end Joint

/-! ## Owners of native addresses -/

section Owners
variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The core address of a skeleton branch is owned by the branch. -/
theorem owner_corePosition (b : GBranch S.tree) : owner S D.tree (D.corePosition b) = b.toNode :=
  (mem_ownRegion_iff S D.tree).mp (ProtGeo.skelAddr_mem_ownRegion S D.tree b)

/-- The native addresses of the chain slot of `b` (its regular tree and its core address) are owned by `b`. -/
theorem owner_of_mem_nodeBlock_inr (b : GBranch S.tree) {x : Address w} (hx : x ∈ D.nodeBlock hS (.inr b)) :
    owner S D.tree x = b.toNode := by
  have hx' : x ∈ nodeAddresses ((D.tree b).plug (nodeSign S.sig b.1) .leaf) (inflatedPosition S D.tree b.toNode) := by
    rw [chain_nodeAddresses, nodeAddresses_leaf]
    exact hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx'
  by_cases hlone : r = (D.tree b).lonePath
  · subst hlone
    exact owner_corePosition D b
  · refine owner_eq_branch S D.tree (MkMark.addrBelow_addrExt _ _) ?_
    rintro ⟨-, s, hs⟩
    have hs' : (D.tree b).lonePath ++ s = r := by
      simp only [addrExt, List.append_assoc] at hs
      exact List.append_cancel_left hs
    have hl := MkMark.lonePath_mem_leaves (D.tree b) (nodeSign S.sig b.1)
    have hs0 : s = [] := MkMark.eq_nil_of_leaf_append _ hl (by rw [hs']; exact hr)
    subst hs0
    exact hlone (by simpa using hs'.symm)

/-- The native addresses of the couple slot of `q` are owned by one of its two leaves. -/
theorem owner_of_mem_nodeBlock_inl (q : SourcePair S) {x : Address w} (hx : x ∈ D.nodeBlock hS (.inl q)) :
    owner S D.tree x = (q.firstLeaf hS).toNode ∨ owner S D.tree x = (q.secondLeaf hS).toNode := by
  have hx' : x ∈ nodeAddresses (D.couple q).trees.1 (inflatedPosition S D.tree (q.firstLeaf hS).toNode) ∪
      nodeAddresses (D.couple q).trees.2 (inflatedPosition S D.tree (q.secondLeaf hS).toNode) := by
    rw [couple_nodeAddresses]
    exact hx
  rcases Finset.mem_union.mp hx' with h | h
  · obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp h
    exact Or.inl (owner_eq_leaf S D.tree (MkMark.addrBelow_addrExt _ _))
  · obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp h
    exact Or.inr (owner_eq_leaf S D.tree (MkMark.addrBelow_addrExt _ _))

/-- The native addresses of a chain slot are owned by its branch. -/
theorem owner_slotOf_inr (z : GNode (D.forest hS)) (β : GBranch S.tree) (hβ : slotOf D hS z = Sum.inr β) :
    owner S D.tree z.1 = β.toNode := by
  obtain ⟨a, rfl⟩ := MkSlots.IntGeo.exists_nativeNodeAt_of_slotOf D hS hβ
  exact owner_of_mem_nodeBlock_inr D hS β (nativeNodeAt_mem_block D hS _ a)

/-- The native addresses of a couple slot are owned by one of its leaves. -/
theorem owner_slotOf_inl (z : GNode (D.forest hS)) (q : SourcePair S) (hq : slotOf D hS z = Sum.inl q) :
    owner S D.tree z.1 = (q.firstLeaf hS).toNode ∨ owner S D.tree z.1 = (q.secondLeaf hS).toNode := by
  obtain ⟨a, rfl⟩ := MkSlots.IntGeo.exists_nativeNodeAt_of_slotOf D hS hq
  exact owner_of_mem_nodeBlock_inl D hS q (nativeNodeAt_mem_block D hS _ a)

end Owners

/-! ## Capped stems avoid the interiors of clean units -/

/-- An address on a capped stem (a prefix of a capped flower). -/
def OnStemAddr (LG : LayeredGarden w) (J : Finset (Fin w)) (z : Address w) : Prop :=
  ∃ ℓ : Address w, CapFlowerAt LG J ℓ ∧ AddrBelow z ℓ

theorem onStemAddr_of_addrBelow {LG : LayeredGarden w} {J : Finset (Fin w)} {x z : Address w}
    (hz : OnStemAddr LG J z) (h : AddrBelow x z) : OnStemAddr LG J x := by
  obtain ⟨ℓ, hℓ, hzℓ⟩ := hz
  exact ⟨ℓ, hℓ, MkMark.addrBelow_trans h hzℓ⟩

section Stem
variable {S : Garden w} (X : GBranch S.tree → RegChain) {LG : LayeredGarden w} {J : Finset (Fin w)}
  (V : Set (Stage1.CLVine S)) (hclean : ∀ c ∈ V, StemAvoid LG J (activeSet S X c.atoms c.upper))
  {U : Finset (GBranch S.tree)} {a b : GBranch S.tree} {R : CLRegionData S U a b} {n : ℕ}
  (B : CLChainAssembly S R n) (hB : ∀ i, ∃ c ∈ V, c.atoms = (assemblyPieceAt B i).atoms)
include hclean hB

/-- **A capped-stem address owned by an atom of the unit is owned by its upper joint.** -/
theorem owner_eq_upper_of_stem {z : Address w} (hz : OnStemAddr LG J z) {β : GBranch S.tree}
    (hβ : owner S X z = β.toNode) (hβU : β ∈ U) : β = a := by
  by_contra hne
  obtain ⟨i, hi, hiu⟩ := exists_piece_nonUpper B β hβU hne
  obtain ⟨c, hcV, hca⟩ := hB i
  have hcu : β ≠ c.upper := MkSlots.ne_upper_of_piece B i c hca hi hiu
  obtain ⟨ℓ, hℓ, hzℓ⟩ := hz
  apply hclean c hcV ℓ hℓ z hzℓ
  show owner S X z ∈ clRealizationNodes S c.atoms ∧ owner S X z ≠ c.upper.toNode
  rw [hβ]
  refine ⟨(branch_mem_clRealizationNodes β).mpr (hca ▸ hi), fun h => hcu ?_⟩
  exact Mole.branch_toNode_injective h

/-- **A capped-stem address owned by a skeleton leaf does not sit on an internal leaf pair of the unit.** -/
theorem not_internalLeaf_of_stem {z : Address w} (hz : OnStemAddr LG J z) {ℓ : GLeaf S.tree}
    (hℓ : owner S X z = ℓ.toNode) : ¬ Mole.IsInternalLeaf S U ℓ := by
  rintro ⟨hm, hn, hp, hg⟩
  -- the parent `x` of `ℓ`, an atom of `U`
  set x : GBranch S.tree := GNode.parent ℓ.toNode hn with hxdef
  have hxU : x ∈ U := hg.1
  -- the core address of `x` is above `z`, so it is on the stem and owned by `x`
  have hreg : z ∈ ownRegion S X ℓ.toNode := (mem_ownRegion_iff S X).mpr hℓ
  have hinf : inflatedPosition S X ℓ.toNode =
      addrExt (inflatedPosition S X x.toNode) ((X x).lonePath ++ [ℓ.toNode.1.2.getLast hn]) := by
    conv_lhs => rw [← Reg.Skeleton.child_parent ℓ.toNode hn]
    exact inflatedPosition_child S X _ _
  have hcore : AddrBelow (addrExt (inflatedPosition S X x.toNode) (X x).lonePath) z := by
    refine MkMark.addrBelow_trans ?_ hreg.1
    rw [hinf]
    refine ⟨rfl, ?_⟩
    show (inflatedPosition S X x.toNode).2 ++ (X x).lonePath <+:
      (inflatedPosition S X x.toNode).2 ++ ((X x).lonePath ++ [ℓ.toNode.1.2.getLast hn])
    rw [← List.append_assoc]
    exact List.prefix_append _ _
  have hxs : OnStemAddr LG J (addrExt (inflatedPosition S X x.toNode) (X x).lonePath) :=
    onStemAddr_of_addrBelow hz hcore
  have hxo : owner S X (addrExt (inflatedPosition S X x.toNode) (X x).lonePath) = x.toNode :=
    (mem_ownRegion_iff S X).mp (ProtGeo.skelAddr_mem_ownRegion S X x)
  have hxa : x = a := owner_eq_upper_of_stem X V hclean B hB hxs hxo hxU
  -- the LP dart of `ℓ` at the joint `a` is internal to the first piece
  obtain ⟨i, hi⟩ := exists_piece_upper B
  have hP := (assemblyPieceAt B i).vine.1
  rw [hi] at hP
  have hgP : S.molecule.InGroup (assemblyPieceAt B i).atoms (.inr ⟨ℓ, hm, hn, hp⟩) :=
    inGroup_of_joint S.molecule hP B.isBlock (piece_atoms_sub B i) hxa hg
  obtain ⟨c, hcV, hca⟩ := hB i
  have hint : Mole.IsInternalLeaf S c.atoms ℓ := ⟨hm, hn, hp, hca ▸ hgP⟩
  obtain ⟨ℓf, hℓf, hzℓf⟩ := hz
  apply hclean c hcV ℓf hℓf z hzℓf
  show owner S X z ∈ clRealizationNodes S c.atoms ∧ owner S X z ≠ c.upper.toNode
  rw [hℓ]
  exact ⟨(leaf_mem_clRealizationNodes ℓ).mpr hint, fun h => Mole.branch_toNode_ne_leaf _ _ h.symm⟩

end Stem

end WaveTurbulence.Flower.MkSlotsT
