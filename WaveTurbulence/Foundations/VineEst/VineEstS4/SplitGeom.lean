/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainNoCross
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainSplit
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalDecorations

/-! # Geometry of splitting a CL block `U = S ∪ T` at the joint `b` (V5 Step 4b, P2.3)

`S` is a CL block with joints `(a, b)`, `T` a CL block with joints `(b, c)`, `S ∩ T = {b}`, and `U = S ∪ T` is a block with
joints `(a, c)`.  Everything here is derived from the block premises:
* internal bonds, internal leaves and the realization nodes of `U` are those of `S` and of `T`;
* the slots of the upper joint `a` and of the lower joint `c` of `U` are those of `S` and of `T`; the excluded child of the
  upper joint `b` of `T` is the kept child of the lower joint `b` of `S`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
variable {w : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

section Split
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)
include hS hT hi hU

theorem split_inGroup (e : GardenDart G) :
    G.molecule.InGroup (S ∪ T) e ↔ G.molecule.InGroup S e ∨ G.molecule.InGroup T e :=
  block_concat_inGroup_iff G.molecule (Mole.garden_isMolecule G) hS hT hi hU e

theorem split_not_both (e : GardenDart G) : ¬ (G.molecule.InGroup S e ∧ G.molecule.InGroup T e) := by
  rintro ⟨hs, ht⟩
  have ha : G.molecule.atom e = b := Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨hs.1, ht.1⟩)
  have hb : G.molecule.atom (G.molecule.mate e) = b := Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨hs.2, ht.2⟩)
  have hd := (isBlock_iff_degree_connected G.molecule T b c).mp hT
  exact Mole.connected_block_no_joint_loop G.molecule hT hd.2 (Or.inl ha) (hb.trans ha.symm)

theorem split_internalLeaf (l : GLeaf G.tree) :
    Mole.IsInternalLeaf G (S ∪ T) l ↔ Mole.IsInternalLeaf G S l ∨ Mole.IsInternalLeaf G T l := by
  constructor
  · rintro ⟨hm, hn, hp, hg⟩
    rcases (split_inGroup hS hT hi hU _).mp hg with h | h
    · exact Or.inl ⟨hm, hn, hp, h⟩
    · exact Or.inr ⟨hm, hn, hp, h⟩
  · rintro (⟨hm, hn, hp, hg⟩ | ⟨hm, hn, hp, hg⟩)
    · exact ⟨hm, hn, hp, (split_inGroup hS hT hi hU _).mpr (Or.inl hg)⟩
    · exact ⟨hm, hn, hp, (split_inGroup hS hT hi hU _).mpr (Or.inr hg)⟩

theorem split_not_internalLeaf_both (l : GLeaf G.tree) :
    ¬ (Mole.IsInternalLeaf G S l ∧ Mole.IsInternalLeaf G T l) := by
  rintro ⟨⟨hm, hn, hp, hg⟩, ⟨hm', hn', hp', hg'⟩⟩
  exact split_not_both hS hT hi hU _ ⟨hg, hg'⟩

theorem split_realization (x : GNode G.tree) :
    x ∈ clRealizationNodes G (S ∪ T) ↔ x ∈ clRealizationNodes G S ∨ x ∈ clRealizationNodes G T := by
  rw [mem_clRealizationNodes, mem_clRealizationNodes, mem_clRealizationNodes]
  unfold Mole.InIncidenceRealization
  constructor
  · rintro (⟨v, hv, rfl⟩ | ⟨l, hl, rfl⟩)
    · rcases Finset.mem_union.mp hv with h | h
      · exact Or.inl (Or.inl ⟨v, h, rfl⟩)
      · exact Or.inr (Or.inl ⟨v, h, rfl⟩)
    · rcases (split_internalLeaf hS hT hi hU l).mp hl with h | h
      · exact Or.inl (Or.inr ⟨l, h, rfl⟩)
      · exact Or.inr (Or.inr ⟨l, h, rfl⟩)
  · rintro ((⟨v, hv, rfl⟩ | ⟨l, hl, rfl⟩) | (⟨v, hv, rfl⟩ | ⟨l, hl, rfl⟩))
    · exact Or.inl ⟨v, Finset.mem_union_left _ hv, rfl⟩
    · exact Or.inr ⟨l, (split_internalLeaf hS hT hi hU l).mpr (Or.inl hl), rfl⟩
    · exact Or.inl ⟨v, Finset.mem_union_right _ hv, rfl⟩
    · exact Or.inr ⟨l, (split_internalLeaf hS hT hi hU l).mpr (Or.inr hl), rfl⟩

theorem split_internalPositions (v : GBranch G.tree) :
    Mole.internalPositions G (S ∪ T) v = Mole.internalPositions G S v ∪ Mole.internalPositions G T v := by
  ext i
  rw [Finset.mem_union, Mole.mem_internalPositions, Mole.mem_internalPositions, Mole.mem_internalPositions]
  constructor
  · rintro ⟨x, hx, hg, hp⟩
    rcases (split_inGroup hS hT hi hU x).mp hg with h | h
    · exact Or.inl ⟨x, hx, h, hp⟩
    · exact Or.inr ⟨x, hx, h, hp⟩
  · rintro (⟨x, hx, hg, hp⟩ | ⟨x, hx, hg, hp⟩)
    · exact ⟨x, hx, (split_inGroup hS hT hi hU x).mpr (Or.inl hg), hp⟩
    · exact ⟨x, hx, (split_inGroup hS hT hi hU x).mpr (Or.inr hg), hp⟩

theorem split_a_not_mem : a ∉ T := by
  intro ha
  have := Finset.mem_inter.mpr ⟨hS.2.1, ha⟩
  rw [hi, Finset.mem_singleton] at this
  exact hS.2.2.2.1 this

theorem split_c_not_mem : c ∉ S := by
  intro hc
  have := Finset.mem_inter.mpr ⟨hc, hT.2.2.1⟩
  rw [hi, Finset.mem_singleton] at this
  exact hT.2.2.2.1 this.symm

theorem split_internalPositions_a : Mole.internalPositions G (S ∪ T) a = Mole.internalPositions G S a := by
  rw [split_internalPositions hS hT hi hU]
  have : Mole.internalPositions G T a = ∅ := by
    ext i
    simp only [Finset.notMem_empty, iff_false]
    intro h
    obtain ⟨x, hx, hg, _⟩ := (Mole.mem_internalPositions G).mp h
    exact split_a_not_mem hS hT hi hU (hx ▸ hg.1)
  rw [this, Finset.union_empty]

theorem split_internalPositions_c : Mole.internalPositions G (S ∪ T) c = Mole.internalPositions G T c := by
  rw [split_internalPositions hS hT hi hU]
  have : Mole.internalPositions G S c = ∅ := by
    ext i
    simp only [Finset.notMem_empty, iff_false]
    intro h
    obtain ⟨x, hx, hg, _⟩ := (Mole.mem_internalPositions G).mp h
    exact split_c_not_mem hS hT hi hU (hx ▸ hg.1)
  rw [this, Finset.empty_union]

theorem split_excluded_a (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) :
    RU.excluded = RS.excluded := by
  by_contra h
  have h1 := (RU.upper RU.excluded)
  have h2 := RS.upper RU.excluded
  rw [split_internalPositions_a hS hT hi hU] at h1
  exact (not_not.mpr rfl : ¬ RU.excluded ≠ RU.excluded) (h1.mp (h2.mpr h))

theorem split_kept_c (RU : CLRegionData G (S ∪ T) a c) (RT : CLRegionData G T b c) :
    RU.kept = RT.kept := by
  have h1 := RU.lower RT.kept
  rw [split_internalPositions_c hS hT hi hU] at h1
  exact (h1.mp ((RT.lower RT.kept).mpr rfl)).symm

theorem split_positive_c (RU : CLRegionData G (S ∪ T) a c) (RT : CLRegionData G T b c) :
    RU.positive = RT.positive ∧ RU.negative = RT.negative := by
  have hk := split_kept_c hS hT hi hU RU RT
  have hpos : RU.positive ≠ RU.kept := fun h => by
    have := (RU.lower_excluded RU.positive).mpr (Or.inl rfl)
    exact this h
  have hneg : RU.negative ≠ RU.kept := fun h => by
    have := (RU.lower_excluded RU.negative).mpr (Or.inr rfl)
    exact this h
  have hpos' := (RT.lower_excluded RU.positive).mp (hk ▸ hpos)
  have hneg' := (RT.lower_excluded RU.negative).mp (hk ▸ hneg)
  have s1 := RU.positive_sign
  have s2 := RU.negative_sign
  have t1 := RT.positive_sign
  have t2 := RT.negative_sign
  rcases hpos' with h | h <;> rcases hneg' with h' | h'
  · exact (RU.distinct (h.trans h'.symm)).elim
  · refine ⟨h, h'⟩
  · exfalso
    rw [h, t2] at s1
    exact absurd s1 (by decide)
  · exact (RU.distinct (h.trans h'.symm)).elim

end Split

end WaveTurbulence.VineEstS4
