/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.BondInclusion
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainNoCross

/-! # The exact internal-bond disjoint union of a proper source concatenation -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract Finset RegRed
variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {S T : Finset V} {a b c : V}

theorem block_concat_internalBondSet_disjoint
    (hT : M.IsBlock T b c) (hi : S ∩ T = {b}) :
    Disjoint (internalBondSet M S) (internalBondSet M T) := by
  apply Finset.disjoint_left.mpr
  intro e heS heT
  have hs := (Finset.mem_filter.mp heS).2
  have ht := (Finset.mem_filter.mp heT).2
  have ha : M.atom e = b := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hs.1,ht.1⟩)
  have hb : M.atom (M.mate e) = b := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hs.2,ht.2⟩)
  have hd := (isBlock_iff_degree_connected M T b c).mp hT
  exact Mole.connected_block_no_joint_loop M hT hd.2 (Or.inl ha) (hb.trans ha.symm)

noncomputable def bondSumMap : Bond M S ⊕ Bond M T → Bond M (S ∪ T)
  | .inl e => includeBond Finset.subset_union_left e
  | .inr e => includeBond Finset.subset_union_right e

theorem bondSumMap_injective (hT : M.IsBlock T b c) (hi : S ∩ T = {b}) :
    Function.Injective (bondSumMap (M := M) (S := S) (T := T)) := by
  rintro (e | e) (f | f) he
  · exact congrArg Sum.inl (includeBond_injective Finset.subset_union_left he)
  · have hv : e.1 = f.1 := congrArg (fun q : Bond M (S ∪ T) => q.1) he
    exact (Finset.disjoint_left.mp (block_concat_internalBondSet_disjoint hT hi) e.2 (hv.symm ▸ f.2)).elim
  · have hv : e.1 = f.1 := congrArg (fun q : Bond M (S ∪ T) => q.1) he
    exact (Finset.disjoint_left.mp (block_concat_internalBondSet_disjoint hT hi) f.2 (hv ▸ e.2)).elim
  · exact congrArg Sum.inr (includeBond_injective Finset.subset_union_right he)

theorem bondSumMap_surjective (hM : M.IsMolecule)
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) :
    Function.Surjective (bondSumMap (M := M) (S := S) (T := T)) := by
  intro e
  have hb := (Finset.mem_filter.mp e.2).1
  rcases (block_concat_inGroup_iff M hM hS hT hi hU e.1).mp (internalBond_inGroup M (S ∪ T) e) with hs | ht
  · exact ⟨.inl ⟨e.1,Finset.mem_filter.mpr ⟨hb,hs⟩⟩,Subtype.ext rfl⟩
  · exact ⟨.inr ⟨e.1,Finset.mem_filter.mpr ⟨hb,ht⟩⟩,Subtype.ext rfl⟩

/-- Actual edge names are retained, not replaced by an abstract matched set. -/
noncomputable def bondUnionEquiv (hM : M.IsMolecule)
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) : Bond M S ⊕ Bond M T ≃ Bond M (S ∪ T) :=
  Equiv.ofBijective bondSumMap ⟨bondSumMap_injective hT hi,bondSumMap_surjective hM hS hT hi hU⟩

end WaveTurbulence.VineEstS2
