/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Geom

/-! # P4-W3: an operative vine is a bad vine; the number of core vines and their exceptional orders

* `op_kind_bad`: the vine at which a `FamilyOperation` acts has type I or II (its `eligible` field), i.e. it is bad
  (`VineType.IsBad`), for either kind.
* `core_kind_bad`, `core_nor_false`, `core_badVineSet`: every core vine of the chain (`IsCoreCLVine`: type I, or type II not
  (II-e)) is bad: its atom set is a bad vine set in V5's / S2a's sense (`∃ X p q, X.IsBad ∧ IsVine X S p q`, `IsBadVineSet`), and
  its row block in the sumint shape is a `Bad` block (`nor = false`).  Every operative member of every level is a core vine
  (`lvl_op_nor_false`).
* `card_core_le_bad`: `#core vines ≤ b`, `b = #{i | nor i = false}` (the exponent of `C₂^b`, R54).
* `sum_zpN_le`: `∑_{core i} 2 zpN(start, i) ≤ n₍₂₎ - M`: the exceptional couple and tree of the core vines are pairwise distinct
  regular objects of the region (the tree at the lower joint, an interior branch; the couple at the pair of the retained leaf, a
  regional pair), so their orders are among those counted by `clLocalOrder2`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 VineParamContract

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssembly G R n)

/-- Every core vine of the chain is bad. -/
theorem core_kind_bad (i : (assemblySourceFamily B).CoreIndex) : ((assemblySourceFamily B).kind i.1).IsBad = true := by
  rcases i.2.2.2 with h | ⟨h, _⟩ <;> rw [h] <;> rfl

/-- The row block of a core vine is a `Bad` block of the sumint shape. -/
theorem core_nor_false (hM9 : VINEPARAM) (i : (assemblySourceFamily B).CoreIndex) :
    (assemblyShape hM9 B).nor i.1 = false := by
  show (!((assemblyPieceAt B i.1).vineType.IsBad)) = false
  rw [show (assemblyPieceAt B i.1).vineType = (assemblySourceFamily B).kind i.1 from rfl, core_kind_bad B i]
  rfl

/-- Every member of every level (in particular every operative member) is a bad vine of the chain. -/
theorem lvl_op_nor_false (hM9 : VINEPARAM) (lv : Lvl B) (j : lv.ι) : (assemblyShape hM9 B).nor (lv.e j).1 = false :=
  core_nor_false B hM9 (lv.e j)

/-- **`#core vines ≤ b`.** -/
theorem card_core_le_bad (hM9 : VINEPARAM) :
    Fintype.card (assemblySourceFamily B).CoreIndex ≤
      (Finset.univ.filter fun i : Fin (assemblyShape hM9 B).I => (assemblyShape hM9 B).nor i = false).card := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun i : (assemblySourceFamily B).CoreIndex => (i.1 : Fin (assemblyShape hM9 B).I))
    (fun i _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, core_nor_false B hM9 i⟩) ?_
  intro i _ j _ h
  exact Subtype.ext h

variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer)

theorem start_lower (i : (assemblySourceFamily B).CoreIndex) :
    ((startState B RD hG layer hLayer).family.placement i).lower = (assemblyPieceAt B i.1).lower :=
  ((assemblySourceFamily B).corePlacement_at i).1

theorem start_placement (i : (assemblySourceFamily B).CoreIndex) :
    IsPlacementAt G (assemblyPieceAt B i.1).atoms ((startState B RD hG layer hLayer).family.placement i).lower
      ((startState B RD hG layer hLayer).family.placement i) := by
  show IsPlacementAt G (assemblyPieceAt B i.1).atoms ((assemblySourceFamily B).corePlacement i).lower
    ((assemblySourceFamily B).corePlacement i)
  obtain ⟨e, h2⟩ := (assemblySourceFamily B).corePlacement_at i
  exact ⟨rfl, fun k => by rw [e]; exact h2 k⟩

theorem start_retained_internal (i : (assemblySourceFamily B).CoreIndex) :
    Mole.IsInternalLeaf G (assemblyPieceAt B i.1).atoms ((startState B RD hG layer hLayer).family.placement i).retained := by
  set P := (startState B RD hG layer hLayer).family.placement i
  have hpp := placement_paired_parent_mem G P (start_placement B RD hG layer hLayer i)
  have ha : G.molecule.atom (retainedLP G P) = P.lower := retained_parent G P
  refine ⟨P.unmarked, retained_nonroot G P, P.paired_nonroot, ?_, hpp⟩
  show G.molecule.atom (retainedLP G P) ∈ (assemblyPieceAt B i.1).atoms
  rw [ha, start_lower B RD hG layer hLayer i]
  exact (assemblyPieceAt B i.1).vine.1.2.2.1

theorem start_lower_inj (hM9 : VINEPARAM) {i j : (assemblySourceFamily B).CoreIndex}
    (h : (assemblyPieceAt B i.1).lower = (assemblyPieceAt B j.1).lower) : i = j := by
  apply Subtype.ext
  rw [← vineOf_lower hM9 B i.1, ← vineOf_lower hM9 B j.1]
  congr 1
  exact Subtype.ext h

theorem start_pair_inj (hM9 : VINEPARAM) {i j : (assemblySourceFamily B).CoreIndex}
    (h : pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement i).retained =
      pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement j).retained) : i = j := by
  apply start_lower_inj B hM9
  rw [← start_lower B RD hG layer hLayer i, ← start_lower B RD hG layer hLayer j]
  refine placement_pair_eq hG _ _ ?_ h
  rw [start_lower B RD hG layer hLayer i, start_lower B RD hG layer hLayer j]
  rcases le_total i.1 j.1 with hij | hji
  · exact Or.inr (assemblyPiece_lower_isDesc B i.1 j.1 hij).1
  · exact Or.inl (assemblyPiece_lower_isDesc B j.1 i.1 hji).1

/-- **The exceptional orders of the core vines are part of `n₍₂₎`.** -/
theorem sum_zpN_le (hM9 : VINEPARAM) :
    ∑ i : (assemblySourceFamily B).CoreIndex, 2 * zpN (startState B RD hG layer hLayer) i ≤
      clLocalOrder2 RD hG R - clLocalOrder1 R := by
  classical
  set A := startState B RD hG layer hLayer
  have h2 : ∀ i, 2 * zpN A i = (RD.tree (A.family.placement i).lower).size +
      (RD.couple (pairOfLeaf G hG (A.family.placement i).retained)).size := fun i =>
    WaveTurbulence.ZpSurj.two_zpN A (pstar := i)
  have hinjL : Set.InjOn (fun i : (assemblySourceFamily B).CoreIndex => (A.family.placement i).lower)
      (Finset.univ : Finset (assemblySourceFamily B).CoreIndex) := by
    intro i _ j _ h
    apply start_lower_inj B hM9
    rw [← start_lower B RD hG layer hLayer i, ← start_lower B RD hG layer hLayer j]
    exact h
  have hinjP : Set.InjOn (fun i : (assemblySourceFamily B).CoreIndex => pairOfLeaf G hG (A.family.placement i).retained)
      (Finset.univ : Finset (assemblySourceFamily B).CoreIndex) := fun i _ j _ h =>
    start_pair_inj B RD hG layer hLayer hM9 h
  have hT : ∑ i, (RD.tree (A.family.placement i).lower).size ≤ ∑ v ∈ clInteriorBranches R, (RD.tree v).size := by
    rw [← Finset.sum_image (f := fun v => (RD.tree v).size) hinjL]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) (fun _ _ _ => Nat.zero_le _)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    rw [start_lower B RD hG layer hLayer i]
    exact lower_mem_interior B i.1
  have hC : ∑ i, (RD.couple (pairOfLeaf G hG (A.family.placement i).retained)).size ≤
      ∑ q ∈ clRegionalPairs hG U, (RD.couple q).size := by
    rw [← Finset.sum_image (f := fun q => (RD.couple q).size) hinjP]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) (fun _ _ _ => Nat.zero_le _)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact pairOfLeaf_mem_regional B hG i.1 _ (start_retained_internal B RD hG layer hLayer i)
  have hO : clLocalOrder2 RD hG R = clLocalOrder1 R + (∑ q ∈ clRegionalPairs hG U, (RD.couple q).size) +
      ∑ v ∈ clInteriorBranches R, (RD.tree v).size := rfl
  simp_rw [h2]
  rw [Finset.sum_add_distrib, hO]
  omega

end WaveTurbulence.VineEstS5C.P4.W13
