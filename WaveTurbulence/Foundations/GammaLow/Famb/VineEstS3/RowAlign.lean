/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.VineMonotone
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyRowEquiv
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInteriorPredecessor
public import Mathlib.Logic.Equiv.Fintype
public import WaveTurbulence.Foundations.Molecule.CorePlacements
public import WaveTurbulence.Foundations.Molecule.VineTwistPlacements
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyRowEquiv
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.VineMonotone
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign` (sha256 fc9af4d9919a2bdd…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Row alignment, part 2: block-aligned, predecessor-monotone branch enumeration (R22 (2))

`assemblyBranchBij hM9 B : ↥(U.erase a) ≃ VIdx` sends an interior atom `z` to a row of the vine block `vineOf z`, ordered
inside the block by decreasing depth.  Along the interior predecessor relation (a strictly deeper heavy-path descendant)
it is lexicographically increasing (`vineOf_desc_le`), so `assemblyIntOrder` is a `CLIntOrder`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist VineParamContract TTree RegRed Finset WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.Reg.Skeleton
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem piece_upper_isDescΓ (B : CLChainAssemblyΓ γF G R n) (i : Fin n) :
    (assemblyPieceAtΓ B i).upper.toNode.IsDesc (assemblyPieceAtΓ B i).lower.toNode :=
  (Mole.cl_parent_strict_descendant G (assemblyPieceAtΓ B i).isBlock (assemblyPiece_clΓ B i)).1

theorem piece_upper_len_ltΓ (B : CLChainAssemblyΓ γF G R n) (i : Fin n) :
    (assemblyPieceAtΓ B i).upper.1.2.length < (assemblyPieceAtΓ B i).lower.1.2.length :=
  (Mole.cl_parent_strict_descendant G (assemblyPieceAtΓ B i).isBlock (assemblyPiece_clΓ B i)).2

/-- The lower joints of the pieces form a descending chain: the lower joint of a later piece is a strict ancestor of
the lower joint of an earlier piece. -/
theorem assemblyPiece_lower_isDescΓ (B : CLChainAssemblyΓ γF G R n) (i j : Fin n) (hij : i ≤ j) :
    (assemblyPieceAtΓ B j).lower.toNode.IsDesc (assemblyPieceAtΓ B i).lower.toNode ∧
      (i < j → (assemblyPieceAtΓ B j).lower.1.2.length < (assemblyPieceAtΓ B i).lower.1.2.length) := by
  induction B with
  | single hV R =>
    have : i = j := Subsingleton.elim _ _
    subst this
    exact ⟨⟨rfl, List.prefix_refl _⟩, fun h => absurd h (lt_irrefl _)⟩
  | @append S T a' b' c' n' RP B hT hi hU R ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact ⟨⟨rfl, List.prefix_refl _⟩, fun h => absurd h (lt_irrefl _)⟩
      · have hn : 0 < n' := B.length_pos
        have h1 := (ih ⟨0, hn⟩ j' (Fin.mk_le_of_le_val (Nat.zero_le _))).1
        have h2 : (assemblyPieceAtΓ B ⟨0, hn⟩).lower = (assemblyPieceAtΓ (.append B hT hi hU R) 0).upper :=
          assemblyPiece_zero_lowerΓ B hn
        have h3 := piece_upper_isDescΓ (.append B hT hi hU R) 0
        have h4 := piece_upper_len_ltΓ (.append B hT hi hU R) 0
        rw [← h2] at h3 h4
        refine ⟨isDesc_trans h1 h3, fun _ => ?_⟩
        have h5 := h1.2.length_le
        exact lt_of_le_of_lt h5 h4
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd (Fin.le_def.mp hij) (by simp)
      · exact ih i' j' (Fin.succ_le_succ_iff.mp hij) |>.imp id (fun h hlt => h (Fin.succ_lt_succ_iff.mp hlt))

section Align
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

/-- The chart-slot bijection: an interior atom to its row, block preserving. -/
noncomputable def chartRowEquivΓ : ↥(clInteriorBranches R) ≃ (assemblyShapeΓ hM9 B).VIdx :=
  (assemblyAtomEquivΓ hM9 B).symm.trans (assemblyVectorEquivΓ hM9 B)

theorem chartRowEquiv_fstΓ (z : ↥(clInteriorBranches R)) :
    ((chartRowEquivΓ hM9 B z).1 : ℕ) = (vineOfΓ hM9 B z : ℕ) := rfl

/-- Depth of the interior atom at the row `⟨i, j⟩` of the chart bijection. -/
noncomputable def slotDepthΓ (x : (assemblyShapeΓ hM9 B).VIdx) : ℕᵒᵈ :=
  OrderDual.toDual ((chartRowEquivΓ hM9 B).symm x).1.1.2.length

/-- Within each block, reorder the slots by decreasing depth. -/
noncomputable def blockSortΓ (i : Fin (assemblyShapeΓ hM9 B).I) :
    Fin ((assemblyShapeΓ hM9 B).n i) ≃ Fin ((assemblyShapeΓ hM9 B).n i) :=
  (exists_sorted_equiv (fun j : Fin ((assemblyShapeΓ hM9 B).n i) => slotDepthΓ hM9 B ⟨i, j⟩) _
    (Fintype.card_fin _)).choose

theorem blockSort_ltΓ (i : Fin (assemblyShapeΓ hM9 B).I) (j j' : Fin ((assemblyShapeΓ hM9 B).n i))
    (h : slotDepthΓ hM9 B ⟨i, j⟩ < slotDepthΓ hM9 B ⟨i, j'⟩) : blockSortΓ hM9 B i j < blockSortΓ hM9 B i j' :=
  (exists_sorted_equiv (fun j : Fin ((assemblyShapeΓ hM9 B).n i) => slotDepthΓ hM9 B ⟨i, j⟩) _
    (Fintype.card_fin _)).choose_spec j j' h

/-- The aligned branch bijection: block `vineOf z`, decreasing depth inside the block. -/
noncomputable def assemblyBranchBijΓ : ↥(clInteriorBranches R) ≃ (assemblyShapeΓ hM9 B).VIdx :=
  (chartRowEquivΓ hM9 B).trans (Equiv.sigmaCongrRight (blockSortΓ hM9 B))

theorem assemblyBranchBij_fstΓ (z : ↥(clInteriorBranches R)) :
    ((assemblyBranchBijΓ hM9 B z).1 : ℕ) = (vineOfΓ hM9 B z : ℕ) := rfl

theorem assemblyBranchBij_lexLtΓ (u v : ↥(clInteriorBranches R))
    (h : vineOfΓ hM9 B u < vineOfΓ hM9 B v ∨
      (vineOfΓ hM9 B u = vineOfΓ hM9 B v ∧ v.1.1.2.length < u.1.1.2.length)) :
    (assemblyShapeΓ hM9 B).LexLt (assemblyBranchBijΓ hM9 B u) (assemblyBranchBijΓ hM9 B v) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · have hu : (chartRowEquivΓ hM9 B u).1 = (chartRowEquivΓ hM9 B v).1 := Fin.ext (by
      rw [chartRowEquiv_fstΓ, chartRowEquiv_fstΓ, h1])
    have hkey : slotDepthΓ hM9 B (chartRowEquivΓ hM9 B u) < slotDepthΓ hM9 B (chartRowEquivΓ hM9 B v) := by
      simp only [slotDepthΓ, Equiv.symm_apply_apply]
      exact OrderDual.toDual_lt_toDual.mpr h2
    simp only [assemblyBranchBijΓ, Equiv.trans_apply, Equiv.sigmaCongrRight_apply]
    revert hkey hu
    generalize chartRowEquivΓ hM9 B u = xu
    generalize chartRowEquivΓ hM9 B v = xv
    obtain ⟨i, ju⟩ := xu
    obtain ⟨i', jv⟩ := xv
    intro hu hkey
    have hi : i = i' := hu
    subst hi
    exact Or.inr ⟨rfl, blockSort_ltΓ hM9 B i ju jv hkey⟩

/-- The aligned, predecessor-monotone enumeration of the interior branches. -/
noncomputable def assemblyIntOrderΓ : CLIntOrder B.isBlock R where
  e := (assemblyBranchBijΓ hM9 B).trans (assemblyRowEquivΓ hM9 B).symm
  prev v u hu := by
    have hdesc := clInteriorPredecessor_isDesc B.isBlock R v u hu
    have hlen := clInteriorPredecessor_deeper B.isBlock R v u hu
    have hle := vineOf_desc_leΓ hM9 B v (u.1.1.2.length - v.1.1.2.length - 1) u hdesc (by omega)
    apply assemblyRowEquiv_symm_ltΓ
    apply assemblyBranchBij_lexLtΓ
    rcases hle.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hlen⟩

end Align

section Anchor

variable (hG : G.IsPlain) (B : CLChainAssemblyΓ γF G R n)

open Classical in
/-- The designated regional pair of the vine `i`: the pair of the retained leaf of a core placement at its lower joint
(when one exists with its pair in the region). -/
noncomputable def vineAnchorΓ (i : Fin n) : Option ↥(clRegionalPairs hG U) :=
  if h : ∃ P : CorePlacement G, IsPlacementAt G (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).lower P ∧
      pairOfLeaf G hG P.retained ∈ clRegionalPairs hG U then
    some ⟨pairOfLeaf G hG h.choose.retained, h.choose_spec.2⟩
  else none

theorem vineAnchor_specΓ (i : Fin n) (p : ↥(clRegionalPairs hG U)) (hp : vineAnchorΓ hG B i = some p) :
    ∃ P : CorePlacement G, IsPlacementAt G (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).lower P ∧
      p.1 = pairOfLeaf G hG P.retained := by
  unfold vineAnchorΓ at hp
  split_ifs at hp with h
  · exact ⟨h.choose, h.choose_spec.1, by rw [← Option.some.inj hp]⟩

theorem vineAnchor_injΓ (i j : Fin n) (p : ↥(clRegionalPairs hG U)) (hi : vineAnchorΓ hG B i = some p)
    (hj : vineAnchorΓ hG B j = some p) : i = j := by
  obtain ⟨P, hP, hpP⟩ := vineAnchor_specΓ hG B i p hi
  obtain ⟨P', hP', hpP'⟩ := vineAnchor_specΓ hG B j p hj
  have hpair : pairOfLeaf G hG P.retained = pairOfLeaf G hG P'.retained := hpP.symm.trans hpP'
  wlog hle : i ≤ j generalizing i j P P'
  · exact (this j i hj hi P' hP' hpP' P hP hpP hpair.symm (le_of_not_ge hle)).symm
  have hdesc := (assemblyPiece_lower_isDescΓ B i j hle)
  have hl := placement_pair_eq hG P P' (Or.inr (by rw [hP.1, hP'.1]; exact hdesc.1)) hpair
  rw [hP.1, hP'.1] at hl
  by_contra hne
  have hlt : i < j := lt_of_le_of_ne hle hne
  have := hdesc.2 hlt
  rw [hl] at this
  exact lt_irrefl _ this

variable (hM9 : NormalChartSupply γF)

theorem card_pairs_eq_vidxΓ : Fintype.card ↥(clRegionalPairs hG U) = Fintype.card (assemblyShapeΓ hM9 B).VIdx :=
  (Fintype.card_coe _).trans ((card_clRegionalPairs B.isBlock R hG).trans
    ((assemblyShape_MΓ hM9 B).symm.trans (Sumint.card_vector_index _).symm))

theorem exists_pairBijΓ : ∃ e : ↥(clRegionalPairs hG U) ≃ (assemblyShapeΓ hM9 B).VIdx,
    ∀ (i : Fin n) (p : ↥(clRegionalPairs hG U)), vineAnchorΓ hG B i = some p → (e p).1 = i := by
  obtain ⟨e, he⟩ := exists_equiv_extending (D := {i : Fin n // (vineAnchorΓ hG B i).isSome})
    (card_pairs_eq_vidxΓ hG B hM9)
    (fun i => ((vineAnchorΓ hG B i.1).get i.2))
    (fun i => (⟨i.1, ⟨0, by simp [SumintShape.n]⟩⟩ : (assemblyShapeΓ hM9 B).VIdx))
    (fun i j h => Subtype.ext (vineAnchor_injΓ hG B i.1 j.1 _ (Option.eq_some_of_isSome i.2)
      (by
        have h' : (vineAnchorΓ hG B i.1).get i.2 = (vineAnchorΓ hG B j.1).get j.2 := h
        rw [h']
        exact Option.eq_some_of_isSome j.2)))
    (fun i j h => Subtype.ext (congrArg Sigma.fst h))
  refine ⟨e, fun i p hp => ?_⟩
  have hs : (vineAnchorΓ hG B i).isSome := by rw [hp]; rfl
  have := he ⟨i, hs⟩
  have hpg : (vineAnchorΓ hG B i).get hs = p := by simp [hp]
  simp only [hpg] at this
  exact congrArg Sigma.fst this

/-- The aligned pair bijection: the anchor pair of each vine `i` lies in block `i`. -/
noncomputable def assemblyPairBijΓ : ↥(clRegionalPairs hG U) ≃ (assemblyShapeΓ hM9 B).VIdx :=
  (exists_pairBijΓ hG B hM9).choose

theorem assemblyPairBij_anchorΓ (i : Fin n) (p : ↥(clRegionalPairs hG U)) (hp : vineAnchorΓ hG B i = some p) :
    (assemblyPairBijΓ hG B hM9 p).1 = i := (exists_pairBijΓ hG B hM9).choose_spec i p hp

/-- The aligned pair enumeration. -/
noncomputable def assemblyPairOrderΓ : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R) :=
  (assemblyPairBijΓ hG B hM9).trans (assemblyRowEquivΓ hM9 B).symm

end Anchor

end WaveTurbulence.GammaLow.Famb.VineEstS3
