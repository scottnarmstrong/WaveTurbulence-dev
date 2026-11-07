/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlignRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ChosenChart
public import WaveTurbulenceVineParam.VineParamGrouped
public import WaveTurbulence.Foundations.Molecule.VineCoherence
public import WaveTurbulenceVineParam.VineParamGroupSet
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData

/-! # `n_(3)` (e): the cohmol incoherency index is bounded by `M₀` (R22 (3))

`cohmolIndex` is the sum over the vines of the chain of the incoherency indices (TARGET Definition `cohmol`) of the
chosen realizations, for the layer of the atoms.  `cohmolIndex_le_M0`: it is at most `M₀` of the source sumint datum,
from `vineparam_grouped` (the chosen charts have the cohmol groups as rung pairs and core triple) and
`realizedIncoherencyIndex_le_chartGroups`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract TTree RegRed Finset WaveTurbulence.Vine.Param
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)

/-- A time variable whose vector slot is the slot `s` of the chart of the vine `i` has the chart atom as its clock. -/
theorem clockAtom_of_slot (t : (assemblyShape hM9 B).TVar) (i : Fin n) (s : Fin (assemblyChartAt hM9 B i).indexing.shape.n)
    (ht : Sumint.timeVectorEquiv _ t = ⟨i, familySlotEquiv (fun i => (assemblyPieceAt B i).vineType)
      (fun i => (assemblyChartAt hM9 B i).indexing.shape) i s⟩) :
    (assemblyClockAtomEquiv hM9 B t).1 = ((assemblyChartAt hM9 B i).indexing.atom s).1 := by
  have hs : assemblyTimeEquiv hM9 B t = (assemblyInputEquiv hM9 B).symm ⟨i, s⟩ := by
    unfold assemblyTimeEquiv
    rw [Equiv.trans_apply, ht, Equiv.symm_apply_eq]
    unfold assemblyVectorEquiv
    have hq := (assemblyInputEquiv hM9 B).apply_symm_apply
      (⟨i, s⟩ : Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n)
    refine Eq.trans ?_ (congrArg (Equiv.sigmaCongrRight
      (familySlotEquiv (fun i => (assemblyPieceAt B i).vineType) fun i =>
        (assemblyChartAt hM9 B i).indexing.shape)) hq).symm
    rfl
  unfold assemblyClockAtomEquiv
  rw [Equiv.trans_apply, hs]
  exact assemblyAtomEquiv_input hM9 B i s

theorem card_groupSet_filter_le {α : Type*} [DecidableEq α] {X : VineType} (A : Shape X) (ℓ : Fin A.n → α)
    (L : α → ℕ) :
    ((shapeGroupSet A ℓ).filter (fun g => ¬ ∀ x ∈ g, ∀ y ∈ g, L x = L y)).card ≤
      (univ.filter fun j : Fin A.m => L (ℓ (A.xSlot j)) ≠ L (ℓ (A.ySlot j))).card +
      (if hn : X.IsBad = false then
        (if L (ℓ (A.uSlot hn 0)) = L (ℓ (A.uSlot hn 1)) ∧ L (ℓ (A.uSlot hn 1)) = L (ℓ (A.uSlot hn 2)) then 0 else 1)
       else 0) := by
  classical
  unfold shapeGroupSet
  rw [Finset.filter_union]
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · rw [Finset.filter_image]
    refine Finset.card_image_le.trans (le_of_eq ?_)
    congr 1
    ext j
    simp [eq_comm]
  · split_ifs with hn h1
    · rw [Finset.filter_singleton]
      simp [h1.1, h1.2]
    · rw [Finset.filter_singleton]
      have : ¬ ∀ x ∈ ({ℓ (A.uSlot hn 0), ℓ (A.uSlot hn 1), ℓ (A.uSlot hn 2)} : Finset α),
          ∀ y ∈ ({ℓ (A.uSlot hn 0), ℓ (A.uSlot hn 1), ℓ (A.uSlot hn 2)} : Finset α), L x = L y := by
        intro h
        apply h1
        exact ⟨h _ (by simp) _ (by simp), h _ (by simp) _ (by simp)⟩
      rw [if_pos this]; simp
    · simp

theorem sum_nor {I : ℕ} (nor : Fin I → Bool) (g : {i // nor i = true} → ℕ) :
    ∑ i : Fin I, (if h : nor i = true then g ⟨i, h⟩ else 0) = ∑ i : {i // nor i = true}, g i := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => nor i = true)]
  have h1 : ∀ i : {i // nor i = true}, (if h : nor i.1 = true then g ⟨i.1, h⟩ else 0) = g i := fun i => by
    rw [dif_pos i.2]
  have h2 : ∀ i : {i // ¬ nor i = true}, (if h : nor i.1 = true then g ⟨i.1, h⟩ else 0) = 0 := fun i => by
    rw [dif_neg i.2]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

/-- The chart slot of a time variable: `t_{j+1}` is the clock of the rung atom `x_j`. -/
theorem clockAtom_x (i : Fin n) (j : Fin (assemblyChartAt hM9 B i).indexing.shape.m) :
    (assemblyClockAtomEquiv hM9 B (.inl ⟨i, j.succ⟩)).1 =
      ((assemblyChartAt hM9 B i).indexing.atom ((assemblyChartAt hM9 B i).indexing.shape.xSlot j)).1 := by
  refine clockAtom_of_slot hM9 B _ i _ ?_
  exact (Sumint.timeVectorEquiv_x (assemblyShape hM9 B) i j).trans
    (Sigma.ext rfl (heq_of_eq (familySlotEquiv_x (fun i => (assemblyPieceAt B i).vineType)
      (fun i => (assemblyChartAt hM9 B i).indexing.shape) i j).symm))

theorem clockAtom_y (i : Fin n) (j : Fin (assemblyChartAt hM9 B i).indexing.shape.m) :
    (assemblyClockAtomEquiv hM9 B (.inr (.inl ⟨i, j⟩))).1 =
      ((assemblyChartAt hM9 B i).indexing.atom ((assemblyChartAt hM9 B i).indexing.shape.ySlot j)).1 := by
  refine clockAtom_of_slot hM9 B _ i _ ?_
  exact (Sumint.timeVectorEquiv_y (assemblyShape hM9 B) i j).trans
    (Sigma.ext rfl (heq_of_eq (familySlotEquiv_y (fun i => (assemblyPieceAt B i).vineType)
      (fun i => (assemblyChartAt hM9 B i).indexing.shape) i j).symm))


theorem clockAtom_u (i : Fin n) (h : (assemblyShape hM9 B).nor i = true)
    (hn : (assemblyPieceAt B i).vineType.IsBad = false) (c : Fin 3) :
    (assemblyClockAtomEquiv hM9 B (.inr (.inr ⟨⟨i, h⟩, c⟩))).1 =
      ((assemblyChartAt hM9 B i).indexing.atom ((assemblyChartAt hM9 B i).indexing.shape.uSlot hn c)).1 := by
  refine clockAtom_of_slot hM9 B _ i _ ?_
  exact (Sumint.timeVectorEquiv_u (assemblyShape hM9 B) ⟨i, h⟩ c).trans
    (Sigma.ext rfl (heq_of_eq (Fin.ext rfl)))

variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)

/-- The layer of a molecule atom (a branch of the skeleton garden). -/
noncomputable def atomLayer (v : GBranch G.tree) : ℕ := layer (RD.coreBranch hG v).toNode

/-- The realization of the `i`-th vine of the chain used for its cohmol groups (intrinsic, `realizedGroupSets_eq`). -/
noncomputable def pieceRealization (i : Fin n) :
    Vine.VineRealization G.molecule (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms
      (assemblyPieceAt B i).upper (assemblyPieceAt B i).lower :=
  Classical.choice (Vine.isVine_iff_realization.mp (assemblyPieceAt B i).vine).2

/-- `n_(3)`, vine part: the sum of the incoherency indices of the vines of the chain (TARGET Definition `cohmol`). -/
noncomputable def cohmolIndex : ℕ :=
  ∑ i : Fin n, Vine.realizedIncoherencyIndex (pieceRealization B i) (atomLayer RD hG layer)

theorem vine_cohmol_le (i : Fin n) :
    Vine.realizedIncoherencyIndex (pieceRealization B i) (atomLayer RD hG layer) ≤
      (univ.filter fun j : Fin ((assemblyShape hM9 B).m i) =>
        assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inl ⟨i, j.succ⟩) ≠
          assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inl ⟨i, j⟩))).card +
      (if h : (assemblyShape hM9 B).nor i = true then
        (if assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨⟨i, h⟩, 0⟩)) =
              assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨⟨i, h⟩, 1⟩)) ∧
            assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨⟨i, h⟩, 1⟩)) =
              assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨⟨i, h⟩, 2⟩)) then 0 else 1)
       else 0) := by
  classical
  have hF : chartAtomGroups (assemblyChartAt hM9 B i) = realizedGroupSet (pieceRealization B i) :=
    chainPieceChart_groups hM9 (Mole.garden_isMolecule G) (assemblyPieceAt B i)
  refine (realizedIncoherencyIndex_le_chartGroups _ _ hF _).trans ?_
  refine (card_groupSet_filter_le _ _ (atomLayer RD hG layer)).trans ?_
  refine Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · refine congrArg Finset.card (Finset.filter_congr (fun j _ => ?_))
    exact Iff.of_eq (congrArg₂ (fun x y => x ≠ y)
      (congrArg (atomLayer RD hG layer) (clockAtom_x hM9 B i j)).symm
      (congrArg (atomLayer RD hG layer) (clockAtom_y hM9 B i j)).symm)
  · by_cases hb : (assemblyPieceAt B i).vineType.IsBad = false
    · have h : (assemblyShape hM9 B).nor i = true := by
        simp [assemblyShape, shapeFamily, hb]
      rw [dif_pos hb, dif_pos h]
      simp only [assemblyTimeQ, clockAtom_u hM9 B i h hb]
    · have h : ¬ (assemblyShape hM9 B).nor i = true := by
        simpa [assemblyShape, shapeFamily] using hb
      rw [dif_neg hb, dif_neg h]

theorem cohmolIndex_le_M0 (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hq : W.q = assemblyTimeQ hM9 B (atomLayer RD hG layer)) :
    cohmolIndex B RD hG layer ≤ (sourceSumintDatum hM9 B hG W).M₀ := by
  classical
  unfold cohmolIndex
  refine (Finset.sum_le_sum (fun i _ => vine_cohmol_le hM9 B RD hG layer i)).trans ?_
  rw [Finset.sum_add_distrib]
  unfold SumintDatum.M₀
  have hq' : (sourceSumintDatum hM9 B hG W).q = assemblyTimeQ hM9 B (atomLayer RD hG layer) := hq
  refine Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · simp only [Finset.card_filter, Fintype.sum_sigma, hq']
    rfl
  · simp only [hq', Finset.card_filter]
    refine (sum_nor (assemblyShape hM9 B).nor (fun i =>
      if (assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨i, 0⟩)) =
            assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨i, 1⟩)) ∧
          assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨i, 1⟩)) =
            assemblyTimeQ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨i, 2⟩))) then 0 else 1)).trans ?_
    exact Finset.sum_congr rfl (fun i _ => (ite_not _ _ _).symm)

end WaveTurbulence.VineEstS3
