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
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.RowAlignRows
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.CohmolBound` (sha256 8295dcf68266a409…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # `n_(3)` (e): the cohmol incoherency index is bounded by `M₀` (R22 (3))

`cohmolIndex` is the sum over the vines of the chain of the incoherency indices (TARGET Definition `cohmol`) of the
chosen realizations, for the layer of the atoms.  `cohmolIndex_le_M0`: it is at most `M₀` of the source sumint datum,
from `vineparam_grouped` (the chosen charts have the cohmol groups as rung pairs and core triple) and
`realizedIncoherencyIndex_le_chartGroups`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract TTree RegRed Finset WaveTurbulence.Vine.Param WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

/-- A time variable whose vector slot is the slot `s` of the chart of the vine `i` has the chart atom as its clock. -/
theorem clockAtom_of_slotΓ (t : (assemblyShapeΓ hM9 B).TVar) (i : Fin n) (s : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n)
    (ht : Sumint.timeVectorEquiv _ t = ⟨i, familySlotEquiv (fun i => (assemblyPieceAtΓ B i).label)
      (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) i s⟩) :
    (assemblyClockAtomEquivΓ hM9 B t).1 = ((assemblyChartAtΓ hM9 B i).indexing.atom s).1 := by
  have hs : assemblyTimeEquivΓ hM9 B t = (assemblyInputEquivΓ hM9 B).symm ⟨i, s⟩ := by
    unfold assemblyTimeEquivΓ
    rw [Equiv.trans_apply, ht, Equiv.symm_apply_eq]
    unfold assemblyVectorEquivΓ
    have hq := (assemblyInputEquivΓ hM9 B).apply_symm_apply
      (⟨i, s⟩ : Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n)
    refine Eq.trans ?_ (congrArg (Equiv.sigmaCongrRight
      (familySlotEquiv (fun i => (assemblyPieceAtΓ B i).label) fun i =>
        (assemblyChartAtΓ hM9 B i).indexing.shape)) hq).symm
    rfl
  unfold assemblyClockAtomEquivΓ
  rw [Equiv.trans_apply, hs]
  exact assemblyAtomEquiv_inputΓ hM9 B i s

/-- The chart slot of a time variable: `t_{j+1}` is the clock of the rung atom `x_j`. -/
theorem clockAtom_xΓ (i : Fin n) (j : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.m) :
    (assemblyClockAtomEquivΓ hM9 B (.inl ⟨i, j.succ⟩)).1 =
      ((assemblyChartAtΓ hM9 B i).indexing.atom ((assemblyChartAtΓ hM9 B i).indexing.shape.xSlot j)).1 := by
  refine clockAtom_of_slotΓ hM9 B _ i _ ?_
  exact (Sumint.timeVectorEquiv_x (assemblyShapeΓ hM9 B) i j).trans
    (Sigma.ext rfl (heq_of_eq (familySlotEquiv_x (fun i => (assemblyPieceAtΓ B i).label)
      (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) i j).symm))

theorem clockAtom_yΓ (i : Fin n) (j : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.m) :
    (assemblyClockAtomEquivΓ hM9 B (.inr (.inl ⟨i, j⟩))).1 =
      ((assemblyChartAtΓ hM9 B i).indexing.atom ((assemblyChartAtΓ hM9 B i).indexing.shape.ySlot j)).1 := by
  refine clockAtom_of_slotΓ hM9 B _ i _ ?_
  exact (Sumint.timeVectorEquiv_y (assemblyShapeΓ hM9 B) i j).trans
    (Sigma.ext rfl (heq_of_eq (familySlotEquiv_y (fun i => (assemblyPieceAtΓ B i).label)
      (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) i j).symm))

theorem clockAtom_uΓ (i : Fin n) (h : (assemblyShapeΓ hM9 B).nor i = true)
    (hn : (assemblyPieceAtΓ B i).label.IsBad = false) (c : Fin 3) :
    (assemblyClockAtomEquivΓ hM9 B (.inr (.inr ⟨⟨i, h⟩, c⟩))).1 =
      ((assemblyChartAtΓ hM9 B i).indexing.atom ((assemblyChartAtΓ hM9 B i).indexing.shape.uSlot hn c)).1 := by
  refine clockAtom_of_slotΓ hM9 B _ i _ ?_
  exact (Sumint.timeVectorEquiv_u (assemblyShapeΓ hM9 B) ⟨i, h⟩ c).trans
    (Sigma.ext rfl (heq_of_eq (Fin.ext rfl)))

variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)

/-- `n_(3)`, vine part: the sum over the ingredients of the chain of their incoherency indices (TARGET Definition
`cohmol`), with the cohmol groups `famGroups` of `𝒱_γ` (for a T-vine its pieces). -/
noncomputable def cohmolIndexΓ : ℕ :=
  ∑ i : Fin n, groupIncoherency (famGroups γF G.molecule (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper
    (assemblyPieceAtΓ B i).lower) (atomLayer RD hG layer)

theorem vine_cohmol_leΓ (i : Fin n) :
    groupIncoherency (famGroups γF G.molecule (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper
      (assemblyPieceAtΓ B i).lower) (atomLayer RD hG layer) ≤
      (univ.filter fun j : Fin ((assemblyShapeΓ hM9 B).m i) =>
        assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inl ⟨i, j.succ⟩) ≠
          assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inl ⟨i, j⟩))).card +
      (if h : (assemblyShapeΓ hM9 B).nor i = true then
        (if assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨⟨i, h⟩, 0⟩)) =
              assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨⟨i, h⟩, 1⟩)) ∧
            assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨⟨i, h⟩, 1⟩)) =
              assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨⟨i, h⟩, 2⟩)) then 0 else 1)
       else 0) := by
  classical
  have hF : chartAtomGroups (assemblyChartAtΓ hM9 B i) = famGroups γF G.molecule (assemblyPieceAtΓ B i).atoms
      (assemblyPieceAtΓ B i).upper (assemblyPieceAtΓ B i).lower :=
    chainPieceChart_groupsΓ hM9 (Mole.garden_isMolecule G) (assemblyPieceAtΓ B i)
  unfold groupIncoherency
  rw [← hF]
  refine (card_groupSet_filter_le _ _ (atomLayer RD hG layer)).trans ?_
  refine Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · refine congrArg Finset.card (Finset.filter_congr (fun j _ => ?_))
    exact Iff.of_eq (congrArg₂ (fun x y => x ≠ y)
      (congrArg (atomLayer RD hG layer) (clockAtom_xΓ hM9 B i j)).symm
      (congrArg (atomLayer RD hG layer) (clockAtom_yΓ hM9 B i j)).symm)
  · by_cases hb : (assemblyPieceAtΓ B i).label.IsBad = false
    · have h : (assemblyShapeΓ hM9 B).nor i = true := by
        simp [assemblyShapeΓ, shapeFamily, hb]
      rw [dif_pos hb, dif_pos h]
      simp only [assemblyTimeQΓ, clockAtom_uΓ hM9 B i h hb]
    · have h : ¬ (assemblyShapeΓ hM9 B).nor i = true := by
        simpa [assemblyShapeΓ, shapeFamily] using hb
      rw [dif_neg hb, dif_neg h]

theorem cohmolIndex_le_M0Γ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    (hq : W.q = assemblyTimeQΓ hM9 B (atomLayer RD hG layer)) :
    cohmolIndexΓ B RD hG layer ≤ (sourceSumintDatumΓ hM9 B hG W).M₀ := by
  classical
  unfold cohmolIndexΓ
  refine (Finset.sum_le_sum (fun i _ => vine_cohmol_leΓ hM9 B RD hG layer i)).trans ?_
  rw [Finset.sum_add_distrib]
  unfold SumintDatum.M₀
  have hq' : (sourceSumintDatumΓ hM9 B hG W).q = assemblyTimeQΓ hM9 B (atomLayer RD hG layer) := hq
  refine Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · simp only [Finset.card_filter, Fintype.sum_sigma, hq']
    rfl
  · simp only [hq', Finset.card_filter]
    refine (sum_nor (assemblyShapeΓ hM9 B).nor (fun i =>
      if (assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨i, 0⟩)) =
            assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨i, 1⟩)) ∧
          assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨i, 1⟩)) =
            assemblyTimeQΓ hM9 B (atomLayer RD hG layer) (.inr (.inr ⟨i, 2⟩))) then 0 else 1)).trans ?_
    exact Finset.sum_congr rfl (fun i _ => (ite_not _ _ _).symm)

end WaveTurbulence.GammaLow.Famb.VineEstS3
