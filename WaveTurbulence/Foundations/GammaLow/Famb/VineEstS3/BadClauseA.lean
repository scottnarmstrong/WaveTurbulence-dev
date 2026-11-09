/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadGeom
public import WaveTurbulence.Foundations.VineEst.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.Molecule.TypeIILowerParent
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseA
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadGeom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseA` (sha256 50882c22471b9039…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # BadClause, part A: assumption (a) of `sumint` from the adjacency of the end rung (TARGET L1841-L1847)

`AClause` is clause (a) of `BadClause` for the constraint set of `step3W`.  If the chosen rung `0` of a vine is
`{left, right}` with `b`'s parent `left`, and either `right` is a child of `b` (II-e) or `L_right < L_b`, then
`AClause` holds: `t_right < t_b < t_left` (parent constraints and `layerOrderPairs`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract TTree RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.GammaLow.Famb.VineEstS2
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)

/-- The constraint set of `step3W`. -/
noncomputable def badConstrΓ : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar) :=
  assemblyTimeConstraintsΓ hM9 B ∪ layerOrderPairs (assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))

/-- Clause (a) of `BadClause` for the vine `i`. -/
def AClauseΓ (i : Fin (assemblyShapeΓ hM9 B).I) : Prop :=
  ∃ h : 0 < (assemblyShapeΓ hM9 B).m i,
    let t0 : (assemblyShapeΓ hM9 B).TVar := .inl ⟨i, 0⟩
    let t1 : (assemblyShapeΓ hM9 B).TVar := .inl ⟨i, ⟨1, by omega⟩⟩
    let s1 : (assemblyShapeΓ hM9 B).TVar := .inr (.inl ⟨i, ⟨0, h⟩⟩)
    ((s1, t0) ∈ badConstrΓ hM9 B RD hG layer ∧ (t0, t1) ∈ badConstrΓ hM9 B RD hG layer) ∨
      ((t1, t0) ∈ badConstrΓ hM9 B RD hG layer ∧ (t0, s1) ∈ badConstrΓ hM9 B RD hG layer)

theorem clock_t0Γ (i : Fin n) :
    (assemblyClockAtomEquivΓ hM9 B (.inl ⟨i, 0⟩)).1 = (assemblyPieceAtΓ B i).lower := by
  refine (clockAtom_of_slotΓ hM9 B _ i (assemblyChartAtΓ hM9 B i).indexing.shape.x0 ?_).trans
    (assemblyChartAtΓ hM9 B i).indexing.lower
  exact (Sumint.timeVectorEquiv_zero (assemblyShapeΓ hM9 B) i).trans
    (Sigma.ext rfl (heq_of_eq (familySlotEquiv_x0 (fun i => (assemblyPieceAtΓ B i).label)
      (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) i).symm))

theorem mem_timeConstraints_of_parentΓ (c1 c2 : (assemblyShapeΓ hM9 B).TVar)
    (hn : (assemblyClockAtomEquivΓ hM9 B c1).1.1.2 ≠ [])
    (h : (assemblyClockAtomEquivΓ hM9 B c1).1.toNode.parent hn = (assemblyClockAtomEquivΓ hM9 B c2).1) :
    (c1, c2) ∈ assemblyTimeConstraintsΓ hM9 B := by
  classical
  unfold assemblyTimeConstraintsΓ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn, h⟩

theorem mem_badConstr_parentΓ (c1 c2 : (assemblyShapeΓ hM9 B).TVar)
    (hn : (assemblyClockAtomEquivΓ hM9 B c1).1.1.2 ≠ [])
    (h : (assemblyClockAtomEquivΓ hM9 B c1).1.toNode.parent hn = (assemblyClockAtomEquivΓ hM9 B c2).1) :
    (c1, c2) ∈ badConstrΓ hM9 B RD hG layer :=
  Finset.mem_union_left _ (mem_timeConstraints_of_parentΓ hM9 B c1 c2 hn h)

theorem mem_badConstr_layerΓ (c1 c2 : (assemblyShapeΓ hM9 B).TVar)
    (h : atomLayer RD hG layer (assemblyClockAtomEquivΓ hM9 B c1).1 + 1 ≤
      atomLayer RD hG layer (assemblyClockAtomEquivΓ hM9 B c2).1) :
    (c1, c2) ∈ badConstrΓ hM9 B RD hG layer :=
  Finset.mem_union_right _ ((mem_layerOrderPairs _ _).mpr h)

/-- Clause (a) from the end-rung adjacency: `t_right < t_b < t_left`. -/
theorem aClause_of_rung0Γ (i : Fin n) (h0 : 0 < (assemblyChartAtΓ hM9 B i).indexing.shape.m)
    (left right : GBranch G.tree)
    (hleft : ∃ hn : (assemblyPieceAtΓ B i).lower.1.2 ≠ [], GNode.parent (assemblyPieceAtΓ B i).lower.toNode hn = left)
    (hright : (∃ hn : right.1.2 ≠ [], GNode.parent right.toNode hn = (assemblyPieceAtΓ B i).lower) ∨
      atomLayer RD hG layer right + 1 ≤ atomLayer RD hG layer (assemblyPieceAtΓ B i).lower)
    (hrung : (((assemblyChartAtΓ hM9 B i).indexing.atom ((assemblyChartAtΓ hM9 B i).indexing.shape.xSlot ⟨0, h0⟩)).1 = left ∧
        ((assemblyChartAtΓ hM9 B i).indexing.atom ((assemblyChartAtΓ hM9 B i).indexing.shape.ySlot ⟨0, h0⟩)).1 = right) ∨
      (((assemblyChartAtΓ hM9 B i).indexing.atom ((assemblyChartAtΓ hM9 B i).indexing.shape.xSlot ⟨0, h0⟩)).1 = right ∧
        ((assemblyChartAtΓ hM9 B i).indexing.atom ((assemblyChartAtΓ hM9 B i).indexing.shape.ySlot ⟨0, h0⟩)).1 = left)) :
    AClauseΓ hM9 B RD hG layer i := by
  have hx := clockAtom_xΓ hM9 B i ⟨0, h0⟩
  have hy := clockAtom_yΓ hM9 B i ⟨0, h0⟩
  have ht0 := clock_t0Γ hM9 B i
  refine ⟨h0, ?_⟩
  -- the constraints `right < b` and `b < left`
  have hbl : ∀ c : (assemblyShapeΓ hM9 B).TVar, (assemblyClockAtomEquivΓ hM9 B c).1 = left →
      ((.inl ⟨i, 0⟩ : (assemblyShapeΓ hM9 B).TVar), c) ∈ badConstrΓ hM9 B RD hG layer := by
    intro c hc
    obtain ⟨hn, hp⟩ := hleft
    refine mem_badConstr_parentΓ hM9 B RD hG layer _ _ (by rw [ht0]; exact hn) ?_
    simp only [ht0, hc]
    exact hp
  have hrb : ∀ c : (assemblyShapeΓ hM9 B).TVar, (assemblyClockAtomEquivΓ hM9 B c).1 = right →
      (c, (.inl ⟨i, 0⟩ : (assemblyShapeΓ hM9 B).TVar)) ∈ badConstrΓ hM9 B RD hG layer := by
    intro c hc
    rcases hright with ⟨hn, hp⟩ | hl
    · refine mem_badConstr_parentΓ hM9 B RD hG layer _ _ (by rw [hc]; exact hn) ?_
      simp only [ht0, hc]
      exact hp
    · refine mem_badConstr_layerΓ hM9 B RD hG layer _ _ ?_
      rw [ht0, hc]
      exact hl
  rcases hrung with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hrb _ (hy.trans h2), hbl _ (hx.trans h1)⟩
  · exact Or.inr ⟨hrb _ (hx.trans h1), hbl _ (hy.trans h2)⟩

variable (hLayer : IsLayering (RD.garden hG) layer)

include hLayer in
/-- For a CL type-II vine, a non-core vine (II-e) or a layer-ineligible one satisfies clause (a). -/
theorem aClause_typeIIΓ (i : Fin n) (hII : (assemblyPieceAtΓ B i).label = .II)
    (hout : (∃ p ∈ (assemblyPieceAtΓ B i).atoms, ∃ q ∈ (assemblyPieceAtΓ B i).atoms,
        Molecpl.IsTypeIIE G (assemblyPieceAtΓ B i).upper (assemblyPieceAtΓ B i).lower p q) ∨
      ¬ ∃ R' : Molecpl.EndRungData G.molecule (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper
          (assemblyPieceAtΓ B i).lower,
        atomLayer RD hG layer (assemblyPieceAtΓ B i).lower ≤
          min (atomLayer RD hG layer R'.left) (atomLayer RD hG layer R'.right)) :
    AClauseΓ hM9 B RD hG layer i := by
  obtain ⟨R, hn, hp, h0, hrung⟩ := rung0_pieceΓ hM9 (assemblyPieceAtΓ B i) hII (assemblyPiece_clΓ B i)
  have hbS : (assemblyPieceAtΓ B i).lower ∈ (assemblyPieceAtΓ B i).atoms := (assemblyPieceAtΓ B i).isBlock.2.2.1
  refine aClause_of_rung0Γ hM9 B RD hG layer i h0 R.left R.right ⟨hn, hp⟩ ?_ hrung
  rcases hout with ⟨p, hpS, q, hqS, ⟨hpn, hpp⟩, ⟨hqn, hqp⟩, -⟩ | hnel
  · left
    have hql := child_mem_rung (assemblyPieceAtΓ B i).isBlock R hqS hbS ⟨hqn, hqp⟩
    rcases hql with hql | hql
    · exfalso
      have hlen : q.1.2.length = (assemblyPieceAtΓ B i).lower.1.2.length + 1 := by
        have := congrArg (fun x : GBranch G.tree => x.1.2) hqp
        change q.1.2.dropLast = _ at this
        have hl := List.length_pos_of_ne_nil hqn
        rw [← this, List.length_dropLast]
        omega
      have hlen2 : R.left.1.2.length + 1 = (assemblyPieceAtΓ B i).lower.1.2.length := by
        have := congrArg (fun x : GBranch G.tree => x.1.2) hp
        change (assemblyPieceAtΓ B i).lower.1.2.dropLast = _ at this
        have hl := List.length_pos_of_ne_nil hn
        rw [← this, List.length_dropLast]
        omega
      rw [hql] at hlen
      omega
    · subst hql
      exact ⟨hqn, hqp⟩
  · right
    by_contra hlt
    apply hnel
    refine ⟨R, ?_⟩
    have h1 : atomLayer RD hG layer (assemblyPieceAtΓ B i).lower ≤ atomLayer RD hG layer R.left := by
      have := layer_core_le RD hG layer hLayer (assemblyPieceAtΓ B i).lower hn
      rw [hp] at this
      exact this
    exact le_min h1 (by omega)

end WaveTurbulence.GammaLow.Famb.VineEstS3
