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

/-! # BadClause, part A: assumption (a) of `sumint` from the adjacency of the end rung (TARGET L1841-L1847)

`AClause` is clause (a) of `BadClause` for the constraint set of `step3W`.  If the chosen rung `0` of a vine is
`{left, right}` with `b`'s parent `left`, and either `right` is a child of `b` (II-e) or `L_right < L_b`, then
`AClause` holds: `t_right < t_b < t_left` (parent constraints and `layerOrderPairs`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract TTree RegRed WaveTurbulence.Reg.Skeleton
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)

/-- The constraint set of `step3W`. -/
noncomputable def badConstr : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar) :=
  assemblyTimeConstraints hM9 B ∪ layerOrderPairs (assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))

/-- Clause (a) of `BadClause` for the vine `i`. -/
def AClause (i : Fin (assemblyShape hM9 B).I) : Prop :=
  ∃ h : 0 < (assemblyShape hM9 B).m i,
    let t0 : (assemblyShape hM9 B).TVar := .inl ⟨i, 0⟩
    let t1 : (assemblyShape hM9 B).TVar := .inl ⟨i, ⟨1, by omega⟩⟩
    let s1 : (assemblyShape hM9 B).TVar := .inr (.inl ⟨i, ⟨0, h⟩⟩)
    ((s1, t0) ∈ badConstr hM9 B RD hG layer ∧ (t0, t1) ∈ badConstr hM9 B RD hG layer) ∨
      ((t1, t0) ∈ badConstr hM9 B RD hG layer ∧ (t0, s1) ∈ badConstr hM9 B RD hG layer)

theorem clock_t0 (i : Fin n) :
    (assemblyClockAtomEquiv hM9 B (.inl ⟨i, 0⟩)).1 = (assemblyPieceAt B i).lower := by
  refine (clockAtom_of_slot hM9 B _ i (assemblyChartAt hM9 B i).indexing.shape.x0 ?_).trans
    (assemblyChartAt hM9 B i).indexing.lower
  exact (Sumint.timeVectorEquiv_zero (assemblyShape hM9 B) i).trans
    (Sigma.ext rfl (heq_of_eq (familySlotEquiv_x0 (fun i => (assemblyPieceAt B i).vineType)
      (fun i => (assemblyChartAt hM9 B i).indexing.shape) i).symm))

theorem mem_timeConstraints_of_parent (c1 c2 : (assemblyShape hM9 B).TVar)
    (hn : (assemblyClockAtomEquiv hM9 B c1).1.1.2 ≠ [])
    (h : (assemblyClockAtomEquiv hM9 B c1).1.toNode.parent hn = (assemblyClockAtomEquiv hM9 B c2).1) :
    (c1, c2) ∈ assemblyTimeConstraints hM9 B := by
  classical
  unfold assemblyTimeConstraints
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn, h⟩

theorem mem_badConstr_parent (c1 c2 : (assemblyShape hM9 B).TVar)
    (hn : (assemblyClockAtomEquiv hM9 B c1).1.1.2 ≠ [])
    (h : (assemblyClockAtomEquiv hM9 B c1).1.toNode.parent hn = (assemblyClockAtomEquiv hM9 B c2).1) :
    (c1, c2) ∈ badConstr hM9 B RD hG layer :=
  Finset.mem_union_left _ (mem_timeConstraints_of_parent hM9 B c1 c2 hn h)

theorem mem_badConstr_layer (c1 c2 : (assemblyShape hM9 B).TVar)
    (h : atomLayer RD hG layer (assemblyClockAtomEquiv hM9 B c1).1 + 1 ≤
      atomLayer RD hG layer (assemblyClockAtomEquiv hM9 B c2).1) :
    (c1, c2) ∈ badConstr hM9 B RD hG layer :=
  Finset.mem_union_right _ ((mem_layerOrderPairs _ _).mpr h)

/-- Clause (a) from the end-rung adjacency: `t_right < t_b < t_left`. -/
theorem aClause_of_rung0 (i : Fin n) (h0 : 0 < (assemblyChartAt hM9 B i).indexing.shape.m)
    (left right : GBranch G.tree)
    (hleft : ∃ hn : (assemblyPieceAt B i).lower.1.2 ≠ [], GNode.parent (assemblyPieceAt B i).lower.toNode hn = left)
    (hright : (∃ hn : right.1.2 ≠ [], GNode.parent right.toNode hn = (assemblyPieceAt B i).lower) ∨
      atomLayer RD hG layer right + 1 ≤ atomLayer RD hG layer (assemblyPieceAt B i).lower)
    (hrung : (((assemblyChartAt hM9 B i).indexing.atom ((assemblyChartAt hM9 B i).indexing.shape.xSlot ⟨0, h0⟩)).1 = left ∧
        ((assemblyChartAt hM9 B i).indexing.atom ((assemblyChartAt hM9 B i).indexing.shape.ySlot ⟨0, h0⟩)).1 = right) ∨
      (((assemblyChartAt hM9 B i).indexing.atom ((assemblyChartAt hM9 B i).indexing.shape.xSlot ⟨0, h0⟩)).1 = right ∧
        ((assemblyChartAt hM9 B i).indexing.atom ((assemblyChartAt hM9 B i).indexing.shape.ySlot ⟨0, h0⟩)).1 = left)) :
    AClause hM9 B RD hG layer i := by
  have hx := clockAtom_x hM9 B i ⟨0, h0⟩
  have hy := clockAtom_y hM9 B i ⟨0, h0⟩
  have ht0 := clock_t0 hM9 B i
  refine ⟨h0, ?_⟩
  -- the constraints `right < b` and `b < left`
  have hbl : ∀ c : (assemblyShape hM9 B).TVar, (assemblyClockAtomEquiv hM9 B c).1 = left →
      ((.inl ⟨i, 0⟩ : (assemblyShape hM9 B).TVar), c) ∈ badConstr hM9 B RD hG layer := by
    intro c hc
    obtain ⟨hn, hp⟩ := hleft
    refine mem_badConstr_parent hM9 B RD hG layer _ _ (by rw [ht0]; exact hn) ?_
    simp only [ht0, hc]
    exact hp
  have hrb : ∀ c : (assemblyShape hM9 B).TVar, (assemblyClockAtomEquiv hM9 B c).1 = right →
      (c, (.inl ⟨i, 0⟩ : (assemblyShape hM9 B).TVar)) ∈ badConstr hM9 B RD hG layer := by
    intro c hc
    rcases hright with ⟨hn, hp⟩ | hl
    · refine mem_badConstr_parent hM9 B RD hG layer _ _ (by rw [hc]; exact hn) ?_
      simp only [ht0, hc]
      exact hp
    · refine mem_badConstr_layer hM9 B RD hG layer _ _ ?_
      rw [ht0, hc]
      exact hl
  rcases hrung with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hrb _ (hy.trans h2), hbl _ (hx.trans h1)⟩
  · exact Or.inr ⟨hrb _ (hx.trans h1), hbl _ (hy.trans h2)⟩

theorem child_mem_rung {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (R : Molecpl.EndRungData G.molecule S a b) {q : GBranch G.tree}
    (hq : q ∈ S) (hbS : b ∈ S) (hpar : Molecpl.IsParent G b q) : q = R.left ∨ q = R.right := by
  obtain ⟨hn, hp⟩ := hpar
  let d : GardenDart G := .inl (⟨q, hn⟩, false)
  have hd : G.molecule.InGroup S d := ⟨hq, by show GNode.parent q.toNode hn ∈ S; rw [hp]; exact hbS⟩
  have h := Molecpl.EndRungData.lower_neighbor hB R (x := G.molecule.mate d) (by
    show GNode.parent q.toNode hn = b
    exact hp) (by
    refine ⟨?_, ?_⟩
    · show GNode.parent q.toNode hn ∈ S
      rw [hp]; exact hbS
    · rw [G.molecule.mate_mate]; exact hq)
  rw [G.molecule.mate_mate] at h
  exact h

variable (hLayer : IsLayering (RD.garden hG) layer)

include hLayer in
/-- For a CL type-II vine, a non-core vine (II-e) or a layer-ineligible one satisfies clause (a). -/
theorem aClause_typeII (i : Fin n) (hII : (assemblyPieceAt B i).vineType = .II)
    (hout : (∃ p ∈ (assemblyPieceAt B i).atoms, ∃ q ∈ (assemblyPieceAt B i).atoms,
        Molecpl.IsTypeIIE G (assemblyPieceAt B i).upper (assemblyPieceAt B i).lower p q) ∨
      ¬ ∃ R' : Molecpl.EndRungData G.molecule (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper
          (assemblyPieceAt B i).lower,
        atomLayer RD hG layer (assemblyPieceAt B i).lower ≤
          min (atomLayer RD hG layer R'.left) (atomLayer RD hG layer R'.right)) :
    AClause hM9 B RD hG layer i := by
  obtain ⟨R, hn, hp, h0, hrung⟩ := rung0_piece hM9 (assemblyPieceAt B i) hII (assemblyPiece_cl B i)
  have hbS : (assemblyPieceAt B i).lower ∈ (assemblyPieceAt B i).atoms := (assemblyPieceAt B i).vine.1.2.2.1
  refine aClause_of_rung0 hM9 B RD hG layer i h0 R.left R.right ⟨hn, hp⟩ ?_ hrung
  rcases hout with ⟨p, hpS, q, hqS, ⟨hpn, hpp⟩, ⟨hqn, hqp⟩, -⟩ | hnel
  · left
    have hql := child_mem_rung (assemblyPieceAt B i).vine.1 R hqS hbS ⟨hqn, hqp⟩
    rcases hql with hql | hql
    · exfalso
      have hlen : q.1.2.length = (assemblyPieceAt B i).lower.1.2.length + 1 := by
        have := congrArg (fun x : GBranch G.tree => x.1.2) hqp
        change q.1.2.dropLast = _ at this
        have hl := List.length_pos_of_ne_nil hqn
        rw [← this, List.length_dropLast]
        omega
      have hlen2 : R.left.1.2.length + 1 = (assemblyPieceAt B i).lower.1.2.length := by
        have := congrArg (fun x : GBranch G.tree => x.1.2) hp
        change (assemblyPieceAt B i).lower.1.2.dropLast = _ at this
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
    have h1 : atomLayer RD hG layer (assemblyPieceAt B i).lower ≤ atomLayer RD hG layer R.left := by
      have := layer_core_le RD hG layer hLayer (assemblyPieceAt B i).lower hn
      rw [hp] at this
      exact this
    exact le_min h1 (by omega)

end WaveTurbulence.VineEstS3
