/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.TightFiniteCover
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionOrder
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceSlotCounts

/-! # Exact total budget of the native regular replacement node cover -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def sourceNodeSet {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Finset (Address w) := forestSet (D.forest hS) TTree.nodes

def replacementNodeBudget {w : ℕ} {S : Garden w} (D : ReconstructionData S) : ReplacementSlot S → ℕ
  | .inl p => 3 * (D.couple p).size + 2
  | .inr b => 3 * (D.tree b).size + 1

theorem nodeBlock_card_le_budget {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (slot : ReplacementSlot S) :
    (D.nodeBlock hS slot).card ≤ replacementNodeBudget D slot := by
  classical
  cases slot with
  | inl p => exact coupleNodes_card_le _ _ _
  | inr b =>
    have h := Finset.card_union_le
      (chainNodes (D.tree b) (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)) {D.corePosition b}
    rw [Finset.card_singleton] at h
    exact h.trans (Nat.add_le_add_right (chainNodes_card_le _ _ _) 1)

theorem sum_replacementNodeBudget {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : (∑ slot : ReplacementSlot S, replacementNodeBudget D slot) =
      3 * (S.order + D.size) + w := by
  classical
  have hp := sourcePair_card_twice S hS
  have hb : Fintype.card (GBranch S.tree) = S.order := Comb.card_gbranch S.tree
  rw [Fintype.sum_sum_type]
  simp only [replacementNodeBudget,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one]
  unfold ReconstructionData.size
  omega

theorem sourceNodeSet_card {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : (sourceNodeSet D hS).card = 3 * (S.order + D.size) + w := by
  rw [sourceNodeSet,Comb.card_forestSet]
  simp only [Comb.card_nodes,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  rw [D.forest_order hS]

theorem sourceNodeSet_covered {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : sourceNodeSet D hS ⊆ Finset.univ.biUnion (D.nodeBlock hS) := by
  classical
  intro a ha
  have hn : a.2 ∈ (D.forest hS a.1).nodes := (mem_forestSet (D.forest hS)).mp ha
  obtain ⟨slot,hslot⟩ := D.node_covered hS (⟨a,hn⟩ : GNode (D.forest hS))
  exact Finset.mem_biUnion.mpr ⟨slot,Finset.mem_univ _,hslot⟩

/-- The actual complete forest has one and only one replacement-slot owner at
every node. This is a literal address-preserving equivalence, with no supplied
partition/disjointness premise. -/
theorem exists_replacementNodeEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) :
    ∃ e : (Σ slot : ReplacementSlot S, ↥(D.nodeBlock hS slot)) ≃ ↥(sourceNodeSet D hS),
      ∀ p, (e p).1 = p.2.1 := by
  classical
  apply tightCover_equiv (sourceNodeSet D hS) (D.nodeBlock hS) (sourceNodeSet_covered D hS)
  calc
    (∑ slot, (D.nodeBlock hS slot).card) ≤ ∑ slot, replacementNodeBudget D slot :=
      Finset.sum_le_sum (fun slot _ => nodeBlock_card_le_budget D hS slot)
    _ = (sourceNodeSet D hS).card := (sum_replacementNodeBudget D hS).trans (sourceNodeSet_card D hS).symm

end WaveTurbulence.RegRed
