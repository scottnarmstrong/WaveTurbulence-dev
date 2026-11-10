/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Incidence
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NodeSlots

/-! # Root ports and the four ordered ports at each branching node

The parent port has index 0 and the three child ports have indices 1,2,3.
The exact equivalence with source incidence slots retains the entire forest
and leaf matching; no unordered graph quotient is taken.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

abbrev Port {w : ℕ} (G : Garden w) := Fin w ⊕ (GBranch G.tree × Fin 4)

def encodeIncidence {w : ℕ} (G : Garden w) : Incidence G → Port G
  | .inr b => .inr (b,0)
  | .inl a => match nodeToSlot a with
      | .inl j => .inl j
      | .inr (b,i) => .inr (b,i.succ)

def decodePort {w : ℕ} (G : Garden w) : Port G → Incidence G
  | .inl j => .inl (GNode.root G.tree j)
  | .inr (b,k) => Fin.cases (.inr b) (fun i => .inl (b.child i)) k

theorem encodeIncidence_child {w : ℕ} (G : Garden w) (b : GBranch G.tree) (i : Fin 3) :
    encodeIncidence G (.inl (b.child i)) = .inr (b,i.succ) := by
  simp only [encodeIncidence,nodeToSlot_child]

theorem decodePort_child {w : ℕ} (G : Garden w) (b : GBranch G.tree) (i : Fin 3) :
    decodePort G (.inr (b,i.succ)) = .inl (b.child i) := rfl

/-- Exact port encoding of every source halfedge. -/
def portEquiv {w : ℕ} (G : Garden w) : Incidence G ≃ Port G where
  toFun := encodeIncidence G
  invFun := decodePort G
  left_inv x := by
    cases x with
    | inr b => rfl
    | inl a =>
      have hi : slotToNode G.tree (nodeToSlot a) = a := (nodeSlotEquiv G.tree).left_inv a
      cases hs : nodeToSlot a with
      | inl j =>
        have hh := congrArg (slotToNode G.tree) hs
        have he : slotToNode G.tree (.inl j) = a := hh.symm.trans hi
        simp only [encodeIncidence,hs,decodePort]
        exact congrArg Sum.inl he
      | inr x =>
        obtain ⟨b,i⟩ := x
        have hh := congrArg (slotToNode G.tree) hs
        have he : slotToNode G.tree (.inr (b,i)) = a := hh.symm.trans hi
        simp only [encodeIncidence,hs,decodePort,Fin.cases_succ]
        exact congrArg Sum.inl he
  right_inv x := by
    cases x with
    | inl j => simp [decodePort,encodeIncidence,nodeToSlot,GNode.root]
    | inr x =>
      obtain ⟨b,k⟩ := x
      refine Fin.cases ?_ (fun i => ?_) k
      · rfl
      · rw [decodePort_child,encodeIncidence_child]

/-- The original garden matching in its ordered root/branch port coordinates. -/
def portMate {w : ℕ} (G : Garden w) (p : Port G) : Port G :=
  portEquiv G (incidenceMate G ((portEquiv G).symm p))

/-- Port encoding preserves exact matching involutivity. -/
theorem portMate_involutive {w : ℕ} (G : Garden w) : Function.Involutive (portMate G) := by
  intro p
  unfold portMate
  rw [Equiv.symm_apply_apply,incidenceMate_involutive G,Equiv.apply_symm_apply]

/-- No fixed active port occurs in an ordinary garden. -/
theorem portMate_ne {w : ℕ} (G : Garden w) (hG : G.IsPlain) (p : Port G) : portMate G p ≠ p := by
  intro hp
  have he := congrArg (portEquiv G).symm hp
  change (portEquiv G).symm (portEquiv G (incidenceMate G ((portEquiv G).symm p))) =
    (portEquiv G).symm p at he
  rw [Equiv.symm_apply_apply] at he
  exact incidenceMate_ne G hG _ he

end WaveTurbulence.Reg.Skeleton
