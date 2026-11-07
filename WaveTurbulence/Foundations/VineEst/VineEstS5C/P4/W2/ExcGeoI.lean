/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo

/-! # P4-W2 (R78 item 4): the geometry of a type-I record

`typeI_qb_qr`: for a core family member `i` of type I, `qbOf` (the parent of the lower joint) and `qrOf` (the parent of the partner of the retained leaf) are BOTH the upper joint `F.upper i`:
the lower joint is a child of the upper joint (`Molecpl.typeI_parent`) and the retained leaf is the child leaf of the lower joint paired to a child leaf of the upper joint
(`Molecpl.typeI_leaf_pair`, `retained_slot_of_leaf_pair` identifies the retained slot with the designated one).  Hence `s₁ = t₁` (`dictS1`, `dictT1` of equal arguments) for every type-I record,
so that the summands A1, A2, TQ, TT of the bundle vanish identically. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist TTree
open WaveTurbulence.VineEstS5B

variable {w : ℕ} {G : Garden w}

theorem parent_child_branch (v : GBranch G.tree) (j : Fin 3) (h : (v.child j).1.2 ≠ []) :
    GNode.parent (v.child j) h = v := by
  apply Subtype.ext
  simp [GNode.parent, GBranch.child]

theorem typeI_qb_qr {ι : Type*} (F : CoreFamily G ι) (i : ι) (hI : F.kind i = VineType.I) :
    qbOf (F.placement i) = F.upper i ∧ qrOf (F.placement i) = F.upper i := by
  have hcore := F.core i
  rw [hI] at hcore
  obtain ⟨hV, hCL, -⟩ := hcore
  obtain ⟨hn, hpar⟩ := Molecpl.typeI_parent G hV hCL
  obtain ⟨l, i', j, hm, hl, hr, hi⟩ := Molecpl.typeI_leaf_pair G hV hCL
  refine ⟨hpar, ?_⟩
  have hB := hV.1
  have hslot := retained_slot_of_leaf_pair G hB hCL hB.2.1 hm hl hr
  have hk : (F.placement i).keep = i' := (hslot _).1 (((F.designated i).2 (F.placement i).keep).2 rfl)
  have hret : (F.placement i).retained = l :=
    Mole.leaf_toNode_injective (by rw [(F.placement i).child, hk, hl])
  have key : ∀ (n : GNode G.tree) (hn : n.1.2 ≠ []) (v : GBranch G.tree) (j : Fin 3), n = v.child j →
      GNode.parent n hn = v := by
    rintro n hn v j rfl
    exact parent_child_branch v j hn
  exact key _ _ _ j (by rw [hret]; exact hr)
end WaveTurbulence.VineEstS5C.P4.W2
