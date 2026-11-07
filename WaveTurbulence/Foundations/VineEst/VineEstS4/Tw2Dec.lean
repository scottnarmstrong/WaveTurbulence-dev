/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw1Geom
public import WaveTurbulence.Foundations.Molecule.TwistEpsilon
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PhaseFactorization
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.EpsilonFactorization

/-! # K^T twist invariance, local labels (V5 Step 4b, step 3, part 2)

Labels `ext'` of the twisted garden and `ext` of the original garden are related by `ext x = ext' (twNode x)`
(`twNode = naiveNodeEquiv ∘ swap(lower, retained)`: the labels of the lower joint and of the retained leaf are exchanged,
TARGET `twistexplain` (d)).  Facts about `twNode` at the lower joint and its children, the conservation equation at the
lower joint (local version of `twistNodeLabels_lower_reflect`), and the epsilon and resonance factors there.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

/-- The lower joint of the twisted garden, typed in `(unitTwistGarden G P).tree`. -/
@[expose, reducible] noncomputable def eLow : GBranch (unitTwistGarden G P).tree := coreBranchEquiv G P P.lower

theorem twNode_lower : twNode P P.lower.toNode = (eLow P).child P.keep := by
  rw [twNode_apply, Equiv.swap_apply_left]
  exact (naiveNodeEquiv_leaf G P P.retained).trans (reversePlacement G P).child

theorem twNode_retained : twNode P P.retained.toNode = (eLow P).toNode := by
  rw [twNode_apply, Equiv.swap_apply_right]
  exact naiveNodeEquiv_branch G P P.lower

theorem twNode_lower_child (i : Fin 3) (hi : i ≠ P.keep) :
    twNode P (P.lower.child i) = (eLow P).child (freeSwap P.keep i) := by
  have h1 : P.lower.child i ≠ P.lower.toNode := child_ne_parent G P.lower i
  have h2 : P.lower.child i ≠ P.retained.toNode := fun h => hi ((lower_child_retained_iff G P i).mp h)
  rw [twNode_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  exact lower_naive_child G P i

theorem twNode_lower_child_keep : twNode P (P.lower.child P.keep) = (eLow P).toNode := by
  rw [← P.child]
  exact twNode_retained P

theorem twNode_branch (v : GBranch G.tree) (hv : v ≠ P.lower) :
    twNode P v.toNode = (coreBranchEquiv G P v).toNode := by
  have h1 : v.toNode ≠ P.lower.toNode := fun h => hv (Mole.branch_toNode_injective h)
  have h2 : v.toNode ≠ P.retained.toNode := Mole.branch_toNode_ne_leaf v P.retained
  rw [twNode_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  exact naiveNodeEquiv_branch G P v

theorem twNode_leaf (l : GLeaf G.tree) (hl : l ≠ P.retained) :
    twNode P l.toNode = (coreLeafEquiv G P l).toNode := by
  have h1 : l.toNode ≠ P.lower.toNode := (Mole.branch_toNode_ne_leaf P.lower l).symm
  have h2 : l.toNode ≠ P.retained.toNode := fun h => hl (Mole.leaf_toNode_injective h)
  rw [twNode_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  exact naiveNodeEquiv_leaf G P l

variable {T : Finset (GBranch G.tree)} {z : GBranch G.tree}

theorem twNode_child (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
    {v : GBranch G.tree} (hv : v ∈ T) (hne : v ≠ P.lower) (i : Fin 3) :
    twNode P (v.child i) = (coreBranchEquiv G P v).child i := by
  obtain ⟨h1, h2, h3⟩ := child_avoid P hB hCL hv hne i
  rw [twNode_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  exact child_naive P hB hCL hv hne i

section LowerGen
variable {E : Type*} (ext : GNode G.tree → E) (ext' : GNode (unitTwistGarden G P).tree → E)
  (hext : ∀ x, ext x = ext' (twNode P x))
include hext

theorem ext_lower_child_gen (i : Fin 3) (hi : i ≠ P.keep) :
    ext (P.lower.child i) = ext' ((eLow P).child (freeSwap P.keep i)) := by
  rw [hext, twNode_lower_child P i hi]

theorem ext_lower_child_keep_gen : ext (P.lower.child P.keep) = ext' (eLow P).toNode := by
  rw [hext, twNode_lower_child_keep P]

theorem ext_lower_gen : ext P.lower.toNode = ext' ((eLow P).child P.keep) := by
  rw [hext, twNode_lower P]

end LowerGen

section Lower
variable {E : Type*} [AddCommGroup E] (ext : GNode G.tree → E) (ext' : GNode (unitTwistGarden G P).tree → E)
  (hext : ∀ x, ext x = ext' (twNode P x))
include hext

theorem ext_lower_child (i : Fin 3) (hi : i ≠ P.keep) :
    ext (P.lower.child i) = ext' ((eLow P).child (freeSwap P.keep i)) := by
  rw [hext, twNode_lower_child P i hi]

theorem ext_lower_child_keep : ext (P.lower.child P.keep) = ext' (eLow P).toNode := by
  rw [hext, twNode_lower_child_keep P]

theorem ext_lower : ext P.lower.toNode = ext' ((eLow P).child P.keep) := by
  rw [hext, twNode_lower P]

/-- The conservation equation at the lower joint holds for `ext` iff it holds for the twisted labels. -/
theorem cons_lower_iff :
    (ext P.lower.toNode = ext (P.lower.child 0) - ext (P.lower.child 1) + ext (P.lower.child 2)) ↔
    (ext' (eLow P).toNode =
      ext' ((eLow P).child 0) - ext' ((eLow P).child 1) +
        ext' ((eLow P).child 2)) := by
  have hk : P.keep = 0 ∨ P.keep = 2 := by have hh := P.outer; omega
  have hl := ext_lower P ext ext' hext
  rcases hk with hk | hk
  · have e1 := ext_lower_child P ext ext' hext 1 (by rw [hk]; decide)
    have e2 := ext_lower_child P ext ext' hext 2 (by rw [hk]; decide)
    have e0 := ext_lower_child_keep P ext ext' hext
    rw [hk] at e0 hl
    have f1 : freeSwap P.keep 1 = 2 := by rw [hk]; simp [freeSwap]
    have f2 : freeSwap P.keep 2 = 1 := by rw [hk]; simp [freeSwap]
    rw [f1] at e1
    rw [f2] at e2
    rw [hl, e0, e1, e2]
    constructor <;> intro h <;> rw [h] <;> abel
  · have e0 := ext_lower_child P ext ext' hext 0 (by rw [hk]; decide)
    have e1 := ext_lower_child P ext ext' hext 1 (by rw [hk]; decide)
    have e2 := ext_lower_child_keep P ext ext' hext
    rw [hk] at e2 hl
    have f0 : freeSwap P.keep 0 = 1 := by rw [hk]; simp [freeSwap]
    have f1 : freeSwap P.keep 1 = 0 := by rw [hk]; simp [freeSwap]
    rw [f0] at e0
    rw [f1] at e1
    rw [hl, e0, e1, e2]
    constructor <;> intro h <;> rw [h] <;> abel

end Lower

section EpsPhase
variable {d : ℕ} (ext : GNode G.tree → (Fin d → ℤ)) (ext' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
  (hext : ∀ x, ext x = ext' (twNode P x))
include hext

/-- The epsilon coefficient at the lower joint is unchanged (local version of `unitTwist_epsCoef`). -/
theorem eps_lower
    (hcons : ext P.lower.toNode = ext (P.lower.child 0) - ext (P.lower.child 1) + ext (P.lower.child 2)) :
    epsBranch ext' (eLow P) = epsBranch ext P.lower := by
  have hk : P.keep = 0 ∨ P.keep = 2 := by have hh := P.outer; omega
  have hl := ext_lower P ext ext' hext
  unfold epsBranch
  rcases hk with hk | hk
  · have e1 := ext_lower_child P ext ext' hext 1 (by rw [hk]; decide)
    have e2 := ext_lower_child P ext ext' hext 2 (by rw [hk]; decide)
    have e0 := ext_lower_child_keep P ext ext' hext
    rw [hk] at e0 hl
    have f1 : freeSwap P.keep 1 = 2 := by rw [hk]; simp [freeSwap]
    have f2 : freeSwap P.keep 2 = 1 := by rw [hk]; simp [freeSwap]
    rw [f1] at e1
    rw [f2] at e2
    have h' := hl.symm.trans (hcons.trans
      (congrArg₂ (fun x y => x + y) (congrArg₂ (fun x y => x - y) e0 e1) e2))
    have rhs := congr (congr (congrArg epsCoef e0) e1) e2
    exact ((congrArg (fun y => epsCoef y _ _) h').trans (epsCoef_exchange_left _ _ _)).trans rhs.symm
  · have e0 := ext_lower_child P ext ext' hext 0 (by rw [hk]; decide)
    have e1 := ext_lower_child P ext ext' hext 1 (by rw [hk]; decide)
    have e2 := ext_lower_child_keep P ext ext' hext
    rw [hk] at e2 hl
    have f0 : freeSwap P.keep 0 = 1 := by rw [hk]; simp [freeSwap]
    have f1 : freeSwap P.keep 1 = 0 := by rw [hk]; simp [freeSwap]
    rw [f0] at e0
    rw [f1] at e1
    have h' := hl.symm.trans (hcons.trans
      (congrArg₂ (fun x y => x + y) (congrArg₂ (fun x y => x - y) e0 e1) e2))
    have rhs := congr (congr (congrArg epsCoef e0) e1) e2
    exact ((congrArg (fun y => epsCoef _ _ y) h').trans (epsCoef_exchange_right _ _ _)).trans rhs.symm

end EpsPhase

section Omega
variable {d : ℕ} (k : GNode G.tree → Mom d) (k' : GNode (unitTwistGarden G P).tree → Mom d)
  (hk : ∀ x, k x = k' (twNode P x))
include hk

/-- The resonance factor at the lower joint is negated. -/
theorem omega_lower : omegaNode (unitTwistGarden G P) k' (eLow P) = -omegaNode G k P.lower := by
  have hkk : P.keep = 0 ∨ P.keep = 2 := by have hh := P.outer; omega
  have hl := ext_lower_gen P k k' hk
  unfold omegaNode resFactor
  rcases hkk with h | h
  · have e1 := ext_lower_child_gen P k k' hk 1 (by rw [h]; decide)
    have e2 := ext_lower_child_gen P k k' hk 2 (by rw [h]; decide)
    have e0 := ext_lower_child_keep_gen P k k' hk
    rw [h] at e0 hl
    have f1 : freeSwap P.keep 1 = 2 := by rw [h]; simp [freeSwap]
    have f2 : freeSwap P.keep 2 = 1 := by rw [h]; simp [freeSwap]
    rw [f1] at e1
    rw [f2] at e2
    rw [e0, e1, e2, hl]
    first | ring1 | linarith
  · have e0 := ext_lower_child_gen P k k' hk 0 (by rw [h]; decide)
    have e1 := ext_lower_child_gen P k k' hk 1 (by rw [h]; decide)
    have e2 := ext_lower_child_keep_gen P k k' hk
    rw [h] at e2 hl
    have f0 : freeSwap P.keep 0 = 1 := by rw [h]; simp [freeSwap]
    have f1 : freeSwap P.keep 1 = 0 := by rw [h]; simp [freeSwap]
    rw [f0] at e0
    rw [f1] at e1
    rw [e0, e1, e2, hl]
    first | ring1 | linarith

end Omega

end WaveTurbulence.VineEstS4
