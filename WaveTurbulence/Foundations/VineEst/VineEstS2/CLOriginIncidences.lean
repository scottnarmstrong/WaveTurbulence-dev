/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.LocalDifferenceProposal
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLBoundaryIdentities
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLIncidenceDifferenceCoefficients

/-! # Proposed molecule-local origin geometry implies actual garden slots -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- A local-origin incidence is an actual parent/child slot. This proves
only the geometric implication; no local-witness property of M9 is assumed. -/
theorem originAt_source_slot (R : CLRegionData G U a b)
    (p : Bond G.molecule U ⊕ Fin 2) (v : GBranch G.tree) (out : Bool)
    (hp : OriginAt G.molecule U b p v out) :
    ∃ i : Fin 4, Mole.slotWeight G v i = (if out then 1 else -1) ∧
      ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
        (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        origin G.molecule U (fun e => Mole.restrictLabels G κ e.1)
          (κ (clBoundaryNodes R 2)) (κ (clBoundaryNodes R 2)-κ (clBoundaryNodes R 3)) p =
          κ (Mole.slotNode G v i) := by
  cases p with
  | inl e =>
    rcases hp with ⟨ha,ho⟩ | ⟨ha,ho⟩
    · refine ⟨Mole.dartPosition G e.1,?_,?_⟩
      · have he := Mole.slotWeight_dart G e.1
        rw [ha] at he
        exact he.trans (by simp only [Molecule.dartSign,ho])
      · intro E _ κ _
        have he := Mole.slotNode_dart G e.1
        rw [ha] at he
        exact congrArg κ he.symm
    · refine ⟨Mole.dartPosition G (G.molecule.mate e.1),?_,?_⟩
      · have he := Mole.slotWeight_dart G (G.molecule.mate e.1)
        rw [ha] at he
        exact he.trans (by simp only [Molecule.dartSign,ho])
      · intro E _ κ hmatch
        have he := Mole.slotNode_dart G (G.molecule.mate e.1)
        rw [ha] at he
        exact (gardenInternal_restrict_mate κ hmatch ⟨e.1,internalBond_inGroup G.molecule U e⟩).symm.trans
          (congrArg κ he.symm)
  | inr j =>
    obtain ⟨rfl,ho⟩ := hp
    by_cases hj : j = 0
    · refine ⟨R.positive.succ,?_,?_⟩
      · rw [slotWeight_child,R.positive_sign]
        simp only [hj,ite_true] at ho
        simp only [ho,Bool.false_eq_true,ite_false,Units.val_one,Int.cast_one]
      · intro E _ κ _
        simp only [origin,hj,ite_true]
        rfl
    · refine ⟨R.negative.succ,?_,?_⟩
      · rw [slotWeight_child,R.negative_sign]
        simp only [hj,ite_false] at ho
        simp only [ho,ite_true,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_neg]
      · intro E _ κ _
        simp only [origin,hj,ite_false,sub_sub_cancel]
        rfl

end WaveTurbulence.VineEstS2
