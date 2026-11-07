/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.SlotBoundarySum
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionData

/-! # Regional incidence cancellation uses only the actual internal matching -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Finset

variable {w : ℕ} (G : Garden w) {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem sum_internalPositions_eq_internalDarts (S : Finset (GBranch G.tree)) (A : GNode G.tree → E) :
    (∑ v ∈ S, ∑ i ∈ Mole.internalPositions G S v, Mole.slotWeight G v i • A (Mole.slotNode G v i)) =
      ∑ x ∈ Finset.univ.filter (G.molecule.InGroup S), G.molecule.dartSign x • Mole.restrictLabels G A x := by
  classical
  let f := fun x : GardenDart G => G.molecule.dartSign x • Mole.restrictLabels G A x
  have he (v : GBranch G.tree) : (G.molecule.dartsAt v).filter (G.molecule.InGroup S) =
      (Finset.univ.filter (G.molecule.InGroup S)).filter (fun x => G.molecule.atom x = v) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Molecule.dartsAt]
    tauto
  apply (Finset.sum_congr rfl (fun v _ => sum_internalPositions_eq_darts G S A v)).trans
  simp_rw [he]
  apply (Finset.sum_fiberwise_eq_sum_filter _ _ _ _).trans
  apply congrArg (fun T : Finset (GardenDart G) => ∑ x ∈ T, f x)
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Molecule.InGroup]
  tauto

theorem sum_internalSlots_zero_local (S : Finset (GBranch G.tree)) (A : GNode G.tree → E)
    (hA : ∀ ℓ, Mole.IsInternalLeaf G S ℓ → A ℓ.toNode = A (G.pair ℓ).toNode) :
    (∑ v ∈ S, ∑ i ∈ Mole.internalPositions G S v, Mole.slotWeight G v i • A (Mole.slotNode G v i)) = 0 := by
  classical
  rw [sum_internalPositions_eq_internalDarts G S A]
  have hm (x : GardenDart G) (hx : G.molecule.InGroup S x) :
      Mole.restrictLabels G A (G.molecule.mate x) = Mole.restrictLabels G A x := by
    rcases x with ⟨c,z⟩ | ℓ
    · cases z <;> rfl
    · exact (hA ℓ.1 ⟨ℓ.2.1,ℓ.2.2.1,ℓ.2.2.2,hx⟩).symm
  apply Finset.sum_involution (fun x _ => G.molecule.mate x)
  · intro x hx
    rw [hm x (Finset.mem_filter.mp hx).2,Mole.dartSign_mate,neg_smul,add_neg_cancel]
  · intro x _ _
    exact G.molecule.mate_ne x
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Molecule.InGroup] at hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Molecule.InGroup,G.molecule.mate_mate]
    exact hx.symm
  · intro x _
    exact G.molecule.mate_mate x

theorem sum_slotSum_eq_externalSlots_local (S : Finset (GBranch G.tree)) (A : GNode G.tree → E)
    (hA : ∀ ℓ, Mole.IsInternalLeaf G S ℓ → A ℓ.toNode = A (G.pair ℓ).toNode) :
    (∑ v ∈ S, Mole.slotSum G A v) = ∑ v ∈ S, externalSlotSum G S A v := by
  classical
  have hv (v : GBranch G.tree) : Mole.slotSum G A v =
      (∑ i ∈ Mole.internalPositions G S v, Mole.slotWeight G v i • A (Mole.slotNode G v i)) +
        externalSlotSum G S A v := by
    have he := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin 4)))
      (fun i => i ∈ Mole.internalPositions G S v) (fun i => Mole.slotWeight G v i • A (Mole.slotNode G v i))
    have hs : Finset.univ.filter (fun i => i ∈ Mole.internalPositions G S v) =
        Mole.internalPositions G S v := by ext i; simp
    rw [hs] at he
    exact he.symm
  simp_rw [hv]
  rw [Finset.sum_add_distrib,sum_internalSlots_zero_local G S A hA,zero_add]

end WaveTurbulence.RegRed
