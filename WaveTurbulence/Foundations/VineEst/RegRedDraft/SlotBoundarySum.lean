/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.GardenConservation
public import WaveTurbulence.Foundations.Molecule.BlockSlots
public import WaveTurbulence.Foundations.Molecule.VineBoundary

/-! # Actual internal garden incidence slots cancel in finite regional sums -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Finset

variable {w : ℕ} (G : Garden w) {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem sum_internalPositions_eq_darts (S : Finset (GBranch G.tree)) (A : GNode G.tree → E)
    (v : GBranch G.tree) :
    (∑ i ∈ Mole.internalPositions G S v, Mole.slotWeight G v i • A (Mole.slotNode G v i)) =
      ∑ x ∈ (G.molecule.dartsAt v).filter (G.molecule.InGroup S),
        G.molecule.dartSign x • Mole.restrictLabels G A x := by
  classical
  have hinj : Set.InjOn (Mole.dartPosition G) ((G.molecule.dartsAt v).filter (G.molecule.InGroup S)) := by
    intro x hx y hy he
    apply Mole.atom_position_injective G
    exact Prod.ext (((Mole.mem_dartsAt _ _ _).mp (Finset.mem_filter.mp hx).1).trans
      ((Mole.mem_dartsAt _ _ _).mp (Finset.mem_filter.mp hy).1).symm) he
  change (∑ i ∈ ((G.molecule.dartsAt v).filter (G.molecule.InGroup S)).image (Mole.dartPosition G), _) = _
  apply (Finset.sum_image hinj).trans
  apply Finset.sum_congr rfl
  intro x hx
  have hv := (Mole.mem_dartsAt _ _ _).mp (Finset.mem_filter.mp hx).1
  rw [← hv,Mole.slotNode_dart,Mole.slotWeight_dart]
  rfl

theorem sum_internalSlots_zero (S : Finset (GBranch G.tree)) (A : GNode G.tree → E)
    (hA : ∀ ℓ, A ℓ.toNode = A (G.pair ℓ).toNode) :
    (∑ v ∈ S, ∑ i ∈ Mole.internalPositions G S v, Mole.slotWeight G v i • A (Mole.slotNode G v i)) = 0 := by
  classical
  let f := fun x : GardenDart G => G.molecule.dartSign x • Mole.restrictLabels G A x
  have he (v : GBranch G.tree) : (G.molecule.dartsAt v).filter (G.molecule.InGroup S) =
      (Finset.univ.filter (G.molecule.InGroup S)).filter (fun x => G.molecule.atom x = v) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Molecule.dartsAt]
    tauto
  have hh : (∑ v ∈ S, ∑ x ∈ (G.molecule.dartsAt v).filter (G.molecule.InGroup S), f x) =
      ∑ x ∈ Finset.univ.filter (G.molecule.InGroup S), f x := by
    simp_rw [he]
    apply (Finset.sum_fiberwise_eq_sum_filter _ _ _ _).trans
    apply congrArg (fun T : Finset (GardenDart G) => ∑ x ∈ T, f x)
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Molecule.InGroup]
    tauto
  apply (Finset.sum_congr rfl (fun v _ => sum_internalPositions_eq_darts G S A v)).trans
  exact hh.trans (Vine.sum_internal_eq_zero G.molecule S (Mole.restrictLabels G A) (Mole.restrictLabels_mate G A hA))

noncomputable def externalSlotSum (S : Finset (GBranch G.tree)) (A : GNode G.tree → E)
    (v : GBranch G.tree) : E :=
  ∑ i ∈ Finset.univ.filter (fun i => i ∉ Mole.internalPositions G S v),
    Mole.slotWeight G v i • A (Mole.slotNode G v i)

/-- Regional cancellation retains only the actual external incidence slots,
including root slots that are absent from the surrounding molecule. -/
theorem sum_slotSum_eq_externalSlots (S : Finset (GBranch G.tree)) (A : GNode G.tree → E)
    (hA : ∀ ℓ, A ℓ.toNode = A (G.pair ℓ).toNode) :
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
  rw [Finset.sum_add_distrib,sum_internalSlots_zero G S A hA,zero_add]

end WaveTurbulence.RegRed
