/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalBondLabels
public import WaveTurbulence.Foundations.Spine.GardenConservation

/-! # Actual internal flow as the signed source slot sum -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}

/-- The integer incidence coefficient agrees with the physical dart sign
at its own atom and vanishes at all other atoms. -/
theorem internalDartCoeff_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : GBranch G.tree) (x : GardenDart G) (y : E) :
    internalDartCoeff G.molecule v x • y =
      if G.molecule.atom x = v then G.molecule.dartSign x • y else 0 := by
  by_cases ho : G.molecule.out x = true <;> by_cases ha : G.molecule.atom x = v <;>
    simp only [internalDartCoeff,Molecule.dartSign,ho,ha,ite_true,ite_false,
      Bool.false_eq_true,one_smul,zero_smul,neg_one_smul,neg_zero]

open Classical in
/-- The occupied slots are derived from actual internal darts. This formula
also applies at joints, where only two of the four slots are occupied. -/
theorem gardenInternalFlow_slots {E : Type*} [AddCommGroup E] [Module ℝ E]
    (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : GBranch G.tree) :
    flow G.molecule U (fun e => Mole.restrictLabels G κ e.1) v =
      ∑ i ∈ Mole.internalPositions G U v, Mole.slotWeight G v i • κ (Mole.slotNode G v i) := by
  classical
  rw [gardenInternalFlow_eq κ hp]
  let F : InternalDart G.molecule U → E := fun x => internalDartCoeff G.molecule v x.1 • κ (Mole.dartNode G x.1)
  let A : Finset (InternalDart G.molecule U) := Finset.univ.filter (fun x => G.molecule.atom x.1 = v)
  have he : (∑ x, F x) = ∑ x ∈ A, F x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hn
    have hx : G.molecule.atom x.1 ≠ v := by
      intro hx
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
    simp only [F,internalDartCoeff_smul,hx,ite_false]
  change (∑ x, F x) = _
  rw [he]
  apply Finset.sum_bij (fun x _ => Mole.dartPosition G x.1)
  · intro x hx
    exact (Mole.mem_internalPositions G).mpr
      ⟨x.1,(Finset.mem_filter.mp hx).2,x.2,rfl⟩
  · intro x hx y hy hxy
    apply Subtype.ext
    apply Mole.atom_position_injective G
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy
  · intro i hi
    obtain ⟨x,hx,hg,hpos⟩ := (Mole.mem_internalPositions G).mp hi
    exact ⟨⟨x,hg⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,hpos⟩
  · intro x hx
    have hv := (Finset.mem_filter.mp hx).2
    change internalDartCoeff G.molecule v x.1 • κ (Mole.dartNode G x.1) = _
    rw [internalDartCoeff_smul,ite_eq_left hv]
    have hs := Mole.slotWeight_dart G x.1
    rw [hv] at hs
    rw [hs]
    have hn := Mole.slotNode_dart G x.1
    rw [hv] at hn
    rw [hn]

end WaveTurbulence.VineEstS2
