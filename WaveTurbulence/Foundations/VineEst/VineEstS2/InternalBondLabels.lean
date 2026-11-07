/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalFlowSum
public import WaveTurbulence.Foundations.Molecule.GardenLabelExtension
public import WaveTurbulence.Foundations.Molecule.RegionIncidences

/-! # Internal bond labels are the actual local garden labels -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree
variable {V D : Type*} [DecidableEq V] [Fintype D]

theorem internalDartValue_of_mate {E : Type*} (M : Molecule V D) (S : Finset V) (q : D → E)
    (hq : ∀ x : InternalDart M S, q (M.mate x.1) = q x.1) (x : InternalDart M S) :
    internalDartValue M S (fun e => q e.1) x = q x.1 := by
  obtain ⟨⟨e,s⟩,rfl⟩ := (internalBondDartEquiv M S).surjective x
  change internalDartValue M S (fun e => q e.1) (internalBondDart M S (e,s)) =
    q (internalBondDart M S (e,s)).1
  rw [internalDartValue_bondDart]
  cases s
  · rfl
  · exact (hq ⟨e.1,internalBond_inGroup M S e⟩).symm

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}

/-- Only matching of genuinely internal paired leaves is used; no exterior
leaf equation is imposed on a regional decoration. -/
theorem gardenInternal_restrict_mate {E : Type*} (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (x : InternalDart G.molecule U) :
    Mole.restrictLabels G κ (G.molecule.mate x.1) = Mole.restrictLabels G κ x.1 := by
  rcases x with ⟨x,hx⟩
  rcases x with ⟨c,s⟩ | ℓ
  · cases s <;> rfl
  · exact (hp ℓ.1 ⟨ℓ.2.1,ℓ.2.2.1,ℓ.2.2.2,hx⟩).symm

/-- Every label in the M9 internal-bond carrier is a literal source node
momentum, independently of the chosen outgoing representative. -/
theorem gardenInternalDartValue {E : Type*} (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (x : InternalDart G.molecule U) :
    internalDartValue G.molecule U (fun e => Mole.restrictLabels G κ e.1) x =
      κ (Mole.dartNode G x.1) :=
  internalDartValue_of_mate G.molecule U (Mole.restrictLabels G κ) (gardenInternal_restrict_mate κ hp) x

open Classical in
theorem gardenInternalFlow_eq {E : Type*} [AddCommGroup E] (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : GBranch G.tree) :
    flow G.molecule U (fun e => Mole.restrictLabels G κ e.1) v =
      ∑ x : InternalDart G.molecule U, internalDartCoeff G.molecule v x.1 • κ (Mole.dartNode G x.1) := by
  classical
  rw [← internalDartFlow_eq_flow]
  apply Finset.sum_congr rfl
  intro x _
  rw [gardenInternalDartValue κ hp]

end WaveTurbulence.VineEstS2
