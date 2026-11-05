/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineRealizationAdjacency
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
import Mathlib.Tactic

/-! # Actual vine groups remain connected after removal of any one atom -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- TARGET subsetvc localization ingredient: every actual vine remains
connected after any one atom is removed. This is derived from the unchanged
realization predicate, including arbitrary zero or positive rung insertions. -/
theorem isVine_erase_connected {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (hV : M.IsVine X S a b) (z : V) : GroupConnected M (S.erase z) := by
  classical
  by_cases hz : z ∈ S
  · obtain ⟨hB,⟨R⟩⟩ := isVine_iff_realization.mp hV
    let n := (X.expand R.k).n
    let g : ℕ → V := fun i => if hi : i<n then (R.atomAt ⟨i,hi⟩).1 else a
    have hgm (i : ℕ) : g i ∈ S := by
      dsimp only [g]
      split_ifs with hi
      · exact (R.atomAt ⟨i,hi⟩).2
      · exact hB.2.1
    have hgl (i : ℕ) (hi : i<n) : R.f (g i)=i := by
      dsimp only [g]
      rw [dite_eq_left hi]
      exact R.label_atomAt ⟨i,hi⟩
    have hgf (v : V) (hv : v ∈ S) : g (R.f v)=v := by
      apply R.injOn (hgm _) hv
      exact hgl _ (mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hv))
    have hedge (p q : ℕ) (hpq : AvoidAdj (X.expand R.k).bonds (R.f z) p q) :
        (Mole.induced M (S.erase z)).Adj (g p) (g q) := by
      have hb := (show EdgeBounded n (X.expand R.k).bonds from expand_endpoints X R.k).adj hpq.2.2
      have hpn : g p ≠ z := by
        intro he
        have hh := congrArg R.f he
        rw [hgl p hb.1] at hh
        exact hpq.1 hh
      have hqn : g q ≠ z := by
        intro he
        have hh := congrArg R.f he
        rw [hgl q hb.2] at hh
        exact hpq.2.1 hh
      apply R.subgroup_adj_of_edge (erase_subset z S)
        (mem_erase.mpr ⟨hpn,hgm p⟩) (mem_erase.mpr ⟨hqn,hgm q⟩)
      rw [hgl p hb.1,hgl q hb.2]
      exact hpq.2.2
    have lift {p q : ℕ} (hp : AvoidPath (X.expand R.k).bonds (R.f z) p q) :
        (Mole.induced M (S.erase z)).SameComponent (g p) (g q) := by
      induction hp with
      | rel u v huv => exact Relation.EqvGen.rel _ _ (hedge u v huv)
      | refl u => exact Relation.EqvGen.refl _
      | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    intro u hu v hv
    obtain ⟨huz,huS⟩ := mem_erase.mp hu
    obtain ⟨hvz,hvS⟩ := mem_erase.mp hv
    have hul := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f huS)
    have hvl := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hvS)
    have hp := expand_vertexConnected X R.k R.length_eq (R.f z) (R.f u) (R.f v) hul hvl
      (fun he => huz (R.injOn huS hz he)) (fun he => hvz (R.injOn hvS hz he))
    have hh := lift hp
    simpa only [hgf u huS,hgf v hvS] using hh
  · rw [Finset.erase_eq_self.mpr hz]
    exact isVine_connected hV

end WaveTurbulence.Vine
