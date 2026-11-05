/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionInteriorConnected
public import WaveTurbulence.Foundations.Molecule.VineVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineRealizationAdjacency
public import WaveTurbulence.Foundations.Molecule.VineActualPartition
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
import Mathlib.Tactic

/-! # Nonjoint atoms of an actual vine form a connected group -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- TARGET defvine/subsetvc: deleting both joints of an actual vine leaves
a connected nonjoint region (possibly empty for type I). -/
theorem isVine_interior_connected {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (hV : M.IsVine X S a b) : GroupConnected M (S \ {a,b}) := by
  classical
  obtain ⟨hB,⟨R⟩⟩ := isVine_iff_realization.mp hV
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
  have hgi (i : ℕ) (hi : i<n) (hi2 : 2 ≤ i) : g i ∈ S \ {a,b} := by
    apply mem_sdiff.mpr
    refine ⟨hgm i,?_⟩
    have hn : ¬R.f (g i)<2 := by rw [hgl i hi]; omega
    have hh := (realization_index_lt_two_iff R hB (hgm i)).not.mp hn
    simpa only [mem_insert,mem_singleton] using hh
  have hedge (p q : ℕ) (hpq : InteriorAdj (X.expand R.k).bonds p q) :
      (Mole.induced M (S \ {a,b})).Adj (g p) (g q) := by
    have hb := (show EdgeBounded n (X.expand R.k).bonds from expand_endpoints X R.k).adj hpq.2.2
    apply R.subgroup_adj_of_edge sdiff_subset (hgi p hb.1 hpq.1) (hgi q hb.2 hpq.2.1)
    rw [hgl p hb.1,hgl q hb.2]
    exact hpq.2.2
  have lift {p q : ℕ} (hp : Relation.EqvGen (InteriorAdj (X.expand R.k).bonds) p q) :
      (Mole.induced M (S \ {a,b})).SameComponent (g p) (g q) := by
    induction hp with
    | rel u v huv => exact Relation.EqvGen.rel _ _ (hedge u v huv)
    | refl u => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  intro u hu v hv
  obtain ⟨huS,huj⟩ := mem_sdiff.mp hu
  obtain ⟨hvS,hvj⟩ := mem_sdiff.mp hv
  have hul := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f huS)
  have hvl := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hvS)
  have hu2 : 2 ≤ R.f u := by
    have hn : ¬R.f u<2 := by
      intro he
      exact huj (by simpa only [mem_insert,mem_singleton] using (realization_index_lt_two_iff R hB huS).mp he)
    omega
  have hv2 : 2 ≤ R.f v := by
    have hn : ¬R.f v<2 := by
      intro he
      exact hvj (by simpa only [mem_insert,mem_singleton] using (realization_index_lt_two_iff R hB hvS).mp he)
    omega
  have hp := Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (expand_interior_connected X R.k R.length_eq (R.f u) hu2 hul))
    (expand_interior_connected X R.k R.length_eq (R.f v) hv2 hvl)
  have hh := lift hp
  simpa only [hgf u huS,hgf v hvS] using hh

end WaveTurbulence.Vine
