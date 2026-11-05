/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockRemovalDegrees
public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
import Mathlib.Tactic

/-! # Ambient deficit is even in each actual residual component
TARGET `cnblock`: handshaking applied to the literal residual half-edges,
combined with deletion of one incoming and one outgoing incidence per joint.
-/

public section
namespace WaveTurbulence.Mole
open Finset TTree
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem componentSet_closed (v : V) {u z : V} (hu : u ∈ Degen.componentSet M v)
    (hz : M.Adj u z) : z ∈ Degen.componentSet M v := by
  obtain ⟨x,hx,hz'⟩ := hz
  have hp := (Degen.mem_componentSet M v u).mp hu
  apply (Degen.mem_componentSet M v z).mpr
  exact ⟨hz' ▸ M.atom_mem (M.mate x),sameComponent_trans M hp.2
    (sameComponent_of_adj M ⟨x,hx,hz'⟩)⟩

theorem componentSets_closed {C : Finset V} (hC : C ∈ Degen.componentSets M)
    {u z : V} (hu : u ∈ C) (hz : M.Adj u z) : z ∈ C := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hC
  exact componentSet_closed M v hu hz

theorem componentSets_subset_atoms {C : Finset V} (hC : C ∈ Degen.componentSets M) : C ⊆ M.atoms := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hC
  exact fun _ hu => ((Degen.mem_componentSet M v _).mp hu).1

theorem componentSets_nonempty {C : Finset V} (hC : C ∈ Degen.componentSets M) : C.Nonempty := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hC
  exact ⟨v,(Degen.mem_componentSet M v v).mpr ⟨hv,sameComponent_refl M v⟩⟩

theorem componentSets_pairwise_disjoint :
    Set.PairwiseDisjoint (Degen.componentSets M : Set (Finset V)) (fun C => C) := by
  intro C hC E hE hne
  apply Finset.disjoint_left.mpr
  intro z hzC hzE
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hC
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hE
  have hu' := ((Degen.mem_componentSet M u z).mp hzC).2
  have hv' := ((Degen.mem_componentSet M v z).mp hzE).2
  exact hne ((Degen.componentSet_eq_iff M hu).mpr
    (sameComponent_trans M hu' (sameComponent_symm M hv')))

theorem degIn_component_eq_deg {C : Finset V} (hC : C ∈ Degen.componentSets M)
    {v : V} (hv : v ∈ C) : M.degIn C v = M.deg v := by
  classical
  apply congrArg Finset.card
  apply Finset.filter_eq_self.mpr
  intro x hx
  have hxv := (mem_dartsAt M v x).mp hx
  refine ⟨hxv.symm ▸ hv,?_⟩
  exact componentSets_closed M hC hv ⟨x,hxv,rfl⟩

theorem even_component_degree_sum {C : Finset V} (hC : C ∈ Degen.componentSets M) :
    Even (∑ v ∈ C, M.deg v) := by
  have he : (∑ v ∈ C, M.deg v) = ∑ v ∈ C, M.degIn C v := by
    exact sum_congr rfl (fun v hv => (degIn_component_eq_deg M hC hv).symm)
  rw [he,sum_degreesIn_eq_two_mul_groupBonds]
  exact ⟨(M.groupBonds C).card,by omega⟩

variable {w : ℕ} (G : Garden w) (F : Finset (GardenBlockSegment G))

/-- Every nonzero component deficit therefore consumes at least two units
of the original garden's degree budget. -/
theorem even_residual_component_deficit
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    {C : Finset (GBranch G.tree)} (hC : C ∈ Degen.componentSets (removeBlockFamily G F)) :
    Even (∑ v ∈ C, (4-G.molecule.deg v)) := by
  have hm : Nat.ModEq 2 (∑ v ∈ C, (4-G.molecule.deg v))
      (∑ v ∈ C, (removeBlockFamily G F).deg v) := by
    apply Nat.ModEq.sum
    intro v hv
    have ha := componentSets_subset_atoms (removeBlockFamily G F) hC hv
    exact block_removal_deficit_modEq G F hdis v (mem_sdiff.mp ha).2
  have he := even_component_degree_sum (removeBlockFamily G F) hC
  apply Nat.even_iff.mpr
  exact (show (∑ v ∈ C, (4-G.molecule.deg v)) % 2 =
    (∑ v ∈ C, (removeBlockFamily G F).deg v) % 2 from hm).trans (Nat.even_iff.mp he)

end WaveTurbulence.Mole
