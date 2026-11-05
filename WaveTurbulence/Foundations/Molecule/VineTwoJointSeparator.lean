/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSeparatorLocalization
public import WaveTurbulence.Foundations.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.Molecule.VineChainInteriorConnected
import Mathlib.Tactic

/-! # Localizing an inner group when a shared outer joint is absent -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Removing the second endpoint leaves a chain connected to its first endpoint. -/
theorem chain_erase_last_connected {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : GroupConnected M (S.erase b) := by
  have reach (u : V) (hu : u ∈ S.erase b) : (Mole.induced M (S.erase b)).SameComponent a u := by
    rcases chain_erase_endpoint_reach (z := b) h u hu with ⟨_hne,hp⟩ | ⟨hne,_hp⟩
    · exact hp
    · exact False.elim (hne rfl)
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

/-- A VC remains connected when either specified joint is removed. -/
theorem isVC_erase_joint_connected {M : Molecule V D} {S : Finset V} {a b z : V}
    (h : IsVC M S a b) (hz : z=a ∨ z=b) : GroupConnected M (S.erase z) := by
  obtain ⟨_hB,n,hchain⟩ := h
  rcases hz with hz | hz
  · rw [hz]
    exact chain_erase_first_connected hchain
  · rw [hz]
    exact chain_erase_last_connected hchain

/-- Two groups whose nonjoint atoms are closed cannot be crossed by a
group which misses one shared joint and stays connected after deleting the
other. All closure assumptions are primitive incidence data. -/
theorem two_groups_missing_right_joint_side (M : Molecule V D) (hM : M.IsMolecule)
    (S T A : Finset V) (a b : V) (haS : a ∈ S) (haT : a ∈ T) (hab : a ≠ b)
    (hT : T ⊆ M.atoms) (hint : ∀ v ∈ T,v ≠ a → v ≠ b → M.degIn T v=4)
    (hAU : A ⊆ S ∪ T) (hbA : b ∉ A) (hconn : GroupConnected M (A.erase a)) : A ⊆ S ∨ A ⊆ T := by
  have hAS' : A ⊆ S.erase b ∪ T.erase b := by
    intro u hu
    have hub : u ≠ b := by intro he; exact hbA (he ▸ hu)
    rcases mem_union.mp (hAU hu) with huS | huT
    · exact mem_union_left _ (mem_erase.mpr ⟨hub,huS⟩)
    · exact mem_union_right _ (mem_erase.mpr ⟨hub,huT⟩)
  have hside := connected_erase_subset_side M (S.erase b) (T.erase b) A a
    (mem_erase.mpr ⟨hab,haS⟩) (mem_erase.mpr ⟨hab,haT⟩) hAS' (by
      intro v hv hva u hu huv
      obtain ⟨hvb,hvT⟩ := mem_erase.mp hv
      have huT : u ∈ T := by
        obtain ⟨d,hdv,hdu⟩ := huv
        exact hdu ▸ Mole.full_degree_no_exit M hM (hT hvT) (hint v hvT hva hvb) hdv
      have hub : u ≠ b := (mem_union.mp hu).elim (fun h => (mem_erase.mp h).1) (fun h => (mem_erase.mp h).1)
      exact mem_erase.mpr ⟨hub,huT⟩) hconn
  exact hside.imp (fun h => h.trans (erase_subset _ _)) (fun h => h.trans (erase_subset _ _))

end WaveTurbulence.Vine
