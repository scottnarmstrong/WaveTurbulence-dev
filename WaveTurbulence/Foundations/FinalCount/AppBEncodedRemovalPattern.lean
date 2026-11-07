/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBAtomCodes
import Mathlib.Tactic

/-! # An exact finite table for an enumerated actual atom removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbEncodedRemovalPattern (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms)
    {m : ℕ} (e : Fin m ≃ {x // x ∈ appbRemovedBonds M Y}) : AppbPattern where
  removed := Y.attach.image (fun v => appbAtomCode M ⟨v.val,hY v.property⟩)
  edges := List.ofFn (fun i : Fin m =>
    (appbAtomCode M ⟨M.atom (e i).val,M.atom_mem _⟩,
      appbAtomCode M ⟨M.atom (M.mate (e i).val),M.atom_mem _⟩))

theorem appb_encoded_edges_length (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms)
    {m : ℕ} (e : Fin m ≃ {x // x ∈ appbRemovedBonds M Y}) :
    (appbEncodedRemovalPattern M Y hY e).edges.length = m := by
  simp only [appbEncodedRemovalPattern,List.length_ofFn]

theorem appb_encoded_vertices_lt (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms)
    {m : ℕ} (e : Fin m ≃ {x // x ∈ appbRemovedBonds M Y}) :
    ∀ a ∈ (appbEncodedRemovalPattern M Y hY e).vertices,a < Fintype.card M.atoms := by
  intro a ha
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨v,hv,rfl⟩ := mem_image.mp ha
    exact appb_atom_code_lt M _
  · obtain ⟨p,hp,ha⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp ha)
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact appb_atom_code_lt M _
    · exact appb_atom_code_lt M _

theorem appb_encoded_removed_atoms (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms)
    (v0 : M.atoms) {m : ℕ} (e : Fin m ≃ {x // x ∈ appbRemovedBonds M Y}) :
    (appbEncodedRemovalPattern M Y hY e).removed.image (fun n => (appbDecodeAtom M v0 n).val) = Y := by
  ext v
  constructor
  · intro hv
    obtain ⟨a,ha,he⟩ := mem_image.mp hv
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ha
    have hd := congrArg Subtype.val (appb_decode_atom_code M v0 ⟨u.val,hY u.property⟩)
    rw [hd] at he
    exact he ▸ u.property
  · intro hv
    refine mem_image.mpr ⟨appbAtomCode M ⟨v,hY hv⟩,?_,?_⟩
    · exact mem_image.mpr ⟨⟨v,hv⟩,mem_attach _ _,rfl⟩
    · exact congrArg Subtype.val (appb_decode_atom_code M v0 ⟨v,hY hv⟩)

end WaveTurbulence.Mole
