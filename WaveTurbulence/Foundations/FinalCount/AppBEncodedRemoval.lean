/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBEncodedRemovalPattern
import Mathlib.Tactic

/-! # A literal realization constructed from an actual incident-bond enumeration -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- This construction encodes existing graph data; it adds no local graph
conditions or quantitative premises. It handles all permitted overlaps of
vertices in a sequential atomic group. -/
noncomputable def appbEncodedRemoval (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms)
    (v0 : M.atoms) {m : ℕ} (e : Fin m ≃ {x // x ∈ appbRemovedBonds M Y}) :
    AppbRealization M (appbEncodedRemovalPattern M Y hY e) := by
  let P := appbEncodedRemovalPattern M Y hY e
  let vertex := fun n => (appbDecodeAtom M v0 n).val
  have hy : P.removed.image vertex = Y := appb_encoded_removed_atoms M Y hY v0 e
  have hlen : P.edges.length = m := appb_encoded_edges_length M Y hY e
  let ee : Fin P.edges.length ≃ {x // x ∈ appbRemovedBonds M (P.removed.image vertex)} :=
    ((finCongr hlen).trans e).trans (Equiv.subtypeEquivRight (fun x => by rw [hy]))
  exact {
    vertex := vertex
    vertex_injective := by
      intro a ha b hb he
      exact appb_decode_atom_injOn M v0 (appb_encoded_vertices_lt M Y hY e a ha)
        (appb_encoded_vertices_lt M Y hY e b hb) (Subtype.ext he)
    vertex_mem := fun a _ => (appbDecodeAtom M v0 a).property
    edge := ee
    endpoints := fun i => by
      change M.ends (e (finCongr hlen i)).val = s(vertex P.edges[i].1,vertex P.edges[i].2)
      have ht : P.edges[i] =
          (appbAtomCode M ⟨M.atom (e (finCongr hlen i)).val,M.atom_mem _⟩,
            appbAtomCode M ⟨M.atom (M.mate (e (finCongr hlen i)).val),M.atom_mem _⟩) := by
        let f := fun j : Fin m =>
          (appbAtomCode M ⟨M.atom (e j).val,M.atom_mem _⟩,
            appbAtomCode M ⟨M.atom (M.mate (e j).val),M.atom_mem _⟩)
        change (List.ofFn f)[i.val] = f (finCongr hlen i)
        rw [List.getElem_ofFn]
        rfl
      rw [ht]
      simp only [vertex,appb_decode_atom_code]
      rfl
  }

end WaveTurbulence.Mole
