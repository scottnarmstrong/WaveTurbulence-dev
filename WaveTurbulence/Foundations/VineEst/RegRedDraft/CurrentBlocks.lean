/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockGeometricDichotomy
public import WaveTurbulence.Foundations.Molecule.MoleculeDegreeCompat

/-! # CLCN C-1: current connected blocks supply the legacy geometric proof inputs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D]

omit [DecidableEq V] [Fintype D] in
/-- The exact current B2 connectedness has MOLE's intrinsic path meaning. -/
theorem groupConnected_iff_mole (M : Molecule V D) (S : Finset V) (hS : S.Nonempty) :
    M.GroupConnected S ↔ Mole.GroupConnected M S := by
  have hrel : (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) =
      (Mole.induced M S).Adj := by
    funext a b
    unfold Molecule.Adj
    apply propext
    constructor
    · rintro ⟨x,hx,ha,hb⟩
      exact ⟨⟨x,hx⟩,ha,hb⟩
    · rintro ⟨⟨x,hx⟩,ha,hb⟩
      exact ⟨x,hx,ha,hb⟩
  unfold Molecule.GroupConnected Mole.GroupConnected Molecule.SameComponent
  rw [hrel]
  exact ⟨fun h => ⟨hS,h⟩,fun h => h.2⟩

theorem isBlock_iff_degree_connected (M : Molecule V D) (S : Finset V) (a b : V) :
    M.IsBlock S a b ↔ M.IsBlockDeg S a b ∧ Mole.GroupConnected M S := by
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,hc⟩
    exact ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩,(groupConnected_iff_mole M S ⟨a,h2⟩).mp hc⟩
  · rintro ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩,hc⟩
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,(groupConnected_iff_mole M S ⟨a,h2⟩).mpr hc⟩

/-- CLCN's actual geometry is produced from current B2 premises, without an
extra supplied realization or connectedness hypothesis. -/
theorem cl_geometric_data {w : ℕ} (G : Garden w) {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hB : G.molecule.IsBlock S a b)
    (hCL : Mole.CLParentPattern G S a b) : Nonempty (Mole.CLGeometricData G S a b) :=
  Mole.cl_geometric_data G hB hCL

end WaveTurbulence.RegRed
