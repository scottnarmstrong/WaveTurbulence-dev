/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceResidual
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): residual groups of a splice, for the molecule and for its adjoint

`SpMol N0 N1 cls`: the molecule-level data of a splice (old-name maps on atoms and darts, merge labelling).
`SpMap.toMol` is the splice of the garden molecules; `SpMap.eraseMol` the splice of the adjoints
`eraseBond M e`, `eraseBond M' e'` for corresponding bonds `od e' = e` (an HVC / HV adjoint).
`SpMol.inducedIso`: a group `B` whose classes are controlled (H1-H3) is induced-isomorphic to its residual
image.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {V0 V1 D0 D1 : Type*} [DecidableEq V0] [Fintype D0] [DecidableEq D0]
  [DecidableEq V1] [Fintype D1] [DecidableEq D1]

/-- The molecule-level data of a splice. -/
structure SpMol (N0 : Molecule V0 D0) (N1 : Molecule V1 D1) (cls : V0 → Option V0) where
  ob : V1 → V0
  od : D1 → D0
  pi : V0 → V1
  pi_mem : ∀ v, pi v ∈ N1.atoms
  ob_pi : ∀ v, ob (pi v) = (cls v).getD v
  ob_inj : Function.Injective ob
  od_inj : Function.Injective od
  od_range : ∀ x, (∃ y, od y = x) ↔ ¬ ∃ a, cls (N0.atom x) = some a ∧ cls (N0.atom (N0.mate x)) = some a
  od_mate : ∀ y, od (N1.mate y) = N0.mate (od y)
  od_out : ∀ y, N0.out (od y) = N1.out y
  ob_atom : ∀ y, ob (N1.atom y) = (cls (N0.atom (od y))).getD (N0.atom (od y))

namespace SpMol
variable {N0 : Molecule V0 D0} {N1 : Molecule V1 D1} {cls : V0 → Option V0} (M : SpMol N0 N1 cls)

/-- The induced isomorphism of a residual atomic group. -/
@[expose] noncomputable def inducedIso (B : Finset V0)
    (H1 : ∀ u ∈ B, ∀ v ∈ B, (cls u).getD u = (cls v).getD v → u = v)
    (H2 : ∀ x, N0.InGroup B x → ¬ ∃ a, cls (N0.atom x) = some a ∧ cls (N0.atom (N0.mate x)) = some a)
    (H3 : ∀ y : D1, N1.InGroup (B.image M.pi) y → N0.InGroup B (M.od y)) :
    InducedIso N0 N1 B (B.image M.pi) := by
  classical
  have hex : ∀ x : {x // N0.InGroup B x}, ∃ y, M.od y = x.1 := fun x => (M.od_range x.1).mpr (H2 x.1 x.2)
  have hatom : ∀ (y : D1), N0.atom (M.od y) ∈ B → N1.atom y = M.pi (N0.atom (M.od y)) := by
    intro y hy
    apply M.ob_inj
    rw [M.ob_atom, M.ob_pi]
  have hxB : ∀ x : {x // N0.InGroup B x}, N0.atom (M.od (hex x).choose) ∈ B := by
    intro x; rw [(hex x).choose_spec]; exact x.2.1
  have hxB2 : ∀ x : {x // N0.InGroup B x}, N0.atom (M.od (N1.mate (hex x).choose)) ∈ B := by
    intro x; rw [M.od_mate, (hex x).choose_spec]; exact x.2.2
  have hfwd : ∀ x : {x // N0.InGroup B x}, N1.InGroup (B.image M.pi) (hex x).choose := by
    intro x
    constructor
    · rw [hatom _ (hxB x)]
      exact Finset.mem_image_of_mem _ (hxB x)
    · rw [hatom _ (hxB2 x)]
      exact Finset.mem_image_of_mem _ (hxB2 x)
  refine
    { π := M.pi
      inj := ?_
      img := rfl
      sub := fun z hz => by
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hz
        exact M.pi_mem v
      e :=
        { toFun := fun x => ⟨(hex x).choose, hfwd x⟩
          invFun := fun y => ⟨M.od y.1, H3 y.1 y.2⟩
          left_inv := fun x => Subtype.ext (hex x).choose_spec
          right_inv := fun y => Subtype.ext (M.od_inj (hex ⟨M.od y.1, H3 y.1 y.2⟩).choose_spec) }
      atom_comm := ?_
      mate_comm := ?_
      out_comm := ?_ }
  · intro u hu v hv h
    apply H1 u hu v hv
    rw [← M.ob_pi u, ← M.ob_pi v, h]
  · intro x
    show N1.atom (hex x).choose = M.pi (N0.atom x.1)
    rw [hatom _ (hxB x), (hex x).choose_spec]
  · intro x
    have hm : N0.InGroup B (N0.mate x.1) :=
      ⟨x.2.2, by simpa [N0.mate_mate] using x.2.1⟩
    show (hex ⟨N0.mate x.1, hm⟩).choose = N1.mate (hex x).choose
    apply M.od_inj
    rw [(hex ⟨N0.mate x.1, hm⟩).choose_spec, M.od_mate, (hex x).choose_spec]
  · intro x
    show N1.out (hex x).choose = N0.out x.1
    rw [← M.od_out, (hex x).choose_spec]

end SpMol

variable {w : ℕ} {G0 G : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}

/-- The splice of the garden molecules. -/
@[expose] noncomputable def SpMap.toMol (M : SpMap G0 G cls) (hcls : ClsOK cls) :
    SpMol G0.molecule G.molecule cls where
  ob := M.ob
  od := M.od
  pi := M.pi hcls
  pi_mem := fun _ => Finset.mem_univ _
  ob_pi := M.ob_pi hcls
  ob_inj := M.ob_inj
  od_inj := M.od_inj
  od_range := M.od_range
  od_mate := M.od_mate
  od_out := M.od_out
  ob_atom := M.ob_atom

/-- The splice of the adjoints `eraseBond M e`, `eraseBond M' e'` of corresponding bonds (`od e' = e`). -/
@[expose] noncomputable def SpMap.eraseMol (M : SpMap G0 G cls) (hcls : ClsOK cls) (e' : GardenDart G) :
    SpMol (Mole.eraseBond G0.molecule (M.od e')) (Mole.eraseBond G.molecule e') cls where
  ob := M.ob
  od := fun y => ⟨M.od y.1, fun h => y.2.1 (M.od_inj h), fun h => y.2.2 (M.od_inj (h.trans (M.od_mate e').symm))⟩
  pi := M.pi hcls
  pi_mem := fun _ => Finset.mem_univ _
  ob_pi := M.ob_pi hcls
  ob_inj := M.ob_inj
  od_inj := fun a b h => Subtype.ext (M.od_inj (congrArg Subtype.val h))
  od_range := by
    intro x
    constructor
    · rintro ⟨y, hy⟩
      have := (M.od_range x.1).mp ⟨y.1, congrArg Subtype.val hy⟩
      exact this
    · intro hx
      obtain ⟨y, hy⟩ := (M.od_range x.1).mpr hx
      refine ⟨⟨y, fun h => x.2.1 (by rw [← hy, h]), fun h => x.2.2 (by rw [← hy, h, M.od_mate])⟩, Subtype.ext hy⟩
  od_mate := fun y => Subtype.ext (M.od_mate y.1)
  od_out := fun y => M.od_out y.1
  ob_atom := fun y => M.ob_atom y.1

end WaveTurbulence.RedSplice
