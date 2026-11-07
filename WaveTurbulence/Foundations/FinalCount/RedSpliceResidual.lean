/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceInduced
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHinge
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): residual atomic groups of a splice are induced-isomorphic to the original ones

Let `B` be an atomic group of `G0` (e.g. an ingredient vine of a group of `𝒞` that was not spliced) and
let some spliced classes meet `B`.  Its residual group in the spliced garden is the image `π''B` under the
representative map `π v = ` (the atom of `G` whose old name is `repC v`).  If
* (H1) distinct atoms of `B` have distinct representatives,
* (H2) no dart of `B` is internal to a merged class,
* (H3) every dart of `G` between two atoms of `π''B` comes from a dart of `B` (no new bonds),
then `B` and `π''B` are isomorphic induced subgraphs, so blocks and vines transport (`InducedIso`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {w : ℕ} {G0 G : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}

/-- The representative of an old atom in the spliced garden. -/
noncomputable def SpMap.pi (M : SpMap G0 G cls) (hcls : ClsOK cls) (v : GBranch G0.tree) : GBranch G.tree :=
  (M.repC_mem_range hcls v).choose

theorem SpMap.ob_pi (M : SpMap G0 G cls) (hcls : ClsOK cls) (v : GBranch G0.tree) :
    M.ob (M.pi hcls v) = repC cls v := (M.repC_mem_range hcls v).choose_spec

/-- The induced isomorphism of a residual atomic group. -/
noncomputable def SpMap.inducedIso (M : SpMap G0 G cls) (hcls : ClsOK cls) (B : Finset (GBranch G0.tree))
    (H1 : ∀ u ∈ B, ∀ v ∈ B, repC cls u = repC cls v → u = v)
    (H2 : ∀ x, G0.molecule.InGroup B x → ¬ ∃ a, cls (G0.molecule.atom x) = some a ∧
      cls (G0.molecule.atom (G0.molecule.mate x)) = some a)
    (H3 : ∀ y : GardenDart G, G.molecule.InGroup (B.image (M.pi hcls)) y → G0.molecule.InGroup B (M.od y)) :
    InducedIso G0.molecule G.molecule B (B.image (M.pi hcls)) := by
  classical
  have hex : ∀ x : {x // G0.molecule.InGroup B x}, ∃ y, M.od y = x.1 := fun x => (M.od_range x.1).mpr (H2 x.1 x.2)
  have hatom : ∀ (y : GardenDart G), G0.molecule.atom (M.od y) ∈ B →
      G.molecule.atom y = M.pi hcls (G0.molecule.atom (M.od y)) := by
    intro y hy
    apply M.ob_inj
    rw [M.ob_atom, M.ob_pi]
  have hxB : ∀ x : {x // G0.molecule.InGroup B x}, G0.molecule.atom (M.od (hex x).choose) ∈ B := by
    intro x; rw [(hex x).choose_spec]; exact x.2.1
  have hxB2 : ∀ x : {x // G0.molecule.InGroup B x},
      G0.molecule.atom (M.od (G.molecule.mate (hex x).choose)) ∈ B := by
    intro x; rw [M.od_mate, (hex x).choose_spec]; exact x.2.2
  have hfwd : ∀ x : {x // G0.molecule.InGroup B x}, G.molecule.InGroup (B.image (M.pi hcls)) (hex x).choose := by
    intro x
    constructor
    · rw [hatom _ (hxB x)]
      exact Finset.mem_image_of_mem _ (hxB x)
    · rw [hatom _ (hxB2 x)]
      exact Finset.mem_image_of_mem _ (hxB2 x)
  refine
    { π := M.pi hcls
      inj := ?_
      img := rfl
      sub := fun _ _ => Finset.mem_univ _
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
    rw [← M.ob_pi hcls u, ← M.ob_pi hcls v, h]
  · intro x
    show G.molecule.atom (hex x).choose = M.pi hcls (G0.molecule.atom x.1)
    rw [hatom _ (hxB x), (hex x).choose_spec]
  · intro x
    have hm : G0.molecule.InGroup B (G0.molecule.mate x.1) :=
      ⟨x.2.2, by simpa [G0.molecule.mate_mate] using x.2.1⟩
    show (hex ⟨G0.molecule.mate x.1, hm⟩).choose = G.molecule.mate (hex x).choose
    apply M.od_inj
    rw [(hex ⟨G0.molecule.mate x.1, hm⟩).choose_spec, M.od_mate, (hex x).choose_spec]
  · intro x
    show G.molecule.out (hex x).choose = G0.molecule.out x.1
    rw [← M.od_out, (hex x).choose_spec]

end WaveTurbulence.RedSplice
