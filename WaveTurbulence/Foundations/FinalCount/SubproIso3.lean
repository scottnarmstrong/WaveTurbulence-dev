/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceTriple
public import WaveTurbulence.Foundations.FinalCount.RedSpliceResidual
import Mathlib.Tactic

/-!
# SUBPRO (S4): induced isomorphisms between unmerged parts of a splice

For an `SpMap G0 G cls` (`G` is `G0` with the blocks labelled by `cls` collapsed), an atom set `B` of `G0` whose atoms
are all unmerged (`cls = none`) is induced-isomorphic to its image in `G` (`exists_iso_up`, via `pi`), and an atom set
`B'` of `G` none of whose atoms is a crown (`cls (ob c) = none`) is induced-isomorphic to its image in `G0`
(`exists_iso_down`, via `ob`).  Both isomorphisms are compatible with the dart map `od`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {w : ℕ} {G0 G : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}

theorem repC_of_none {v : GBranch G0.tree} (h : cls v = none) : repC cls v = v := by simp [repC, h]

/-- Up: an unmerged atom set of `G0` is induced-isomorphic to its image in `G`. -/
theorem exists_iso_up (M : SpMap G0 G cls) (hcls : ClsOK cls) (B : Finset (GBranch G0.tree))
    (hB : ∀ v ∈ B, cls v = none) :
    ∃ I : InducedIso G0.molecule G.molecule B (B.image (M.pi hcls)),
      I.π = M.pi hcls ∧ ∀ x, M.od (I.e x).1 = x.1 := by
  classical
  have hex : ∀ x : {x // G0.molecule.InGroup B x}, ∃ y, M.od y = x.1 := fun x =>
    (M.od_range x.1).mpr (by
      rintro ⟨a, ha, -⟩
      rw [hB _ x.2.1] at ha; cases ha)
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
  have H3 : ∀ y : GardenDart G, G.molecule.InGroup (B.image (M.pi hcls)) y → G0.molecule.InGroup B (M.od y) := by
    intro y hy
    have key : ∀ t : GBranch G.tree, t ∈ B.image (M.pi hcls) → ∀ u : GBranch G0.tree, M.ob t = repC cls u → u ∈ B := by
      intro t ht u hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
      rw [M.ob_pi, repC_of_none (hB b hb)] at hu
      have := (repC_eq_iff_of_unmerged hcls (hB b hb)).mp hu.symm
      exact this ▸ hb
    refine ⟨key _ hy.1 _ (M.ob_atom y), ?_⟩
    rw [← M.od_mate]
    exact key _ hy.2 _ (M.ob_atom _)
  refine ⟨
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
      out_comm := ?_ }, rfl, fun x => (hex x).choose_spec⟩
  · intro u hu v hv h
    have := congrArg M.ob h
    rw [M.ob_pi, M.ob_pi, repC_of_none (hB u hu), repC_of_none (hB v hv)] at this
    exact this
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

/-- Down: a crown-free atom set of `G` is induced-isomorphic to its image in `G0`. -/
theorem exists_iso_down (M : SpMap G0 G cls) (hcls : ClsOK cls) (B' : Finset (GBranch G.tree))
    (hB : ∀ c ∈ B', cls (M.ob c) = none) :
    ∃ I : InducedIso G.molecule G0.molecule B' (B'.image M.ob),
      I.π = M.ob ∧ ∀ x, M.od x.1 = (I.e x).1 := by
  classical
  have hatom : ∀ y : GardenDart G, G.molecule.atom y ∈ B' → G0.molecule.atom (M.od y) = M.ob (G.molecule.atom y) := by
    intro y hy
    have h1 := M.ob_atom y
    exact ((repC_eq_iff_of_unmerged hcls (hB _ hy)).mp h1.symm)
  have hfwd : ∀ y : {y : GardenDart G // G.molecule.InGroup B' y}, G0.molecule.InGroup (B'.image M.ob) (M.od y.1) := by
    intro y
    refine ⟨?_, ?_⟩
    · rw [hatom _ y.2.1]; exact Finset.mem_image_of_mem _ y.2.1
    · rw [← M.od_mate, hatom _ y.2.2]; exact Finset.mem_image_of_mem _ y.2.2
  have hbwd : ∀ x : {x : GardenDart G0 // G0.molecule.InGroup (B'.image M.ob) x}, ∃ y : GardenDart G,
      M.od y = x.1 ∧ G.molecule.InGroup B' y := by
    intro x
    have hn : ∀ t ∈ B'.image M.ob, cls t = none := by
      intro t ht
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
      exact hB c hc
    obtain ⟨y, hy⟩ := (M.od_range x.1).mpr (by
      rintro ⟨a, ha, -⟩
      rw [hn _ x.2.1] at ha; cases ha)
    have key : ∀ u, u ∈ B'.image M.ob → ∀ c : GBranch G.tree, M.ob c = repC cls u → c ∈ B' := by
      intro u hu c hc
      obtain ⟨c0, hc0, rfl⟩ := Finset.mem_image.mp hu
      rw [repC_of_none (hB c0 hc0)] at hc
      exact (M.ob_inj hc) ▸ hc0
    refine ⟨y, hy, key _ (hy ▸ x.2.1) _ (M.ob_atom y), ?_⟩
    have := key _ (hy ▸ x.2.2 : G0.molecule.atom (G0.molecule.mate (M.od y)) ∈ B'.image M.ob) (G.molecule.atom (G.molecule.mate y))
      (by rw [M.ob_atom, M.od_mate])
    exact this
  refine ⟨
    { π := M.ob
      inj := fun u _ v _ h => M.ob_inj h
      img := rfl
      sub := fun _ _ => Finset.mem_univ _
      e :=
        { toFun := fun y => ⟨M.od y.1, hfwd y⟩
          invFun := fun x => ⟨(hbwd x).choose, (hbwd x).choose_spec.2⟩
          left_inv := fun y => Subtype.ext (M.od_inj (hbwd ⟨M.od y.1, hfwd y⟩).choose_spec.1)
          right_inv := fun x => Subtype.ext (hbwd x).choose_spec.1 }
      atom_comm := ?_
      mate_comm := ?_
      out_comm := ?_ }, rfl, fun x => rfl⟩
  · intro y
    exact hatom y.1 y.2.1
  · intro y
    exact Subtype.ext_iff.mp rfl ▸ (M.od_mate y.1).symm ▸ rfl
  · intro y
    exact M.od_out y.1

end WaveTurbulence.RedSplice
