/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproBlockGeo
import Mathlib.Tactic

/-!
# SUBPRO (S4): the darts at a hinge atom are the external darts of its unit
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1 WaveTurbulence.Mole

variable {R : ℕ} {G : Garden (2 * R)}

/-- A dart of `M_sb` at the crown of a unit is the lift of an external dart of the unit at one of its joints. -/
theorem crown_dart (hM : G.molecule.IsMolecule) (σ : Prescription G) {u : CLBlock G} (hu : u ∈ unitBlocks G σ)
    {v : GBranch (stSt G σ).G.tree} (hv : (stSt G σ).M.ob v = u.upper) {x : GardenDart (stSt G σ).G}
    (hx : (stSt G σ).G.molecule.atom x = v) :
    G.molecule.atom ((stSt G σ).M.od x) ∈ u.atoms ∧ ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od x) ∧
      (G.molecule.atom ((stSt G σ).M.od x) = u.upper ∨ G.molecule.atom ((stSt G σ).M.od x) = u.lower) := by
  have hrep : repC (stSt G σ).cls (G.molecule.atom ((stSt G σ).M.od x)) = u.upper := by
    rw [← (stSt G σ).M.ob_atom, hx, hv]
  have hcls : (stSt G σ).cls (G.molecule.atom ((stSt G σ).M.od x)) = some u.upper := by
    unfold repC at hrep
    rcases hc : (stSt G σ).cls (G.molecule.atom ((stSt G σ).M.od x)) with _ | a
    · rw [hc] at hrep
      have h1 : (stSt G σ).cls u.upper = some u.upper := stSt_cls_mem hM σ hu u.isBlock.2.1
      simp only [Option.getD_none] at hrep
      rw [hrep] at hc
      rw [hc] at h1; cases h1
    · rw [hc] at hrep; simp only [Option.getD_some] at hrep; rw [hrep]
  have hmem : G.molecule.atom ((stSt G σ).M.od x) ∈ u.atoms := mem_of_cls_eq hM σ hu hcls
  have hext : ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od x) := by
    intro hin
    have := ((stSt G σ).M.od_range ((stSt G σ).M.od x)).mp ⟨x, rfl⟩
    exact this ⟨u.upper, hcls, stSt_cls_mem hM σ hu hin.2⟩
  refine ⟨hmem, hext, ?_⟩
  by_contra hne
  push Not at hne
  exact hext (block_interior_ext hM u.isBlock hmem hne.1 hne.2 rfl)

/-- The joint-pair dichotomy: the out/in darts at a hinge either are the chosen proper pair or avoid it; in both cases
their lifts sit at one common joint of the unit. -/
theorem common_joint (hM : G.molecule.IsMolecule) (σ : Prescription G) {u : CLBlock G} (hu : u ∈ unitBlocks G σ)
    {v : GBranch (stSt G σ).G.tree} (hv : (stSt G σ).M.ob v = u.upper)
    {oc ic : GardenDart (stSt G σ).G} {jc : GBranch G.tree} (hjc : jc = u.upper ∨ jc = u.lower)
    (hoc : G.molecule.atom ((stSt G σ).M.od oc) = jc) (hic : G.molecule.atom ((stSt G σ).M.od ic) = jc)
    (hoc_ext : ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od oc))
    (hic_ext : ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od ic))
    (hoc_out : (stSt G σ).G.molecule.out oc = true) (hic_out : (stSt G σ).G.molecule.out ic = false)
    {ao ai : GardenDart (stSt G σ).G} (hao : (stSt G σ).G.molecule.atom ao = v)
    (hai : (stSt G σ).G.molecule.atom ai = v)
    (hao_out : (stSt G σ).G.molecule.out ao = true) (hai_out : (stSt G σ).G.molecule.out ai = false)
    (hxor : (ao = oc ∧ ai = ic) ∨ (ao ≠ oc ∧ ai ≠ ic)) :
    ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt G σ).M.od ao) = j ∧
      G.molecule.atom ((stSt G σ).M.od ai) = j := by
  classical
  rcases hxor with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · exact ⟨jc, hjc, hoc, hic⟩
  · obtain ⟨hao1, hao2, hao3⟩ := crown_dart hM σ hu hv hao
    obtain ⟨hai1, hai2, hai3⟩ := crown_dart hM σ hu hv hai
    -- the external darts at `jc` are exactly the lifts of the chosen pair
    have hblock : ∃ j', G.molecule.IsBlock u.atoms jc j' := by
      rcases hjc with h | h
      · exact ⟨u.lower, h ▸ u.isBlock⟩
      · exact ⟨u.upper, h ▸ block_swap_joints _ u.isBlock⟩
    have hcard := joint_ext_card hM hblock.choose_spec
    set E := (G.molecule.dartsAt jc).filter (fun d => ¬ G.molecule.InGroup u.atoms d) with hE
    have hoE : (stSt G σ).M.od oc ∈ E := by simp [hE, Molecule.dartsAt, hoc, hoc_ext]
    have hiE : (stSt G σ).M.od ic ∈ E := by simp [hE, Molecule.dartsAt, hic, hic_ext]
    have hne : (stSt G σ).M.od oc ≠ (stSt G σ).M.od ic := by
      intro h
      have := congrArg (G.molecule.out) h
      rw [(stSt G σ).M.od_out, (stSt G σ).M.od_out, hoc_out, hic_out] at this
      cases this
    have hE2 : E = {(stSt G σ).M.od oc, (stSt G σ).M.od ic} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hoE
        · rw [Finset.mem_singleton.mp hd]; exact hiE
      · have : ({(stSt G σ).M.od oc, (stSt G σ).M.od ic} : Finset (GardenDart G)).card = 2 := Finset.card_pair hne
        omega
    -- the joints of the unit are distinct
    have hul : u.upper ≠ u.lower := u.isBlock.2.2.2.1
    have hao' : G.molecule.atom ((stSt G σ).M.od ao) ≠ jc := by
      intro h
      have : (stSt G σ).M.od ao ∈ E := by simp [hE, Molecule.dartsAt, h, hao2]
      rw [hE2] at this
      rcases Finset.mem_insert.mp this with h' | h'
      · exact h1 ((stSt G σ).M.od_inj h')
      · have := (stSt G σ).M.od_inj (Finset.mem_singleton.mp h')
        rw [this] at hao_out; rw [hic_out] at hao_out; cases hao_out
    have hai' : G.molecule.atom ((stSt G σ).M.od ai) ≠ jc := by
      intro h
      have : (stSt G σ).M.od ai ∈ E := by simp [hE, Molecule.dartsAt, h, hai2]
      rw [hE2] at this
      rcases Finset.mem_insert.mp this with h' | h'
      · have := (stSt G σ).M.od_inj h'
        rw [this] at hai_out; rw [hoc_out] at hai_out; cases hai_out
      · exact h2 ((stSt G σ).M.od_inj (Finset.mem_singleton.mp h'))
    rcases hjc with hj | hj
    · refine ⟨u.lower, Or.inr rfl, ?_, ?_⟩
      · rcases hao3 with h | h
        · exact absurd (h.trans hj.symm) hao'
        · exact h
      · rcases hai3 with h | h
        · exact absurd (h.trans hj.symm) hai'
        · exact h
    · refine ⟨u.upper, Or.inl rfl, ?_, ?_⟩
      · rcases hao3 with h | h
        · exact h
        · exact absurd (h.trans hj.symm) hao'
      · rcases hai3 with h | h
        · exact h
        · exact absurd (h.trans hj.symm) hai'

end WaveTurbulence.Subpro
