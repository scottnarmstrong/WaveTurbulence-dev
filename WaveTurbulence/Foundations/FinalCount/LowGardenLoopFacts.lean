/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowIface3
public import WaveTurbulence.Foundations.FinalCount.LowGardenLift
/-! **LOW-GARDEN (session 3): the combinatorics of loop atoms.**  A loop atom of `M` (`SubHypLoop R M`) carries exactly one loop, so
`M.deg v = M.unloop.deg v + 2` (`effDeg_eq_deg`) and `|loopAtoms M| = |loopBonds M|` (`card_loopAtoms_eq`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section facts
variable {V : Type} [DecidableEq V] [Infinite V] {D : Type} [Fintype D] [DecidableEq D] {R : ℕ} {M : Molecule V D}

theorem loopDarts_eq (hS : SubHypLoop R M) {v : V} (hv : v ∈ M.atoms) {y : D} (hy : M.atom y = v)
    (hl : M.atom (M.mate y) = v) {z : D} (hz : M.atom z = v) (hzl : M.atom (M.mate z) = v) :
    z = y ∨ z = M.mate y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw, hwl⟩ := hS.nonloop v hv
  have hb : M.deg v ≤ 4 := deg_le_four M (hS.bounds v hv)
  have h1 : y ≠ M.mate y := (M.mate_ne y).symm
  have h2 : z ≠ M.mate z := (M.mate_ne z).symm
  have h3 : M.mate z ≠ y := fun e => hcon.2 (by rw [← e, M.mate_mate])
  have h4 : M.mate z ≠ M.mate y := fun e => hcon.1 (by have := congrArg M.mate e; rwa [M.mate_mate, M.mate_mate] at this)
  have hwy : w ≠ y := fun e => hwl (by rw [e]; exact hl)
  have hwmy : w ≠ M.mate y := fun e => hwl (by rw [e, M.mate_mate]; exact hy)
  have hwz : w ≠ z := fun e => hwl (by rw [e]; exact hzl)
  have hwmz : w ≠ M.mate z := fun e => hwl (by rw [e, M.mate_mate]; exact hz)
  have hsub : ({y, M.mate y, z, M.mate z, w} : Finset D) ⊆ M.dartsAt v := by
    intro u hu
    rw [mem_dartsAt']
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hc : ({y, M.mate y, z, M.mate z, w} : Finset D).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hwmz.symm
    · simp [h2, hwz.symm]
    · simp [Ne.symm hcon.2, Ne.symm h4, hwmy.symm]
    · simp [h1, Ne.symm hcon.1, hwy.symm, Ne.symm h4, Ne.symm h3]
  have := Finset.card_le_card hsub
  unfold Molecule.deg at hb
  omega

theorem deg_loop_atom (hS : SubHypLoop R M) {v : V} (hv : v ∈ M.atoms) {y : D} (hy : M.atom y = v)
    (hl : M.atom (M.mate y) = v) : M.deg v = M.unloop.deg v + 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := M.dartsAt v) (fun x => M.atom (M.mate x) = v)
  have hloop : (M.dartsAt v).filter (fun x => M.atom (M.mate x) = v) = {y, M.mate y} := by
    ext z
    simp only [Finset.mem_filter, mem_dartsAt', Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hzl⟩; exact loopDarts_eq hS hv hy hl hz hzl
    · rintro (rfl | rfl)
      · exact ⟨hy, hl⟩
      · exact ⟨hl, by rw [M.mate_mate]; exact hy⟩
  have hnl : ((M.dartsAt v).filter (fun x => ¬ M.atom (M.mate x) = v)).card = M.unloop.deg v := by
    unfold Molecule.deg
    symm
    refine Finset.card_bij (fun x _ => x.1) (fun x hx => ?_) (fun a _ b _ e => Subtype.ext e) (fun x hx => ?_)
    · have := (mem_dartsAt' M.unloop v x).1 hx
      exact Finset.mem_filter.2 ⟨(mem_dartsAt' M v x.1).2 this, fun h => x.2 (this.trans h.symm)⟩
    · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      have hx1' := (mem_dartsAt' M v x).1 hx1
      exact ⟨⟨x, fun h => hx2 (by rw [← h]; exact hx1')⟩, (mem_dartsAt' M.unloop v _).2 hx1', rfl⟩
  rw [hloop, Finset.card_pair (M.mate_ne y).symm, hnl] at hsplit
  have e : M.deg v = (M.dartsAt v).card := rfl
  omega

theorem effDeg_eq_deg (hS : SubHypLoop R M) {v : V} (hv : v ∈ M.atoms) : effDeg M v = M.deg v := by
  unfold effDeg
  by_cases hB : v ∈ loopAtoms M
  · obtain ⟨-, z, hz1, hz2⟩ := Finset.mem_filter.1 hB
    rw [if_pos hB, deg_loop_atom hS hv hz1 hz2]
  · rw [if_neg hB, add_zero]
    exact deg_unloop_eq M fun z hz hzl => hB (Finset.mem_filter.2 ⟨hv, z, hz, hzl⟩)

theorem card_loopAtoms_eq (hS : SubHypLoop R M) : (loopAtoms M).card = M.loopBonds.card := by
  symm
  refine Finset.card_bij (fun x _ => M.atom x) (fun x hx => ?_) (fun a ha b hb e => ?_) (fun v hv => ?_)
  · obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨M.atom_mem x, x, rfl, hb2.symm⟩
  · obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    have hbo : M.out b = true := by simpa [Molecule.bonds] using hb1
    have hao : M.out a = true := by simpa [Molecule.bonds] using ha1
    have hv := M.atom_mem a
    rcases loopDarts_eq hS hv rfl ha2.symm (z := b) e.symm (hb2.symm.trans e.symm) with h | h
    · exact h.symm
    · exfalso
      have := M.out_mate a
      rw [← h, hbo, hao] at this
      simp at this
  · obtain ⟨hvA, z, hz1, hz2⟩ := Finset.mem_filter.1 hv
    by_cases ho : M.out z = true
    · exact ⟨z, Finset.mem_filter.2 ⟨by simp [Molecule.bonds, ho], hz1.trans hz2.symm⟩, hz1⟩
    · refine ⟨M.mate z, Finset.mem_filter.2 ⟨?_, ?_⟩, hz2⟩
      · have := M.out_mate z
        have ho' : M.out z = false := by simpa using ho
        simpa [Molecule.bonds, ho'] using this
      · rw [M.mate_mate]; exact (hz1.trans hz2.symm).symm

end facts
end WaveTurbulence.FinalCountAsm
