/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineActualSingleBackbones
public import WaveTurbulence.Foundations.Molecule.VineFoldAllocationCover
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
import Mathlib.Tactic

/-! # Every noncentral atom reaches a joint along single bonds after expansion -/

public section
namespace WaveTurbulence.Vine

/-- Each slot starts on the core single-bond backbone. In particular,
no slot starts at a normal vine's isolated doubled-edge center. -/
theorem template_slot_starts_backbone (X : VineType) : ∀ s ∈ X.template.slots,
    OnSingleBackbone X s.1.1 ∧ OnSingleBackbone X s.2.1 := by
  cases X <;> decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every atom except a possible normal center belongs to the expanded
single-bond backbone. Fresh atoms reach the appropriate old starting port
through their actual rail prefix. The four-atom type-II case is included. -/
theorem VineRealization.single_backbone_to_atom {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hM : M.IsMolecule)
    (v : V) (hv : v ∈ S) (hgood : OnSingleBackbone X (R.f v)) :
    Relation.EqvGen (SingleGroupAdj M S)
      (R.coreAtom ⟨0,by cases X <;> decide⟩).1 v := by
  by_cases hold : R.f v<X.template.n
  · let i : Fin X.template.n := ⟨R.f v,hold⟩
    have he : (R.coreAtom i).1=v := by
      apply R.injOn (R.coreAtom i).2 hv
      exact R.label_coreAtom i
    simpa only [he] using R.core_single_to_zero hM i hgood
  · have hbound := Finset.mem_range.mp (R.image_eq ▸ Finset.mem_image_of_mem R.f hv)
    obtain ⟨pre,post,s,k,hloc,hlo,hhi⟩ := fold_fresh_allocation X.template
      (X.template.slots.zip R.k) (R.f v) (by omega) hbound
    obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
    let F := R.slot_rail_frame pre post s k hloc Q hports hlabels
    have hsk : (s,k) ∈ X.template.slots.zip R.k := by
      rw [hloc]
      exact List.mem_append_right _ List.mem_cons_self
    have hs := (List.of_mem_zip hsk).1
    have hb := template_slot_endpoints X s hs
    have hg := template_slot_starts_backbone X s hs
    obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
      (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hv hlo hhi
    rcases he with rfl | rfl
    · have hu : (R.coreAtom ⟨s.1.1,hb.1⟩).1=Q.u 0 := by
        apply R.injOn (R.coreAtom ⟨s.1.1,hb.1⟩).2 (hmem 0).1
        rw [R.label_coreAtom,hports.1]
      have hp := R.core_single_to_zero hM ⟨s.1.1,hb.1⟩ hg.1
      rw [hu] at hp
      exact Relation.EqvGen.trans _ _ _ hp (F.upper_single_prefix hM S hmem i hin)
    · have hu : (R.coreAtom ⟨s.2.1,hb.2.2.1⟩).1=Q.v 0 := by
        apply R.injOn (R.coreAtom ⟨s.2.1,hb.2.2.1⟩).2 (hmem 0).2
        rw [R.label_coreAtom,hports.2.1]
      have hp := R.core_single_to_zero hM ⟨s.2.1,hb.2.2.1⟩ hg.2
      rw [hu] at hp
      exact Relation.EqvGen.trans _ _ _ hp (F.lower_single_prefix hM S hmem i hin)

end WaveTurbulence.Vine
