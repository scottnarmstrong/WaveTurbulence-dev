/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotSinglePaths
public import WaveTurbulence.Foundations.Molecule.VineSingleBackbones
import Mathlib.Tactic

/-! # Single core edges lift to actual single-bond paths after expansion -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Each literal slot has its actual rung count and location in the
source instruction list. -/
theorem VineRealization.slot_location {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (hs : s ∈ X.template.slots) :
    ∃ k pre post,X.template.slots.zip R.k=pre++(s,k)::post := by
  have hm : (X.template.slots.zip R.k).map Prod.fst=X.template.slots :=
    List.map_fst_zip R.length_eq.symm.le
  have hsm : s ∈ (X.template.slots.zip R.k).map Prod.fst := hm.symm ▸ hs
  obtain ⟨sk,hsk,he⟩ := List.mem_map.mp hsm
  obtain ⟨pre,post,hloc⟩ := List.append_of_mem hsk
  refine ⟨sk.2,pre,post,?_⟩
  have hpair : sk=(s,sk.2) := Prod.ext he rfl
  simpa only [← hpair] using hloc

/-- Each single base edge lifts to a path of single bonds in the actual
expanded vine. A marked edge is replaced by its complete source rail. -/
theorem VineRealization.core_single_edge_path {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hM : M.IsMolecule)
    (i j : Fin X.template.n) (he : (i.1,j.1) ∈ singleBonds X.template.bonds) :
    Relation.EqvGen (SingleGroupAdj M S) (R.coreAtom i).1 (R.coreAtom j).1 := by
  have hm := (List.mem_filter.mp he).1
  have hc : X.template.bonds.count (i.1,j.1)+X.template.bonds.count (j.1,i.1)=1 :=
    of_decide_eq_true (List.mem_filter.mp he).2
  have hij : i ≠ j := by
    intro heq
    subst j
    have hz := template_no_loop_counts X i
    omega
  by_cases hslot : ∃ s ∈ X.template.slots,(i.1,j.1)=s.1 ∨ (i.1,j.1)=s.2
  · obtain ⟨s,hs,heq⟩ := hslot
    obtain ⟨k,pre,post,hloc⟩ := R.slot_location s hs
    obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
    have hp := R.slot_single_paths hM pre post s k hloc Q hmem hports hlabels
    rcases heq with heq | heq
    · have hu : (R.coreAtom i).1=Q.u 0 := by
        apply R.injOn (R.coreAtom i).2 (hmem 0).1
        rw [R.label_coreAtom,hports.1]
        exact congrArg Prod.fst heq
      have hv : (R.coreAtom j).1=Q.u (k+1) := by
        apply R.injOn (R.coreAtom j).2 (hmem (k+1)).1
        rw [R.label_coreAtom,hports.2.2.1]
        exact congrArg Prod.snd heq
      simpa only [← hu,← hv] using hp.1
    · have hu : (R.coreAtom i).1=Q.v 0 := by
        apply R.injOn (R.coreAtom i).2 (hmem 0).2
        rw [R.label_coreAtom,hports.2.1]
        exact congrArg Prod.fst heq
      have hv : (R.coreAtom j).1=Q.v (k+1) := by
        apply R.injOn (R.coreAtom j).2 (hmem (k+1)).2
        rw [R.label_coreAtom,hports.2.2.2]
        exact congrArg Prod.snd heq
      simpa only [← hu,← hv] using hp.2
  · apply Relation.EqvGen.rel
    apply R.single_core_untouched i j hij hc hm
    intro s hs
    exact ⟨fun hh => hslot ⟨s,hs,Or.inl hh⟩,fun hh => hslot ⟨s,hs,Or.inr hh⟩⟩

end WaveTurbulence.Vine
