/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVIIRedProtectedPaths
public import WaveTurbulence.Foundations.Molecule.VineVIIGreenProtectedPaths
public import WaveTurbulence.Foundations.Molecule.VineVIIProtectedCoreLabels
public import WaveTurbulence.Foundations.Molecule.VineCoreSinglePaths
import Mathlib.Tactic

/-! # Each retained VII core edge lifts to a path outside the removed side -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every protected old VII edge lifts through the actual red or green
rail or remains an untouched single bond. Cyan edges and the side joint
bond are excluded by the literal protected-edge predicate. -/
theorem VineRealization.typeVII_protected_core_edge {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hM : M.IsMolecule)
    (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) (i j : Fin 11)
    (he : (i.1,j.1) ∈ protectedCoreBonds .VII {4,5,6,7,8}) :
    Relation.EqvGen (ProtectedSingleAdj M S (R.selectedAtoms (sideLabels (11+2*kr) kc))
      (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1)
      (R.coreAtom i).1 (R.coreAtom j).1 := by
  have hsingle := (List.mem_filter.mp he).1
  have hm := (List.mem_filter.mp hsingle).1
  have hc : VineType.VII.template.bonds.count (i.1,j.1)+
      VineType.VII.template.bonds.count (j.1,i.1)=1 :=
    of_decide_eq_true (List.mem_filter.mp hsingle).2
  have hguard : ¬(i.1 ∈ ({4,5,6,7,8} : Finset ℕ) ∧ j.1 ∈ ({4,5,6,7,8} : Finset ℕ)) :=
    of_decide_eq_true (List.mem_filter.mp he).2
  have hij : i ≠ j := by
    intro heq
    subst j
    have hz := template_no_loop_counts .VII i
    omega
  by_cases hslot : ∃ s ∈ VineType.VII.template.slots,(i.1,j.1)=s.1 ∨ (i.1,j.1)=s.2
  · obtain ⟨s,hs,heq⟩ := hslot
    have hs' : s=((2,7),(3,8)) ∨ s=((5,7),(6,8)) ∨ s=((7,9),(8,10)) := by
      simpa only [VineType.template,List.mem_cons,List.not_mem_nil,or_false] using hs
    rcases hs' with rfl | rfl | rfl
    · have hp := R.typeVII_red_protected_paths hM kr kc kg hks
      rcases heq with heq | heq
      · have hi : i=(2 : Fin 11) := Fin.ext (congrArg Prod.fst heq)
        have hj : j=(7 : Fin 11) := Fin.ext (congrArg Prod.snd heq)
        simpa only [hi,hj] using hp.1
      · have hi : i=(3 : Fin 11) := Fin.ext (congrArg Prod.fst heq)
        have hj : j=(8 : Fin 11) := Fin.ext (congrArg Prod.snd heq)
        simpa only [hi,hj] using hp.2
    · rcases heq with heq | heq
      · have hi : i.1=5 := congrArg Prod.fst heq
        have hj : j.1=7 := congrArg Prod.snd heq
        exact False.elim (hguard (by rw [hi,hj]; decide))
      · have hi : i.1=6 := congrArg Prod.fst heq
        have hj : j.1=8 := congrArg Prod.snd heq
        exact False.elim (hguard (by rw [hi,hj]; decide))
    · have hp := R.typeVII_green_protected_paths hM kr kc kg hks
      rcases heq with heq | heq
      · have hi : i=(7 : Fin 11) := Fin.ext (congrArg Prod.fst heq)
        have hj : j=(9 : Fin 11) := Fin.ext (congrArg Prod.snd heq)
        simpa only [hi,hj] using hp.1
      · have hi : i=(8 : Fin 11) := Fin.ext (congrArg Prod.fst heq)
        have hj : j=(10 : Fin 11) := Fin.ext (congrArg Prod.snd heq)
        simpa only [hi,hj] using hp.2
  · have hd := R.single_core_untouched i j hij hc hm (by
      intro s hs
      exact ⟨fun hh => hslot ⟨s,hs,Or.inl hh⟩,fun hh => hslot ⟨s,hs,Or.inr hh⟩⟩)
    have ha := R.protectedVII_core_atoms (11+2*kr) kc (by omega) i j he
    exact Relation.EqvGen.rel _ _ ⟨hd,ha⟩

end WaveTurbulence.Vine
