/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideVIIData
public import WaveTurbulence.Foundations.Molecule.VineSlotCoreSeparation
public import WaveTurbulence.Foundations.Molecule.VineSlotBoundaryEdges
public import WaveTurbulence.Foundations.Molecule.VinePrependDistinct
public import WaveTurbulence.Foundations.Molecule.VineCapFamilyDistinct
import Mathlib.Tactic

/-! # Construct the triangular cap frame in a type-VI realization -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual cyan slot, with its old doubled initial pair included and
traversed in reverse, supplies the complete type-VI cap frame. -/
theorem typeVI_side_data (M : Molecule V D) {S : Finset V} {a b : V}
    (R : VineRealization M .VI S a b) (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) :
    let c : Fin 15 → V := fun i => (R.coreAtom i).1
    ∃ T : SideLadderData M (c 12) (c 10) (c 11) (c 5) (c 7) (kc+1),
      Function.Injective (capAtomFamily (c 12) (c 10) (c 11) T.ladder.u T.ladder.v (kc+2)) ∧
      ∃ Q : FullRungSequence M kc,
        (∀ i,Q.u i ∈ S ∧ Q.v i ∈ S) ∧
        (Q.u 0=c 8 ∧ Q.v 0=c 9 ∧ Q.u (kc+1)=c 10 ∧ Q.v (kc+1)=c 11) ∧
        (∀ i,1 ≤ i → i ≤ kc → R.f (Q.u i)=15+2*kr+(i-1) ∧
          R.f (Q.v i)=15+2*kr+kc+(i-1)) ∧
        (∀ i, i ≤ kc → T.ladder.u (kc+1-i)=Q.u i ∧ T.ladder.v (kc+1-i)=Q.v i) := by
  let c : Fin 15 → V := fun i => (R.coreAtom i).1
  have hdist (i j : Fin 15) (hne : i.1 ≠ j.1) : c i ≠ c j :=
    fun he => hne (congrArg Fin.val (R.coreAtom_injective he))
  have hloc : VineType.VI.template.slots.zip R.k=
      [(((2,4),(3,5)),kr)]++(((8,10),(9,11)),kc)::[(((6,13),(7,14)),kg)] := by rw [hks]; rfl
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports _ _ _ _ hloc
  have hd := R.slot_full_distinct _ _ _ _ hloc (by decide) Q hports hlabels
  have hrail := R.slot_boundary_adj _ _ _ _ hloc Q hmem hports
  have he (v : V) (hv : v ∈ S) (i : Fin 15) (hvi : R.f v=i.1) : v=c i :=
    R.injOn hv (R.coreAtom i).2 (hvi.trans (R.label_coreAtom i).symm)
  have hu0 := he (Q.u 0) (hmem 0).1 (8 : Fin 15) hports.1
  have hv0 := he (Q.v 0) (hmem 0).2 (9 : Fin 15) hports.2.1
  have huN := he (Q.u (kc+1)) (hmem (kc+1)).1 (10 : Fin 15) hports.2.2.1
  have hvN := he (Q.v (kc+1)) (hmem (kc+1)).2 (11 : Fin 15) hports.2.2.2
  have hp := R.core_outside_slot_rails _ _ _ Q hports hlabels (5 : Fin 15) (by decide)
  have hq := R.core_outside_slot_rails _ _ _ Q hports hlabels (7 : Fin 15) (by decide)
  have hc := R.core_outside_slot_rails _ _ _ Q hports hlabels (12 : Fin 15) (by decide)
  obtain ⟨R67⟩ := R.core_twoIncidences (8 : Fin 15) (9 : Fin 15) (by decide)
  have h60 : M.Adj (c 8) (c 5) := Mole.adj_symmetric M
    (R.core_untouched_adj (5 : Fin 15) (8 : Fin 15) (by decide) (by decide))
  have h73 : M.Adj (c 9) (c 7) := Mole.adj_symmetric M
    (R.core_untouched_adj (7 : Fin 15) (9 : Fin 15) (by decide) (by decide))
  have hcross01 : Q.v 0 ≠ Q.u 1 := by
    intro hh
    have hh' := hd (a₁ := Sum.inr ⟨0,by omega⟩) (a₂ := Sum.inl ⟨1,by omega⟩) hh
    cases hh'
  have hcross10 : Q.u 0 ≠ Q.v 1 := by
    intro hh
    have hh' := hd (a₁ := Sum.inl ⟨0,by omega⟩) (a₂ := Sum.inr ⟨1,by omega⟩) hh
    cases hh'
  obtain ⟨RU⟩ := fourIncidences_of_double_and_edges R67 h60
    (by simpa only [hu0] using hrail.1) (hdist 9 5 (by decide))
    (by simpa only [hv0] using hcross01) (hp 1 (by omega)).1
  obtain ⟨RV⟩ := fourIncidences_of_double_and_edges R67.mates h73
    (by simpa only [hv0] using hrail.2.1) (hdist 8 7 (by decide))
    (by simpa only [hu0] using hcross10) (hq 1 (by omega)).2
  let E := Q.prepend (c 5) (c 7) hd (by simpa only [hu0,hv0] using RU)
    (by simpa only [hu0,hv0] using RV)
  let T := E.reverse
  have hTu0 : T.u 0=c 10 := by
    change prependRail Q.u (c 5) (kc+1+1-0)=c 10
    simpa only [Nat.sub_zero,prependRail] using huN
  have hTv0 : T.v 0=c 11 := by
    change prependRail Q.v (c 7) (kc+1+1-0)=c 11
    simpa only [Nat.sub_zero,prependRail] using hvN
  have hTuN : T.u (kc+1+1)=c 5 := by change prependRail Q.u (c 5) (kc+1+1-(kc+1+1))=c 5; simp only [Nat.sub_self,prependRail]
  have hTvN : T.v (kc+1+1)=c 7 := by change prependRail Q.v (c 7) (kc+1+1-(kc+1+1))=c 7; simp only [Nat.sub_self,prependRail]
  have hTu1 : T.u 1=Q.u kc := by
    change prependRail Q.u (c 5) (kc+1+1-1)=Q.u kc
    rw [show kc+1+1-1=kc+1 by omega]
    rfl
  have hTv1 : T.v 1=Q.v kc := by
    change prependRail Q.v (c 7) (kc+1+1-1)=Q.v kc
    rw [show kc+1+1-1=kc+1 by omega]
    rfl
  obtain ⟨R810⟩ := R.core_twoIncidences (10 : Fin 15) (12 : Fin 15) (by decide)
  let R108 := R810.mates
  obtain ⟨R910⟩ := R.core_twoIncidences (11 : Fin 15) (12 : Fin 15) (by decide)
  let R109 := R910.mates
  have h89 := R.core_untouched_adj (10 : Fin 15) (11 : Fin 15) (by decide) (by decide)
  have hvNU : c 11 ≠ Q.u kc := by
    intro hh
    rw [← hvN] at hh
    have hh' := hd (a₁ := Sum.inr ⟨kc+1,by omega⟩) (a₂ := Sum.inl ⟨kc,by omega⟩) hh
    cases hh'
  have huNV : c 10 ≠ Q.v kc := by
    intro hh
    rw [← huN] at hh
    have hh' := hd (a₁ := Sum.inl ⟨kc+1,by omega⟩) (a₂ := Sum.inr ⟨kc,by omega⟩) hh
    cases hh'
  obtain ⟨R8⟩ := fourIncidences_of_double_and_edges R108.mates h89
    (by simpa only [huN] using Mole.adj_symmetric M hrail.2.2.1)
    (hdist 12 11 (by decide)) (hc kc (by omega)).1 hvNU
  obtain ⟨R9⟩ := fourIncidences_of_double_and_edges R109.mates (Mole.adj_symmetric M h89)
    (by simpa only [hvN] using Mole.adj_symmetric M hrail.2.2.2)
    (hdist 12 10 (by decide)) (hc kc (by omega)).2 huNV
  have hcore : Function.Injective ![c 12,c 10,c 11,c 5,c 7] := by
    have hi : Function.Injective (![12,10,11,5,7] : Fin 5 → Fin 15) := by decide
    intro i j hh
    apply hi
    apply R.coreAtom_injective
    have hmap : ![c 12,c 10,c 11,c 5,c 7]=c ∘ (![12,10,11,5,7] : Fin 5 → Fin 15) := by
      funext i
      fin_cases i <;> rfl
    rw [hmap] at hh
    exact hh
  let B : SideLadderData M (c 12) (c 10) (c 11) (c 5) (c 7) (kc+1) :=
    ⟨T,hTu0,hTv0,hTuN,hTvN,hcore,
      FourIncidences.ofTwoPairs R108 R109 (hdist 10 11 (by decide)),
      by simpa only [hTu1] using R8,by simpa only [hTv1] using R9⟩
  have hE := prependRail_pair_injective Q.u Q.v (c 5) (c 7) kc hd hp hq (hdist 5 7 (by decide))
  have hT := reverseRail_pair_injective (prependRail Q.u (c 5)) (prependRail Q.v (c 7)) (kc+1) hE
  have hcenter (i : ℕ) (hi : i ≤ kc+1+1) : c 12 ≠ T.u i ∧ c 12 ≠ T.v i := by
    change c 12 ≠ prependRail Q.u (c 5) (kc+1+1-i) ∧ c 12 ≠ prependRail Q.v (c 7) (kc+1+1-i)
    generalize hj : kc+1+1-i=j
    cases j with
    | zero => exact ⟨hdist 12 5 (by decide),hdist 12 7 (by decide)⟩
    | succ j => exact hc j (by omega)
  have hfamily := capAtomFamily_injective_of_full_frame (c 12) T.u T.v (kc+1) hT hcenter
  refine ⟨B,?_,Q,hmem,⟨hu0,hv0,huN,hvN⟩,?_,?_⟩
  · simpa only [hTu0,hTv0] using hfamily
  · intro i hi hin
    simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hlabels i hi hin
  · intro i hi
    change prependRail Q.u (c 5) (kc+1+1-(kc+1-i))=Q.u i ∧
      prependRail Q.v (c 7) (kc+1+1-(kc+1-i))=Q.v i
    rw [show kc+1+1-(kc+1-i)=i+1 by omega]
    exact ⟨rfl,rfl⟩

end WaveTurbulence.Vine
