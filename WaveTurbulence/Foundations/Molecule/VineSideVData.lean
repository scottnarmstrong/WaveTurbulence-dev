/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideVIIIData
import Mathlib.Tactic

/-! # Both old doubled pairs belong to the type-V cap frame -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual type-V slot supplies a complete triangular cap frame.
Both old doubled endpoint pairs are included as rungs; the outer joints
remain external ports. No positivity assumption on inserted rungs is needed. -/
theorem typeV_side_data (M : Molecule V D) {S : Finset V} {a b : V}
    (R : VineRealization M .V S a b) (k : ℕ) (hks : R.k=[k]) :
    let c : Fin 9 → V := fun i => (R.coreAtom i).1
    ∃ T : SideLadderData M (c 8) (c 6) (c 7) (c 0) (c 1) (k+2),
      Function.Injective (capAtomFamily (c 8) (c 6) (c 7) T.ladder.u T.ladder.v (k+3)) ∧
      ∃ Q : FullRungSequence M k,
        (∀ i,Q.u i ∈ S ∧ Q.v i ∈ S) ∧
        (Q.u 0=c 2 ∧ Q.v 0=c 3 ∧ Q.u (k+1)=c 4 ∧ Q.v (k+1)=c 5) ∧
        (∀ i,1 ≤ i → i ≤ k → R.f (Q.u i)=9+(i-1) ∧ R.f (Q.v i)=9+k+(i-1)) ∧
        (∀ i,i ≤ k+1 → T.ladder.u (k+2-i)=Q.u i ∧ T.ladder.v (k+2-i)=Q.v i) := by
  let c : Fin 9 → V := fun i => (R.coreAtom i).1
  have hdist (i j : Fin 9) (hne : i.1 ≠ j.1) : c i ≠ c j :=
    fun he => hne (congrArg Fin.val (R.coreAtom_injective he))
  have hloc : VineType.V.template.slots.zip R.k=[]++(((2,4),(3,5)),k)::[] := by rw [hks]; rfl
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports _ _ _ _ hloc
  have hd := R.slot_full_distinct _ _ _ _ hloc (by decide) Q hports hlabels
  have hrail := R.slot_boundary_adj _ _ _ _ hloc Q hmem hports
  have he (v : V) (hv : v ∈ S) (i : Fin 9) (hvi : R.f v=i.1) : v=c i :=
    R.injOn hv (R.coreAtom i).2 (hvi.trans (R.label_coreAtom i).symm)
  have hu0 := he (Q.u 0) (hmem 0).1 (2 : Fin 9) hports.1
  have hv0 := he (Q.v 0) (hmem 0).2 (3 : Fin 9) hports.2.1
  have huN := he (Q.u (k+1)) (hmem (k+1)).1 (4 : Fin 9) hports.2.2.1
  have hvN := he (Q.v (k+1)) (hmem (k+1)).2 (5 : Fin 9) hports.2.2.2
  have hp := R.core_outside_slot_rails _ _ _ Q hports hlabels (0 : Fin 9) (by decide)
  have hq := R.core_outside_slot_rails _ _ _ Q hports hlabels (1 : Fin 9) (by decide)
  have h6 := R.core_outside_slot_rails _ _ _ Q hports hlabels (6 : Fin 9) (by decide)
  have h7 := R.core_outside_slot_rails _ _ _ Q hports hlabels (7 : Fin 9) (by decide)
  have h8 := R.core_outside_slot_rails _ _ _ Q hports hlabels (8 : Fin 9) (by decide)
  obtain ⟨R23⟩ := R.core_twoIncidences (2 : Fin 9) (3 : Fin 9) (by decide)
  have h20 := Mole.adj_symmetric M (R.core_untouched_adj (0 : Fin 9) (2 : Fin 9) (by decide) (by decide))
  have h31 := Mole.adj_symmetric M (R.core_untouched_adj (1 : Fin 9) (3 : Fin 9) (by decide) (by decide))
  have hcross01 : Q.v 0 ≠ Q.u 1 := by
    intro hh
    have hh' := hd (a₁ := Sum.inr ⟨0,by omega⟩) (a₂ := Sum.inl ⟨1,by omega⟩) hh
    cases hh'
  have hcross10 : Q.u 0 ≠ Q.v 1 := by
    intro hh
    have hh' := hd (a₁ := Sum.inl ⟨0,by omega⟩) (a₂ := Sum.inr ⟨1,by omega⟩) hh
    cases hh'
  obtain ⟨RU⟩ := fourIncidences_of_double_and_edges R23 h20
    (by simpa only [hu0] using hrail.1) (hdist 3 0 (by decide))
    (by simpa only [hv0] using hcross01) (hp 1 (by omega)).1
  obtain ⟨RV⟩ := fourIncidences_of_double_and_edges R23.mates h31
    (by simpa only [hv0] using hrail.2.1) (hdist 2 1 (by decide))
    (by simpa only [hu0] using hcross10) (hq 1 (by omega)).2
  let E := Q.prepend (c 0) (c 1) hd (by simpa only [hu0,hv0] using RU)
    (by simpa only [hu0,hv0] using RV)
  let B := E.reverse
  have hBu0 : B.u 0=c 4 := by
    change prependRail Q.u (c 0) (k+1+1-0)=c 4
    simpa only [Nat.sub_zero,prependRail] using huN
  have hBv0 : B.v 0=c 5 := by
    change prependRail Q.v (c 1) (k+1+1-0)=c 5
    simpa only [Nat.sub_zero,prependRail] using hvN
  have hBu1 : B.u 1=Q.u k := by
    change prependRail Q.u (c 0) (k+1+1-1)=Q.u k
    rw [show k+1+1-1=k+1 by omega]
    rfl
  have hBv1 : B.v 1=Q.v k := by
    change prependRail Q.v (c 1) (k+1+1-1)=Q.v k
    rw [show k+1+1-1=k+1 by omega]
    rfl
  have hE := prependRail_pair_injective Q.u Q.v (c 0) (c 1) k hd hp hq (hdist 0 1 (by decide))
  have hB := reverseRail_pair_injective (prependRail Q.u (c 0)) (prependRail Q.v (c 1)) (k+1) hE
  have hsep (j : Fin 9) (hj : j.1=6 ∨ j.1=7 ∨ j.1=8) :
      ∀ i,i ≤ k+1+1 → c j ≠ B.u i ∧ c j ≠ B.v i := by
    have hc : ∀ i,i ≤ k+1 → c j ≠ Q.u i ∧ c j ≠ Q.v i := by
      rcases hj with hj | hj | hj
      · have he : j=6 := Fin.ext hj
        subst j
        exact h6
      · have he : j=7 := Fin.ext hj
        subst j
        exact h7
      · have he : j=8 := Fin.ext hj
        subst j
        exact h8
    have hh := prependRail_separation Q.u Q.v (c 0) (c 1) (c j) k hc
      (hdist j 0 (by rcases hj with h | h | h <;> omega))
      (hdist j 1 (by rcases hj with h | h | h <;> omega))
    intro i hi
    exact hh (k+1+1-i) (by omega)
  obtain ⟨R45⟩ := R.core_twoIncidences (4 : Fin 9) (5 : Fin 9) (by decide)
  have h46 := R.core_untouched_adj (4 : Fin 9) (6 : Fin 9) (by decide) (by decide)
  have h57 := R.core_untouched_adj (5 : Fin 9) (7 : Fin 9) (by decide) (by decide)
  have hvNU : c 5 ≠ Q.u k := by
    intro hh
    rw [← hvN] at hh
    have hh' := hd (a₁ := Sum.inr ⟨k+1,by omega⟩) (a₂ := Sum.inl ⟨k,by omega⟩) hh
    cases hh'
  have huNV : c 4 ≠ Q.v k := by
    intro hh
    rw [← huN] at hh
    have hh' := hd (a₁ := Sum.inl ⟨k+1,by omega⟩) (a₂ := Sum.inr ⟨k,by omega⟩) hh
    cases hh'
  obtain ⟨R4⟩ := fourIncidences_of_double_and_edges R45 h46
    (by simpa only [huN] using Mole.adj_symmetric M hrail.2.2.1)
    (hdist 5 6 (by decide)) hvNU (h6 k (by omega)).1
  obtain ⟨R5⟩ := fourIncidences_of_double_and_edges R45.mates h57
    (by simpa only [hvN] using Mole.adj_symmetric M hrail.2.2.2)
    (hdist 4 7 (by decide)) huNV (h7 k (by omega)).2
  let T := B.prepend (c 6) (c 7) hB
    (by simpa only [hBu0,hBv0,hBu1] using R4)
    (by simpa only [hBu0,hBv0,hBv1] using R5)
  have hTu0 : T.u 0=c 6 := rfl
  have hTv0 : T.v 0=c 7 := rfl
  have hTuN : T.u (k+2+1)=c 0 := by
    change prependRail B.u (c 6) (k+2+1)=c 0
    change B.u (k+2)=c 0
    change prependRail Q.u (c 0) (k+1+1-(k+2))=c 0
    rw [show k+1+1-(k+2)=0 by omega]
    rfl
  have hTvN : T.v (k+2+1)=c 1 := by
    change prependRail B.v (c 7) (k+2+1)=c 1
    change B.v (k+2)=c 1
    change prependRail Q.v (c 1) (k+1+1-(k+2))=c 1
    rw [show k+1+1-(k+2)=0 by omega]
    rfl
  obtain ⟨R68⟩ := R.core_twoIncidences (6 : Fin 9) (8 : Fin 9) (by decide)
  obtain ⟨R78⟩ := R.core_twoIncidences (7 : Fin 9) (8 : Fin 9) (by decide)
  have h67 := R.core_untouched_adj (6 : Fin 9) (7 : Fin 9) (by decide) (by decide)
  obtain ⟨R6⟩ := fourIncidences_of_double_and_edges R68 h67 (Mole.adj_symmetric M h46)
    (hdist 8 7 (by decide)) (hdist 8 4 (by decide)) (hdist 7 4 (by decide))
  obtain ⟨R7⟩ := fourIncidences_of_double_and_edges R78 (Mole.adj_symmetric M h67) (Mole.adj_symmetric M h57)
    (hdist 8 6 (by decide)) (hdist 8 5 (by decide)) (hdist 6 5 (by decide))
  have hcore : Function.Injective ![c 8,c 6,c 7,c 0,c 1] := by
    have hi : Function.Injective (![8,6,7,0,1] : Fin 5 → Fin 9) := by decide
    have hmap : ![c 8,c 6,c 7,c 0,c 1]=c ∘ (![8,6,7,0,1] : Fin 5 → Fin 9) := by
      funext i
      fin_cases i <;> rfl
    rw [hmap]
    exact R.coreAtom_injective.comp hi
  let F : SideLadderData M (c 8) (c 6) (c 7) (c 0) (c 1) (k+2) :=
    ⟨T,hTu0,hTv0,hTuN,hTvN,hcore,
      FourIncidences.ofTwoPairs R68.mates R78.mates (hdist 6 7 (by decide)),
      by simpa only [show T.u 1=c 4 from hBu0] using R6,
      by simpa only [show T.v 1=c 5 from hBv0] using R7⟩
  have hT := prependRail_pair_injective B.u B.v (c 6) (c 7) (k+1) hB
    (hsep 6 (Or.inl rfl)) (hsep 7 (Or.inr (Or.inl rfl))) (hdist 6 7 (by decide))
  have hcenter := prependRail_separation B.u B.v (c 6) (c 7) (c 8) (k+1)
    (hsep 8 (Or.inr (Or.inr rfl))) (hdist 8 6 (by decide)) (hdist 8 7 (by decide))
  have hfamily := capAtomFamily_injective_of_full_frame (c 8) T.u T.v (k+2) hT hcenter
  refine ⟨F,hfamily,Q,hmem,⟨hu0,hv0,huN,hvN⟩,?_,?_⟩
  · intro i hi hin
    simpa only [List.foldl_nil,VineType.template] using hlabels i hi hin
  · intro i hi
    have he : k+2-i=(k+1-i)+1 := by omega
    change prependRail B.u (c 6) (k+2-i)=Q.u i ∧ prependRail B.v (c 7) (k+2-i)=Q.v i
    rw [he]
    change prependRail Q.u (c 0) (k+1+1-(k+1-i))=Q.u i ∧
      prependRail Q.v (c 1) (k+1+1-(k+1-i))=Q.v i
    rw [show k+1+1-(k+1-i)=i+1 by omega]
    exact ⟨rfl,rfl⟩

end WaveTurbulence.Vine
