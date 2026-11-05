/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideLadderData
public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineCoreJointEdges
public import WaveTurbulence.Foundations.Molecule.VineUntouchedCoreEdges
public import WaveTurbulence.Foundations.Molecule.VineZeroSlotEdges
public import WaveTurbulence.Foundations.Molecule.VineFullRungRailEdges
import Mathlib.Tactic

/-! # Construct the type-VII side-ladder data from the pinned realization -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The pinned type-VII realization supplies the actual side-ladder rows,
including the zero-rung case. No side-incidence witness is assumed. -/
theorem typeVII_side_data (M : Molecule V D) {S : Finset V} {a b : V}
    (R : VineRealization M .VII S a b) (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) :
    let c : Fin 11 → V := fun i => (R.coreAtom i).1
    ∃ D : SideLadderData M (c 4) (c 5) (c 6) (c 7) (c 8) kc,
      (∀ i,D.ladder.u i ∈ S ∧ D.ladder.v i ∈ S) ∧
      ∀ i,1 ≤ i → i ≤ kc → R.f (D.ladder.u i)=11+2*kr+(i-1) ∧
        R.f (D.ladder.v i)=11+2*kr+kc+(i-1) := by
  let c : Fin 11 → V := fun i => (R.coreAtom i).1
  have hlabelc (i : Fin 11) : R.f (c i)=i.1 := R.label_coreAtom i
  have hdist (i j : Fin 11) (hne : i.1 ≠ j.1) : c i ≠ c j :=
    fun he => hne (congrArg Fin.val (R.coreAtom_injective he))
  have hloc : VineType.VII.template.slots.zip R.k=
      [(((2,7),(3,8)),kr)]++(((5,7),(6,8)),kc)::[(((7,9),(8,10)),kg)] := by rw [hks]; rfl
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports _ _ _ _ hloc
  dsimp only at hports hlabels
  have hu0 : Q.u 0=c 5 := R.injOn (hmem 0).1 (R.coreAtom (5 : Fin 11)).2 (hports.1.trans (hlabelc 5).symm)
  have hv0 : Q.v 0=c 6 := R.injOn (hmem 0).2 (R.coreAtom (6 : Fin 11)).2 (hports.2.1.trans (hlabelc 6).symm)
  have huN : Q.u (kc+1)=c 7 := R.injOn (hmem (kc+1)).1 (R.coreAtom (7 : Fin 11)).2 (hports.2.2.1.trans (hlabelc 7).symm)
  have hvN : Q.v (kc+1)=c 8 := R.injOn (hmem (kc+1)).2 (R.coreAtom (8 : Fin 11)).2 (hports.2.2.2.trans (hlabelc 8).symm)
  have hN : 11 ≤ ([(((2,7),(3,8)),kr)].foldl
      (fun U sk => insertRungs U sk.1 sk.2) VineType.VII.template).n := by
    simp only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template]
    omega
  have hfirstU : 7 ≤ R.f (Q.u 1) := by
    by_cases hk : kc=0
    · subst kc
      have hh : R.f (Q.u 1)=7 := by simpa only [Nat.zero_add] using hports.2.2.1
      omega
    · have hh := (hlabels 1 le_rfl (by omega)).1
      omega
  have hfirstV : 7 ≤ R.f (Q.v 1) := by
    by_cases hk : kc=0
    · subst kc
      have hh : R.f (Q.v 1)=8 := by simpa only [Nat.zero_add] using hports.2.2.2
      omega
    · have hh := (hlabels 1 le_rfl (by omega)).2
      omega
  have hnotU (i : Fin 11) (hi : i.1<7) : c i ≠ Q.u 1 := by
    intro he
    have hh := congrArg R.f he
    rw [hlabelc] at hh
    omega
  have hnotV (i : Fin 11) (hi : i.1<7) : c i ≠ Q.v 1 := by
    intro he
    have hh := congrArg R.f he
    rw [hlabelc] at hh
    omega
  have hrailU : M.Adj (c 5) (Q.u 1) := by
    by_cases hk : kc=0
    · subst kc
      have hslot : (((5,7),(6,8)),0) ∈ VineType.VII.template.slots.zip R.k := by
        rw [hloc]
        exact List.mem_append_right _ List.mem_cons_self
      exact R.zero_slot_adj _ hslot (5,7) (Or.inl rfl) (R.coreAtom (5 : Fin 11)).2 (hmem 1).1
        (hlabelc 5) hports.2.2.1
    · have hh := Mole.adj_symmetric M (Q.upper_prev_adj 1 le_rfl (by omega))
      simpa only [hu0] using hh
  have hrailV : M.Adj (c 6) (Q.v 1) := by
    by_cases hk : kc=0
    · subst kc
      have hslot : (((5,7),(6,8)),0) ∈ VineType.VII.template.slots.zip R.k := by
        rw [hloc]
        exact List.mem_append_right _ List.mem_cons_self
      exact R.zero_slot_adj _ hslot (6,8) (Or.inr rfl) (R.coreAtom (6 : Fin 11)).2 (hmem 1).2
        (hlabelc 6) hports.2.2.2
    · have hh := Mole.adj_symmetric M (Q.lower_prev_adj 1 le_rfl (by omega))
      simpa only [hv0] using hh
  obtain ⟨R45⟩ := R.core_twoIncidences (4 : Fin 11) (5 : Fin 11) (by decide)
  obtain ⟨R46⟩ := R.core_twoIncidences (4 : Fin 11) (6 : Fin 11) (by decide)
  have h56 : M.Adj (c 5) (c 6) := R.core_untouched_adj (5 : Fin 11) (6 : Fin 11) (by decide) (by decide)
  obtain ⟨R5⟩ := fourIncidences_of_double_and_edges R45.mates h56 hrailU
    (hdist 4 6 (by decide)) (hnotU 4 (by decide)) (hnotU 6 (by decide))
  obtain ⟨R6⟩ := fourIncidences_of_double_and_edges R46.mates (Mole.adj_symmetric M h56) hrailV
    (hdist 4 5 (by decide)) (hnotV 4 (by decide)) (hnotV 5 (by decide))
  have hcore : Function.Injective ![c 4,c 5,c 6,c 7,c 8] := by
    intro i j he
    fin_cases i <;> fin_cases j
    · exact rfl
    · exact False.elim (hdist 4 5 (by decide) he)
    · exact False.elim (hdist 4 6 (by decide) he)
    · exact False.elim (hdist 4 7 (by decide) he)
    · exact False.elim (hdist 4 8 (by decide) he)
    · exact False.elim (hdist 5 4 (by decide) he)
    · exact rfl
    · exact False.elim (hdist 5 6 (by decide) he)
    · exact False.elim (hdist 5 7 (by decide) he)
    · exact False.elim (hdist 5 8 (by decide) he)
    · exact False.elim (hdist 6 4 (by decide) he)
    · exact False.elim (hdist 6 5 (by decide) he)
    · exact rfl
    · exact False.elim (hdist 6 7 (by decide) he)
    · exact False.elim (hdist 6 8 (by decide) he)
    · exact False.elim (hdist 7 4 (by decide) he)
    · exact False.elim (hdist 7 5 (by decide) he)
    · exact False.elim (hdist 7 6 (by decide) he)
    · exact rfl
    · exact False.elim (hdist 7 8 (by decide) he)
    · exact False.elim (hdist 8 4 (by decide) he)
    · exact False.elim (hdist 8 5 (by decide) he)
    · exact False.elim (hdist 8 6 (by decide) he)
    · exact False.elim (hdist 8 7 (by decide) he)
    · exact rfl
  refine ⟨⟨Q,hu0,hv0,huN,hvN,hcore,
    FourIncidences.ofTwoPairs R45 R46 (hdist 5 6 (by decide)),R5,R6⟩,hmem,?_⟩
  intro i hi hin
  simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hlabels i hi hin

end WaveTurbulence.Vine
