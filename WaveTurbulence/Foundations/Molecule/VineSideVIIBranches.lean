/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideVIIData
public import WaveTurbulence.Foundations.Molecule.VineSideLabels
public import WaveTurbulence.Foundations.Molecule.VineSelectedAtoms
import Mathlib.Tactic

/-! # Branching at both joints of the selected type-VII side -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Both terminal core atoms of the full selected side have two distinct
neighbors inside that side, for every cyan rung count including zero. -/
theorem typeVII_selected_side_branches (M : Molecule V D) {S : Finset V} {a b : V}
    (R : VineRealization M .VII S a b) (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) :
    let c : Fin 11 → V := fun i => (R.coreAtom i).1
    let A := R.selectedAtoms (sideLabels (11+2*kr) kc)
    (∃ u v,(Mole.induced M A).Adj (c 7) u ∧ (Mole.induced M A).Adj (c 7) v ∧ u ≠ v) ∧
    (∃ u v,(Mole.induced M A).Adj (c 8) u ∧ (Mole.induced M A).Adj (c 8) v ∧ u ≠ v) := by
  let c : Fin 11 → V := fun i => (R.coreAtom i).1
  let A := R.selectedAtoms (sideLabels (11+2*kr) kc)
  have hlabelc (i : Fin 11) : R.f (c i)=i.1 := R.label_coreAtom i
  have hci (i : Fin 11) (hlo : 4 ≤ i.1) (hhi : i.1 ≤ 8) : c i ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨(R.coreAtom i).2,?_⟩
    apply (mem_sideLabels_iff _ _ _).mpr
    rw [hlabelc]
    omega
  have hdist (i j : Fin 11) (hne : i.1 ≠ j.1) : c i ≠ c j :=
    fun he => hne (congrArg Fin.val (R.coreAtom_injective he))
  have h78 : M.Adj (c 7) (c 8) := R.core_untouched_adj (7 : Fin 11) (8 : Fin 11) (by decide) (by decide)
  have hrails : ∃ p q,p ∈ A ∧ q ∈ A ∧ M.Adj (c 7) p ∧ M.Adj (c 8) q ∧ p ≠ c 8 ∧ q ≠ c 7 := by
    by_cases hk : kc=0
    · subst kc
      have hslot : (((5,7),(6,8)),0) ∈ VineType.VII.template.slots.zip R.k := by
        rw [hks]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      refine ⟨c 5,c 6,hci 5 (by decide) (by decide),hci 6 (by decide) (by decide),?_,?_,
        hdist 5 8 (by decide),hdist 6 7 (by decide)⟩
      · exact Mole.adj_symmetric M (R.zero_slot_adj _ hslot (5,7) (Or.inl rfl)
          (R.coreAtom (5 : Fin 11)).2 (R.coreAtom (7 : Fin 11)).2 (hlabelc 5) (hlabelc 7))
      · exact Mole.adj_symmetric M (R.zero_slot_adj _ hslot (6,8) (Or.inr rfl)
          (R.coreAtom (6 : Fin 11)).2 (R.coreAtom (8 : Fin 11)).2 (hlabelc 6) (hlabelc 8))
    · have hpos : 1 ≤ kc := by omega
      have hloc : VineType.VII.template.slots.zip R.k=
          [(((2,7),(3,8)),kr)]++(((5,7),(6,8)),kc)::[(((7,9),(8,10)),kg)] := by rw [hks]; rfl
      obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports _ _ _ _ hloc
      dsimp only at hports
      have hlast : R.f (Q.u kc)=11+2*kr+(kc-1) ∧ R.f (Q.v kc)=11+2*kr+kc+(kc-1) := by
        simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hlabels kc hpos le_rfl
      have huN : Q.u (kc+1)=c 7 := R.injOn (hmem (kc+1)).1 (R.coreAtom (7 : Fin 11)).2
        (hports.2.2.1.trans (hlabelc 7).symm)
      have hvN : Q.v (kc+1)=c 8 := R.injOn (hmem (kc+1)).2 (R.coreAtom (8 : Fin 11)).2
        (hports.2.2.2.trans (hlabelc 8).symm)
      have huA : Q.u kc ∈ A := by
        refine Finset.mem_filter.mpr ⟨(hmem kc).1,?_⟩
        apply (mem_sideLabels_iff _ _ _).mpr
        right; right; right; right; right
        rw [hlast.1]
        constructor <;> omega
      have hvA : Q.v kc ∈ A := by
        refine Finset.mem_filter.mpr ⟨(hmem kc).2,?_⟩
        apply (mem_sideLabels_iff _ _ _).mpr
        right; right; right; right; right
        rw [hlast.2]
        constructor <;> omega
      refine ⟨Q.u kc,Q.v kc,huA,hvA,?_,?_,?_,?_⟩
      · simpa only [huN] using Mole.adj_symmetric M (Q.upper_next_adj kc hpos le_rfl)
      · simpa only [hvN] using Mole.adj_symmetric M (Q.lower_next_adj kc hpos le_rfl)
      · intro he
        have hh := congrArg R.f he
        rw [hlast.1,hlabelc 8] at hh
        omega
      · intro he
        have hh := congrArg R.f he
        rw [hlast.2,hlabelc 7] at hh
        omega
  obtain ⟨p,q,hp,hq,h7p,h8q,hp8,hq7⟩ := hrails
  have h7 := hci 7 (by decide) (by decide)
  have h8 := hci 8 (by decide) (by decide)
  constructor
  · exact ⟨c 8,p,(Mole.induced_adj_iff M A _ _).mpr ⟨h78,h7,h8⟩,
      (Mole.induced_adj_iff M A _ _).mpr ⟨h7p,h7,hp⟩,Ne.symm hp8⟩
  · exact ⟨c 7,q,(Mole.induced_adj_iff M A _ _).mpr ⟨Mole.adj_symmetric M h78,h8,h7⟩,
      (Mole.induced_adj_iff M A _ _).mpr ⟨h8q,h8,hq⟩,Ne.symm hq7⟩

end WaveTurbulence.Vine
