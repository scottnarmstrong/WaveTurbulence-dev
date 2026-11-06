/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceJointPairDichotomy
public import WaveTurbulence.Foundations.Molecule.VineNestedGaps
public import WaveTurbulence.Foundations.Molecule.VineVertexConnected
/-! A block that is the union of two blocks meeting only at `c` is cut by deleting `c`: so it
is never a single vine (whose interior atoms are non-cut). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem block_union_darts_in_left {M : Molecule V D} {P Q : Finset V} {a b c : V}
    (hP : M.IsBlock P a c) (hQ : M.IsBlock Q c b) (hPQ : P ∩ Q = {c})
    (hU : M.IsBlock (P ∪ Q) a b) {p : V} (hp : p ∈ P) (hpc : p ≠ c) {x : D}
    (hx : M.atom x = p) (hxU : M.InGroup (P ∪ Q) x) : M.InGroup P x := by
  have hbP : b ∉ P := by
    intro hb
    have : b ∈ P ∩ Q := mem_inter.mpr ⟨hb, hQ.2.2.1⟩
    rw [hPQ] at this
    exact hQ.2.2.2.1 (mem_singleton.mp this).symm
  have hdeg : M.degIn P p = M.degIn (P ∪ Q) p := by
    by_cases hpa : p = a
    · subst hpa
      rw [(Mole.block_joint_degrees M hP).1, (Mole.block_joint_degrees M hU).1]
    · have h1 := hP.2.2.2.2.2.2.2.2.1 p hp hpa hpc
      have h2 := hU.2.2.2.2.2.2.2.2.1 p (mem_union_left _ hp) hpa (fun h => hbP (by rw [← h]; exact hp))
      rw [h1, h2]
  have heq := Vine.internal_darts_eq_of_nested_degree M (subset_union_left (s₁ := P) (s₂ := Q)) p hdeg
  have hmem : x ∈ (M.dartsAt p).filter (M.InGroup (P ∪ Q)) :=
    mem_filter.mpr ⟨(Mole.mem_dartsAt M p x).mpr hx, hxU⟩
  rw [← heq] at hmem
  exact (mem_filter.mp hmem).2

theorem block_union_erase_not_connected {M : Molecule V D} {P Q : Finset V} {a b c : V}
    (hP : M.IsBlock P a c) (hQ : M.IsBlock Q c b) (hPQ : P ∩ Q = {c})
    (hU : M.IsBlock (P ∪ Q) a b) : ¬ Vine.GroupConnected M ((P ∪ Q).erase c) := by
  intro h
  have hac : a ≠ c := hP.2.2.2.1
  have hbc : b ≠ c := hQ.2.2.2.1.symm
  have haU : a ∈ (P ∪ Q).erase c := mem_erase.mpr ⟨hac, mem_union_left _ hP.2.1⟩
  have hbU : b ∈ (P ∪ Q).erase c := mem_erase.mpr ⟨hbc, mem_union_right _ hQ.2.2.1⟩
  have hbP : b ∉ P := by
    intro hb
    have : b ∈ P ∩ Q := mem_inter.mpr ⟨hb, hQ.2.2.1⟩
    rw [hPQ] at this
    exact hbc (mem_singleton.mp this)
  have key : ∀ p q, Relation.EqvGen (Mole.induced M ((P ∪ Q).erase c)).Adj p q →
      p = q ∨ (p ∈ (P ∪ Q).erase c ∧ q ∈ (P ∪ Q).erase c ∧ (p ∈ P ↔ q ∈ P)) := by
    intro p q hpq
    induction hpq with
    | rel u v huv =>
      obtain ⟨⟨x, hxu, hxv⟩, hu, hv⟩ := (Mole.induced_adj_iff M _ _ _).mp huv
      subst hxu hxv
      have hx : M.InGroup ((P ∪ Q).erase c) x := ⟨hu, hv⟩
      have hxU : M.InGroup (P ∪ Q) x := ⟨(mem_erase.mp hx.1).2, (mem_erase.mp hx.2).2⟩
      have hmU : M.InGroup (P ∪ Q) (M.mate x) := by
        refine ⟨?_, ?_⟩
        · simpa [Molecule.mate_mate] using hxU.2
        · simpa [Molecule.mate_mate] using hxU.1
      refine Or.inr ⟨hx.1, hx.2, ⟨fun hu => ?_, fun hv => ?_⟩⟩
      · exact (block_union_darts_in_left hP hQ hPQ hU hu (mem_erase.mp hx.1).1 rfl hxU).2
      · have := block_union_darts_in_left hP hQ hPQ hU hv (mem_erase.mp hx.2).1 (x := M.mate x) rfl hmU
        simpa [Molecule.mate_mate] using this.2
    | refl u => exact Or.inl rfl
    | symm u v _ ih =>
      rcases ih with rfl | ⟨h1, h2, h3⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h2, h1, h3.symm⟩
    | trans u v w _ _ ih1 ih2 =>
      rcases ih1 with rfl | ⟨h1, h2, h3⟩
      · exact ih2
      · rcases ih2 with rfl | ⟨h4, h5, h6⟩
        · exact Or.inr ⟨h1, h2, h3⟩
        · exact Or.inr ⟨h1, h5, h3.trans h6⟩
  rcases key a b (h a haU b hbU) with hab | ⟨_, _, hi⟩
  · exact hbP (hab ▸ hP.2.1)
  · exact hbP (hi.mp hP.2.1)

end WaveTurbulence.LGSpine
