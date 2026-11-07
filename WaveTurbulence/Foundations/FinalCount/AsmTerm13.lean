/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm12
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 13: cluster sums and `iso ≤ e`.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem cluster_card_sum {M : Molecule V D} {𝒦 : Finset (Finset V)} (h : Clusters M 𝒦) :
    ∑ K ∈ 𝒦, K.card = (𝒦.biUnion id).card := by
  rw [Finset.card_biUnion]
  · simp
  · intro K hK K' hK' hne
    exact h.disj K hK K' hK' hne

/-- Every dropped atom costs one `e`-dart: `iso ≤ eDart M E` (atoms of positive degree). -/
theorem iso_le_eDart (M : Molecule V D) (E : Finset V) (hdpos : ∀ a ∈ M.atoms \ E, 1 ≤ M.deg a) :
    ((eraseSet M E).atoms.filter fun a => ¬ keepM M E a).card ≤ eDart M E := by
  unfold eDart
  -- each dropped atom has a dart whose mate sits in `E`
  have key : ∀ a ∈ (eraseSet M E).atoms.filter (fun a => ¬ keepM M E a), ∃ x : D, M.atom x = a ∧ M.atom (M.mate x) ∈ E := by
    intro a ha
    obtain ⟨haN, hk⟩ := Finset.mem_filter.1 ha
    have haM : a ∈ M.atoms \ E := by rwa [eraseSet_atoms] at haN
    obtain ⟨z, hz⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one (hdpos a haM))
    have hza : M.atom z = a := by simpa [Molecule.dartsAt] using hz
    by_contra hn
    push Not at hn
    apply hk
    unfold keepM
    refine Finset.card_pos.2 ⟨⟨z, ?_, ?_⟩, ?_⟩
    · rw [hza]; exact (Finset.mem_sdiff.1 haM).2
    · exact hn z hza
    · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]; exact hza
  set S := (eraseSet M E).atoms.filter fun a => ¬ keepM M E a with hS
  let g : S → D := fun a => M.mate (Classical.choose (key a.1 a.2))
  have hg1 : ∀ a : S, M.atom (Classical.choose (key a.1 a.2)) = a.1 := fun a => (Classical.choose_spec (key a.1 a.2)).1
  have hg2 : ∀ a : S, M.atom (M.mate (Classical.choose (key a.1 a.2))) ∈ E := fun a => (Classical.choose_spec (key a.1 a.2)).2
  calc S.card = (Finset.univ : Finset S).card := by simp
    _ ≤ (Finset.univ.filter fun x : D => M.atom x ∈ E ∧ M.atom (M.mate x) ∉ E).card := by
      refine Finset.card_le_card_of_injOn g ?_ ?_
      · intro a _
        have haM : a.1 ∈ M.atoms \ E := by
          have := (Finset.mem_filter.1 a.2).1; rwa [eraseSet_atoms] at this
        simp only [Finset.coe_filter, Finset.mem_univ, true_and]
        refine ⟨hg2 a, ?_⟩
        show M.atom (M.mate (M.mate (Classical.choose (key a.1 a.2)))) ∉ E
        rw [M.mate_mate, hg1 a]
        exact (Finset.mem_sdiff.1 haM).2
      · intro a _ b _ hab
        have : M.atom (M.mate (g a)) = M.atom (M.mate (g b)) := by rw [hab]
        have h1 : M.mate (g a) = Classical.choose (key a.1 a.2) := M.mate_mate _
        have h2 : M.mate (g b) = Classical.choose (key b.1 b.2) := M.mate_mate _
        rw [h1, h2, hg1 a, hg1 b] at this
        exact Subtype.ext this

end WaveTurbulence.FinalCountAsm
