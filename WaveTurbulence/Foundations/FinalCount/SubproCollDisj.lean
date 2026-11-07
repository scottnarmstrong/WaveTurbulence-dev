/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproInterleaved
import Mathlib.Tactic

/-!
# S4-DISJ goal 1: atom-disjointness of the second collection (TARGET L2175)

For the literal source second collection `collection` of lg-spine (`IsSourceSecondCollection`: maximal eligible objects, one vine of
each SG double vine omitted), two members have equal or disjoint atom sets. The three cases of the overlap classification
(`disjointlem`): same joints (the diamond / double-vine contradiction), one common joint (one-joint union), and interleaved
(`interleaved_false`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

/-- Nested members of the second collection have equal atom sets (maximality). -/
theorem collection_nested_eq {w d : ℕ} {G : Garden w} {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)}
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P Q : Object G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection) (hsub : P.atoms ⊆ Q.atoms) :
    P.atoms = Q.atoms := by
  obtain ⟨hQel, hQo, _⟩ := (hc.2.2 Q).mp hQm
  obtain ⟨_, _, hPmax⟩ := (hc.2.2 P).mp hPm
  by_contra heq
  have hlt : P.atoms.card < Q.atoms.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩)
  have h2 := hPmax Q hQel hQo (object_contained_of_card_lt' P Q hsub hlt)
  exact absurd (Finset.card_le_card (Object.contained_atoms_subset Q P h2)) (by omega)

/-- **Pairwise atom-disjointness of the source second collection.** -/
theorem collection_atoms_eq_or_disjoint {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P Q : Object G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection) :
    P.atoms = Q.atoms ∨ Disjoint P.atoms Q.atoms := by
  by_cases hdis : Disjoint P.atoms Q.atoms
  · exact Or.inr hdis
  left
  by_cases hnP : P.atoms ⊆ Q.atoms
  · exact collection_nested_eq hc hPm hQm hnP
  by_cases hnQ : Q.atoms ⊆ P.atoms
  · exact (collection_nested_eq hc hQm hPm hnQ).symm
  exfalso
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises P
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises Q
  have hne : (P.atoms ∩ Q.atoms).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hdis
  obtain ⟨hAblk, hBblk, hcl⟩ := Mole.molecule_overlap_classification G.molecule hM RA RB hne hnP hnQ hdA hdB
    hiA hiB
  obtain ⟨hPsg, _⟩ := ((hc.2.2 P).mp hPm).1
  obtain ⟨hQsg, _⟩ := ((hc.2.2 Q).mp hQm).1
  rcases hcl with ⟨h1, h2, _, _⟩ | ⟨_, _, a, b, c, h2, h3, _, _, _, h5, hU12⟩ | ⟨_, ⟨T⟩⟩
  · have hQj : (Q.upper = P.upper ∧ Q.lower = P.lower) ∨ (Q.upper = P.lower ∧ Q.lower = P.upper) := by
      rcases Mole.finset_pair_eq_pair_iff.mp h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1.symm, e2.symm⟩
      · exact Or.inr ⟨e2.symm, e1.symm⟩
    by_cases hhyp : (∃ R, P.shape = .hyper R) ∨ (∃ R, Q.shape = .hyper R)
    · exact object_diamond_false hM h2 hQj hnP hnQ hhyp
    · push Not at hhyp
      have hPvc : ∃ h, P.shape = .vc h := (object_shape_cases P).resolve_right (by
        rintro ⟨R, hR⟩; exact hhyp.1 R hR)
      have hQvc : ∃ h, Q.shape = .vc h := (object_shape_cases Q).resolve_right (by
        rintro ⟨R, hR⟩; exact hhyp.2 R hR)
      exact ordinary_diamond_false G hM hκ hc0 hc hPm hQm hPvc hQvc h2 hQj hnP hnQ hPsg hQsg
  · by_cases hhyp : (∃ R, P.shape = .hyper R) ∨ (∃ R, Q.shape = .hyper R)
    · have hcP : P.upper = c ∨ P.lower = c := by
        have : c ∈ ({P.upper, P.lower} : Finset _) := by rw [h2]; simp
        simpa [eq_comm] using this
      have hcQ : Q.upper = c ∨ Q.lower = c := by
        have : c ∈ ({Q.upper, Q.lower} : Finset _) := by rw [h3]; simp
        simpa [eq_comm] using this
      exact object_one_joint_hyper_false hM hcP hcQ h5 hhyp
    · push Not at hhyp
      have hPvc : ∃ h, P.shape = .vc h := (object_shape_cases P).resolve_right (by
        rintro ⟨R, hR⟩; exact hhyp.1 R hR)
      have hQvc : ∃ h, Q.shape = .vc h := (object_shape_cases Q).resolve_right (by
        rintro ⟨R, hR⟩; exact hhyp.2 R hR)
      exact one_joint_pair_false G hM hκ hc0 hc hPm hQm hPvc hQvc h2 h3 h5 hU12
  · have hPvc : ∃ h, P.shape = .vc h := (object_shape_cases P).resolve_right (by
      rintro ⟨R, hR⟩
      have h1 := object_hyper_degIn P ⟨R, hR⟩ (Or.inl rfl)
      have h2 := (Mole.block_joint_degrees G.molecule hAblk).1
      omega)
    have hQvc : ∃ h, Q.shape = .vc h := (object_shape_cases Q).resolve_right (by
      rintro ⟨R, hR⟩
      have h1 := object_hyper_degIn Q ⟨R, hR⟩ (Or.inl rfl)
      have h2 := (Mole.block_joint_degrees G.molecule hBblk).1
      omega)
    exact interleaved_false G hM hκ hc0 hc hPm hQm hPvc hQvc T

end WaveTurbulence.Subpro
