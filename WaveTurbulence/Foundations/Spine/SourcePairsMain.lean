/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourcePairsCompatible
/-! `source_second_collection_pairs_compatible`. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

theorem source_second_collection_pairs_compatible {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P Q : Object G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection)
    {v : GBranch G.tree} (hvP : v = P.upper ∨ v = P.lower) (hvQ : v = Q.upper ∨ v = Q.lower)
    {x y x' y' : GardenDart G}
    (hxy : SourceObjectJointPair P v x y) (hxy' : SourceObjectJointPair Q v x' y') :
    (x = x' ∧ y = y') ∨
      (P.atoms = Q.atoms ∧ (∃ R, P.shape = .hyper R) ∧ ∃ R, Q.shape = .hyper R) := by
  by_cases hnP : P.atoms ⊆ Q.atoms
  · exact nested_pairs hc hPm hQm hnP hvP hvQ hxy hxy'
  by_cases hnQ : Q.atoms ⊆ P.atoms
  · rcases nested_pairs hc hQm hPm hnQ hvQ hvP hxy' hxy with h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, h.2.2, h.2.1⟩
  exfalso
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises P
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises Q
  have hvPa := object_mem_of_joint P hvP
  have hvQa := object_mem_of_joint Q hvQ
  obtain ⟨_, _, hcl⟩ := Mole.molecule_overlap_classification G.molecule hM RA RB
    ⟨v, mem_inter.mpr ⟨hvPa, hvQa⟩⟩ hnP hnQ hdA hdB hiA hiB
  obtain ⟨hPsg, _⟩ := ((hc.2.2 P).mp hPm).1
  obtain ⟨hQsg, _⟩ := ((hc.2.2 Q).mp hQm).1
  rcases hcl with ⟨h1, h2, _, _⟩ | ⟨_, _, a, b, c, h2, h3, _, _, _, h5, _⟩ | ⟨hdis, _⟩
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
      exact one_joint_pair_false G hM hκ hc0 hc hPm hQm hPvc hQvc h2 h3 h5 ‹_›
  · have hv : v ∈ ({P.upper, P.lower} : Finset _) ∩ {Q.upper, Q.lower} := by
      simp only [mem_inter, mem_insert, mem_singleton]; exact ⟨hvP, hvQ⟩
    exact (Finset.disjoint_left.mp hdis) (mem_inter.mp hv).1 (mem_inter.mp hv).2

end WaveTurbulence.LGSpine
