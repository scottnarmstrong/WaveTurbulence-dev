/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.S1OverlapMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Overlap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.S1OverlapMain`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# Stage 1 combinatorics: the overlap dichotomy for vine-like objects

TARGET vinechainlem (L1930-L1933), proof of DH23 Lemma 8.1: two overlapping non-nested designated
vine-like objects are contained in a larger vine-like object (scenarios (b), (c) of `disjointlem`)
or are two type-V vines with the same joints meeting exactly in them (scenario (a)).


**Low-range change (L6-HDS).** Two overlapping, non-nested maximal vine-like objects are two T-vines with the same
joints and `σ = 1` (a DV′ of the low family; main: two vines (V)); partner uniqueness is `DS.dv_partner_unique_unordered`.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem overlap_dichotomy (hM : M.IsMolecule) {P Q : Src.Object Src.γL M}
    (hne : (P.atoms ∩ Q.atoms).Nonempty) (hPQ : ¬ P.atoms ⊆ Q.atoms) (hQP : ¬ Q.atoms ⊆ P.atoms) :
    (∃ W : Src.Object Src.γL M, P.atoms ∪ Q.atoms ⊆ W.atoms) ∨
    (∃ a b, M.sigma a b = 1 ∧ M.IsTVine P.atoms a b ∧ M.IsTVine Q.atoms a b ∧ P.atoms ∩ Q.atoms = {a, b}) := by
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises P
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises Q
  obtain ⟨hA, hB, hcase⟩ := Mole.molecule_overlap_classification M hM RA RB hne hPQ hQP hdA hdB hiA hiB
  obtain ⟨nP, hcP⟩ := chain_of_isBlock P hA
  obtain ⟨nQ, hcQ⟩ := chain_of_isBlock Q hB
  rcases hcase with ⟨hj, hint, hsA, hsB⟩ | ⟨hj, _, a, b, c, hjA, hjB, hab, hac, hbc, hint, _⟩ |
      ⟨hdis, ⟨T⟩⟩
  · -- scenario (a): two T-vines with the same joints and `σ = 1`
    right
    have hvP : M.IsTVine P.atoms P.upper P.lower := isTVine_of_chain_sigma hM hcP hA hsA
    have hvQ : M.IsTVine Q.atoms Q.upper Q.lower := isTVine_of_chain_sigma hM hcQ hB hsB
    refine ⟨P.upper, P.lower, hsA, hvP, ?_, hint⟩
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2] at hvQ; exact hvQ
    · rw [← h1, ← h2] at hvQ; exact DS.isTVine_swap hvQ
  · -- scenario (b): one common joint
    left
    have hcP' : Src.Chain Src.γL M P.atoms a c nP := chain_orient hcP hjA
    have hcQ' : Src.Chain Src.γL M Q.atoms c b nQ := by
      have := chain_orient hcQ (show ({Q.upper, Q.lower} : Finset V) = {c, b} by
        rw [hjB, Finset.pair_comm])
      exact this
    have hbP : M.IsBlock P.atoms a c := block_orient hA hjA
    have hbQ : M.IsBlock Q.atoms c b := block_orient hB (by rw [hjB, Finset.pair_comm])
    obtain ⟨W, hW, _, _⟩ := exists_object_union hM hcP' hcQ' hint hbP hbQ
    exact ⟨W, hW.symm ▸ Finset.Subset.refl _⟩
  · -- scenario (c): three concatenated blocks
    left
    have hcP' : Src.Chain Src.γL M P.atoms T.p0 T.p2 nP := chain_orient hcP T.left_joints
    have hcQ' : Src.Chain Src.γL M Q.atoms T.p1 T.p3 nQ := chain_orient hcQ T.right_joints
    have hbP : M.IsBlock P.atoms T.p0 T.p2 := block_orient hA T.left_joints
    have hbQ : M.IsBlock Q.atoms T.p1 T.p3 := block_orient hB T.right_joints
    have hQeq : Q.atoms = T.C1 ∪ T.C2 := T.right_union
    have hbQ' : M.IsBlock (T.C1 ∪ T.C2) T.p1 T.p3 := hQeq ▸ hbQ
    have h1ne : T.p1 ≠ T.p2 := T.block1.2.2.2.1
    have h2ne : T.p2 ≠ T.p3 := T.block2.2.2.2.1
    have hp1 : T.p1 ∈ T.C1 := T.block1.2.1
    have hp3 : T.p3 ∈ T.C2 := T.block2.2.2.1
    have HL : ∀ x : D, M.atom x ∈ T.C1 → M.atom x ≠ T.p2 → M.InGroup Q.atoms x →
        M.InGroup T.C1 x := by
      intro x hx hx2 hg
      exact block_union_darts_in_left T.block1 T.block2 T.right_inter hbQ' hx hx2 rfl (hQeq ▸ hg)
    obtain ⟨n0, n1, _, hc2⟩ := chain_split_S1Split hcQ' hQeq T.right_inter hp1 hp3 h1ne (Ne.symm h2ne) HL
    have hint : P.atoms ∩ T.C2 = {T.p2} := by
      have hmem : ∀ x, x ∈ P.atoms ↔ x ∈ T.C0 ∨ x ∈ T.C1 := by
        intro x
        exact (Eq.to_iff (congrArg (fun s => x ∈ s) T.left_union)).trans mem_union
      ext x
      constructor
      · intro hx
        obtain ⟨hxP, hx2⟩ := mem_inter.mp hx
        rcases (hmem x).mp hxP with h0 | h1
        · exact absurd hx2 (Finset.disjoint_left.mp T.exterior_disjoint h0)
        · have : x ∈ T.C1 ∩ T.C2 := mem_inter.mpr ⟨h1, hx2⟩
          rw [T.right_inter] at this
          exact this
      · intro hx
        have hx' := mem_singleton.mp hx
        rw [hx']
        have : T.p2 ∈ T.C1 ∩ T.C2 := by rw [T.right_inter]; exact mem_singleton_self _
        exact mem_inter.mpr ⟨(hmem _).mpr (Or.inr (mem_inter.mp this).1), (mem_inter.mp this).2⟩
    obtain ⟨W, hW, _, _⟩ := exists_object_union hM hcP' hc2 hint hbP T.block2
    refine ⟨W, ?_⟩
    rw [hW]
    apply Finset.union_subset subset_union_left
    intro x hx
    have hx' : x ∈ T.C1 ∪ T.C2 := hQeq ▸ hx
    rcases mem_union.mp hx' with h1 | h2
    · have hxP : x ∈ P.atoms := by rw [T.left_union]; exact mem_union_right _ h1
      exact mem_union_left _ hxP
    · exact mem_union_right _ h2

end WaveTurbulence.GammaLow.FinalCount.H
