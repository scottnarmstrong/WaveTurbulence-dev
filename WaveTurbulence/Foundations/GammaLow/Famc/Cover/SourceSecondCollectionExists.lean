/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.Spine.SourceThreeBlockExclusion
public import WaveTurbulence.Foundations.Molecule.VineNestedBlockRecognition
public import WaveTurbulence.Foundations.Spine.FiniteMatchingOmission
/-! # The source second collection exists, over `𝒱_γ` (packet L5c)

Main's `Spine/SourceDoubleVinePartner.lean` and `Spine/SourceSecondCollectionExists.lean`, sha256 in
`COPIED-SHA256SUMS`, for `DV′` (L6's `Src.DoubleVine`: two members of `𝒱_γ` with `σ = 1` sharing exactly both
joints). Partner uniqueness: three such members at the same joints would saturate a component
(`no_three_joint_blocks`, using `degIn {a, b} a = σ = 1` and the interior connectivity `FamFacts.interior_connected`
in place of main's type-(V) facts). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Set Finset WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine (no_three_joint_blocks exists_matching_omission)

variable {γv : ℝ}

/-- Three distinct `𝒱_γ` members with `σ = 1` at the same joints would saturate a component (main
`source_doubleVine_partner_unique`). -/
theorem source_doubleVine_partner_unique (hfam : FamFacts γv) {V D : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] (M : Molecule V D) (hM : M.IsMolecule) {S T U : Finset V} {a b : V}
    (hS : IsSomeVine γv M S a b) (hT : IsSomeVine γv M T a b) (hU : IsSomeVine γv M U a b)
    (hσ : M.sigma a b = 1) (hST : S ∩ T = {a, b}) (hSU : S ∩ U = {a, b}) : T = U := by
  have hSB := isBlock_of_isSomeVine hS
  have hTB := isBlock_of_isSomeVine hT
  have hUB := isBlock_of_isSomeVine hU
  by_cases hTU : T ⊆ U
  · exact Vine.nested_blocks_both_joints_eq M hTB hUB (isSomeVine_connected hU) hTU hTB.2.1 hTB.2.2.1
  · have hInt := Mole.block_same_joints_intersection M hM hTB hUB hTU (hfam.interior_connected _ hT)
    have hpa : M.degIn {a, b} a = 1 := (block_degIn_pair_eq_sigma hSB).trans hσ
    have hpb : M.degIn {a, b} b = 1 := by
      have h := block_degIn_pair_eq_sigma (Mole.block_swap_joints M hSB)
      rw [Finset.pair_comm, sigma_comm] at h
      exact h.trans hσ
    exact (no_three_joint_blocks M hM hSB hTB hUB hST hSU hInt (by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact hpa
      · exact (mem_singleton.mp hv).symm ▸ hpb)).elim

/-- Partner uniqueness does not depend on the ordering of the source joints. -/
theorem source_doubleVine_partner_unique_unordered (hfam : FamFacts γv) {V D : Type} [DecidableEq V]
    [Fintype D] [DecidableEq D] (M : Molecule V D) (hM : M.IsMolecule) {S T U : Finset V} {a b c e : V}
    (hσ : M.sigma a b = 1) (hS : IsSomeVine γv M S a b) (hT : IsSomeVine γv M T a b)
    (hS' : IsSomeVine γv M S c e) (hU : IsSomeVine γv M U c e)
    (hST : S ∩ T = {a, b}) (hSU : S ∩ U = {c, e}) : T = U := by
  have hj := Vine.block_joints_unique M (isBlock_of_isSomeVine hS) (isBlock_of_isSomeVine hS')
  have hj' : ({a, b} : Set V) = {c, e} := by
    simpa only [Finset.coe_pair] using congrArg (fun s : Finset V => (s : Set V)) hj
  rcases Set.pair_eq_pair_iff.mp hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact source_doubleVine_partner_unique hfam M hM hS hT hU hσ hST hSU
  · apply source_doubleVine_partner_unique hfam M hM hS hT (isSomeVine_swap hU) hσ hST
    simpa only [Finset.pair_comm] using hSU

/-- Existence of the source's fixed omission and maximal eligible-object collection over `𝒱_γ` (main
`exists_sourceSecondCollection`). -/
theorem exists_sourceSecondCollection (hfam : FamFacts γv) {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (F : Set (GBranch G.tree)) :
    ∃ omitted collection, IsSourceSecondCollection γv G L γ η base κ F omitted collection := by
  classical
  let R : Finset (GBranch G.tree) → Finset (GBranch G.tree) → Prop := fun S T =>
    ∃ a b, ∃ _ : G.molecule.sigma a b = 1, ∃ hS : IsSomeVine γv G.molecule S a b,
      ∃ hT : IsSomeVine γv G.molecule T a b,
      S ∩ T = {a, b} ∧ Disjoint (↑(S ∪ T) : Set (GBranch G.tree)) F ∧
      (Object.ofVine hS).HasGapKind L γ η base κ .SG ∧
      (Object.ofVine hT).HasGapKind L γ η base κ .SG
  have hsym : ∀ ⦃S T⦄, R S T → R T S := by
    rintro S T ⟨a, b, hσ, hS, hT, hi, hF, hs, ht⟩
    exact ⟨a, b, hσ, hT, hS, by simpa only [Finset.inter_comm] using hi,
      by rwa [Finset.union_comm], ht, hs⟩
  have hirr : ∀ S, ¬ R S S := by
    rintro S ⟨a, b, hσ, hS, hT, hi, _, _, _⟩
    have he : S = {a, b} := by simpa only [Finset.inter_self] using hi
    have hSB := isBlock_of_isSomeVine hS
    have hd := (Mole.block_joint_degrees G.molecule hSB).1
    have hp := (block_degIn_pair_eq_sigma hSB).trans hσ
    rw [he] at hd
    omega
  have hu : ∀ S T U, R S T → R S U → T = U := by
    rintro S T U ⟨a, b, hσ, hS, hT, hST, _, _, _⟩ ⟨c, e, _, hS', hU, hSU, _, _, _⟩
    exact source_doubleVine_partner_unique_unordered hfam G.molecule hM hσ hS hT hS' hU hST hSU
  obtain ⟨omitted, homit, hxor⟩ := exists_matching_omission R hsym hirr hu
  let collection : Set (Object γv G.molecule) := {P |
    eligibleSecondObject γv G L γ η base κ F P ∧ P.atoms ∉ omitted ∧
      ∀ Q : Object γv G.molecule, eligibleSecondObject γv G L γ η base κ F Q →
        Q.atoms ∉ omitted → P.IsContained Q → Q.IsContained P}
  refine ⟨omitted, collection, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨T, a, b, hσ, hs, ht, hi, hF, hsg, htg⟩ := homit S hS
    exact ⟨⟨S, T, a, b, hσ, hs, ht, hi⟩, hF, hsg, htg, Or.inl rfl⟩
  · intro D hDF hfirst hsecond
    exact hxor D.first D.second
      ⟨D.upper, D.lower, D.sigma_one, D.first_vine, D.second_vine, D.overlap, hDF, hfirst, hsecond⟩
  · intro P
    rfl

end WaveTurbulence.GammaLow.Famc
