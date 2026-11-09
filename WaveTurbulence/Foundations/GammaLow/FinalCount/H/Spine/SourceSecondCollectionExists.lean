/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSecondCollectionExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceSecondCollectionExists`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The literal secondary collection of TARGET L2101–L2104 exists on an actual molecule. 

**Low-range change (L6-HDS).** The pairs of the omission matching are DV′s of the low family (`σ = 1`, two
members of `𝒱_{γL}`; main: two vines (V)); irreflexivity is `DS.pair_degree_one`, partner uniqueness
`DS.dv_partner_unique_unordered` (N2 Thm 1.15 (F1) for the T-vine branch).
-/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open Set Finset
open scoped Classical

/-- Existence of the source's fixed omission and maximal eligible-object collection.
The only graph premise is the actual molecule condition; the matching is proved geometrically. -/
theorem exists_sourceSecondCollection {w d : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule)
    (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (F : Set (GBranch G.tree)) :
    ∃ omitted collection, Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection := by
  classical
  let R : Finset (GBranch G.tree) → Finset (GBranch G.tree) → Prop := fun S T =>
    ∃ a b, G.molecule.sigma a b = 1 ∧ ∃ hS : Src.IsSomeVine Src.γL G.molecule S a b,
      ∃ hT : Src.IsSomeVine Src.γL G.molecule T a b,
      S ∩ T = {a,b} ∧ Disjoint (↑(S ∪ T) : Set (GBranch G.tree)) F ∧
      (Src.Object.ofVine hS).HasGapKind L γ η base κ .SG ∧
      (Src.Object.ofVine hT).HasGapKind L γ η base κ .SG
  have hsym : ∀ ⦃S T⦄, R S T → R T S := by
    rintro S T ⟨a, b, hσ, hS, hT, hi, hF, hs, ht⟩
    exact ⟨a, b, hσ, hT, hS, by simpa only [Finset.inter_comm] using hi,
      by rwa [Finset.union_comm], ht, hs⟩
  have hirr : ∀ S, ¬ R S S := by
    rintro S ⟨a, b, hσ, hS, hT, hi, _, _, _⟩
    have he : S = {a,b} := by simpa only [Finset.inter_self] using hi
    have hd := (Mole.block_joint_degrees G.molecule hS.block).1
    have hp := (DS.pair_degree_one hS.block hσ).1
    rw [he] at hd
    omega
  have hu : ∀ S T U, R S T → R S U → T = U := by
    rintro S T U ⟨a, b, hσ, hS, hT, hST, _, _, _⟩ ⟨c, e, _, hS', hU, hSU, _, _, _⟩
    exact DS.dv_partner_unique_unordered hM hσ hS.block (DS.isTVine_of_sigma_one hT hσ) hS'.block hU.block hST hSU
  obtain ⟨omitted, homit, hxor⟩ := exists_matching_omission R hsym hirr hu
  let collection : Set (Src.Object Src.γL G.molecule) := {P |
    Src.eligibleSecondObject Src.γL G L γ η base κ F P ∧ P.atoms ∉ omitted ∧
      ∀ Q : Src.Object Src.γL G.molecule, Src.eligibleSecondObject Src.γL G L γ η base κ F Q →
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

end WaveTurbulence.GammaLow.FinalCount.H
