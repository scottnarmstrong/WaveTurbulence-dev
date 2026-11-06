/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.Spine.SourceDoubleVinePartner
public import WaveTurbulence.Foundations.Spine.FiniteMatchingOmission
/-! The literal secondary collection of TARGET L2101–L2104 exists on an actual molecule. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped Classical

/-- Existence of the source's fixed omission and maximal eligible-object collection.
The only graph premise is the actual molecule axiom; the matching is proved geometrically. -/
theorem exists_sourceSecondCollection {w d : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule)
    (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (F : Set (GBranch G.tree)) :
    ∃ omitted collection, SourceVine.IsSourceSecondCollection G L γ η base κ F omitted collection := by
  classical
  let R : Finset (GBranch G.tree) → Finset (GBranch G.tree) → Prop := fun S T =>
    ∃ a b, ∃ hS : G.molecule.IsVine .V S a b, ∃ hT : G.molecule.IsVine .V T a b,
      S ∩ T = {a,b} ∧ Disjoint (↑(S ∪ T) : Set (GBranch G.tree)) F ∧
      (SourceVine.Object.ofVine hS).HasGapKind L γ η base κ .SG ∧
      (SourceVine.Object.ofVine hT).HasGapKind L γ η base κ .SG
  have hsym : ∀ ⦃S T⦄, R S T → R T S := by
    rintro S T ⟨a, b, hS, hT, hi, hF, hs, ht⟩
    exact ⟨a, b, hT, hS, by simpa only [Finset.inter_comm] using hi,
      by rwa [Finset.union_comm], ht, hs⟩
  have hirr : ∀ S, ¬ R S S := by
    rintro S ⟨a, b, hS, hT, hi, _, _, _⟩
    have he : S = {a,b} := by simpa only [Finset.inter_self] using hi
    have hd := (Mole.block_joint_degrees G.molecule hS.1).1
    have hp := (Vine.isVine_joint_pair_degrees hS).1
    change G.molecule.degIn {a,b} a = 1 at hp
    rw [he] at hd
    omega
  have hu : ∀ S T U, R S T → R S U → T = U := by
    rintro S T U ⟨a, b, hS, hT, hST, _, _, _⟩ ⟨c, e, hS', hU, hSU, _, _, _⟩
    exact source_doubleVine_partner_unique_unordered G.molecule hM hS hT hS' hU hST hSU
  obtain ⟨omitted, homit, hxor⟩ := exists_matching_omission R hsym hirr hu
  let collection : Set (SourceVine.Object G.molecule) := {P |
    SourceVine.eligibleSecondObject G L γ η base κ F P ∧ P.atoms ∉ omitted ∧
      ∀ Q : SourceVine.Object G.molecule, SourceVine.eligibleSecondObject G L γ η base κ F Q →
        Q.atoms ∉ omitted → P.IsContained Q → Q.IsContained P}
  refine ⟨omitted, collection, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨T, a, b, hs, ht, hi, hF, hsg, htg⟩ := homit S hS
    exact ⟨⟨S, T, a, b, hs, ht, hi⟩, hF, hsg, htg, Or.inl rfl⟩
  · intro D hDF hfirst hsecond
    exact hxor D.first D.second
      ⟨D.upper, D.lower, D.first_vine, D.second_vine, D.overlap, hDF, hfirst, hsecond⟩
  · intro P
    rfl

end WaveTurbulence.LGSpine
