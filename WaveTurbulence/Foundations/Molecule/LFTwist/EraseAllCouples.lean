/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CoupleErasureCoherence

/-! # Finite erasure of all coherent regular couples once the trees are nil -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

/-- A trivial slot is left alone; every other slot is collapsed by the actual C3 operation. -/
theorem eraseOneCouple {w : ℕ} {S : Garden w} (hS : S.IsPlain) {p : ℕ} {kind : Bool}
    (LG : LayeredGarden w) (D : ReconstructionData S) (hd : D.Decodes hS LG.garden)
    (hc : CanonicalObject p kind LG) (hall : AllAttachmentsCoherent LG D hS) (hn : TreesNil D)
    (q : SourcePair S) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ AllAttachmentsCoherent LH E hS ∧ E.tree = D.tree ∧
      E.couple q = .triv ∧ (∀ r, r ≠ q → E.couple r = D.couple r) ∧
      inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  by_cases hq : D.couple q = .triv
  · exact ⟨D,LG,hd,hc,hall,rfl,hq,fun _ _ => rfl,rfl⟩
  · let E := D.eraseCouple q
    let LH := collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p
    have he : E.Decodes hS LH.garden := D.eraseCouple_collapse_decodes hS hd q hq
    exact ⟨E,LH,he,hc.eraseCouple D hS hd hall q,
      eraseCouple_allAttachmentsCoherent LG D hS hd hc hn hall q,rfl,D.eraseCouple_at q,
      fun r hr => D.eraseCouple_other q r hr,eraseCouple_inducedPrelayer_eq LG D hS hd q hq p⟩

/-- Collapse any finite list of coherent couple slots, keeping the canonical kind and every core layer. -/
theorem eraseCouples_list {w : ℕ} {S : Garden w} (hS : S.IsPlain) {p : ℕ} {kind : Bool}
    (qs : List (SourcePair S)) (LG : LayeredGarden w) (D : ReconstructionData S)
    (hd : D.Decodes hS LG.garden) (hc : CanonicalObject p kind LG)
    (hall : AllAttachmentsCoherent LG D hS) (hn : TreesNil D) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ AllAttachmentsCoherent LH E hS ∧ E.tree = D.tree ∧
      (∀ q ∈ qs, E.couple q = .triv) ∧ (∀ q, q ∉ qs → E.couple q = D.couple q) ∧
      inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  induction qs generalizing LG D with
  | nil =>
    refine ⟨D,LG,hd,hc,hall,rfl,?_,?_,rfl⟩
    · intro q hq
      simp only [List.not_mem_nil] at hq
    · intro q _
      rfl
  | cons q qs ih =>
    obtain ⟨E₀,LH₀,he₀,hc₀,hall₀,htree₀,hq₀,hother₀,hcore₀⟩ := eraseOneCouple hS LG D hd hc hall hn q
    have hn₀ : TreesNil E₀ := fun b => (congrFun htree₀ b).trans (hn b)
    obtain ⟨E,LH,he,hc',hall',htree,htriv,hother,hcore⟩ := ih LH₀ E₀ he₀ hc₀ hall₀ hn₀
    refine ⟨E,LH,he,hc',hall',htree.trans htree₀,?_,?_,hcore.trans hcore₀⟩
    · intro r hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst r
        by_cases hq : q ∈ qs
        · exact htriv q hq
        · exact (hother q hq).trans hq₀
      · exact htriv r hmem
    · intro r hmem
      have hrne : r ≠ q := fun h => hmem (List.mem_cons.mpr (Or.inl h))
      have hrn : r ∉ qs := fun h => hmem (List.mem_cons.mpr (Or.inr h))
      exact (hother r hrn).trans (hother₀ r hrne)

/-- The fully collapsed assignment is the exact source identity assignment. -/
theorem eraseAllCouples {w : ℕ} {S : Garden w} (hS : S.IsPlain) {p : ℕ} {kind : Bool}
    (LG : LayeredGarden w) (D : ReconstructionData S) (hd : D.Decodes hS LG.garden)
    (hc : CanonicalObject p kind LG) (hall : AllAttachmentsCoherent LG D hS) (hn : TreesNil D) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ E = ReconstructionData.identity S ∧
      inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  classical
  obtain ⟨E,LH,he,hc',hall',htree,htriv,hother,hcore⟩ :=
    eraseCouples_list hS (Finset.univ.toList) LG D hd hc hall hn
  have hE : E = ReconstructionData.identity S := ReconstructionData.ext_tree_couple E _
    (funext (fun b => (congrFun htree b).trans (hn b)))
    (funext (fun q => htriv q (Finset.mem_toList.mpr (Finset.mem_univ q))))
  exact ⟨E,LH,he,hc',hE,hcore⟩

end WaveTurbulence.LFTwist
