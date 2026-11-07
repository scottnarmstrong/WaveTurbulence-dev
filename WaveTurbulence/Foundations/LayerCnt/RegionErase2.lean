/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.RegionErase
import Mathlib.Tactic

/-! # Region erasure of couples (arbitrary tree codes) and the combined region erasure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree Reg Reg.Skeleton Links LFTwist
variable {w : ℕ}

theorem indep_pos_leaves {S : Garden w} (D : ReconstructionData S) (l m : GLeaf S.tree) (hne : l ≠ m) :
    Indep (inflatedPosition S D.tree l.toNode) (inflatedPosition S D.tree m.toNode) := by
  have h0 := leaves_incomparable (G := S) hne
  have h : IncompAddr l.1 m.1 := ⟨fun hb => h0.1 ⟨hb.1.symm, hb.2⟩, fun hb => h0.2 ⟨hb.1.symm, hb.2⟩⟩
  have h2 := inflatedPosition_incomp S D.tree l.toNode m.toNode h
  exact ⟨fun hu => h2.1 ((under_iff_below_addr _ _).mp hu), fun hu => h2.2 ((under_iff_below_addr _ _).mp hu)⟩

/-- Every other couple's coherence links lie outside the couple being erased (arbitrary tree codes). -/
theorem couple_links_outside {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (q r : SourcePair S) (hqr : q ≠ r)
    (z : Address w) (hz : z ∈ pairEndpoints ((D.couple q).linksAt
      (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))) :
    ¬ InRegion (inflatedPosition S D.tree (r.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (r.secondLeaf hS).toNode) z := by
  have hu := cpl_endpoints_under (D.couple q) _ _ z
    (Finset.mem_union_left _ hz)
  have key : ∀ (l m : GLeaf S.tree), pairOfLeaf S hS l = q → pairOfLeaf S hS m = r →
      ¬ (Under (inflatedPosition S D.tree l.toNode) z ∧ Under (inflatedPosition S D.tree m.toNode) z) := by
    intro l m hl hm ⟨h1, h2⟩
    have hne : l ≠ m := fun he => hqr (hl.symm.trans ((congrArg (pairOfLeaf S hS) he).trans hm))
    exact (indep_pos_leaves D l m hne).not_both h1 h2
  rcases hu with hu | hu
  · rintro (hr | hr)
    · exact key _ _ (pairOfLeaf_firstLeaf S hS q) (pairOfLeaf_firstLeaf S hS r) ⟨hu, hr⟩
    · exact key _ _ (pairOfLeaf_firstLeaf S hS q) (pairOfLeaf_secondLeaf S hS r) ⟨hu, hr⟩
  · rintro (hr | hr)
    · exact key _ _ (pairOfLeaf_secondLeaf S hS q) (pairOfLeaf_firstLeaf S hS r) ⟨hu, hr⟩
    · exact key _ _ (pairOfLeaf_secondLeaf S hS q) (pairOfLeaf_secondLeaf S hS r) ⟨hu, hr⟩

/-- Couple erasure keeps every other couple's coherence (arbitrary tree codes). -/
theorem cohQ_eraseCouple {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG) (r q : SourcePair S) (hq : CohQ LG D hS q) :
    CohQ (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd r) p) (D.eraseCouple r) hS q := by
  let C := collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd r) p
  have hA := collapseCouple_outAgree LG (D.decoded_couple_isSubCouple hS hd r) p hc.criterion hc.plain
  by_cases hqr : q = r
  · subst q
    unfold CohQ
    rw [D.eraseCouple_at]
    simp only [CohOn, RegCpl.linksAt, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · unfold CohQ
    rw [D.eraseCouple_other r q hqr]
    change CohOn C ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))
    intro l hl
    have ha := couple_links_outside D hS q r hqr l.1
      ((mem_pairEndpoints_iff _ _).mpr ⟨l,hl,Or.inl rfl⟩)
    have hb := couple_links_outside D hS q r hqr l.2
      ((mem_pairEndpoints_iff _ _).mpr ⟨l,hl,Or.inr rfl⟩)
    exact (hA.layer l.1 ha).symm.trans ((hq l hl).trans (hA.layer l.2 hb))

/-- Collapse the couples of a list `qs ⊆ Q`, keeping tree codes, the canonical kind and the induced pre-layering. -/
theorem eraseCouples_set {S : Garden w} (hS : S.IsPlain) {p : ℕ} {kind : Bool}
    (Q : Finset (SourcePair S)) (qs : List (SourcePair S)) (hqs : ∀ q ∈ qs, q ∈ Q)
    (LG : LayeredGarden w) (D : ReconstructionData S)
    (hd : D.Decodes hS LG.garden) (hc : CanonicalObject p kind LG)
    (hQ : ∀ q ∈ Q, CohQ LG D hS q) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ E.tree = D.tree ∧
      (∀ q ∈ qs, E.couple q = .triv) ∧ (∀ q, q ∉ qs → E.couple q = D.couple q) ∧
      inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  induction qs generalizing LG D with
  | nil =>
    refine ⟨D, LG, hd, hc, rfl, ?_, ?_, rfl⟩
    · intro q hq
      simp only [List.not_mem_nil] at hq
    · intro q _
      rfl
  | cons q qs ih =>
    have hqQ : q ∈ Q := hqs q List.mem_cons_self
    obtain ⟨E₀, LH₀, he₀, hc₀, hQ₀, htree₀, hq₀, hother₀, hcore₀⟩ :
        ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
          CanonicalObject p kind LH ∧ (∀ r ∈ Q, CohQ LH E hS r) ∧ E.tree = D.tree ∧
          E.couple q = .triv ∧ (∀ r, r ≠ q → E.couple r = D.couple r) ∧
          inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
      by_cases hq : D.couple q = .triv
      · exact ⟨D, LG, hd, hc, hQ, rfl, hq, fun _ _ => rfl, rfl⟩
      · exact ⟨D.eraseCouple q, collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p,
          D.eraseCouple_collapse_decodes hS hd q hq, canonObj_eraseCouple hc D hS hd q (hQ q hqQ),
          fun r hr => cohQ_eraseCouple LG D hS hd hc q r (hQ r hr), rfl, D.eraseCouple_at q,
          fun r hr => D.eraseCouple_other q r hr, eraseCouple_inducedPrelayer_eq LG D hS hd q hq p⟩
    obtain ⟨E, LH, he, hc', htree, htriv, hother, hcore⟩ :=
      ih (fun r hr => hqs r (List.mem_cons_of_mem _ hr)) LH₀ E₀ he₀ hc₀ hQ₀
    refine ⟨E, LH, he, hc', htree.trans htree₀, ?_, ?_, hcore.trans hcore₀⟩
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

/-- **Region erasure.** Erasing the coherent trees of `T` and couples of `Q` (only their own coherence assumed)
yields a canonical object with the same induced pre-layering and trivial attachments on `T`, `Q`. -/
theorem erase_region {S : Garden w} (hS : S.IsPlain) {p : ℕ} {kind : Bool}
    (T : Finset (GBranch S.tree)) (Q : Finset (SourcePair S))
    (LG : LayeredGarden w) (D : ReconstructionData S) (hd : D.Decodes hS LG.garden)
    (hc : CanonicalObject p kind LG) (hT : ∀ c ∈ T, CohT LG D c) (hQ : ∀ q ∈ Q, CohQ LG D hS q) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ (∀ b ∈ T, E.tree b = .nil) ∧ (∀ q ∈ Q, E.couple q = .triv) ∧
      inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  classical
  obtain ⟨E₁, LH₁, he₁, hc₁, hQ₁, hnil, -, hcpl, hcore₁⟩ :=
    eraseTrees_set hS T Q T.toList (fun b hb => Finset.mem_toList.mp hb) LG D hd hc hT hQ
  obtain ⟨E, LH, he, hc₂, htree, htriv, -, hcore₂⟩ :=
    eraseCouples_set hS Q Q.toList (fun q hq => Finset.mem_toList.mp hq) LH₁ E₁ he₁ hc₁ hQ₁
  exact ⟨E, LH, he, hc₂, fun b hb => by rw [htree]; exact hnil b (Finset.mem_toList.mpr hb),
    fun q hq => htriv q (Finset.mem_toList.mpr hq), hcore₂.trans hcore₁⟩

end WaveTurbulence.LayerCnt
