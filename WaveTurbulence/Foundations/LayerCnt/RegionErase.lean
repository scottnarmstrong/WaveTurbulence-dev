/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.SkeletonExtension
import Mathlib.Tactic

/-! # Erasing a chosen set of coherent regular attachments (TARGET Remark `sublayer`, region version)

Set-indexed versions of lftwist's `eraseTrees_list` / `eraseCouples_list`: only the slots of a chosen set are erased,
and only their own coherence is assumed.  Trees are erased first, then couples (couple erasure keeps the other couples'
links outside the erased couple's region for arbitrary tree codes).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree Reg Reg.Skeleton Links LFTwist
variable {w : ℕ}

/-- Coherence of the native regular tree at `b`. -/
@[expose] def CohT {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S) (b : GBranch S.tree) : Prop :=
  CohOn LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))

/-- Coherence of the native regular couple at the leaf pair `q`. -/
@[expose] def CohQ {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain)
    (q : SourcePair S) : Prop :=
  CohOn LG ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
    (inflatedPosition S D.tree (q.secondLeaf hS).toNode))

theorem canonObj_eraseTree {S : Garden w} {LG : LayeredGarden w} {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS LG.garden) (b : GBranch S.tree) (hcoh : CohT LG D b) :
    CanonicalObject p kind (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)) := by
  cases hc with
  | garden hc => exact .garden (eraseCoherentTree_canonG LG D hS hd hc b hcoh)
  | couple hc => exact .couple (eraseCoherentTree_canonC _ D hS hd hc b hcoh)

theorem canonObj_eraseCouple {S : Garden w} {LG : LayeredGarden w} {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS LG.garden) (q : SourcePair S) (hcoh : CohQ LG D hS q) :
    CanonicalObject p kind (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p) := by
  cases hc with
  | garden hc => exact .garden (eraseCoherentCouple_canonG LG D hS hd hc q hcoh)
  | couple hc => exact .couple (eraseCoherentCouple_canonC _ D hS hd hc q hcoh)

/-- Erasing the tree at `b` keeps every other slot's coherence. -/
theorem cohT_eraseTree {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS LG.garden) (b c : GBranch S.tree) (hc : CohT LG D c) :
    CohT (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)) (D.eraseTree b) c := by
  by_cases he : c = b
  · subst c
    unfold CohT
    rw [D.eraseTree_at]
    simp only [CohOn, RegChain.linksAt, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · have hh := hc
    unfold CohT at hh ⊢
    rw [eraseTree_chain_links D b c he] at hh
    exact (cohOn_map_iff _ _ _ (eraseTree_native_layerAt LG D hS hd b) _).mp hh

theorem cohQ_eraseTree {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS LG.garden) (b : GBranch S.tree) (q : SourcePair S) (hq : CohQ LG D hS q) :
    CohQ (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)) (D.eraseTree b) hS q := by
  have hh := hq
  unfold CohQ at hh ⊢
  rw [eraseTree_couple_links D hS b q] at hh
  exact (cohOn_map_iff _ _ _ (eraseTree_native_layerAt LG D hS hd b) _).mp hh

/-- Erase the trees of a list `bs ⊆ T` (their coherence is the only coherence used). -/
theorem eraseTrees_set {S : Garden w} (hS : S.IsPlain) {p : ℕ} {kind : Bool}
    (T : Finset (GBranch S.tree)) (Q : Finset (SourcePair S))
    (bs : List (GBranch S.tree)) (hbs : ∀ b ∈ bs, b ∈ T) (LG : LayeredGarden w) (D : ReconstructionData S)
    (hd : D.Decodes hS LG.garden) (hc : CanonicalObject p kind LG)
    (hT : ∀ c ∈ T, CohT LG D c) (hQ : ∀ q ∈ Q, CohQ LG D hS q) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ (∀ q ∈ Q, CohQ LH E hS q) ∧
      (∀ b ∈ bs, E.tree b = .nil) ∧ (∀ b, b ∉ bs → E.tree b = D.tree b) ∧
      E.couple = D.couple ∧ inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  induction bs generalizing LG D with
  | nil =>
    refine ⟨D, LG, hd, hc, hQ, ?_, ?_, rfl, rfl⟩
    · intro b hb
      simp only [List.not_mem_nil] at hb
    · intro b _
      rfl
  | cons b bs ih =>
    have hbT : b ∈ T := hbs b (List.mem_cons_self)
    let E₀ := D.eraseTree b
    let LH₀ := collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)
    have he₀ : E₀.Decodes hS LH₀.garden := eraseTree_collapse_decodes D hS hd b
    have hc₀ : CanonicalObject p kind LH₀ := canonObj_eraseTree hc D hS hd b (hT b hbT)
    obtain ⟨E, LH, he, hc', hQ', hnil, hother, hcpl, hcore⟩ :=
      ih (fun c hc => hbs c (List.mem_cons_of_mem _ hc)) LH₀ E₀ he₀ hc₀
        (fun c hc => cohT_eraseTree LG D hS hd b c (hT c hc))
        (fun q hq => cohQ_eraseTree LG D hS hd b q (hQ q hq))
    refine ⟨E, LH, he, hc', hQ', ?_, ?_, hcpl, ?_⟩
    · intro c hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst c
        by_cases hb : b ∈ bs
        · exact hnil b hb
        · exact (hother b hb).trans (D.eraseTree_at b)
      · exact hnil c hmem
    · intro c hmem
      have hcne : c ≠ b := fun h => hmem (List.mem_cons.mpr (Or.inl h))
      have hcn : c ∉ bs := fun h => hmem (List.mem_cons.mpr (Or.inr h))
      exact (hother c hcn).trans (D.eraseTree_other b c hcne)
    · exact hcore.trans (eraseTree_inducedPrelayer_eq LG D hS hd b)

end WaveTurbulence.LayerCnt
