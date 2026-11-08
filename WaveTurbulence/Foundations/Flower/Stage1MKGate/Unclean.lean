/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Gate
public import WaveTurbulence.Foundations.Flower.MkMarkX.Transport

/-! # B4 STAGE1MK-GATE: stem-uncleanness is a fine′-class invariant

* `batchIso_v0Corr`: along an LF batch from a selected family (any marking), the selected collection `𝒱₀(σ)` (all of
  it, marked vines included) corresponds to `𝒱₀` of the output at the transported prescription (main's
  `vinesV0_image`/`vinesV0_preimage` at each operation's twist site `selectedMemberSite`).
* `notClean_iff_of_related`: for a stem-dependent weight, a point of a fine′ class (marking `fineMk = markIX`) is
  stem-unclean iff every point is: `X` is carried by every fine′ batch (B2e's `markInvariantBatchV_markX`, the batch
  members being unmarked for `markIX ⊇ markX`), and `𝒱₀` corresponds. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)

namespace WaveTurbulence.Flower.Stage1MKGate

variable {w : ℕ}

/-- The image of a marked set along a molecule isomorphism. -/
def imgMark {S S' : Garden w} (F : MolIso S.molecule S'.molecule) (M : Set (CLVine S)) : Set (CLVine S') :=
  {c' | ∃ c ∈ M, c'.atoms = F.img c.atoms}

theorem markTransported_imgMark {S S' : Garden w} (F : MolIso S.molecule S'.molecule) (M : Set (CLVine S)) :
    Stage1Mk.MarkTransported F M (imgMark F M) := by
  intro c c' h
  refine ⟨fun hc => ⟨c, hc, h⟩, fun ⟨c₀, hc₀, h₀⟩ => ?_⟩
  have e : c₀.atoms = c.atoms := F.img_injective (h₀.symm.trans h)
  rwa [← clVine_eq_of_atoms e]

/-- `𝒱₀(σ)` of the source and of the target correspond along `F`. -/
def V0Corr {S S' : Garden w} (F : MolIso S.molecule S'.molecule) (σ : Prescription S) : Prop :=
  (∀ c ∈ vinesV0 S σ, ∃ c' ∈ vinesV0 S' (transportPrescription F σ), c'.atoms = F.img c.atoms) ∧
  (∀ c' ∈ vinesV0 S' (transportPrescription F σ), ∃ c ∈ vinesV0 S σ, c'.atoms = F.img c.atoms)

theorem molIsoRefl_img (S : Garden w) (U : Finset (GBranch S.tree)) : (molIsoRefl S).img U = U := by
  show U.image id = U
  exact Finset.image_id

theorem v0Corr_refl (S : Garden w) (σ : Prescription S) : V0Corr (molIsoRefl S) σ := by
  rw [V0Corr, transportPrescription_refl]
  exact ⟨fun c hc => ⟨c, hc, (molIsoRefl_img S _).symm⟩, fun c hc => ⟨c, hc, (molIsoRefl_img S _).symm⟩⟩

theorem v0Corr_trans {S S' S'' : Garden w} (F : MolIso S.molecule S'.molecule)
    (G : MolIso S'.molecule S''.molecule) (σ : Prescription S) (h1 : V0Corr F σ)
    (h2 : V0Corr G (transportPrescription F σ)) : V0Corr (molIsoTrans F G) σ := by
  rw [V0Corr, ← transportPrescription_trans]
  refine ⟨fun c hc => ?_, fun c'' hc'' => ?_⟩
  · obtain ⟨c', hc', e1⟩ := h1.1 c hc
    obtain ⟨c'', hc'', e2⟩ := h2.1 c' hc'
    exact ⟨c'', hc'', by rw [MkMark.img_trans, e2, e1]⟩
  · obtain ⟨c', hc', e2⟩ := h2.2 c'' hc''
    obtain ⟨c, hc, e1⟩ := h1.2 c' hc'
    exact ⟨c, hc, by rw [MkMark.img_trans, e2, e1]⟩

/-- One LF operation from a selected family (any marking) keeps `𝒱₀` in correspondence. -/
theorem operation_v0Corr {p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i) : V0Corr (operationMolIso op) σ := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · exact v0Corr_refl A.skeleton σ
    · exact ⟨fun c hc' => (vinesV0_image (selectedMemberSite hF i) σ hc').imp fun c' h => ⟨h.1, h.2.1⟩,
        fun c' hc' => (vinesV0_preimage (selectedMemberSite hF i) σ hc').imp fun c h => ⟨h.1, h.2.1⟩⟩

/-- **Along a batch from a selected family, `𝒱₀` corresponds.** -/
theorem batchIso_v0Corr {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F) :
    ∀ (σ : Prescription A.skeleton) (Mk : Set (CLVine A.skeleton)), IsV0Fam A.family σ Mk → V0Corr F σ := by
  induction h with
  | nil A => exact fun σ _ _ => v0Corr_refl A.skeleton σ
  | skip _ _ ih => exact ih
  | @apply L A B i op J h ih =>
    intro σ Mk hF
    exact v0Corr_trans _ _ σ (operation_v0Corr hF op)
      (ih _ _ (isV0Fam_operationMk hF op (markTransported_imgMark (operationMolIso op) Mk)))

section Related
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel σf : Fin w → Option ℕ)

/-- A stem-unclean point: some vine of `𝒱₀(σ)` has its active set on the capped stem. -/
theorem not_cleanPt_iff (a : PrescribedPrimeGarden w) :
    ¬ CleanPt J a ↔ ∃ c ∈ vinesV0 a.prime.skeleton a.totalSigma, c ∈ MkMarkX.markX J a.prime := by
  simp only [CleanPt, not_forall, exists_prop, MkMarkX.mem_markX_iff]
  exact ⟨fun ⟨c, hc, hn⟩ => ⟨c, hc, (mem_vinesV0.mp hc).1.1, hn⟩, fun ⟨c, hc, _, hn⟩ => ⟨c, hc, hn⟩⟩

/-- **One fine′ batch edge keeps stem-uncleanness** (stem-dependent weight, marking `fineMk`). -/
theorem notClean_iff_of_batchReach (hS : StemDep σf kSel) {p : ℕ} {kind : Bool} {a b : PrescribedPrimeGarden w}
    (h : BatchReach (p := p) (kind := kind) a b (fineMk J pat t s kSel σf)) : ¬ CleanPt J a ↔ ¬ CleanPt J b := by
  obtain ⟨L, B, hb, -, rfl⟩ := h
  have hmk : ∀ {LG : LayeredGarden w} (A : PrimeData LG), fineMk J pat t s kSel σf A = MkMarkX.markIX J pat t s kSel A :=
    fun A => by simp only [fineMk, hS, ↓reduceIte]
  have hX := MkMarkX.markInvariantBatchV_markX J hb a.prime.prime
    (fun i => ⟨i.1, i.2.1.1, rfl, fun hx => (mem_vinesV0.mp i.2.1).2
      (by show (i.1 : CLVine _) ∈ fineMk J pat t s kSel σf a.prime; rw [hmk]; exact Or.inr hx)⟩) trivial
  have hV := batchIso_v0Corr (batchMolIso_spec hb) a.totalSigma _ (fineState_isV0FamMk a.prime a.totalSigma)
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription (transportGroupPrescription (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [not_cleanPt_iff, not_cleanPt_iff]
  constructor
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨c', hc', e⟩ := hV.1 c hc
    rw [ht] at hc'
    exact ⟨c', hc', (hX c c' e).mp hcx⟩
  · rintro ⟨c', hc', hcx⟩
    have hc'' : c' ∈ vinesV0 B.skeleton (transportPrescription (batchMolIso hb) a.totalSigma) := by
      rw [ht]; exact hc'
    obtain ⟨c, hc, e⟩ := hV.2 c' hc''
    exact ⟨c, hc, (hX c c' e).mpr hcx⟩

/-- **Stem-uncleanness is a fine′-class invariant** (stem-dependent weight, marking `fineMk`). -/
theorem notClean_iff_of_related (hS : StemDep σf kSel) {p : ℕ} {kind : Bool} {a b : PrescribedPrimeGarden w}
    (h : Related (p := p) (kind := kind) a b (fineMk J pat t s kSel σf)) : ¬ CleanPt J a ↔ ¬ CleanPt J b := by
  induction h with
  | rel x y h => exact notClean_iff_of_batchReach J pat t s kSel σf hS h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end Related

end WaveTurbulence.Flower.Stage1MKGate
