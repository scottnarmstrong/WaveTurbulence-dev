/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Expand
/-! # FL-FACE: supplement Lemma 9.1, exact raw faces on the `kernelKgen` time domain

**`faceIntegral_expand`.** Let `S` be a set of selected branching nodes, at most one per tree, all free (`fix v =
none`), none in `off`, with nonzero frequencies `ω_v = π ζ_v δ L^{2γ} Ω_v` (`nodeFreq`). Then the free-time integral
inside the frozen `kernelKgen`,
`∫ τ, (kDomainFix LG up fix).indicator (phaseProdOff L γ δ LG.garden off k) (LG.garden.extendFix fix τ)`,
equals `∏_{v ∈ S} (i ω_v)⁻¹ · ∑_{F ∈ faces S} faceSign S F · faceIntegral … F`, where each face substitutes the
selected time `t_v` by the parent time, the external top time `min (up v) (𝔏_v + 1)`, a (maximal) branching child
time or the layer floor, keeps every other constraint, and thereby adds `ω_v` to the phase at that endpoint.

**`faceCount_le`** (in `Count`): `(faces S).card ≤ 8 ^ S.card`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset MeasureTheory Set

variable {w : ℕ}

/-- Expanding a product over `S` of sums over the endpoints into a sum over the faces. -/
theorem prod_sum_faces {T : Fin w → TTree} (S : Finset (GBranch T)) {M : Type*} [CommSemiring M]
    (g : GBranch T → FaceEnd T → M) :
    ∏ v ∈ S, ∑ E ∈ endChoices v, g v E = ∑ F ∈ faces S, ∏ v ∈ S, g v (F v) := by
  have h1 : ∏ v ∈ S, ∑ E ∈ endChoices v, g v E =
      ∏ b, ∑ E ∈ (if b ∈ S then endChoices b else {FaceEnd.top}), (if b ∈ S then g b E else 1) := by
    calc ∏ v ∈ S, ∑ E ∈ endChoices v, g v E
        = ∏ b ∈ univ ∩ S, ∑ E ∈ endChoices b, g b E := by rw [Finset.univ_inter]
      _ = ∏ b, if b ∈ S then ∑ E ∈ endChoices b, g b E else 1 := (prod_ite_mem univ S _).symm
      _ = _ := prod_congr rfl fun b _ => by split_ifs <;> simp
  rw [h1, prod_univ_sum]
  refine sum_congr rfl fun F _ => ?_
  rw [prod_ite_mem univ S (fun b => g b (F b)), Finset.univ_inter]

section Layered

variable (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
  (θ : GBranch LG.garden.tree → ℝ) (S : Finset (GBranch LG.garden.tree))

/-- The `kDomainFix`-indicator × phase integrand is integrable. -/
theorem integrable_kDomainFix_integrand :
    Integrable fun τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ =>
      (kDomainFix LG up fix).indicator (phaseVec θ) (LG.garden.extendFix fix τ) :=
  integrable_indicator_comp (LG.garden.extendFix fix) (measurable_extendFix' fix) _
    (measurableSet_kDomainFix LG up fix) _ (continuous_phaseVec θ).measurable
    (fun t => (norm_phaseVec θ t).le) (fun i => (LG.layer i.1.toNode : ℝ))
    (fun τ hτ i => by
      obtain ⟨h1, h2, -, -⟩ := (hτ i.1).1 i.2
      rw [extendFix_of_none fix τ i.1 i.2] at h1 h2
      exact ⟨h1, h2⟩)

/-- Each face integrand is integrable. -/
theorem integrable_face_integrand (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree) :
    Integrable fun τ : {b : GBranch LG.garden.tree // fixSel fix S b = none} → ℝ =>
      (faceDomain LG up fix S F).indicator (phaseVec θ)
        (faceSubst LG up S F (LG.garden.extendFix (fixSel fix S) τ)) :=
  integrable_indicator_comp (fun τ => faceSubst LG up S F (LG.garden.extendFix (fixSel fix S) τ))
    ((measurable_faceSubst LG up S F).comp (measurable_extendFix' _)) _
    (measurableSet_faceDomain LG up fix S F) _ (continuous_phaseVec θ).measurable
    (fun t => (norm_phaseVec θ t).le) (fun i => (LG.layer i.1.toNode : ℝ))
    (fun τ hτ i => by
      have hi := fixSel_eq_none.1 i.2
      obtain ⟨h1, h2, -, -⟩ := (hτ.1 i.1 hi.1).1 hi.2
      have he : faceSubst LG up S F (LG.garden.extendFix (fixSel fix S) τ) i.1 = τ i := by
        simp only [faceSubst, hi.1, ↓reduceIte]
        exact extendFix_of_none _ τ i.1 i.2
      rw [he] at h1 h2
      exact ⟨h1, h2⟩)

/-- Fubini over the selected coordinates: the time integral is the integral over the remaining free times of the
unselected factor times the product of the one-dimensional selected integrals. -/
theorem integral_kDomainFix_eq_restFac (hS : SelOnePerTree S) (hfix : ∀ v ∈ S, fix v = none) :
    (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
        (kDomainFix LG up fix).indicator (phaseVec θ) (LG.garden.extendFix fix τ)) =
      ∫ ρ : {b : GBranch LG.garden.tree // fixSel fix S b = none} → ℝ,
        restFac LG up fix θ S (LG.garden.extendFix (fixSel fix S) ρ) *
          ∏ i : S, ∫ u : ℝ, sliceFac LG up θ i.1 (LG.garden.extendFix (fixSel fix S) ρ) u := by
  have hmp := measurePreserving_splitEquiv fix S hfix
  set f : ({b : GBranch LG.garden.tree // fix b = none} → ℝ) → ℂ := fun τ =>
    (kDomainFix LG up fix).indicator (phaseVec θ) (LG.garden.extendFix fix τ) with hf
  rw [← hmp.integral_comp' f]
  have hint : Integrable (fun x => f (splitEquiv fix S hfix x)) ((volume : Measure (S → ℝ)).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hmp.integrable_comp_emb (splitEquiv fix S hfix).measurableEmbedding).2
      (integrable_kDomainFix_integrand LG up fix θ)
  rw [Measure.volume_eq_prod, integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  simp only [hf, integrand_split LG up fix θ S hS hfix]
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod
    (fun (i : S) (u : ℝ) => sliceFac LG up θ i.1 (LG.garden.extendFix (fixSel fix S) ρ) u)]

/-- The unselected factor times the cells of a face is the face integrand at the remaining free times. -/
theorem restFac_mul_prod_cellFac (hS : SelOnePerTree S) (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree)
    (hF : F ∈ faces S) (t₀ : GBranch LG.garden.tree → ℝ) :
    restFac LG up fix θ S t₀ * ∏ v ∈ S, cellFac LG up θ v (F v) t₀ =
      (faceDomain LG up fix S F).indicator (phaseVec θ) (faceSubst LG up S F t₀) := by
  set t := faceSubst LG up S F t₀ with ht
  have hag : ∀ b ∉ S, t b = t₀ b := fun b hb => by simp only [ht, faceSubst, hb, ↓reduceIte]
  have hsel : ∀ v ∈ S, t v = endVal LG up v t₀ (F v) := fun v hv => by
    simp only [ht, faceSubst, hv, ↓reduceIte]
  have hdom : t ∈ faceDomain LG up fix S F ↔
      t₀ ∈ restDomain LG up fix S ∧ ∀ v ∈ S, faceCell LG up v (F v) t₀ :=
    and_congr (restDomain_congr LG up fix S hag)
      (forall₂_congr fun v hv => faceCell_congr LG up hS hv hag (mem_faces hF hv))
  rw [Set.indicator_apply]
  by_cases hA : t₀ ∈ restDomain LG up fix S ∧ ∀ v ∈ S, faceCell LG up v (F v) t₀
  · rw [ite_eq_left (hdom.2 hA), phaseVec_split LG θ S t, restFac, ite_eq_left hA.1]
    have h1 : (∏ v ∈ S, Complex.exp (((θ v * t v : ℝ) : ℂ) * Complex.I)) =
        ∏ v ∈ S, cellFac LG up θ v (F v) t₀ :=
      prod_congr rfl fun v hv => by rw [cellFac, ite_eq_left (hA.2 v hv), hsel v hv]
    have h2 : (∏ b ∈ Sᶜ, Complex.exp (((θ b * t b : ℝ) : ℂ) * Complex.I)) =
        ∏ b ∈ Sᶜ, Complex.exp (((θ b * t₀ b : ℝ) : ℂ) * Complex.I) :=
      prod_congr rfl fun b hb => by rw [hag b (mem_compl.1 hb)]
    rw [h1, h2, mul_comm]
  · rw [ite_eq_right (fun h => hA (hdom.1 h))]
    rcases not_and_or.1 hA with h | h
    · rw [restFac, ite_eq_right h, zero_mul]
    · obtain ⟨v, hv⟩ := not_forall.1 h
      obtain ⟨hvS, hv'⟩ := Classical.not_imp.1 hv
      rw [prod_eq_zero hvS (by rw [cellFac, ite_eq_right hv']), mul_zero]

/-- **Supplement Lemma 9.1 (exact raw faces), for a general phase product `phaseVec θ`.** For selected free
branching nodes, at most one per tree, with nonzero frequencies `θ_v`, the free-time integral of the
`kDomainFix`-indicator × `phaseVec θ` integrand equals `∏_{v ∈ S} (i θ_v)⁻¹` times the signed sum of the face
integrals over `faces S`. -/
theorem faceIntegral_expand_freq (hS : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a = b)
    (hfix : ∀ v ∈ S, fix v = none) (hθ : ∀ v ∈ S, θ v ≠ 0) :
    (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
        (kDomainFix LG up fix).indicator (phaseVec θ) (LG.garden.extendFix fix τ)) =
      (∏ v ∈ S, (Complex.I * θ v)⁻¹) * ∑ F ∈ faces S, faceSign S F * faceIntegralFreq LG up fix θ S F := by
  rw [integral_kDomainFix_eq_restFac LG up fix θ S hS hfix]
  have hρ : ∀ ρ : {b : GBranch LG.garden.tree // fixSel fix S b = none} → ℝ,
      restFac LG up fix θ S (LG.garden.extendFix (fixSel fix S) ρ) *
          ∏ i : S, ∫ u : ℝ, sliceFac LG up θ i.1 (LG.garden.extendFix (fixSel fix S) ρ) u =
        (∏ v ∈ S, (Complex.I * θ v)⁻¹) *
          ∑ F ∈ faces S, faceSign S F * (faceDomain LG up fix S F).indicator
            (phaseVec θ) (faceSubst LG up S F (LG.garden.extendFix (fixSel fix S) ρ)) := by
    intro ρ
    set t₀ := LG.garden.extendFix (fixSel fix S) ρ
    have h1 : ∀ v ∈ S, ∫ u : ℝ, sliceFac LG up θ v t₀ u =
        (Complex.I * θ v)⁻¹ *
          ∑ E ∈ endChoices v, (if E.isUpper then (1 : ℂ) else -1) * cellFac LG up θ v E t₀ :=
      fun v hv => integral_slice_faces LG up v t₀ _ (hθ v hv)
    rw [prod_coe_sort S (fun v => ∫ u : ℝ, sliceFac LG up θ v t₀ u), prod_congr rfl h1,
      prod_mul_distrib, prod_sum_faces S, mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun F hF => ?_
    rw [prod_mul_distrib, ← restFac_mul_prod_cellFac LG up fix θ S hS F hF t₀, faceSign]
    ring
  refine (integral_congr_ae (Filter.Eventually.of_forall hρ)).trans ?_
  rw [integral_const_mul, integral_finsetSum (faces S) fun F _ =>
    (integrable_face_integrand LG up fix θ S F).const_mul (faceSign S F)]
  congr 1
  refine sum_congr rfl fun F _ => ?_
  rw [integral_const_mul]
  rfl

/-- **Supplement Lemma 9.1 (exact raw faces) on the `kernelKgen` time domain.** For selected free branching nodes,
at most one per tree, outside `off` and with nonzero frequencies `ω_v = π ζ_v δ L^{2γ} Ω_v`, the free-time integral
of the `kDomainFix`-indicator × `phaseProdOff` integrand equals `∏_{v ∈ S} (i ω_v)⁻¹` times the signed sum of the
face integrals over `faces S` (at most `8 ^ #S` faces, `faceCount_le`). -/
theorem faceIntegral_expand (L γ δ : ℝ) {d : ℕ} (off : Finset (GBranch LG.garden.tree))
    (k : GNode LG.garden.tree → Mom d) (hS : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a = b)
    (hfix : ∀ v ∈ S, fix v = none) (hoff : ∀ v ∈ S, v ∉ off) (hω : ∀ v ∈ S, nodeFreq L γ δ LG.garden k v ≠ 0) :
    (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
        (kDomainFix LG up fix).indicator (phaseProdOff L γ δ LG.garden off k) (LG.garden.extendFix fix τ)) =
      (∏ v ∈ S, (Complex.I * nodeFreq L γ δ LG.garden k v)⁻¹) *
        ∑ F ∈ faces S, faceSign S F * faceIntegral L γ δ LG up fix off k S F := by
  have hfreq : ∀ v ∈ S, offFreq L γ δ LG.garden off k v = nodeFreq L γ δ LG.garden k v := fun v hv => by
    simp only [offFreq, hoff v hv, ↓reduceIte]
  have hface : ∀ F, faceIntegral L γ δ LG up fix off k S F =
      faceIntegralFreq LG up fix (offFreq L γ δ LG.garden off k) S F := fun F => by
    unfold faceIntegral faceIntegralFreq
    rw [phaseProdOff_eq_phaseVec]
  rw [phaseProdOff_eq_phaseVec, faceIntegral_expand_freq LG up fix _ S hS hfix fun v hv => (hfreq v hv).symm ▸ hω v hv,
    prod_congr rfl fun v hv => by rw [hfreq v hv]]
  simp only [hface]

end Layered

end WaveTurbulence.Flower.FlFace
