/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleStarId

/-! # FILT-COH (b): exchanging the star presentation with the lattice sum and the source profile

* `couple_star_swap`: the star weight of a coset decoration is IncTop's root-modulated presentation value; the
  presentation integral commutes with the absolutely summable lattice sum.
* `star_profile_fubini`: the presentation integral of root-modulated source profiles is the paired inverse
  profile of the joint star density (Fubini on `volume × (leaf spatial × presentation)`). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure)
open scoped ENNReal

variable {d : ℕ}

/-- **Star weight ↦ presentation mixture of lattice characters.** -/
theorem couple_star_swap {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden) {α : Type}
    [MeasurableSpace α] (G : RootMeasure d Q.links.length α) (L : ℝ) (k : Mom d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (hm : ∀ p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
      m (cosetDecoration LG.garden L k
        ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) =
        (G.at k).value (pairedLattice L p))
    (c : (Fin Q.links.length × Fin 2 → Fin d → ℤ) → ℂ) (g : (Fin Q.links.length × Fin 2 → Fin d → ℤ) → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ 1) (hg : Summable (fun p => ‖g p‖)) (A : ℂ) :
    A * ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
        m (cosetDecoration LG.garden L k
          ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) * (c p * g p) =
      ∫ a, G.base.amplitude a * IncTop.rootChar (G.root a) k *
        (A * ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          ((Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ) * c p) * g p)
        ∂G.base.μ := by
  classical
  let F : ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → α → ℂ := fun p a =>
    G.base.amplitude a * IncTop.rootChar (G.root a) k *
      (Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ) * (c p * g p)
  have hnorm : ∀ p a, ‖F p a‖ ≤ ‖G.base.amplitude a‖ * ‖g p‖ := by
    intro p a
    simp only [F, norm_mul, IncTop.norm_rootChar, Circle.norm_coe, mul_one]
    have := hc p
    have h0 := norm_nonneg (G.base.amplitude a)
    have h1 := norm_nonneg (g p)
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left h1 this) h0
  have hFm : ∀ p, AEStronglyMeasurable (F p) G.base.μ := by
    intro p
    have h1 : Measurable (fun a => IncTop.rootChar (G.root a) k) := IncTop.measurable_rootChar G.root_measurable k
    have h2 : Measurable (fun a => (Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ)) := by
      have hc' : Continuous (fun v : PairedMomentum d Q.links.length =>
          (Real.fourierChar (inner ℝ v (pairedLattice L p)) : ℂ)) := by fun_prop
      exact hc'.measurable.comp G.base.frequency_measurable
    exact (((G.amplitude_measurable.mul h1).mul h2).mul measurable_const).aestronglyMeasurable
  have hFi : ∀ p, Integrable (F p) G.base.μ := fun p =>
    (G.base.amplitude_integrable.norm.mul_const ‖g p‖).mono' (hFm p) (ae_of_all _ (hnorm p))
  have hFs : Summable (fun p => ∫ a, ‖F p a‖ ∂G.base.μ) := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun a => norm_nonneg _) (fun p => ?_)
      (hg.mul_left (∫ a, ‖G.base.amplitude a‖ ∂G.base.μ))
    rw [← integral_mul_const]
    exact integral_mono (hFi p).norm (G.base.amplitude_integrable.norm.mul_const _) (hnorm p)
  have hval : ∀ p, m (cosetDecoration LG.garden L k
      ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) * (c p * g p) =
      ∫ a, F p a ∂G.base.μ := by
    intro p
    rw [hm p, IncTop.RootMeasure.at_value, ← integral_mul_const]
  simp_rw [hval]
  rw [integral_tsum_of_summable_integral_norm hFi hFs, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [F]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  ring

/-- **Fubini for star-mixed source profiles.** -/
theorem star_profile_fubini {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {α : Type*} [MeasurableSpace α] (R : α → SymFam Q d) (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (amp : α → ℂ) (Ξ : α → Mom d) (μa : Measure α) [SFinite μa] (k : Mom d) (t : Fin 2 → ℝ)
    (hint : Integrable (fun q => starDensity hQ hG R F S amp Ξ q k)
      (volume.prod ((RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod μa))) :
    ∫ a, amp a * IncTop.rootChar (Ξ a) k * RA1Leafwise.sourceScalarProfile hQ hG (R a) F S t k ∂μa =
      pairedInverseProfile (fun lam => ∫ u, starDensity hQ hG R F S amp Ξ (lam, u) k
        ∂(RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod μa) t := by
  classical
  let μL := RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  have : SFinite μL := by
    unfold μL RA1Leafwise.leafSpatialMeasure
    infer_instance
  let f : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α) → ℂ :=
    fun q => starDensity hQ hG R F S amp Ξ q k * e2 q.1 (t 0) (t 1)
  have he2 : Continuous (fun lam : ℝ × ℝ => e2 lam (t 0) (t 1)) := by
    have := continuous_e2.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ × ℝ => (t 0, t 1)))
    exact this
  have hf : Integrable f (volume.prod (μL.prod μa)) := by
    refine hint.norm.mono' (hint.aestronglyMeasurable.mul (he2.comp_aestronglyMeasurable
      measurable_fst.aemeasurable.aestronglyMeasurable)) (ae_of_all _ fun q => ?_)
    simp only [f, norm_mul, norm_e2, mul_one, le_refl]
  have hmp := measurePreserving_prodAssoc (volume : Measure (ℝ × ℝ)) μL μa
  have hf' : Integrable (fun x => f (MeasurableEquiv.prodAssoc x)) ((volume.prod μL).prod μa) :=
    (hmp.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).2 hf
  -- the right side as one integral
  have hR : pairedInverseProfile (fun lam => ∫ u, starDensity hQ hG R F S amp Ξ (lam, u) k ∂μL.prod μa) t =
      ∫ q, f q ∂volume.prod (μL.prod μa) := by
    unfold pairedInverseProfile
    rw [integral_prod f hf]
    refine integral_congr_ae (ae_of_all _ fun lam => ?_)
    simp only [f]
    rw [integral_mul_const]
  rw [hR, ← hmp.integral_comp' f, integral_prod_symm _ hf']
  refine integral_congr_ae ?_
  filter_upwards [hf'.prod_left_ae] with a ha
  rw [integral_prod _ ha]
  simp only [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, f]
  unfold RA1Leafwise.sourceScalarProfile pairedInverseProfile
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun lam => ?_)
  simp only [starDensity_eq]
  rw [← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  ring

end WaveTurbulence.Flower.FiltCoh
