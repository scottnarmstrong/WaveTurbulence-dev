/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafScalarProfile
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafSpatialHigherEnvelope
public import WaveTurbulence.Foundations.Flower.IncTop.Top.StarPresentation

/-! # FILT-COH (b): the leaf engine for star-mixed couple densities

A star weight is a Fourier mixture over a presentation parameter `a` of a root character `e(⟨Ξ a, k⟩)` and a
lattice character; the lattice character shifts the cell modulations of the symbol (`R a`), the root character
adds `Ξ a` to the leaf root frequency. `star_leaf_profile_le` runs main's generic paired mixture estimate
(`RegAsymp.mixedRestrictionNorm_paired_spatialMixture_le`) over the product of the leaf spatial measure and the
presentation measure. Given an envelope of the symbols UNIFORM in `a` and in the modulations (`r * B λ`), the
mass separates: `(∫ wL B) × (leaf moment mass) × (∫ (1+‖Ξ‖)^N |amp|)`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory Finset WithLp Links Incoh WaveTurbulence.Fourier ClassJR
open scoped ENNReal

variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
variable {α : Type*} [MeasurableSpace α]

/-- A family of cell symbols indexed by the presentation parameter. -/
abbrev SymFam (Q : RegCpl) (d : ℕ) :=
  (ℝ × ℝ) → (Fin Q.links.length → Mom d) → (Fin Q.links.length → Mom d) →
    ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ

/-- The star-mixed scalar amplitude. -/
@[expose] def starAmplitude (R : α → SymFam Q d) (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (amp : α → ℂ)
    (q : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α)) : ℂ :=
  amp q.2.2 * RA1Leafwise.leafScalarAmplitude hQ hG (R q.2.2) F S (q.1, q.2.1)

/-- The star-mixed masked density: the root character joins the leaf root frequency. -/
@[expose] def starDensity (R : α → SymFam Q d) (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (amp : α → ℂ) (Ξ : α → Mom d)
    (q : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α))
    (k : Mom d) : ℂ :=
  maskedModulation q.2.1.1.1 (starAmplitude hQ hG R F S amp q) (∑ a, toLp 2 (q.2.1.2 a) + Ξ q.2.2) k

/-- Joint measurability of the star amplitude in all variables. -/
theorem stronglyMeasurable_starAmplitude {K M : ℕ} (R : α → SymFam Q d)
    (hR : ∀ z, StronglyMeasurable (fun p : α × ((ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) => R p.1 p.2.1 p.2.2.1 p.2.2.2 z))
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : ∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    {amp : α → ℂ} (hamp : Measurable amp) :
    StronglyMeasurable (starAmplitude hQ hG R F S amp) := by
  classical
  have hm : Measurable (fun p :
      ((Fin (2*Q.links.length+1) → Fin d → ℤ) × ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) ×
      (((ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ)) × α) =>
      if p.1.2 ∈ S p.1.1 then RA1Leafwise.leafSpectrumCoefficient F p.1.1 p.2.1.2 *
        R p.2.2 p.2.1.1 (RA1Leafwise.leafModulations hQ hG p.2.1.2).1
          (RA1Leafwise.leafModulations hQ hG p.2.1.2).2 p.1.2 else 0) := by
    apply measurable_from_prod_countable_right
    intro c
    by_cases hc : c.2 ∈ S c.1
    · simp only [hc,ite_true]
      have hcoefMap : Measurable (fun p : ((ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ)) × α =>
          (c.1,p.1.2)) := measurable_const.prodMk measurable_fst.snd
      have hcoef := (RA1Leafwise.stronglyMeasurable_leafSpectrumCoefficient
        (m := 2*Q.links.length+1) hK hB hF).comp_measurable hcoefMap
      have hscalarMap : Measurable (fun p : ((ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ)) × α =>
          (p.2,(p.1.1,RA1Leafwise.leafModulations hQ hG p.1.2))) :=
        measurable_snd.prodMk (measurable_fst.fst.prodMk
          ((RA1Leafwise.continuous_leafModulations hQ hG d).measurable.comp measurable_fst.snd))
      have hscalar := (hR c.2).comp_measurable hscalarMap
      exact (hcoef.mul hscalar).measurable
    · simp only [hc,ite_false]
      exact measurable_const
  have hp : Measurable (fun q : (ℝ × ℝ) ×
      (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α) =>
      (q.2.1.1,((q.1,q.2.1.2),q.2.2))) :=
    measurable_snd.fst.fst.prodMk ((measurable_fst.prodMk measurable_snd.fst.snd).prodMk measurable_snd.snd)
  have hcomp := (hm.comp hp).stronglyMeasurable
  have hamp' : StronglyMeasurable (fun q : (ℝ × ℝ) ×
      (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α) => amp q.2.2) :=
    (hamp.comp measurable_snd.snd).stronglyMeasurable
  convert hamp'.mul hcomp using 1
  funext q
  simp only [starAmplitude, RA1Leafwise.leafScalarAmplitude, Function.comp_apply, Pi.mul_apply]

/-- The real leaf moment weight, whose `ofReal` is main's `leafSpatialHigherEnvelope`. -/
@[expose] def leafMomentReal {n m : ℕ} (N W : ℕ) (F : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (p : RA1Leafwise.LeafSpatialSample d n m) : ℝ :=
  if p.1.2 ∈ S p.1.1 then (∏ a, Fourier.momentumBracket (NTSP.intVec (p.1.1 a))^W) *
    (∏ a, (1+‖toLp 2 (p.2 a)‖)^N) * ‖RA1Leafwise.leafSpectrumCoefficient F p.1.1 p.2‖ else 0

theorem leafMomentReal_nonneg {n m : ℕ} (N W : ℕ) (F : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (p : RA1Leafwise.LeafSpatialSample d n m) : 0 ≤ leafMomentReal N W F S p := by
  unfold leafMomentReal
  split_ifs
  · have h1 : 0 ≤ ∏ a, Fourier.momentumBracket (NTSP.intVec (p.1.1 a))^W :=
      Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
    positivity
  · exact le_rfl

theorem ofReal_leafMomentReal {n m : ℕ} (N W : ℕ) (F : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (p : RA1Leafwise.LeafSpatialSample d n m) :
    ENNReal.ofReal (leafMomentReal N W F S p) = RA1Leafwise.leafSpatialHigherEnvelope N W F S p := by
  unfold leafMomentReal RA1Leafwise.leafSpatialHigherEnvelope RA1Leafwise.leafHigherMomentWeight
  split_ifs
  · have h1 : 0 ≤ ∏ a, Fourier.momentumBracket (NTSP.intVec (p.1.1 a))^W :=
      Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul h1, ofReal_norm]
  · exact ENNReal.ofReal_zero

/-- Product measures of separated integrands. -/
theorem lintegral_prod_prod_sep {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μx : Measure X) (μy : Measure Y) (μz : Measure Z) [SFinite μy] [SFinite μz]
    {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞} {h : Z → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (c : ℝ≥0∞) :
    ∫⁻ q, f q.1 * (c * (g q.2.1 * h q.2.2)) ∂μx.prod (μy.prod μz) =
      (∫⁻ x, f x ∂μx) * (c * ((∫⁻ y, g y ∂μy) * ∫⁻ z, h z ∂μz)) := by
  have hgh : Measurable (fun u : Y × Z => c * (g u.1 * h u.2)) :=
    measurable_const.mul ((hg.comp measurable_fst).mul (hh.comp measurable_snd))
  rw [lintegral_prod_mul (f := f) (g := fun u : Y × Z => c * (g u.1 * h u.2)) hf.aemeasurable
    hgh.aemeasurable]
  congr 1
  have hm : Measurable (fun u : Y × Z => g u.1 * h u.2) :=
    (hg.comp measurable_fst).mul (hh.comp measurable_snd)
  rw [lintegral_const_mul c hm]
  congr 1
  exact lintegral_prod_mul (f := g) (g := h) hg.aemeasurable hh.aemeasurable

omit [MeasurableSpace α] in
/-- The pointwise separated bound of the star envelope. -/
theorem star_envelope_pointwise {N W : ℕ} (R : α → SymFam Q d) (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (amp : α → ℂ) (Ξ : α → Mom d) {κc r : ℝ} (hκc : 0 ≤ κc) {B : (ℝ × ℝ) → ℝ} (lam : ℝ × ℝ)
    (hq : ∀ a z β γ', ‖R a lam β γ' z‖ ≤ r * B lam)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
    (αf : Fin (2*Q.links.length+1) → Fin d → ℝ) (a : α) :
    κc * (∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W) *
        (1+‖∑ i, toLp 2 (αf i) + Ξ a‖)^N * ‖starAmplitude hQ hG R F S amp (lam, (((c, z), αf), a))‖ ≤
      (κc * r) * B lam * leafMomentReal (N+1) W F S ((c, z), αf) * ((1+‖Ξ a‖)^N * ‖amp a‖) := by
  have hcent : 0 ≤ ∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W :=
    Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
  have hfreq : (1+‖∑ i, toLp 2 (αf i) + Ξ a‖)^N ≤ (∏ i, (1+‖toLp 2 (αf i)‖)^(N+1)) * (1+‖Ξ a‖)^N := by
    have h2 := IncTop.one_add_norm_sum_le_prod Finset.univ (fun i => toLp 2 (αf i))
    have h3 := norm_add_le (∑ i, toLp 2 (αf i)) (Ξ a)
    have h5 := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ 1+‖Ξ a‖)
    have h6 := mul_nonneg (norm_nonneg (∑ i, toLp 2 (αf i))) (norm_nonneg (Ξ a))
    have h1 : 1+‖∑ i, toLp 2 (αf i) + Ξ a‖ ≤ (∏ i, (1+‖toLp 2 (αf i)‖)) * (1+‖Ξ a‖) := by
      nlinarith
    have h7 : ((∏ i, (1+‖toLp 2 (αf i)‖)) * (1+‖Ξ a‖))^N ≤
        (∏ i, (1+‖toLp 2 (αf i)‖)^(N+1)) * (1+‖Ξ a‖)^N := by
      rw [mul_pow, ← Finset.prod_pow]
      refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_)
        (by positivity)
      exact pow_le_pow_right₀ (by linarith [norm_nonneg (toLp 2 (αf i))]) (Nat.le_succ N)
    exact (pow_le_pow_left₀ (by positivity) h1 N).trans h7
  have hamp_le : ‖starAmplitude hQ hG R F S amp (lam, (((c, z), αf), a))‖ ≤
      ‖amp a‖ * ((if z ∈ S c then ‖RA1Leafwise.leafSpectrumCoefficient F c αf‖ else 0) * (r * B lam)) := by
    simp only [starAmplitude, RA1Leafwise.leafScalarAmplitude, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hq _ _ _ _) (norm_nonneg _)
    · simp
  have hA : 0 ≤ κc * (∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W) := mul_nonneg hκc hcent
  have hP : 0 ≤ (1+‖∑ i, toLp 2 (αf i) + Ξ a‖)^N := by positivity
  calc κc * (∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W) *
        (1+‖∑ i, toLp 2 (αf i) + Ξ a‖)^N * ‖starAmplitude hQ hG R F S amp (lam, (((c, z), αf), a))‖
      ≤ κc * (∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W) *
          ((∏ i, (1+‖toLp 2 (αf i)‖)^(N+1)) * (1+‖Ξ a‖)^N) *
          (‖amp a‖ * ((if z ∈ S c then ‖RA1Leafwise.leafSpectrumCoefficient F c αf‖ else 0) * (r * B lam))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfreq hA) hamp_le (norm_nonneg _) (by positivity)
    _ = _ := by unfold leafMomentReal; split_ifs <;> ring

/-- The star envelope: measurable, integrable, dominating every derivative, with separated mass. -/
theorem exists_star_envelope {N W K M : ℕ} (R : α → SymFam Q d)
    (hR : ∀ z, StronglyMeasurable (fun p : α × ((ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) => R p.1 p.2.1 p.2.2.1 p.2.2.2 z))
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {Binput Ccover : ℝ} (hK : d+2+N ≤ K) (hM : W+2*d ≤ M)
    (hBi : 0 ≤ Binput) (hF : ∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {η : ℝ} (hη : 0 ≤ η)
    (μa : Measure α) [SFinite μa] {amp : α → ℂ} (hamp : Measurable amp) {Ξ : α → Mom d}
    (hΞ : Measurable Ξ) {Mm : ℝ≥0∞}
    (hmom : (∫⁻ a, ENNReal.ofReal ((1+‖Ξ a‖)^N) * ‖amp a‖ₑ ∂μa) ≤ Mm) (hMm : Mm < ⊤)
    {r : ℝ} (hr : 0 ≤ r) {B : (ℝ × ℝ) → ℝ} (hB : Measurable B) (hBn : ∀ lam, 0 ≤ B lam)
    (hBfin : (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) < ⊤)
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ a z β γ', ‖R a lam β γ' z‖ ≤ r * B lam) :
    ∃ v : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α) → ℝ,
      Measurable v ∧ (∀ q, 0 ≤ v q) ∧
      Integrable v (volume.prod ((RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod μa)) ∧
      (∀ j ≤ N, ∀ k q, Fourier.momentumBracket k ^ W *
        ‖iteratedFDeriv ℝ j (fun k => starDensity hQ hG R F S amp Ξ q k) k‖ ≤ v q) ∧
      (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q)
        ∂volume.prod ((RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod μa)) ≤
        ENNReal.ofReal (Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) N W * r) *
          (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) *
          (ENNReal.ofReal (Ccover^Q.links.length)*
            ENNReal.ofReal (Incoh.leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^
              (2*Q.links.length+1)) * Mm := by
  classical
  let μL := RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  have : SFinite μL := by
    unfold μL RA1Leafwise.leafSpatialMeasure
    infer_instance
  let μ := μL.prod μa
  set κc := Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) N W
  have hκc : 0 ≤ κc := by
    have := zero_le_one.trans (Incoh.one_le_rootMaskDerivativeConstant d N)
    unfold κc Incoh.maskedSourceSpatialConstant
    positivity
  let ampF := starAmplitude hQ hG R F S amp
  have ha : StronglyMeasurable ampF :=
    stronglyMeasurable_starAmplitude hQ hG R hR (by omega) hBi hF S hamp
  let cq : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α) → Fin (2*Q.links.length+1) → Fin d → ℤ :=
    fun q => q.2.1.1.1
  have hc : Measurable cq := measurable_snd.fst.fst.fst
  let vf : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α) → Mom d :=
    fun q => ∑ a, toLp 2 (q.2.1.2 a) + Ξ q.2.2
  have hvf : StronglyMeasurable vf := by
    have hc' : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => ∑ a, toLp 2 (α a)) := by fun_prop
    exact ((hc'.measurable.comp measurable_snd.fst.snd).add
      (hΞ.comp measurable_snd.snd)).stronglyMeasurable
  let v := fun q => κc * (∏ i, Fourier.momentumBracket (NTSP.intVec (cq q i))^W) *
    (1+‖vf q‖)^N * ‖ampF q‖
  have hvm : Measurable v := measurable_maskedModulation_envelope N W cq hc ampF ha vf hvf
  have hvn : ∀ q, 0 ≤ v q := fun q => by
    have : 0 ≤ ∏ i, Fourier.momentumBracket (NTSP.intVec (cq q i))^W :=
      Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
    positivity
  -- the separated pointwise bound
  let w : α → ℝ := fun a => (1+‖Ξ a‖)^N * ‖amp a‖
  have hpt : ∀ᵐ q ∂(volume.prod μ), v q ≤
      (κc * r) * B q.1 * leafMomentReal (N+1) W F S q.2.1 * w q.2.2 := by
    have hb' := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (ℝ × ℝ))) (ν := μ)).ae hb
    filter_upwards [hb'] with q hq
    obtain ⟨lam, ⟨⟨c, z⟩, αf⟩, a⟩ := q
    exact star_envelope_pointwise hQ hG R F S amp Ξ hκc lam hq c z αf a
  -- the engine
  have hfin_mass : (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) ≤
      ENNReal.ofReal (κc * r) * (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) *
        (∫⁻ p, RA1Leafwise.leafSpatialHigherEnvelope (N+1) W F S p ∂μL) * Mm := by
    have hLm : Measurable (fun p => ENNReal.ofReal (leafMomentReal (N+1) W F S p)) := by
      simp_rw [ofReal_leafMomentReal]
      exact RA1Leafwise.measurable_leafSpatialHigherEnvelope (N+1) W (by omega) hBi hF S
    have hwm : Measurable (fun a => ENNReal.ofReal (w a)) :=
      ENNReal.measurable_ofReal.comp (((measurable_const.add hΞ.norm).pow_const N).mul hamp.norm)
    have hwL : Measurable (fun lam : ℝ × ℝ => wL η lam * ENNReal.ofReal (B lam)) :=
      (measurable_wL η).mul (ENNReal.measurable_ofReal.comp hB)
    calc (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ)
        ≤ ∫⁻ q, (wL η q.1 * ENNReal.ofReal (B q.1)) *
            (ENNReal.ofReal (κc * r) * (ENNReal.ofReal (leafMomentReal (N+1) W F S q.2.1) *
              ENNReal.ofReal (w q.2.2))) ∂volume.prod μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with q hq
          have hBq := hBn q.1
          have hLq := leafMomentReal_nonneg (N+1) W F S q.2.1
          have hwq : 0 ≤ w q.2.2 := by positivity
          calc wL η q.1 * ENNReal.ofReal (v q)
              ≤ wL η q.1 * ENNReal.ofReal ((κc * r) * B q.1 * leafMomentReal (N+1) W F S q.2.1 * w q.2.2) :=
                mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hq)
            _ = _ := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                  ENNReal.ofReal_mul (by positivity)]
                ring
      _ = (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) * (ENNReal.ofReal (κc * r) *
            ((∫⁻ p, ENNReal.ofReal (leafMomentReal (N+1) W F S p) ∂μL) *
              ∫⁻ a, ENNReal.ofReal (w a) ∂μa)) :=
          lintegral_prod_prod_sep volume μL μa hwL hLm hwm _
      _ ≤ (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) * (ENNReal.ofReal (κc * r) *
            ((∫⁻ p, RA1Leafwise.leafSpatialHigherEnvelope (N+1) W F S p ∂μL) * Mm)) := by
          simp_rw [ofReal_leafMomentReal]
          gcongr
          refine le_trans (le_of_eq ?_) hmom
          refine lintegral_congr fun a => ?_
          simp only [w]
          rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
      _ = _ := by ring
  have hleaf := RA1Leafwise.lintegral_leafSpatialHigherEnvelope_le (N+1) W (by omega) hM hBi hF S hcard
  have hfin : (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) < ⊤ :=
    hfin_mass.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBfin)
      (hleaf.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness)))) hMm)
  have hv : Integrable v (volume.prod μ) := integrable_of_weighted_lintegral_lt_top μ hη v hvm hvn hfin
  exact ⟨v, hvm, hvn, hv,
    fun j hj k q => weighted_norm_iteratedFDeriv_maskedModulation_le (cq q) (ampF q) (vf q) k hj,
    hfin_mass.trans (mul_le_mul' (mul_le_mul' le_rfl hleaf) le_rfl)⟩

/-- **The star leaf engine.** -/
theorem star_leaf_profile_le {N W K M : ℕ} (R : α → SymFam Q d)
    (hR : ∀ z, StronglyMeasurable (fun p : α × ((ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) => R p.1 p.2.1 p.2.2.1 p.2.2.2 z))
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {Binput Ccover : ℝ} (hK : d+2+N ≤ K) (hM : W+2*d ≤ M)
    (hBi : 0 ≤ Binput) (hF : ∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {η : ℝ} (hη : 0 ≤ η) {T : Set (Fin 2 → ℝ)} (hT : ∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1)
    (μa : Measure α) [SFinite μa] {amp : α → ℂ} (hamp : Measurable amp) {Ξ : α → Mom d}
    (hΞ : Measurable Ξ) {Mm : ℝ≥0∞}
    (hmom : (∫⁻ a, ENNReal.ofReal ((1+‖Ξ a‖)^N) * ‖amp a‖ₑ ∂μa) ≤ Mm) (hMm : Mm < ⊤)
    {r : ℝ} (hr : 0 ≤ r) {B : (ℝ × ℝ) → ℝ} (hB : Measurable B) (hBn : ∀ lam, 0 ≤ B lam)
    (hBfin : (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) < ⊤)
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ a z β γ', ‖R a lam β γ' z‖ ≤ r * B lam) :
    mixedRestrictionNorm η N W T Set.univ
      (fun t k => pairedInverseProfile (fun lam => ∫ u,
        starDensity hQ hG R F S amp Ξ (lam,u) k.val
          ∂(RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod μa) t.val) ≤
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
        (ENNReal.ofReal (Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) N W * r) *
          (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) *
          (ENNReal.ofReal (Ccover^Q.links.length)*
            ENNReal.ofReal (Incoh.leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^
              (2*Q.links.length+1)) * Mm) := by
  classical
  obtain ⟨v, hvm, hvn, hv, hbd, hmass⟩ := exists_star_envelope hQ hG R hR hK hM hBi hF S hcard hη μa hamp hΞ hmom hMm hr hB hBn hBfin hb
  let μL := RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  have : SFinite μL := by
    unfold μL RA1Leafwise.leafSpatialMeasure
    infer_instance
  let ampF := starAmplitude hQ hG R F S amp
  have ha : StronglyMeasurable ampF :=
    stronglyMeasurable_starAmplitude hQ hG R hR (by omega) hBi hF S hamp
  let cq : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α) →
      Fin (2*Q.links.length+1) → Fin d → ℤ := fun q => q.2.1.1.1
  have hc : Measurable cq := measurable_snd.fst.fst.fst
  let vf : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) × α) → Mom d :=
    fun q => ∑ a, toLp 2 (q.2.1.2 a) + Ξ q.2.2
  have hvf : StronglyMeasurable vf := by
    have hc' : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => ∑ a, toLp 2 (α a)) := by fun_prop
    exact ((hc'.measurable.comp measurable_snd.fst.snd).add
      (hΞ.comp measurable_snd.snd)).stronglyMeasurable
  have hsm (k : Mom d) : StronglyMeasurable (fun q => starDensity hQ hG R F S amp Ξ q k) := by
    have hmask : Measurable (fun c : Fin (2*Q.links.length+1) → Fin d → ℤ => sourceRootMask c k) :=
      measurable_of_countable _
    have hchar : Continuous (fun v : Mom d => (Real.fourierChar (inner ℝ v k):ℂ)) := by fun_prop
    exact (hmask.stronglyMeasurable.comp_measurable hc).mul
      (ha.mul (hchar.stronglyMeasurable.comp_measurable hvf.measurable))
  have hh := mixedRestrictionNorm_paired_spatialMixture_le (μL.prod μa) hη
    (fun k q => starDensity hQ hG R F S amp Ξ q k) v
    (fun q => (contDiff_maskedModulation (cq q) _ _).of_le (by simp))
    (fun k => hsm k)
    (fun j _hj k => (stronglyMeasurable_derivative_maskedModulation cq hc ampF ha vf hvf k j).aestronglyMeasurable)
    hv hvm hvn hbd hT
  exact hh.trans (mul_le_mul' le_rfl hmass)

/-- The star density is jointly integrable. -/
theorem integrable_starDensity {N W K M : ℕ} (R : α → SymFam Q d)
    (hR : ∀ z, StronglyMeasurable (fun p : α × ((ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) => R p.1 p.2.1 p.2.2.1 p.2.2.2 z))
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {Binput Ccover : ℝ} (hK : d+2+N ≤ K) (hM : W+2*d ≤ M)
    (hBi : 0 ≤ Binput) (hF : ∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {η : ℝ} (hη : 0 ≤ η)
    (μa : Measure α) [SFinite μa] {amp : α → ℂ} (hamp : Measurable amp) {Ξ : α → Mom d}
    (hΞ : Measurable Ξ) {Mm : ℝ≥0∞}
    (hmom : (∫⁻ a, ENNReal.ofReal ((1+‖Ξ a‖)^N) * ‖amp a‖ₑ ∂μa) ≤ Mm) (hMm : Mm < ⊤)
    {r : ℝ} (hr : 0 ≤ r) {B : (ℝ × ℝ) → ℝ} (hB : Measurable B) (hBn : ∀ lam, 0 ≤ B lam)
    (hBfin : (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) < ⊤)
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ a z β γ', ‖R a lam β γ' z‖ ≤ r * B lam) (k : Mom d) :
    Integrable (fun q => starDensity hQ hG R F S amp Ξ q k)
      (volume.prod ((RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod μa)) := by
  classical
  obtain ⟨v, _hvm, _hvn, hv, hbd, _⟩ := exists_star_envelope hQ hG R hR hK hM hBi hF S hcard hη μa hamp hΞ hmom hMm hr hB hBn hBfin hb
  let ampF := starAmplitude hQ hG R F S amp
  have ha : StronglyMeasurable ampF :=
    stronglyMeasurable_starAmplitude hQ hG R hR (by omega) hBi hF S hamp
  have hc : Measurable (fun q : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length
      (2*Q.links.length+1) × α) => q.2.1.1.1) := measurable_snd.fst.fst.fst
  have hvf : StronglyMeasurable (fun q : (ℝ × ℝ) × (RA1Leafwise.LeafSpatialSample d Q.links.length
      (2*Q.links.length+1) × α) => ∑ a, toLp 2 (q.2.1.2 a) + Ξ q.2.2) := by
    have hc' : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => ∑ a, toLp 2 (α a)) := by fun_prop
    exact ((hc'.measurable.comp measurable_snd.fst.snd).add
      (hΞ.comp measurable_snd.snd)).stronglyMeasurable
  have hmask : Measurable (fun c : Fin (2*Q.links.length+1) → Fin d → ℤ => sourceRootMask c k) :=
    measurable_of_countable _
  have hchar : Continuous (fun v : Mom d => (Real.fourierChar (inner ℝ v k):ℂ)) := by fun_prop
  have hsm := (hmask.stronglyMeasurable.comp_measurable hc).mul
      (ha.mul (hchar.stronglyMeasurable.comp_measurable hvf.measurable))
  refine hv.mono' hsm.aestronglyMeasurable (ae_of_all _ fun q => ?_)
  have h0 := hbd 0 (Nat.zero_le N) k q
  rw [norm_iteratedFDeriv_zero] at h0
  exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_momentumBracket k))).trans h0

end WaveTurbulence.Flower.FiltCoh
