/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.GenLink

/-! # D6a PROT-PTW: the pointwise spectral chain (o82 Prop 14.2, first step)

At **fixed link times** `t`, the weighted source integrand (star-measure value, per-link weights, literal temporal
phase, leaf weight) is bounded by its envelope: the star-measure amplitude, the cell spectral amplitudes, and the product
of the weighted link factors at the same times. This is the identity chain of INC-TOP/D5b-1 (`F`-mixture, cells,
localized lattice/Fourier exchange, link factorization) run pointwise in time with general link weights; no time
integral has been taken, so pins and endpoint substitutions are allowed afterwards. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A

variable {d n m w : ℕ}

theorem enorm_finsetProd {ι : Type*} (s : Finset ι) (g : ι → ℂ) : ‖∏ i ∈ s, g i‖ₑ = ∏ i ∈ s, ‖g i‖ₑ := by
  rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  simp_rw [ofReal_norm]

/-- The weighted source integrand at fixed link times. -/
def arrayIntegrand {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (F : SpatialMeasure (PairedMomentum d n) α) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (ψ : Fin n → LPair d → ℂ) (f : Fin m → Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ, F.value (pairedLattice L p) * arrayWeight ψ p *
    sourceTemporalPhase L γ δ Q p t * ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))

/-- The links of one star frequency, one cell and one spectral variable. -/
def cellLinks {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (F : SpatialMeasure (PairedMomentum d n) α) (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (a : α) (ξ : LocalizedCellIndex n m → Fin d → ℝ) : Fin n → LayerLink d :=
  (MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (F.frequency a)) z ξ

/-- The pointwise envelope of `arrayIntegrand`: amplitudes times the absolute weighted link product. -/
def arrayEnvelope {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (F : SpatialMeasure (PairedMomentum d n) α) (ζ : Circle) (_L _γ _δ : ℝ) (Q : Fin n → LayerLink d)
    (_ψ : Fin n → LPair d → ℂ) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) (k : Mom d)
    (G : Fin n → (Fin 2 → ℝ) → LayerLink d → ℝ≥0∞) (t : Fin n → Fin 2 → ℝ) : ℝ≥0∞ :=
  ∫⁻ a, ‖F.amplitude a‖ₑ * (∑' u : SourceCellIndex S, ∫⁻ ξ,
    ‖(MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f u.1 u.2.val k ξ‖ₑ *
      ∏ i, G i (t i) (cellLinks P F Q u.2.val a ξ i)) ∂F.μ

/-- **Pointwise envelope bound.** Any per-link majorant `G` of the weighted link factors works (`G = ‖·‖ₑ` itself, or a
trivial supremum on exceptional links). -/
theorem enorm_arrayIntegrand_le {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (F : SpatialMeasure (PairedMomentum d n) α) (ζ : Circle) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (ψ : Fin n → LPair d → ℂ) {Bψ : ℝ} (hBψ : 0 ≤ Bψ)
    (hψ : ∀ i q, ‖ψ i q‖ ≤ Bψ) (f : Fin m → Mom d → ℂ) {K M : ℕ} {B : ℝ}
    (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B) (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) (k : Mom d)
    (hcover : ∀ c x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (G : Fin n → (Fin 2 → ℝ) → LayerLink d → ℝ≥0∞)
    (hG : ∀ i s A, ‖genLinkTimeFactor L γ δ A (ψ i) s‖ₑ ≤ G i s A) (t : Fin n → Fin 2 → ℝ) :
    ‖arrayIntegrand P F ζ L γ δ Q ψ f k t‖ₑ ≤ arrayEnvelope P F ζ L γ δ Q ψ f S k G t := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let lw := fun p : (Fin n × Fin 2) → Fin d → ℤ => P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))
  let cw := fun (p : (Fin n × Fin 2) → Fin d → ℤ) (u : SourceCellIndex S) =>
    P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u
  have hcw : (∑' u : SourceCellIndex S, ∑' p, ‖cw p u‖ₑ) < ⊤ :=
    (MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_lt_topSpatial (P := P)) f S hS hL hK hM hB h k
  have hsumc : Summable (fun q : SourceCellIndex S × ((Fin n × Fin 2) → Fin d → ℤ) => ‖cw q.2 q.1‖) := by
    apply tsum_enorm_ne_top_iff_summable_norm.mp
    rw [ENNReal.tsum_prod']
    exact hcw.ne
  have hlw (p : (Fin n × Fin 2) → Fin d → ℤ) : HasSum (cw p) (lw p) :=
    P.hasSum_sourceCellWeight_of_cover_at f S k _ (fun c => hcover c _)
  have hs : Summable (fun p => ‖lw p‖) := by
    have hsw : Summable (fun p => ∑' u, ‖cw p u‖) := (hsumc.prod_symm.prod).congr (fun p => rfl)
    refine hsw.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
    rw [← (hlw p).tsum_eq]
    exact norm_tsum_le_tsum_norm (hsumc.prod_symm.prod_factor p)
  -- the spatial measure as a mixture of characters
  let X := fun p : (Fin n × Fin 2) → Fin d → ℤ => arrayWeight ψ p * sourceTemporalPhase L γ δ Q p t * ((ζ : ℂ) * lw p)
  have hX (p) : ‖X p‖ ≤ Bψ ^ n * ‖lw p‖ := by
    simp only [X, norm_mul, Circle.norm_coe, one_mul]
    calc ‖arrayWeight ψ p‖ * ‖sourceTemporalPhase L γ δ Q p t‖ * ‖lw p‖ ≤ Bψ ^ n * 1 * ‖lw p‖ := by
          gcongr
          · exact norm_arrayWeight_le ψ hBψ hψ p
          · exact norm_sourceTemporalPhase_le_one L γ δ Q p t
      _ = _ := by ring
  let Gm := fun p a => F.amplitude a * (Real.fourierChar (inner ℝ (F.frequency a) (pairedLattice L p)) : ℂ) * X p
  have hi (p) : Integrable (Gm p) F.μ := (F.integrable_character (pairedLattice L p)).mul_const _
  have hn (p) : (∫ a, ‖Gm p a‖ ∂F.μ) ≤ F.mass * (Bψ ^ n * ‖lw p‖) := by
    simp only [Gm, norm_mul, Circle.norm_coe, mul_one, integral_mul_const, SpatialMeasure.mass]
    exact mul_le_mul_of_nonneg_left (hX p) (integral_nonneg fun _ => norm_nonneg _)
  have hsum : Summable (fun p => ∫ a, ‖Gm p a‖ ∂F.μ) :=
    ((hs.mul_left (Bψ ^ n)).mul_left F.mass).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hn
  have hmix : arrayIntegrand P F ζ L γ δ Q ψ f k t = ∫ a, ∑' p, Gm p a ∂F.μ := by
    rw [← (hasSum_integral_of_summable_integral_norm hi hsum).tsum_eq]
    apply tsum_congr
    intro p
    rw [integral_mul_const, ← SpatialMeasure.value]
    dsimp only [X]
    ring
  -- per star frequency: cells, then the localized Fourier exchange
  have hcell (a : α) : (∑' p, Gm p a) = F.amplitude a * ∑' u : SourceCellIndex S, ∫ ξ,
      (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f u.1 u.2.val k ξ *
        ∏ i, genLinkTimeFactor L γ δ (cellLinks P F Q u.2.val a ξ i) (ψ i) (t i) := by
    let Qa := spatialFrequencyLinks Q (F.frequency a)
    let A := fun p : (Fin n × Fin 2) → Fin d → ℤ => sourceTemporalPhaseSpatial L γ δ Qa p t * arrayWeight ψ p
    have hA (p) : ‖A p‖ ≤ Bψ ^ n := by
      simp only [A, norm_mul]
      calc _ ≤ 1 * Bψ ^ n := mul_le_mul (norm_sourceTemporalPhase_le_oneSpatial L γ δ Qa p t)
            (norm_arrayWeight_le ψ hBψ hψ p) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have h1 : (∑' p, Gm p a) = F.amplitude a * ∑' p, A p * ((ζ : ℂ) * lw p) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      simp only [Gm, X, A, Qa, sourceTemporalPhaseSpatial_eq_character]
      ring
    have hsum2 : Summable (fun q : SourceCellIndex S × ((Fin n × Fin 2) → Fin d → ℤ) =>
        A q.2 * ((ζ : ℂ) * cw q.2 q.1)) := by
      apply Summable.of_norm_bounded (hsumc.mul_left (Bψ ^ n))
      intro q
      simp only [norm_mul, Circle.norm_coe, one_mul]
      exact mul_le_mul_of_nonneg_right (hA q.2) (norm_nonneg _)
    have h2 : (∑' p, A p * ((ζ : ℂ) * lw p)) = ∑' u : SourceCellIndex S, ∑' p, A p * ((ζ : ℂ) * cw p u) := by
      calc
        _ = ∑' p, ∑' u : SourceCellIndex S, A p * ((ζ : ℂ) * cw p u) := by
          apply tsum_congr
          intro p
          rw [← (hlw p).tsum_eq, ← tsum_mul_left, ← tsum_mul_left]
        _ = _ := (hsum2.prod_symm).tsum_comm.symm.trans (by rfl)
    rw [h1, h2]
    congr 1
    apply tsum_congr
    intro u
    have h3 := P.localized_lattice_sum_eq_spectralIntegral ζ f u.1 u.2.val hLp hK hB h k A
    have h4 : (∑' p, A p * ((ζ : ℂ) * cw p u)) = ∑' p, A p * ((ζ : ℂ) * P.localizedLeafWeight f u.1 k
        (fun i j => latticePoint L (p (i, j))) * halfCellArrayWeight u.2.val (latticeMomentumArray L p)) := by
      apply tsum_congr
      intro p
      simp only [cw, MomentumTreeData.sourceCellWeight, mul_assoc]
      rfl
    rw [h4, h3]
    apply integral_congr_ae
    apply ae_of_all
    intro ξ
    dsimp only
    rw [← tsum_genLinkArraySummand hLp γ δ (cellLinks P F Q u.2.val a ξ) ψ t, ← tsum_mul_left]
    apply tsum_congr
    intro p
    rw [P.localizedSourceSpectralDensity_eq_root_link_phase ζ f u.1 u.2.val k _ ξ, genLinkArraySummand_eq,
      show cellLinks P F Q u.2.val a ξ = (MomentumTreeData.spectralLinksSpatial (P := P)) Qa u.2.val ξ from rfl,
      ← (MomentumTreeData.sourceTemporalPhase_mul_cutoff_mul_characterSpatial (P := P)) L γ δ Qa u.2.val ξ p t]
    unfold MomentumTreeData.sourceSpectralAmplitudeSpatial
    simp only [A]
    ring
  rw [hmix]
  apply (enorm_integral_le_lintegral_enorm _).trans
  unfold arrayEnvelope
  apply lintegral_mono
  intro a
  dsimp only
  rw [hcell a, enorm_mul]
  apply mul_le_mul' le_rfl
  apply (enorm_tsum_le_tsum_enorm).trans
  apply ENNReal.tsum_le_tsum
  intro u
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro ξ
  dsimp only
  rw [enorm_mul, enorm_finsetProd]
  exact mul_le_mul' le_rfl (Finset.prod_le_prod fun i _ => hG i (t i) _)

end WaveTurbulence.Flower.ProtPtw
