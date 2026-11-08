/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.CoupleRootRestriction
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization

/-! Ported by source from C2-B-TOP `C2BTop.CoupleRootRate` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Root-modulated raw couples at the printed Proposition 5.1 rate

`exists_rootRawCoupleKernel_rate` (two clocks) and `exists_rootRawOneClockKernel_rate` (one clock):
main's `exists_rawCoupleKernel_upper_propositionRate` / `exists_rawOneClockKernel_upper_propositionRate`
for the raw operators carrying the root-modulated internal weight `(G.at k).value`, at the extra cost
`rootJetConstant (30d) * G.momentMass (30d)`.  Constants and thresholds precede `G`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh

/-- The common cell constant of C2-B-REG's couple restriction estimate. -/
def coupleCellConstant (d m J W M n : ℕ) (C B : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (maskedSourceSpatialConstantSpatial d m J W) * ENNReal.ofReal (C ^ n) *
    (ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W * B) ^ m *
      ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))

/-- Two-clock restriction estimate with the root-modulated weight. -/
theorem exists_rootRawCoupleKernel_restriction_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
        η < incoherenceExponent d γ →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
        ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w J W K M : ℕ,
          ∀ P : MomentumTreeData n m w, ∀ _Croot : RootInputCoordinates P,
          (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
          ∀ Q : Fin n → LayerLink d,
          (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
          1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
          ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
          ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → W + 2 * d ≤ M → 0 ≤ B →
          (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
          ∀ E : Set (Fin 2 → ℝ),
          (∀ t ∈ E, R.baseRootTimes Q ≤ t) →
          (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) →
          ∀ ζ : Circle, ∀ A : Set (Mom d),
          ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α), G.momentMass J < ⊤ →
          Fourier.mixedRestrictionNorm η J W E A
            (fun t k => (MomentumTreeData.weightedSourceCoupleKernel (P := P)) (G.at k) ζ R L γ δ Q I f t k) ≤
            ENNReal.ofReal (rootJetConstant J) *
              (coupleCellConstant d m J W M n Cₗ B * G.momentMass J) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootMaskedCoupleExtension_bound d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨Cₗ, hCₗ, C₀, hC₀, ?_⟩
  intro η hη hη₁ χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w J W K M P Croot hinputs Q hspan hg R I hI hbox f B hK hM hB hf E hE hχone ζ A α _ G
    hfin
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  choose S hScard hcover using (fun c => hloc n m w P hinputs c)
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (a : α) :
      eLpNorm (R.linkDensity L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) I) 1 ≤
      ENNReal.ofReal ((Cᵣ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
    simpa only [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P)), incoherenceCount_spatialFrequencyLinks] using
      hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) hspan I hI hbox R
  have hagree (t : E) (k : A) :
      (MomentumTreeData.fourierMaskedSourceCoupleExtension (P := P)) (G.at k) χ ζ R L γ δ Q I f S 0 t k =
        (MomentumTreeData.weightedSourceCoupleKernel (P := P)) (G.at k) ζ R L γ δ Q I f t k :=
    (MomentumTreeData.fourierMaskedSourceCoupleExtension_agrees_above (P := P)) (G.at k) hχ hc Croot ζ R L γ δ Q I hI hbox f S
      hcover hScard hLone (by omega) (by omega) hB hf
      (N := ENNReal.ofReal ((Cᵣ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)))
      ENNReal.ofReal_lt_top hroot t (hE t t.property) (hχone t t.property) k
  apply (Fourier.mixedRestrictionNorm_le_extension
    (fun t k => (MomentumTreeData.fourierMaskedSourceCoupleExtension (P := P)) (G.at k) χ ζ R L γ δ Q I f S 0 t k) hagree).trans
  exact hb L hLa n m w J W K M P Q hspan hg R I hI hbox f B hK hM hB hf S Cₗ hScard 0 ζ G hfin

/-- One-clock restriction estimate with the root-modulated weight. -/
theorem exists_rootRawOneClockKernel_restriction_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
        η < incoherenceExponent d γ →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
        ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w J W K M : ℕ,
          ∀ P : MomentumTreeData n m w, ∀ _Croot : RootInputCoordinates P,
          (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
          ∀ Q : Fin n → LayerLink d,
          (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
          1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ a : Fin 2, ∀ b : ℝ,
          ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
          ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → W + 2 * d ≤ M → 0 ≤ B →
          (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
          ∀ E : Set (Fin 2 → ℝ),
          (∀ t ∈ E, R.baseRootTimes Q ≤ t + R.oneClockShift a Q b) →
          (∀ t ∈ E, ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j) →
          (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ)
            ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) →
          ∀ ζ : Circle, ∀ A : Set (Mom d),
          ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α), G.momentMass J < ⊤ →
          Fourier.mixedRestrictionNorm η J W E A
            (fun t k => weightedSourceOneClockKernel P (G.at k) ζ R a L γ δ Q I f t k) ≤
            ENNReal.ofReal (rootJetConstant J) *
              (coupleCellConstant d m J W M n Cₗ B * G.momentMass J) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootMaskedCoupleExtension_bound d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨Cₗ, hCₗ, C₀, hC₀, ?_⟩
  intro η hη hη₁ χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w J W K M P Croot hinputs Q hspan hg R a b I hI hbox f B hK hM hB hf E hE hpass hχone
    ζ A α _ G hfin
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  choose S hScard hcover using (fun c => hloc n m w P hinputs c)
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (a' : α) :
      eLpNorm (R.linkDensity L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a')) z ξ) I) 1 ≤
      ENNReal.ofReal ((Cᵣ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
    simpa only [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P)), incoherenceCount_spatialFrequencyLinks] using
      hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a')) z ξ) hspan I hI
        hbox R
  have hagree (t : E) (k : A) :
      (MomentumTreeData.fourierMaskedSourceCoupleExtension (P := P)) (G.at k) χ ζ R L γ δ Q I f S (R.oneClockShift a Q b) t k =
        weightedSourceOneClockKernel P (G.at k) ζ R a L γ δ Q I f t k :=
    fourierMaskedSourceCoupleExtension_agrees_oneClock P (G.at k) hχ hc Croot ζ R a b L γ δ Q I hI hbox
      f S hcover hScard hLone (by omega) (by omega) hB hf
      (N := ENNReal.ofReal ((Cᵣ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)))
      ENNReal.ofReal_lt_top hroot t (hE t t.property) (hpass t t.property) (hχone t t.property) k
  apply (Fourier.mixedRestrictionNorm_le_extension
    (fun t k => (MomentumTreeData.fourierMaskedSourceCoupleExtension (P := P)) (G.at k) χ ζ R L γ δ Q I f S
      (R.oneClockShift a Q b) t k) hagree).trans
  exact hb L hLa n m w J W K M P Q hspan hg R I hI hbox f B hK hM hB hf S Cₗ hScard
    (R.oneClockShift a Q b) ζ G hfin

/-- The extra root cost is `⊤` exactly when the moment mass is; then any bound with a positive
remaining factor is trivial. -/
theorem le_top_of_momentMass_top {d n : ℕ} {α : Type} [MeasurableSpace α] (G : RootMeasure d n α)
    (J : ℕ) (h : G.momentMass J = ⊤) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (X : ℝ≥0∞) :
    X ≤ ENNReal.ofReal c * G.momentMass J * ENNReal.ofReal r := by
  rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne', ENNReal.top_mul (ENNReal.ofReal_pos.mpr hr).ne']
  exact le_top

/-- Root-modulated two-clock raw couple, printed rate (`30d, 30d`). -/
theorem exists_rootRawCoupleKernel_rate (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w : ℕ, m ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, RootInputCoordinates P →
        (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
        ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, R.baseRootTimes Q ≤ t) →
        (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) →
        ∀ ζ : Circle, ∀ A : Set (Mom d),
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α),
        Fourier.mixedRestrictionNorm η (30 * d) (30 * d) E A
          (fun t k => (MomentumTreeData.weightedSourceCoupleKernel (P := P)) (G.at k) ζ R L γ δ Q I f t k) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
            ENNReal.ofReal ((C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, C₀, hC₀, hb⟩ := exists_rootRawCoupleKernel_restriction_bound d hd
  let C₁ := maskedSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (30 * d) B Cₗ * C₀
  have hC₁ : 0 < C₁ := mul_pos (maskedSourceExponentialCoefficient_posSpatial _ _ _ _ _ _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n m w hm P Croot hinputs Q hspan hg R I hI hbox f hf E hE hχone ζ A α _ G
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hrate : 0 < (C₁ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) :=
    mul_pos (pow_pos (mul_pos hC₁ hδ) _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hLone) _)
  by_cases hfin : G.momentMass (30 * d) = ⊤
  · exact le_top_of_momentMass_top G _ hfin (rootJetConstant_pos _) hrate _
  have hraw := hb L hL n m w (30 * d) (30 * d) (40 * d) (40 * d) P Croot hinputs Q hspan hg
    R I hI hbox f B (by omega) (by omega) hB hf E hE hχone ζ A G (lt_top_iff_ne_top.mpr hfin)
  apply hraw.trans
  have habs : coupleCellConstant d m (30 * d) (30 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((C₀ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) ≤
      ENNReal.ofReal ((C₁ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
    apply (masked_source_ennreal_coefficient_leSpatial hn hm hB hCₗ.le hC₀.le hδ.le
      (Real.rpow_nonneg (zero_le_one.trans hLone) _)).trans
    apply ENNReal.ofReal_le_ofReal
    change (C₁ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) ≤ _
    exact mul_le_mul_of_nonneg_left (incoherence_rpow_le_sqrt_loss hLone hη.le hsmall)
      (pow_nonneg (mul_nonneg hC₁.le hδ.le) _)
  calc
    _ = ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
        (coupleCellConstant d m (30 * d) (30 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((C₀ * δ) ^ n *
          L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q))) := by ring
    _ ≤ _ := mul_le_mul' le_rfl habs

/-- Root-modulated one-clock raw couple, printed rate (`30d, 30d`). -/
theorem exists_rootRawOneClockKernel_rate (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w : ℕ, m ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, RootInputCoordinates P →
        (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
        ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ a : Fin 2, ∀ b : ℝ,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, R.baseRootTimes Q ≤ t + R.oneClockShift a Q b) →
        (∀ t ∈ E, ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j) →
        (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ)
          ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) →
        ∀ ζ : Circle, ∀ A : Set (Mom d),
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α),
        Fourier.mixedRestrictionNorm η (30 * d) (30 * d) E A
          (fun t k => weightedSourceOneClockKernel P (G.at k) ζ R a L γ δ Q I f t k) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
            ENNReal.ofReal ((C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, C₀, hC₀, hb⟩ := exists_rootRawOneClockKernel_restriction_bound d hd
  let C₁ := maskedSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (30 * d) B Cₗ * C₀
  have hC₁ : 0 < C₁ := mul_pos (maskedSourceExponentialCoefficient_posSpatial _ _ _ _ _ _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n m w hm P Croot hinputs Q hspan hg R a b I hI hbox f hf E hE hpass hχone ζ A α _ G
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hrate : 0 < (C₁ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) :=
    mul_pos (pow_pos (mul_pos hC₁ hδ) _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hLone) _)
  by_cases hfin : G.momentMass (30 * d) = ⊤
  · exact le_top_of_momentMass_top G _ hfin (rootJetConstant_pos _) hrate _
  have hraw := hb L hL n m w (30 * d) (30 * d) (40 * d) (40 * d) P Croot hinputs Q hspan hg
    R a b I hI hbox f B (by omega) (by omega) hB hf E hE hpass hχone ζ A G (lt_top_iff_ne_top.mpr hfin)
  apply hraw.trans
  have habs : coupleCellConstant d m (30 * d) (30 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((C₀ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) ≤
      ENNReal.ofReal ((C₁ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
    apply (masked_source_ennreal_coefficient_leSpatial hn hm hB hCₗ.le hC₀.le hδ.le
      (Real.rpow_nonneg (zero_le_one.trans hLone) _)).trans
    apply ENNReal.ofReal_le_ofReal
    change (C₁ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) ≤ _
    exact mul_le_mul_of_nonneg_left (incoherence_rpow_le_sqrt_loss hLone hη.le hsmall)
      (pow_nonneg (mul_nonneg hC₁.le hδ.le) _)
  calc
    _ = ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
        (coupleCellConstant d m (30 * d) (30 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((C₀ * δ) ^ n *
          L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q))) := by ring
    _ ≤ _ := mul_le_mul' le_rfl habs

end WaveTurbulence.Flower.IncTop