/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltGate.CoupleAgree
public import WaveTurbulence.Foundations.Flower.FiltGate.CellQuarter
public import WaveTurbulence.Foundations.Flower.FiltGate.Statements
public import WaveTurbulence.Foundations.Flower.IncTop.Top.CoupleRootRate

/-! # D5b-3 FILT-GATE: filtered root-modulated raw couples at both gate weights

- `exists_coupleExtension_gate_decayFilt`: the cell bound for `(θ, c) ∈ {(η, 0), (1/4, 4d)}` (`GateWeight`): D5b-2's
  `exists_coupleExtension_cutoffUniform_decayFilt` at `θ = η`, `CellQuarter` at `θ = 1/4`, one threshold.
- Twins of INC-TOP `Top/CoupleRootRate` (copied by source, sha256 in COPIED-SHA256SUMS):
  `exists_rootRawCoupleKernel_restriction_boundFilt`, `exists_rootRawOneClockKernel_restriction_boundFilt`,
  `exists_rootRawCoupleKernel_rateFilt`, `exists_rootRawOneClockKernel_rateFilt`. The weight pair `(θ, c)` is chosen
  after `L`; link `i` carries `φ i` with `PresentedMult L Kφ (φ i)`; the rates are INC-TOP's with `C` replaced by
  `Kφ * C` and the loss `L^c`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.Incoh WaveTurbulence.Flower.IncTop WaveTurbulence.Flower.FiltSrc
  WaveTurbulence.Flower.FiltProd WaveTurbulence.Flower.FiltLink

/-- **The filtered couple cell bound at both gate weights** (o82 Prop 15.1 at `θ = η`, Lemma 16.1 at `θ = 1/4`). -/
theorem exists_coupleExtension_gate_decayFilt (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c →
        ∀ n : ℕ, ∀ Q : Fin n → LayerLink d, 1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        Fourier.timeFourierNorm θ (RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I) ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) * L ^ c) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_coupleExtension_cutoffUniform_decayFilt d hd
  obtain ⟨C₂, hC₂, h₂⟩ := exists_coupleExtension_quarter_decayFilt d hd
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
  intro η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, h₁⟩ := h₁ η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, hL₂, h₂⟩ := h₂ η hη χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL θ c hθc n Q hg hspan K hK φ hφ I hI hbox R
  have hLone : 1 ≤ L := hL₁.trans ((le_max_left _ _).trans hL)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  rcases hθc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine (h₁ L ((le_max_left _ _).trans hL) n Q hg hspan K hK φ hφ I hI hbox R).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_zero, mul_one]
    exact mul_le_mul_of_nonneg_right (kpow_mono hK hC₁.le (le_max_left _ _) hδ.le n) (Real.rpow_nonneg hL0 _)
  · refine (h₂ L ((le_max_right _ _).trans hL) n Q hg hspan K hK φ hφ I hI hbox R).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (kpow_mono hK hC₂.le (le_max_right _ _) hδ.le n) (Real.rpow_nonneg hL0 _)) (Real.rpow_nonneg hL0 _)

/-- Two-clock filtered restriction estimate with the root-modulated weight, at both gate weights. -/
theorem exists_rootRawCoupleKernel_restriction_boundFilt (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
        η < incoherenceExponent d γ →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
        ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ n m w J W K M : ℕ,
          ∀ P : MomentumTreeData n m w, ∀ _Croot : RootInputCoordinates P,
          (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
          ∀ Q : Fin n → LayerLink d,
          (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
          1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
          ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
          ∀ (Kφ : ℝ), 0 ≤ Kφ → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L Kφ (φ i)) →
          ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → W + 2 * d ≤ M → 0 ≤ B →
          (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
          ∀ E : Set (Fin 2 → ℝ),
          (∀ t ∈ E, R.baseRootTimes Q ≤ t) →
          (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) →
          ∀ ζ : Circle, ∀ A : Set (Mom d),
          ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α), G.momentMass J < ⊤ →
          Fourier.mixedRestrictionNorm θ J W E A
            (fun t k => (MomentumTreeData.weightedSourceCoupleKernelFilt (P := P)) (G.at k) ζ R L γ δ Q φ I f t k) ≤
            ENNReal.ofReal (rootJetConstant J) *
              (coupleCellConstant d m J W M n Cₗ B * G.momentMass J) *
            ENNReal.ofReal ((Kφ * C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) * L ^ c) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  obtain ⟨C₀, hC₀, hb⟩ := exists_coupleExtension_gate_decayFilt d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensityFilt_L1_bound d hd
  refine ⟨Cₗ, hCₗ, C₀, hC₀, ?_⟩
  intro η hη hη₁ χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  let Cphys := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hCphys : Cphys < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL θ c hθc n m w J W K M P Croot hinputs Q hspan hg R I hI hbox Kφ hKφ φ hφ f B hK hM hB hf E hE
    hχone ζ A α _ G hfin
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  have hLp : 0 < L := zero_lt_one.trans_le hLone
  have hφB : ∀ i u, ‖φ i u‖ ≤ Kφ := fun i u => FiltProd.PresentedMult.norm_le (hφ i) hLp.le hKφ u
  choose S hScard hcover using (fun c => hloc n m w P hinputs c)
  let Nr := ENNReal.ofReal ((Kφ * Cᵣ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (a : α) :
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ)
          φ I) 1 ≤ Nr := by
    simpa only [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P)),
      incoherenceCount_spatialFrequencyLinks] using
      hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ)
        hspan Kφ hKφ φ hφ I hI hbox R
  have hagree (t : E) (k : A) :
      (MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt (P := P)) (G.at k) χ ζ R L γ δ Q φ I f S 0 t k =
        (MomentumTreeData.weightedSourceCoupleKernelFilt (P := P)) (G.at k) ζ R L γ δ Q φ I f t k :=
    (MomentumTreeData.fourierMaskedSourceCoupleExtension_agrees_aboveFilt (P := P)) (G.at k) hχ hc Croot ζ R
      L γ δ Q φ hφB I hI hbox f S hcover hScard hLone (by omega) (by omega) hB hf (N := Nr)
      ENNReal.ofReal_lt_top hroot t (hE t t.property) (hχone t t.property) k
  apply (Fourier.mixedRestrictionNorm_le_extension
    (fun t k => (MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt (P := P)) (G.at k) χ ζ R L γ δ Q φ I f S 0
      t k) hagree).trans
  refine rootMaskedCoupleExtensionFilt_le_of_cells P hχ R hLp γ δ Q φ I hI f hK hM hB hf S hScard 0 ζ G hfin θ
    (H := Cphys * Nr) (ENNReal.mul_lt_top hCphys ENNReal.ofReal_lt_top) ?_ ?_ ?_
  · intro z ξ a
    exact RootCoordinates.integrable_coupleExtensionFilt R hχ hc hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) φ hI hbox
  · intro z ξ a
    exact (RootCoordinates.eLpNorm_coupleExtension_one_leFilt R hχ hc hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) φ hI
        hbox).trans (mul_le_mul' le_rfl (hroot z ξ a))
  · intro z ξ a
    have hQ' : incoherenceCount ((MomentumTreeData.spectralLinksSpatial (P := P))
        (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) = incoherenceCount Q := by
      rw [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P)), incoherenceCount_spatialFrequencyLinks]
    have h := hb L hLa θ c hθc n
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ)
      (hQ' ▸ hg) hspan Kφ hKφ φ hφ I hI hbox R
    rw [hQ'] at h
    exact h

/-- One-clock filtered restriction estimate with the root-modulated weight, at both gate weights. -/
theorem exists_rootRawOneClockKernel_restriction_boundFilt (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
        η < incoherenceExponent d γ →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
        ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ n m w J W K M : ℕ,
          ∀ P : MomentumTreeData n m w, ∀ _Croot : RootInputCoordinates P,
          (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
          ∀ Q : Fin n → LayerLink d,
          (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
          1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ a : Fin 2, ∀ b : ℝ,
          ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
          ∀ (Kφ : ℝ), 0 ≤ Kφ → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L Kφ (φ i)) →
          ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → W + 2 * d ≤ M → 0 ≤ B →
          (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
          ∀ E : Set (Fin 2 → ℝ),
          (∀ t ∈ E, R.baseRootTimes Q ≤ t + R.oneClockShift a Q b) →
          (∀ t ∈ E, ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j) →
          (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ)
            ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) →
          ∀ ζ : Circle, ∀ A : Set (Mom d),
          ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α), G.momentMass J < ⊤ →
          Fourier.mixedRestrictionNorm θ J W E A
            (fun t k => weightedSourceOneClockKernelFilt P (G.at k) ζ R a L γ δ Q φ I f t k) ≤
            ENNReal.ofReal (rootJetConstant J) *
              (coupleCellConstant d m J W M n Cₗ B * G.momentMass J) *
            ENNReal.ofReal ((Kφ * C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) * L ^ c) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  obtain ⟨C₀, hC₀, hb⟩ := exists_coupleExtension_gate_decayFilt d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensityFilt_L1_bound d hd
  refine ⟨Cₗ, hCₗ, C₀, hC₀, ?_⟩
  intro η hη hη₁ χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  let Cphys := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hCphys : Cphys < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL θ c hθc n m w J W K M P Croot hinputs Q hspan hg R a b I hI hbox Kφ hKφ φ hφ f B hK hM hB hf E hE
    hpass hχone ζ A α _ G hfin
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  have hLp : 0 < L := zero_lt_one.trans_le hLone
  have hφB : ∀ i u, ‖φ i u‖ ≤ Kφ := fun i u => FiltProd.PresentedMult.norm_le (hφ i) hLp.le hKφ u
  choose S hScard hcover using (fun c => hloc n m w P hinputs c)
  let Nr := ENNReal.ofReal ((Kφ * Cᵣ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (a' : α) :
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a')) z ξ)
          φ I) 1 ≤ Nr := by
    simpa only [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P)),
      incoherenceCount_spatialFrequencyLinks] using
      hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a')) z ξ)
        hspan Kφ hKφ φ hφ I hI hbox R
  have hagree (t : E) (k : A) :
      (MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt (P := P)) (G.at k) χ ζ R L γ δ Q φ I f S
          (R.oneClockShift a Q b) t k =
        weightedSourceOneClockKernelFilt P (G.at k) ζ R a L γ δ Q φ I f t k :=
    fourierMaskedSourceCoupleExtension_agrees_oneClockFilt P (G.at k) hχ hc Croot ζ R a b L γ δ Q φ hφB I hI hbox
      f S hcover hScard hLone (by omega) (by omega) hB hf (N := Nr) ENNReal.ofReal_lt_top hroot t
      (hE t t.property) (hpass t t.property) (hχone t t.property) k
  apply (Fourier.mixedRestrictionNorm_le_extension
    (fun t k => (MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt (P := P)) (G.at k) χ ζ R L γ δ Q φ I f S
      (R.oneClockShift a Q b) t k) hagree).trans
  refine rootMaskedCoupleExtensionFilt_le_of_cells P hχ R hLp γ δ Q φ I hI f hK hM hB hf S hScard (R.oneClockShift a Q b) ζ G hfin θ
    (H := Cphys * Nr) (ENNReal.mul_lt_top hCphys ENNReal.ofReal_lt_top) ?_ ?_ ?_
  · intro z ξ a
    exact RootCoordinates.integrable_coupleExtensionFilt R hχ hc hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) φ hI hbox
  · intro z ξ a
    exact (RootCoordinates.eLpNorm_coupleExtension_one_leFilt R hχ hc hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) φ hI
        hbox).trans (mul_le_mul' le_rfl (hroot z ξ a))
  · intro z ξ a
    have hQ' : incoherenceCount ((MomentumTreeData.spectralLinksSpatial (P := P))
        (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) = incoherenceCount Q := by
      rw [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P)), incoherenceCount_spatialFrequencyLinks]
    have h := hb L hLa θ c hθc n
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ)
      (hQ' ▸ hg) hspan Kφ hKφ φ hφ I hI hbox R
    rw [hQ'] at h
    exact h

/-- The cell-constant absorption with the multiplier constant and the loss carried. -/
theorem couple_rate_absorb {d m n : ℕ} (hn : 1 ≤ n) (hm : m ≤ 3 * n) {B Cₗ C₀ Kφ δ L η γ₁ c : ℝ}
    (hB : 0 ≤ B) (hCₗ : 0 ≤ Cₗ) (hC₀ : 0 ≤ C₀) (hKφ : 0 ≤ Kφ) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hsmall : (100 * (d : ℝ)) ^ 2 * η ≤ 1) (g : ℕ) :
    coupleCellConstant d m (30 * d) (30 * d) (40 * d) n Cₗ B *
        ENNReal.ofReal ((Kφ * C₀ * δ) ^ n * L ^ (-(γ₁ - 100 * (d : ℝ) * η) * g) * L ^ c) ≤
      ENNReal.ofReal ((Kφ * (maskedSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (30 * d) B Cₗ * C₀) *
        δ) ^ n * L ^ (-(γ₁ - Real.sqrt η) * g) * L ^ c) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have h1 := masked_source_ennreal_coefficient_leSpatial (d := d) (J := 30 * d) (M := 40 * d) (W := 30 * d) hn hm hB
    hCₗ (mul_nonneg hKφ hC₀) hδ
    (mul_nonneg (Real.rpow_nonneg hL0 (-(γ₁ - 100 * (d : ℝ) * η) * g)) (Real.rpow_nonneg hL0 c))
  rw [mul_assoc ((Kφ * C₀ * δ) ^ n)]
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_assoc ((Kφ * (maskedSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (30 * d) B Cₗ * C₀) * δ) ^ n),
    show maskedSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (30 * d) B Cₗ * (Kφ * C₀) * δ =
      Kφ * (maskedSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (30 * d) B Cₗ * C₀) * δ by ring]
  have hcoef := maskedSourceExponentialCoefficient_posSpatial d (30 * d) (40 * d) (30 * d) B Cₗ
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (incoherence_rpow_le_sqrt_loss hL hη hsmall) (Real.rpow_nonneg hL0 c)) ?_
  exact pow_nonneg (mul_nonneg (mul_nonneg hKφ (mul_nonneg hcoef.le hC₀)) hδ) n

/-- Root-modulated two-clock filtered raw couple, printed rate (`30d, 30d`), at both gate weights. -/
theorem exists_rootRawCoupleKernel_rateFilt (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ n m w : ℕ, m ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, RootInputCoordinates P →
        (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
        ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ (Kφ : ℝ), 0 < Kφ → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L Kφ (φ i)) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, R.baseRootTimes Q ≤ t) →
        (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) →
        ∀ ζ : Circle, ∀ A : Set (Mom d),
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α),
        Fourier.mixedRestrictionNorm θ (30 * d) (30 * d) E A
          (fun t k => (MomentumTreeData.weightedSourceCoupleKernelFilt (P := P)) (G.at k) ζ R L γ δ Q φ I f t k) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
            ENNReal.ofReal ((Kφ * C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) * L ^ c) := by
  obtain ⟨Cₗ, hCₗ, C₀, hC₀, hb⟩ := exists_rootRawCoupleKernel_restriction_boundFilt d hd
  let C₁ := maskedSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (30 * d) B Cₗ * C₀
  have hC₁ : 0 < C₁ := mul_pos (maskedSourceExponentialCoefficient_posSpatial _ _ _ _ _ _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL θ c hθc n m w hm P Croot hinputs Q hspan hg R I hI hbox Kφ hKφ φ hφ f hf E hE hχone ζ A α _ G
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hrate : 0 < (Kφ * C₁ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) * L ^ c :=
    mul_pos (mul_pos (pow_pos (mul_pos (mul_pos hKφ hC₁) hδ) _) (Real.rpow_pos_of_pos hLp _))
      (Real.rpow_pos_of_pos hLp _)
  by_cases hfin : G.momentMass (30 * d) = ⊤
  · exact le_top_of_momentMass_top G _ hfin (rootJetConstant_pos _) hrate _
  have hraw := hb L hL θ c hθc n m w (30 * d) (30 * d) (40 * d) (40 * d) P Croot hinputs Q hspan hg
    R I hI hbox Kφ hKφ.le φ hφ f B (by omega) (by omega) hB hf E hE hχone ζ A G (lt_top_iff_ne_top.mpr hfin)
  apply hraw.trans
  have habs := couple_rate_absorb (γ₁ := incoherenceExponent d γ) (c := c) hn hm hB hCₗ.le hC₀.le hKφ.le hδ.le
    hLone hη.le hsmall (incoherenceCount Q) (L := L)
  calc
    _ = ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
        (coupleCellConstant d m (30 * d) (30 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((Kφ * C₀ * δ) ^ n *
          L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) * L ^ c)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl habs

/-- Root-modulated one-clock filtered raw couple, printed rate (`30d, 30d`), at both gate weights. -/
theorem exists_rootRawOneClockKernel_rateFilt (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ n m w : ℕ, m ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, RootInputCoordinates P →
        (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
        ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ a : Fin 2, ∀ b : ℝ,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ (Kφ : ℝ), 0 < Kφ → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L Kφ (φ i)) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, R.baseRootTimes Q ≤ t + R.oneClockShift a Q b) →
        (∀ t ∈ E, ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j) →
        (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ)
          ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) →
        ∀ ζ : Circle, ∀ A : Set (Mom d),
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α),
        Fourier.mixedRestrictionNorm θ (30 * d) (30 * d) E A
          (fun t k => weightedSourceOneClockKernelFilt P (G.at k) ζ R a L γ δ Q φ I f t k) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
            ENNReal.ofReal ((Kφ * C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) * L ^ c) := by
  obtain ⟨Cₗ, hCₗ, C₀, hC₀, hb⟩ := exists_rootRawOneClockKernel_restriction_boundFilt d hd
  let C₁ := maskedSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (30 * d) B Cₗ * C₀
  have hC₁ : 0 < C₁ := mul_pos (maskedSourceExponentialCoefficient_posSpatial _ _ _ _ _ _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL θ c hθc n m w hm P Croot hinputs Q hspan hg R a b I hI hbox Kφ hKφ φ hφ f hf E hE hpass hχone
    ζ A α _ G
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hrate : 0 < (Kφ * C₁ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) * L ^ c :=
    mul_pos (mul_pos (pow_pos (mul_pos (mul_pos hKφ hC₁) hδ) _) (Real.rpow_pos_of_pos hLp _))
      (Real.rpow_pos_of_pos hLp _)
  by_cases hfin : G.momentMass (30 * d) = ⊤
  · exact le_top_of_momentMass_top G _ hfin (rootJetConstant_pos _) hrate _
  have hraw := hb L hL θ c hθc n m w (30 * d) (30 * d) (40 * d) (40 * d) P Croot hinputs Q hspan hg
    R a b I hI hbox Kφ hKφ.le φ hφ f B (by omega) (by omega) hB hf E hE hpass hχone ζ A G
    (lt_top_iff_ne_top.mpr hfin)
  apply hraw.trans
  have habs := couple_rate_absorb (γ₁ := incoherenceExponent d γ) (c := c) hn hm hB hCₗ.le hC₀.le hKφ.le hδ.le
    hLone hη.le hsmall (incoherenceCount Q) (L := L)
  calc
    _ = ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
        (coupleCellConstant d m (30 * d) (30 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((Kφ * C₀ * δ) ^ n *
          L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) * L ^ c)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl habs

end WaveTurbulence.Flower.FiltGate
