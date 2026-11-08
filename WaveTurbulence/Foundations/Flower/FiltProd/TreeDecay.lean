/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Tree
public import WaveTurbulence.Foundations.Flower.FiltProd.Sel
public import WaveTurbulence.Foundations.Flower.FiltProd.Mix
public import WaveTurbulence.Foundations.Incoh.ParameterTreeDecay

/-! # D5b-2 FILT-PROD: tree decay (twins of `CausalTreePhaseDecay`, `ParameterTreeExtension`, `ParameterTreeNegativeBound`, `ParameterTreeQuarterBound`, `ParameterTreeDecay`)

Families over a carrier `V` carry `φ : V → Fin n → ℝ → ℂ`; the decay hypothesis is `∀ v i, PresentedMult L K (φ v i)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc


/-- The actual normalized link mixture against the fully causal selected-clock kernel. -/
def treeCausalPhaseExtensionFilt {d n : ℕ} {V : Type*} (m : ℕ) (χ : ℝ → ℝ)
    (L γ δ : ℝ) (Q : V → Fin n → LayerLink d) (φ : V → Fin n → ℝ → ℂ) (J : Finset (Fin n))
    (S : V → Set (Fin n → LinkMixturePoint d))
    (p : V → (Fin n → LinkMixturePoint d) → CausalBoxData m) (t : Fin 2 → ℝ) (v : V) : ℂ :=
  ∫ z, normalizedLinkMixtureAmplitudeFilt L γ δ (Q v) (φ v) J (S v) z *
    universalCausalBoxKernel m χ t (p v z) ∂productLinkMixtureMeasure d n J

/-- A dimensional per-link constant and a cutoff-dependent prefactor control both tree cases. -/
theorem exists_treeCausalPhaseExtensionFilt_quarter_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g k : ℕ, ∀ V : Type*,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ v i, |((Q v i).leftLayer : ℝ) - (Q v i).rightLayer| + 1 ≤ D) →
        (∀ v, incoherenceCount (Q v) = g) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : V → Fin n → ℝ → ℂ, (∀ v i, PresentedMult L K (φ v i)) →
        ∀ J : Finset (Fin n), J.card ≤ k →
        ∀ S : V → Set (Fin n → LinkMixturePoint d), (∀ v, MeasurableSet (S v)) →
        ∀ p : V → (Fin n → LinkMixturePoint d) → CausalBoxData m, (∀ v, Measurable (p v)) →
        Fourier.mixedFourierNorm00 (1 / 4) (treeCausalPhaseExtensionFilt m χ L γ δ Q φ J S p) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_normalizedReplacedFiltLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro m χ hχ hcχ
  obtain ⟨C, hC, hKer⟩ := exists_universalCausalBoxKernel_bound m hχ hcχ
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g k V Q hspan hg K hK φ hφ J hJ S hS p hp
  let M := ENNReal.ofReal ((K * C₀ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * k))
  have hm (v : V) : (∫⁻ z, ‖normalizedLinkMixtureAmplitudeFilt L γ δ (Q v) (φ v) J (S v) z‖ₑ
      ∂productLinkMixtureMeasure d n J) ≤ M := by
    have hB : ∀ i u, ‖φ v i u‖ ≤ K := fun i u =>
      PresentedMult.norm_le (hφ v i) (zero_lt_one.trans_le (hL₀.trans hL)).le hK u
    apply (lintegral_normalizedLinkMixtureAmplitudeFilt_le (hL₀.trans hL) hδ γ (Q v) (φ v) hK hB J (hS v)).trans
    simpa only [hg v] using hb L hL n (Q v) (hspan v) K hK (φ v) (hφ v) k J hJ
  have hs := mixedFourierNorm00_causalBox_mixture_le m hχ.continuous.measurable h
    (productLinkMixtureMeasure d n J) (fun v => normalizedLinkMixtureAmplitudeFilt L γ δ (Q v) (φ v) J (S v)) p
    (fun v => integrable_normalizedLinkMixtureAmplitudeFilt (zero_lt_one.trans_le (hL₀.trans hL)) γ δ (Q v) (φ v) J (hS v))
    (fun v => stronglyMeasurable_normalizedLinkMixtureAmplitudeFilt (zero_lt_one.trans_le (hL₀.trans hL)) γ δ (Q v) (φ v) J (hS v)) hp hm
  exact hs.trans ((mul_le_mul' le_rfl hKer).trans_eq (mul_comm M _))



/-- Literal causal extension of the actual root marginal, with arbitrary vector parameters. -/
def RootCoordinates.parameterTreeCausalExtensionFilt {d n : ℕ} {V : Type*}
    (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : V → Fin n → LayerLink d) (φ : V → Fin n → ℝ → ℂ)
    (I : V → Set (Fin n → Fin 2 → ℝ)) (t : Fin 2 → ℝ) (v : V) : ℂ :=
  Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ (Q v) (φ v) (I v)) t

/-- The landed global common-extension identity holds for every parameter carrier. -/
theorem parameterTreeCausalExtension_eq_phaseKernelFilt {d n m : ℕ} {V : Type*}
    (R : RootCoordinates n) (Q : V → Fin n → LayerLink d) (T : ∀ v, TreeClockFibers m (Q v)) (φ : V → Fin n → ℝ → ℂ)
    (hfirst : ∀ v, R.rootVertex 0 = (T v).selection.coordinates.rootVertex 0)
    (hlast : ∀ v, R.rootVertex 1 = (T v).selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ} (hmχ : Measurable χ)
    (hc : Fourier.CutoffControl χ)
    (hχroot : ∀ v a, a ∈ R.rootBox (Q v) → ∀ j, χ (a j) = 1)
    (hχselected : ∀ v a, a ∈ (T v).selection.coordinates.rootBox (Q v) → ∀ j, χ (a j) = 1) :
    RootCoordinates.parameterTreeCausalExtensionFilt R χ L γ δ Q φ (fun v => (T v).timeDomain) =
      fun t v => TreeClockFibers.causalPhaseKernelFilt (T v) (φ v) χ L γ δ t := by
  funext t v
  have he := treeCausalExtension_eq_phaseKernel R (fun _ : Mom d => Q v) (fun _ => T v) (fun _ => φ v)
    (fun _ => hfirst v) (fun _ => hlast v) hL γ δ hmχ hc
    (fun _ => hχroot v) (fun _ => hχselected v)
  exact congrFun (congrFun he t) (0 : Mom d)



/-- TARGET (incohproof26) for arbitrary source parameter families. -/
theorem exists_parameterTreeCausalExtensionFilt_negative_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g : ℕ, ∀ V : Type*,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ v i, |((Q v i).leftLayer : ℝ) - (Q v i).rightLayer| + 1 ≤ D) →
        (∀ v, incoherenceCount (Q v) = g) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : V → Fin n → ℝ → ℂ, (∀ v i, PresentedMult L K (φ v i)) →
        ∀ I : V → Set (Fin n → Fin 2 → ℝ), (∀ v, MeasurableSet (I v)) →
        (∀ v, I v ⊆ univ.pi (fun i => linkBox (Q v i))) → ∀ R : RootCoordinates n,
        Fourier.mixedFourierNorm00 (-η) (RootCoordinates.parameterTreeCausalExtensionFilt R χ L γ δ Q φ I) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootDensityFilt_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro η hη _ χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  let A := ENNReal.ofReal (4 * Fourier.negativeFrequencyConstant η) *
    Fourier.orderedFourMomentFactor hc.radius hc.bound * ENNReal.ofReal (hc.bound ^ 2)
  have hA : A ≠ ⊤ := by
    have hm := Fourier.orderedFourMomentFactor_ne_top hc.radius hc.bound
    dsimp only [A]
    finiteness
  let C : ℝ := 1 + A.toReal
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hA]
    exact ENNReal.ofReal_le_ofReal (by dsimp only [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro γ hγ hηγ δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηγ δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g V Q hspan hcount K hK φ hφ I hI hbox R
  have hLp : 0 < L := zero_lt_one.trans_le (hL₀.trans hL)
  have hr (v : V) : eLpNorm (RootCoordinates.linkDensityFilt R L γ δ (Q v) (φ v) (I v)) 1 ≤
      ENNReal.ofReal ((K * C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * g)) := by
    simpa only [hcount v] using hb L hL n (Q v) (hspan v) K hK (φ v) (hφ v) (I v) (hI v) (hbox v) R
  exact (mixedFourierNorm00_cutoffTriangle_le hη hχ hcχ hc
    (fun t v => RootCoordinates.linkDensityFilt R L γ δ (Q v) (φ v) (I v) t)
    (fun v => RootCoordinates.integrable_linkDensityFilt R hLp γ δ (Q v) (φ v) (hI v) (hbox v)) hr).trans
    (mul_le_mul' hAC le_rfl)



/-- TARGET (incohproof28), for the actual common extension, with only two selected-link losses. -/
theorem exists_parameterTreeCausalExtensionFilt_quarter_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, m ≤ 2 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g : ℕ, ∀ V : Type*,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ k i, |((Q k i).leftLayer : ℝ) - (Q k i).rightLayer| + 1 ≤ D) →
        (∀ k, incoherenceCount (Q k) = g) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : V → Fin n → ℝ → ℂ, (∀ v i, PresentedMult L K (φ v i)) →
        ∀ T : (∀ k, TreeClockFibers m (Q k)), ∀ R : RootCoordinates n,
        ∀ J : Finset (Fin n), J.card ≤ 2 →
        (∀ k, R.rootVertex 0 = (T k).selection.coordinates.rootVertex 0) →
        (∀ k, R.rootVertex 1 = (T k).selection.coordinates.rootVertex (Fin.last (m + 1))) →
        (∀ k, (T k).selection.coordinates.rootLinks = J) →
        (∀ k v, v ∈ R.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        (∀ k v, v ∈ (T k).selection.coordinates.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        Fourier.mixedFourierNorm00 (1 / 4)
          (RootCoordinates.parameterTreeCausalExtensionFilt R χ L γ δ Q φ (fun k => (T k).timeDomain)) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * 2)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_treeCausalPhaseExtensionFilt_quarter_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro m hm χ hχ hcχ
  obtain ⟨C, hC, hb⟩ := hb m χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro γ hγ η hη hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g V Q hspan hg K hK φ hφ T R J hj hfirst hlast hJ hχroot hχsel
  have he := parameterTreeCausalExtension_eq_phaseKernelFilt R Q T φ hfirst hlast
    (zero_lt_one.trans_le (hL₀.trans hL)) γ δ hχ.continuous.measurable hc hχroot hχsel
  have hr : RootCoordinates.parameterTreeCausalExtensionFilt R χ L γ δ Q φ (fun k => (T k).timeDomain) =
      treeCausalPhaseExtensionFilt m χ L γ δ Q φ J
        (fun k => (T k).mixtureDomain) (fun k => (T k).mixtureParameters L γ δ) := by
    rw [he]
    funext t k
    rw [TreeClockFibers.causalPhaseKernelFilt]
    rw [hJ k]
    rfl
  rw [hr]
  exact hb L hL n g 2 V Q hspan hg K hK φ hφ J hj
    (fun k => (T k).mixtureDomain) (fun k => (T k).measurableSet_mixtureDomain)
    (fun k => (T k).mixtureParameters L γ δ) (fun k => (T k).measurable_mixtureParameters L γ δ)



/-- TARGET (incohproof24), with the literal source extension and printed `100dηg` loss. -/
theorem exists_parameterTreeCausalExtensionFilt_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, m ≤ 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g : ℕ, 1 ≤ g → ∀ V : Type*,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ k i, |((Q k i).leftLayer : ℝ) - (Q k i).rightLayer| + 1 ≤ D) →
        (∀ k, incoherenceCount (Q k) = g) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : V → Fin n → ℝ → ℂ, (∀ v i, PresentedMult L K (φ v i)) →
        ∀ T : (∀ k, TreeClockFibers m (Q k)), ∀ R : RootCoordinates n,
        ∀ J : Finset (Fin n), J.card ≤ 2 →
        (∀ k, R.rootVertex 0 = (T k).selection.coordinates.rootVertex 0) →
        (∀ k, R.rootVertex 1 = (T k).selection.coordinates.rootVertex (Fin.last (m + 1))) →
        (∀ k, (T k).selection.coordinates.rootLinks = J) →
        (∀ k v, v ∈ R.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        (∀ k v, v ∈ (T k).selection.coordinates.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        Fourier.mixedFourierNorm00 η
          (RootCoordinates.parameterTreeCausalExtensionFilt R χ L γ δ Q φ (fun k => (T k).timeDomain)) ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * g)) := by
  obtain ⟨Cₙ, hCₙ, hn⟩ := exists_parameterTreeCausalExtensionFilt_negative_bound d hd
  obtain ⟨Cₚ, hCₚ, hp⟩ := exists_parameterTreeCausalExtensionFilt_quarter_bound d hd
  let C₀ := max Cₙ Cₚ
  have hC₀ : 0 < C₀ := hCₙ.trans_le (le_max_left _ _)
  refine ⟨C₀, hC₀, ?_⟩
  intro m hm η hη hη₁ χ hχ hcχ
  obtain ⟨C₁, hC₁, hn⟩ := hn η hη (by linarith only [hη₁]) χ hχ hcχ
  obtain ⟨C₂, hC₂, hp⟩ := hp m hm χ hχ hcχ
  let C := max C₁ C₂
  have hC : 0 < C := hC₁.trans_le (le_max_left _ _)
  obtain ⟨Lₐ, hLₐ, ha⟩ := exists_constant_absorption_threshold C hη
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨Lₙ, hLₙ, hn⟩ := hn γ hγ hηγ δ hδ D hD
  obtain ⟨Lₚ, hLₚ, hp⟩ := hp γ hγ η hη hηγ δ hδ hδ₁ D hD
  refine ⟨max Lₐ (max Lₙ Lₚ), hLₐ.trans (le_max_left _ _), ?_⟩
  intro L hL n g hg V Q hspan hcount K hK φ hφ T R J hJcard hfirst hlast hJ hχroot hχsel
  have hLa : Lₐ ≤ L := (le_max_left _ _).trans hL
  have hLn : Lₙ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLp : Lₚ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLone : 1 ≤ L := hLₐ.trans hLa
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  let A := (K * C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * g)
  let F := RootCoordinates.parameterTreeCausalExtensionFilt R χ L γ δ Q φ (fun k => (T k).timeDomain)
  let M := ENNReal.ofReal C * ENNReal.ofReal A
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcoefₙ : (K * Cₙ * δ) ^ n ≤ (K * C₀ * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg hK hCₙ.le) hδ.le)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) hK) hδ.le) n
  have hcoefₚ : (K * Cₚ * δ) ^ n ≤ (K * C₀ * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg hK hCₚ.le) hδ.le)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hK) hδ.le) n
  have hneg : Fourier.mixedFourierNorm00 (-η) F ≤ M := by
    apply (hn L hLn n g V Q hspan hcount K hK φ hφ (fun k => (T k).timeDomain)
      (fun k => (T k).measurableSet_timeDomain) (fun k => (T k).timeDomain_subset_linkBoxes) R).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoefₙ (Real.rpow_nonneg hLpos.le _))
  have hpos : Fourier.mixedFourierNorm00 (1 / 4) F ≤ M * ENNReal.ofReal (L ^ ((d : ℝ) * 2)) := by
    have hbound := hp L hLp n g V Q hspan hcount K hK φ hφ T R J hJcard hfirst hlast hJ hχroot hχsel
    apply hbound.trans
    have hm : (K * Cₚ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * 2) ≤
        A * L ^ ((d : ℝ) * 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefₚ (Real.rpow_nonneg hLpos.le _)) (Real.rpow_nonneg hLpos.le _)
    calc
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (A * L ^ ((d : ℝ) * 2)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (ENNReal.ofReal_le_ofReal hm)
      _ = _ := by rw [ENNReal.ofReal_mul hA, ← mul_assoc]
  have hinterp := mixedFourierNorm00_le_of_tree_endpoints (d := d) hη
    (by linarith only [hη₁]) hLone F M hneg hpos
  have hCa : C ≤ L ^ (η * g) := (ha L hLa).trans
    (Real.rpow_le_rpow_of_exponent_le hLone (by
      have hgR : 1 ≤ (g : ℝ) := by exact_mod_cast hg
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hgR hη.le))
  apply hinterp.trans
  calc
    _ = ENNReal.ofReal (C * A * L ^ (16 * (d : ℝ) * η)) := by
      dsimp only [M]
      rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (mul_nonneg hC.le hA)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (tree_interpolation_scale_le (by omega) hg (mul_nonneg (mul_nonneg hK hC₀.le) hδ.le) hη.le hLone hCa)


end WaveTurbulence.Flower.FiltProd
