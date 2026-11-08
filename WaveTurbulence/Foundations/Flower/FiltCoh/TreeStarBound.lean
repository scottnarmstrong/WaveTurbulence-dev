/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarExt

/-! # FILT-COH (c2): star-weighted layer-zero paired trees at weight `θ ≤ 1 - η/8`

`exists_tree_star_bound_theta`: for a layer-zero regular paired tree, separately normalized leaf profiles and ANY
star weights presented with `30d`-th total-frequency moments `cω`, the star-weighted kernel has `X^{θ,30d,0}` norm
`≤ Ck (Ck δ)^n ∏ cω`. Route: `tree_star_kernel_eq_ext` (presentation × leaf-cell mixture), the root-character
mixture bound `star_rootAmplitudeMixture_le` with main's moving-root amplitude envelopes, main's paired-profile
majorant, the uniform physical-symbol envelope `physical_symbol_envelope_u`, and main's tree budget
`tree_error_budget_absorption`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst Set MainCoef
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure rootChar rootJetConstant)
open scoped ENNReal

variable {d : ℕ}

/-- **The norm of the star tree extension.** -/
theorem tree_star_ext_norm_le {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hd : 3 ≤ d) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) {Binput Ccover : ℝ} (hBi : 0 ≤ Binput)
    (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal Binput)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    {I : Type*} [Fintype I] (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, StronglyMeasurable (Function.uncurry (C i)))
    {θ : ℝ} (hθ : 0 ≤ θ) (E : I → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam)) < ⊤)
    (hEnv : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (LG.garden.sig 0)).length → Mom d),
      ‖physicalWeightedCellSymbol L δ γ z β γ' (J i) (C i) lam‖ ≤ E i lam)
    {α : Type} [MeasurableSpace α] (Gm : RootMeasure d (X.treeLinks (LG.garden.sig 0)).length α)
    (hfin : Gm.momentMass (30*d) < ⊤) :
    Fourier.mixedFourierNorm θ (30*d) 0 (fun t k =>
      ∫ u, (Gm.at k).amplitude u.2 *
        rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u.1 *
        (unitSquareCutoff t * pairedInverseProfile (fun lam => treeStarProfile hX L δ γ Gm.base.frequency
          c J C S lam u) t) ∂(treeLeafCellMeasure S).prod Gm.base.μ) ≤
      (ENNReal.ofReal (rootLocalOverlapConstant d) * (ENNReal.ofReal (rootJetConstant (30*d)) *
        ((ENNReal.ofReal (treeRootLeafDerivativeConstant d (30*d)) *
          (ENNReal.ofReal (Ccover^(X.treeLinks (LG.garden.sig 0)).length) *
            ENNReal.ofReal (leafMomentLocalizationConstant d (30*d+1) (40*d) *
              treeAugmentedInputBound d (40*d) (40*d) Binput)^(Fintype.card (TPlus LG.garden)+1))) *
          Gm.momentMass (30*d)))) *
        (ENNReal.ofReal (2^θ) * Fourier.timeFourierNorm θ unitSquareCutoff *
          ∫⁻ lam, wL θ lam * ENNReal.ofReal (∑ i, treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  set f := RA1Leafwise.treeInputFunctionsL LG H with hfdef
  have hmP := stronglyMeasurable_treeStarProfile hX hLp δ γ Gm.base.frequency_measurable c J C hC S
  let Bs : (ℝ × ℝ) → ℝ≥0∞ := fun lam =>
    ENNReal.ofReal (∑ i, treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam)
  have hmB : Measurable Bs := ENNReal.measurable_ofReal.comp
    (Finset.measurable_sum _ (fun i _ => measurable_const.mul (hmE i)))
  have hbound (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) × α) :
      ∀ᵐ lam : ℝ × ℝ, ‖treeStarProfile hX L δ γ Gm.base.frequency c J C S lam u‖ₑ ≤ Bs lam := by
    filter_upwards [ae_all_iff.mpr hEnv] with lam hlam
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_treeStarProfile_le hX L δ γ Gm.base.frequency c hc J C S E hpE lam hlam u)
  have hfB : (∫⁻ lam, wL θ lam * Bs lam) < ⊤ := by
    have he : (∫⁻ lam, wL θ lam * Bs lam) =
        ∑ i, ENNReal.ofReal (treeSpectralFrequencyLoss X (LG.garden.sig 0)) *
          ∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam) := by
      simp only [Bs]
      have hsum (lam : ℝ × ℝ) : ENNReal.ofReal (∑ i, treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam) =
          ∑ i, ENNReal.ofReal (treeSpectralFrequencyLoss X (LG.garden.sig 0)) * ENNReal.ofReal (E i lam) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg
          (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X _)) (hpE i lam))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X _))]
      simp_rw [hsum, Finset.mul_sum]
      rw [lintegral_finsetSum (f := fun i lam => wL θ lam * (ENNReal.ofReal
        (treeSpectralFrequencyLoss X (LG.garden.sig 0)) * ENNReal.ofReal (E i lam))) Finset.univ
        (fun i _ => (measurable_wL θ).mul (measurable_const.mul (ENNReal.measurable_ofReal.comp (hmE i))))]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp_rw [mul_left_comm (wL θ _)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [he]
    exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfE i))
  have hiA (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) × α) :
      Integrable (fun lam => treeStarProfile hX L δ γ Gm.base.frequency c J C S lam u) :=
    integrable_of_wL_envelope hθ (hmP.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (hbound u) hfB
  have hmass : (∫⁻ lam, Bs lam) < ⊤ := lt_of_le_of_lt (lintegral_mono fun lam =>
    le_mul_of_one_le_left bot_le (one_le_wL hθ lam)) hfB
  have hH : ((∫⁻ t, ‖unitSquareCutoff t‖ₑ) * ∫⁻ lam, Bs lam) < ⊤ :=
    ENNReal.mul_lt_top (hasFiniteIntegral_iff_enorm.mp integrable_unitSquareCutoff.2) hmass
  have hmain := star_rootAmplitudeMixture_le (N := 30*d) (treeLeafCellMeasure S) Gm θ
    (treeRootLeafAmplitude f S) (treeRootLeafEnvelope (30*d) f S)
    (fun q k u hq => treeRootLeafAmplitude_eq_zero f S q k u hq)
    (fun q u => contDiff_infty.mp (contDiff_treeRootLeafAmplitude f S q u) (30*d))
    (fun q j _ k => stronglyMeasurable_rootChar_treeRootLeafAmplitude_jets f (K := 40*d) (by omega) hf S
      Gm.root_measurable q k j)
    (fun q => integrable_treeRootLeafEnvelope (30*d) f (K := 40*d) (M := 40*d) (by omega) (by omega) hBi hf S hS q)
    (fun q => measurable_treeRootLeafEnvelope (30*d) f (K := 40*d) (by omega) hf S q)
    (treeRootLeafEnvelope_nonneg (30*d) f S)
    (fun q j hj k u => norm_iteratedFDeriv_treeRootLeafAmplitude_le f S q hj k u)
    (fun q => lintegral_treeRootLeafEnvelope_le (30*d) f (K := 40*d) (M := 40*d) (by omega) (by omega) hBi hf S hS q)
    (fun t u => unitSquareCutoff t * pairedInverseProfile (fun lam =>
      treeStarProfile hX L δ γ Gm.base.frequency c J C S lam u) t)
    (stronglyMeasurable_treePairedProfile (fun lam u => treeStarProfile hX L δ γ Gm.base.frequency c J C S lam u) hmP)
    (fun u => integrable_mul_pairedInverseProfile integrable_unitSquareCutoff (hiA u)) hH
    (fun u => eLpNorm_treePairedProfile_one_le (hiA u) (hbound u)) hfin
  refine hmain.trans (mul_le_mul' le_rfl ?_)
  exact mixedFourierNorm00_pairedProfile_le hθ integrable_unitSquareCutoff hiA hmB hbound

end WaveTurbulence.Flower.FiltCoh
