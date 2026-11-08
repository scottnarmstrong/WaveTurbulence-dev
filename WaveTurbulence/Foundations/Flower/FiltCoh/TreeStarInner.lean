/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarMix

/-! # FILT-COH (c2): the twisted tree source sum as one moving-root mixture of shifted physical symbols

`tree_star_inner_mixture`: with main's normalization pushed in (`physicalWeightedCellSymbol_eq_tree`), the
character-twisted lattice source sum of a layer-zero paired tree (times the coupling power and the garden sign) is
`∫ rootAmplitudeSum · 𝒫(Σ_Z coef_Z · treeNormalizedScalar(physical symbol at shifted modulations))`; the finite
exchanges use only an integrable envelope of the physical symbols that is uniform in the modulations. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure rootChar rootJetConstant)
open scoped ENNReal

variable {d : ℕ}

/-- The shifted physical symbol family. -/
@[expose] def shiftedSymbol {n : ℕ} (L δ γ : ℝ) (ν : PairedMomentum d n) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) :
    (ℝ × ℝ) → (Fin n → Mom d) → (Fin n → Mom d) → ((Fin n × Fin 2) → Fin d → ℤ) → ℂ :=
  fun lam β γ' z => physicalWeightedCellSymbol L δ γ z (shiftL β ν 0) (shiftL γ' ν 1) J C lam

theorem stronglyMeasurable_shiftedSymbol {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (ν : PairedMomentum d n)
    (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      shiftedSymbol L δ γ ν J C p.1 p.2.1 p.2.2 z) :=
  stronglyMeasurable_shift_fixed (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' J C lam) z
    (stronglyMeasurable_physicalWeightedCellSymbol_joint hL δ γ J hC z) ν

/-- **The twisted tree source sum as one moving-root mixture of shifted physical symbols.** -/
theorem tree_star_inner_mixture {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (h0 : ∀ a, LG.layer a = 0)
    {I : Type*} [Fintype I] (c : I → ℂ) (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i)) {L : ℝ} (hL : 1 ≤ L) (γ δ t s : ℝ)
    (hH : RA1Leafwise.treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s = fun g =>
      RA1Leafwise.treeWickArrayWeight g * ∑ i, c i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
        (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s)
    {K M : ℕ} {B Ccover : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm K M (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    {θ : ℝ} (hθ : 0 ≤ θ) (E : I → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam)) < ⊤)
    (hEnv : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (LG.garden.sig 0)).length → Mom d),
      ‖physicalWeightedCellSymbol L δ γ z β γ' (J i) (C i) lam‖ ≤ E i lam)
    (ζ : ℂ) (k : Mom d) (ν : PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) :
    (coupling d L γ δ : ℂ)^LG.garden.order * ζ *
      ∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
        ((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) *
          RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p) *
        (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
          (fun j i => latticePoint L (p (j,i))) =
      ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u *
        pairedInverseProfile (fun lam => ∑ i, (ζ * c i) *
          treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u) ![t,s]
        ∂treeLeafCellMeasure S := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*(X.treeLinks (LG.garden.sig 0)).length):ℝ):ℂ)
  have hinner := tree_char_inner_eq hX h0 c J C hC hL (2*δ*L^(2*γ)) γ δ t s hH hK hM hB H hf S hcover hS k ν
  rw [hinner]
  -- normalization: the physical symbol is `q` times the tree profile scalar
  have hR (i : I) (lam : ℝ × ℝ) (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u =
        q * treeNormalizedScalar hX (fun lam β γ' z => treeProfileArrayScalar L (2*δ*L^(2*γ))
          RA1Leafwise.treeWickArrayWeight z (shiftL β ν 0) (shiftL γ' ν 1) (J i) (C i) lam) S lam u := by
    unfold treeNormalizedScalar shiftedSymbol
    rw [physicalWeightedCellSymbol_eq_tree hLp δ γ, mul_div_assoc]
  -- measurability and integrability of every shifted symbol
  have hmR (i : I) : StronglyMeasurable (Function.uncurry
      (treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S)) :=
    stronglyMeasurable_treeNormalizedScalar hX _
      (fun z => stronglyMeasurable_shiftedSymbol hLp δ γ ν (J i) (hC i).meas z) S
  have hbd (i : I) (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      ∀ᵐ lam : ℝ × ℝ, ‖treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u‖ ≤
        treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam := by
    filter_upwards [hEnv i] with lam hlam
    have hh := treeNormalizedScalar_norm_le hX (shiftedSymbol L δ γ ν (J i) (C i)) S zero_le_one
      (hpE i lam) lam (fun z β γ' => by
        have h1 := hlam z (shiftL β ν 0) (shiftL γ' ν 1)
        have h2 : (0:ℝ) ≤ (∑ j, ‖β j‖) + (∑ j, ‖γ' j‖) := by positivity
        calc ‖shiftedSymbol L δ γ ν (J i) (C i) lam β γ' z‖ ≤ E i lam := h1
          _ ≤ 1 * (1 + ((∑ j, ‖β j‖) + (∑ j, ‖γ' j‖))) * E i lam := by
              nlinarith [hpE i lam]) u
    simpa only [one_mul] using hh
  have hiLam (i : I) (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      Integrable (fun lam => treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u) := by
    refine integrable_of_wL_envelope hθ
      ((hmR i).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (B := fun lam => ENNReal.ofReal (treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam)) ?_ ?_
    · filter_upwards [hbd i u] with lam hlam
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hlam
    · have hc : (∫⁻ lam, wL θ lam * ENNReal.ofReal (treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam)) =
          ENNReal.ofReal (treeSpectralFrequencyLoss X (LG.garden.sig 0)) *
            ∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun lam => ?_
        rw [ENNReal.ofReal_mul (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X _))]
        ring
      rw [hc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfE i)
  -- the moving-root integrand is integrable for every coefficient
  have hiU (i : I) (tt : Fin 2 → ℝ) :
      Integrable (fun u => rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u) tt)
        (treeLeafCellMeasure S) := by
    have hmeas := stronglyMeasurable_treePairedProfile (fun lam u =>
      treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u) (hmR i)
    have hm' : StronglyMeasurable (fun u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ) =>
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u) tt) := by
      have he2 : StronglyMeasurable (fun p : ((ℝ × ℝ) ×
          (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ))) =>
          e2 p.1 (tt 0) (tt 1)) :=
        (continuous_e2.measurable.comp
          (measurable_fst.prodMk (measurable_const (a := ((tt 0, tt 1) : ℝ × ℝ))))).stronglyMeasurable
      have hpre : StronglyMeasurable (fun p : ((ℝ × ℝ) ×
          (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ))) =>
          treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S p.1 p.2 * e2 p.1 (tt 0) (tt 1)) :=
        (hmR i).mul he2
      exact (hpre.comp_measurable (measurable_snd.prodMk measurable_fst)).integral_prod_right'
    have hiE : Integrable (E i) := by
      refine ⟨(hmE i).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hpE i))]
      refine lt_of_le_of_lt (lintegral_mono fun lam => ?_) (hfE i)
      exact le_mul_of_one_le_left bot_le (one_le_wL hθ lam)
    refine integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar _ hK hM hB hf S hS _ hm'
      (D := treeSpectralFrequencyLoss X (LG.garden.sig 0) * ∫ lam, E i lam) (fun u => ?_) k
    unfold pairedInverseProfile
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_ae ((hiLam i u).norm.congr (ae_of_all _ fun lam => ?_)) (hiE.const_mul _) ?_).trans
      (integral_const_mul _ _).le
    · simp only [norm_mul, norm_e2, mul_one]
    · filter_upwards [hbd i u] with lam hlam
      simpa only [norm_mul, norm_e2, mul_one] using hlam
  -- assemble
  have horder : LG.garden.order = 2*(X.treeLinks (LG.garden.sig 0)).length := tree_order_eq_twice_links hX
  have hcq : (coupling d L γ δ : ℂ)^LG.garden.order = q := by
    rw [horder]
    simp only [q, coupling, Complex.ofReal_pow]
  rw [hcq]
  have hsum (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      pairedInverseProfile (fun lam => ∑ i, (ζ * c i) *
        treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u) ![t,s] =
      ∑ i, (ζ * c i) * pairedInverseProfile (fun lam =>
        treeNormalizedScalar hX (shiftedSymbol L δ γ ν (J i) (C i)) S lam u) ![t,s] := by
    rw [tree_pairedInverseProfile_finsetSum Finset.univ _ (fun i _ => (hiLam i u).const_mul _)]
    exact Finset.sum_congr rfl fun i _ => tree_pairedInverseProfile_const_mul _ _ _
  simp_rw [hsum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => ((hiU i ![t,s]).const_mul (ζ * c i)).congr
    (ae_of_all _ fun u => by dsimp only; ring))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [hR i]
  rw [tree_pairedInverseProfile_const_mul]
  ring

end WaveTurbulence.Flower.FiltCoh
