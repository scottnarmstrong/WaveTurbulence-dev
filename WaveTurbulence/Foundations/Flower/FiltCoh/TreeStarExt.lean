/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarInner

/-! # FILT-COH (c2): the extension of a star-weighted layer-zero paired tree and its norm

* `treeStarProfile`: the profile `Σ_Z c_Z · treeNormalizedScalar(shifted physical symbol)` with the presentation
  parameter `a` (link frequency `ν a`), as a function of `(lam, (u, a))`.
* `tree_star_kernel_eq_ext`: on the time box the star-weighted kernel is the presentation × leaf-cell mixture
  `∫ (G.at k).amplitude a · rootAmplitudeSum k u · χ_□(t) 𝒫(treeStarProfile)(t)` (Fubini).
* `tree_star_ext_norm_le`: its `X^{θ,J,0}` norm is the root-mixture constant times the weighted mass of a common
  frequency envelope (`star_rootAmplitudeMixture_le`, main's `mixedFourierNorm00_pairedProfile_le`). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure rootChar rootJetConstant)
open scoped ENNReal

variable {d : ℕ}

/-- The star tree profile with presentation parameter. -/
@[expose] def treeStarProfile {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) (L δ γ : ℝ) {α : Type}
    (ν : α → PairedMomentum d (X.treeLinks (G.sig 0)).length) {I : Type*} [Fintype I] (c : I → ℂ)
    (J : I → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (lam : ℝ × ℝ) (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) × α) : ℂ :=
  ∑ i, c i * treeNormalizedScalar hX (shiftedSymbol L δ γ (ν u.2) (J i) (C i)) S lam u.1

theorem stronglyMeasurable_treeStarProfile {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) {L : ℝ}
    (hL : 0 < L) (δ γ : ℝ) {α : Type} [MeasurableSpace α]
    {ν : α → PairedMomentum d (X.treeLinks (G.sig 0)).length} (hν : Measurable ν)
    {I : Type*} [Fintype I] (c : I → ℂ) (J : I → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, StronglyMeasurable (Function.uncurry (C i)))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (Function.uncurry (treeStarProfile hX L δ γ ν c J C S)) := by
  unfold treeStarProfile
  refine Finset.stronglyMeasurable_fun_sum _ (fun i _ => ?_)
  refine StronglyMeasurable.const_mul ?_ (c i)
  exact stronglyMeasurable_treeNormalizedScalar_param hX
    (fun a lam β γ' z => shiftedSymbol L δ γ (ν a) (J i) (C i) lam β γ' z)
    (fun z => stronglyMeasurable_shifted (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' (J i) (C i) lam)
      z (stronglyMeasurable_physicalWeightedCellSymbol_joint hL δ γ (J i) (hC i) z) hν) S

theorem norm_treeStarProfile_le {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) (L δ γ : ℝ)
    {α : Type} (ν : α → PairedMomentum d (X.treeLinks (G.sig 0)).length)
    {I : Type*} [Fintype I] (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (J : I → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (E : I → (ℝ × ℝ) → ℝ) (hpE : ∀ i lam, 0 ≤ E i lam) (lam : ℝ × ℝ)
    (hEnv : ∀ i, ∀ (z : (Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (G.sig 0)).length → Mom d),
      ‖physicalWeightedCellSymbol L δ γ z β γ' (J i) (C i) lam‖ ≤ E i lam)
    (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) × α) :
    ‖treeStarProfile hX L δ γ ν c J C S lam u‖ ≤
      ∑ i, treeSpectralFrequencyLoss X (G.sig 0) * E i lam := by
  unfold treeStarProfile
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have hh := treeNormalizedScalar_norm_le hX (shiftedSymbol L δ γ (ν u.2) (J i) (C i)) S zero_le_one
    (hpE i lam) lam (fun z β γ' => by
      have h1 := hEnv i z (shiftL β (ν u.2) 0) (shiftL γ' (ν u.2) 1)
      have h2 : (0:ℝ) ≤ (∑ j, ‖β j‖) + (∑ j, ‖γ' j‖) := by positivity
      calc ‖shiftedSymbol L δ γ (ν u.2) (J i) (C i) lam β γ' z‖ ≤ E i lam := h1
        _ ≤ 1 * (1 + ((∑ j, ‖β j‖) + (∑ j, ‖γ' j‖))) * E i lam := by nlinarith [hpE i lam]) u.1
  rw [one_mul] at hh
  have hl : 0 ≤ treeSpectralFrequencyLoss X (G.sig 0) * E i lam :=
    mul_nonneg (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X _)) (hpE i lam)
  calc ‖c i‖ * ‖treeNormalizedScalar hX (shiftedSymbol L δ γ (ν u.2) (J i) (C i)) S lam u.1‖
      ≤ 1 * (treeSpectralFrequencyLoss X (G.sig 0) * E i lam) :=
        mul_le_mul (hc i) hh (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Fubini for an amplitude mixture with a bounded kernel. -/
theorem fubini_amp_mixture {U α : Type*} [MeasurableSpace U] [MeasurableSpace α] (μ : Measure U) [SFinite μ]
    (ν : Measure α) [SFinite ν] (f : U → ℂ) (hf : Integrable f μ) (g : α → ℂ) (hg : Integrable g ν)
    (h : U × α → ℂ) (hh : AEStronglyMeasurable h (μ.prod ν)) {D : ℝ} (hD : ∀ z, ‖h z‖ ≤ D) :
    ∫ a, g a * ∫ u, f u * h (u, a) ∂μ ∂ν = ∫ z, g z.2 * f z.1 * h z ∂(μ.prod ν) := by
  have hF : Integrable (fun z => g z.2 * f z.1 * h z) (μ.prod ν) :=
    ((hf.mul_prod hg).mul_bdd hh (ae_of_all _ hD)).congr (ae_of_all _ fun z => by dsimp only; ring)
  rw [integral_prod_symm _ hF]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp only
  ring

/-- The star-weighted kernel as an iterated presentation / leaf-cell integral. -/
theorem tree_star_kernel_eq_inner {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hwf : X.wf = true) (h0 : ∀ a, LG.layer a = 0) (hd : 3 ≤ d) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ)
    {Binput Ccover : ℝ} (hBi : 0 ≤ Binput) (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal Binput)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    {I : Type*} [Fintype I] (c : I → ℂ) (_hc : ∀ i, ‖LG.garden.zeta * c i‖ ≤ 1)
    (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i))
    (hH : ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      RA1Leafwise.treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s = fun g =>
      RA1Leafwise.treeWickArrayWeight g * ∑ i, c i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
        (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s)
    {θ : ℝ} (hθ : 0 ≤ θ) (E : I → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam)) < ⊤)
    (hEnv : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (LG.garden.sig 0)).length → Mom d),
      ‖physicalWeightedCellSymbol L δ γ z β γ' (J i) (C i) lam‖ ≤ E i lam)
    (Jst : ℕ) (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sset, IncTop.StarPresented Jst (ω a) (cω a))
    (t : Fin 2 → ℝ) (hs : 0 ≤ t 1) (hst : t 1 < t 0) (ht : t 0 ≤ 1) (k : Mom d) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t 0) (t 1) k (fun _ => 0) 0 (IncTop.starWeight Sset ω) =
      ∫ a, ((IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).at k).amplitude a *
        ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u *
          pairedInverseProfile (fun lam => treeStarProfile hX L δ γ
            (IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).base.frequency
            (fun i => LG.garden.zeta * c i) J C S lam (u, a)) t ∂treeLeafCellMeasure S
        ∂(IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).base.μ := by
  set Gm := IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX) with hGm
  have htv : (![t 0, t 1] : Fin 2 → ℝ) = t := by funext i; fin_cases i <;> rfl
  rw [kernelLeavesW_tree_star_eq hX hwf h0 (by omega) hL γ δ (K := 40*d) (M := 40*d) (by omega) (by omega) H hf
    Jst Sset ω cω hpres hs hst ht k]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  have hinner := tree_star_inner_mixture hX h0 c J C hC hL γ δ (t 0) (t 1) (hH _ _ hs hst ht)
    (K := 40*d) (M := 40*d) (by omega) (by omega) hBi H hf S hcover hS hθ E hmE hpE hfE hEnv LG.garden.zeta k
    (Gm.base.frequency a)
  rw [htv] at hinner
  dsimp only
  rw [IncTop.RootMeasure.at_amplitude, mul_assoc, hinner]
  simp only [treeStarProfile]
  ring

/-- **The star-weighted layer-zero tree kernel is the presentation × leaf-cell mixture on the time box.** -/
theorem tree_star_kernel_eq_ext {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hwf : X.wf = true) (h0 : ∀ a, LG.layer a = 0) (hd : 3 ≤ d) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ)
    {Binput Ccover : ℝ} (hBi : 0 ≤ Binput) (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal Binput)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    {I : Type*} [Fintype I] (c : I → ℂ) (hc : ∀ i, ‖LG.garden.zeta * c i‖ ≤ 1)
    (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i))
    (hH : ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      RA1Leafwise.treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s = fun g =>
      RA1Leafwise.treeWickArrayWeight g * ∑ i, c i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
        (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s)
    {θ : ℝ} (hθ : 0 ≤ θ) (E : I → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam)) < ⊤)
    (hEnv : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (LG.garden.sig 0)).length → Mom d),
      ‖physicalWeightedCellSymbol L δ γ z β γ' (J i) (C i) lam‖ ≤ E i lam)
    (Jst : ℕ) (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sset, IncTop.StarPresented Jst (ω a) (cω a))
    (t : Fin 2 → ℝ) (hs : 0 ≤ t 1) (hst : t 1 < t 0) (ht : t 0 ≤ 1) (k : Mom d) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t 0) (t 1) k (fun _ => 0) 0 (IncTop.starWeight Sset ω) =
      ∫ u, ((IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).at k).amplitude u.2 *
        rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u.1 *
        (unitSquareCutoff t * pairedInverseProfile (fun lam => treeStarProfile hX L δ γ
          (IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).base.frequency
          (fun i => LG.garden.zeta * c i) J C S lam u) t)
        ∂(treeLeafCellMeasure S).prod (IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).base.μ := by
  set Gm := IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX) with hGm
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hbox : ∀ i, t i ∈ Icc (0:ℝ) 1 := by
    intro i
    fin_cases i
    · exact ⟨hs.trans hst.le, ht⟩
    · exact ⟨hs, hst.le.trans ht⟩
  rw [tree_star_kernel_eq_inner hX hwf h0 hd hL γ δ hBi H hf S hcover hS c hc J C hC hH hθ E hmE hpE hfE hEnv
    Jst Sset ω cω hpres t hs hst ht k]
  have hiE (i : I) : Integrable (E i) := by
    refine ⟨(hmE i).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hpE i))]
    refine lt_of_le_of_lt (lintegral_mono fun lam => ?_) (hfE i)
    exact le_mul_of_one_le_left bot_le (one_le_wL hθ lam)
  have hmP := stronglyMeasurable_treeStarProfile hX hLp δ γ Gm.base.frequency_measurable
    (fun i => LG.garden.zeta * c i) J C (fun i => (hC i).meas) S
  have hiSum : Integrable (fun lam => ∑ i, treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam) :=
    integrable_finsetSum _ (fun i _ => (hiE i).const_mul _)
  have hpip (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) × _) :
      ‖pairedInverseProfile (fun lam => treeStarProfile hX L δ γ Gm.base.frequency
        (fun i => LG.garden.zeta * c i) J C S lam u) t‖ ≤
        ∫ lam, ∑ i, treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam := by
    unfold pairedInverseProfile
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hiSum ?_
    filter_upwards [ae_all_iff.mpr hEnv] with lam hlam
    simpa only [norm_mul, norm_e2, mul_one] using
      norm_treeStarProfile_le hX L δ γ Gm.base.frequency _ hc J C S E hpE lam hlam u
  have hmpip := (stronglyMeasurable_treePairedProfile (fun lam u => treeStarProfile hX L δ γ Gm.base.frequency
    (fun i => LG.garden.zeta * c i) J C S lam u) hmP).comp_measurable
      ((measurable_const (a := t)).prodMk measurable_id)
  have hrA : Integrable (fun u => rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S)
      k u) (treeLeafCellMeasure S) := by
    have hh := integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar (RA1Leafwise.treeInputFunctionsL LG H)
      (K := 40*d) (M := 40*d) (by omega) (by omega) hBi hf S hS (fun _ => (1:ℂ)) stronglyMeasurable_const
      (D := 1) (fun _ => by simp) k
    simpa only [mul_one] using hh
  have hfub := fubini_amp_mixture (treeLeafCellMeasure S) Gm.base.μ _ hrA _ (Gm.at k).amplitude_integrable
    (fun u => unitSquareCutoff t * pairedInverseProfile (fun lam => treeStarProfile hX L δ γ Gm.base.frequency
      (fun i => LG.garden.zeta * c i) J C S lam u) t) hmpip.aestronglyMeasurable (fun u => by
        rw [unitSquareCutoff_eq_one hbox, one_mul]; exact hpip u)
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun a => ?_)) hfub
  dsimp only
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp only
  rw [unitSquareCutoff_eq_one hbox, one_mul]

end WaveTurbulence.Flower.FiltCoh
