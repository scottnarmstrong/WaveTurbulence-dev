/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltWickTree
public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarFinal

/-! # FILT-COH (d2f): layer-zero paired trees with star weights and both filter layers

`exists_tree_filt_bound_theta`: for a layer-zero regular paired tree with normalized leaf profiles, ANY star weights
(`StarPresented (30d)`) and two filter layers with scales `M, Mu ≥ L`, the kernel with D5's multiplier
`d5Mult S ω F ann M Fu Mu` has `X^{θ,30d,0}` norm `≤ Ck (Ck δ)^n ∏ cω`, every `θ ≤ 1 - η/8`, order `n > 0`.

FiltCoh's tree star pipeline (`TreeStarExt`, `TreeStarBound`, `TreeStarFinal`) with the filtered physical symbol:
`treeFiltProfile` (presentation-parametrized moving-root profile of shifted filtered symbols), the kernel as the
presentation × leaf-cell mixture (`tree_filt_kernel_eq_ext`), its norm (`tree_filt_ext_norm_le`, INC-TOP's root
mixture bound on main's root partition) and main's tree budget, with the envelope `filt_symbol_envelope`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst Set MainCoef
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure rootChar rootJetConstant)
open scoped ENNReal

variable {d : ℕ}

attribute [-instance] WaveTurbulence.Mole.instFintypePositionCode

/-- The filtered tree profile with presentation parameter. -/
@[expose] def treeFiltProfile {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) (L δ γ : ℝ)
    (ψ : Fin (X.treeLinks (G.sig 0)).length → ℝ → ℂ) {α : Type}
    (ν : α → PairedMomentum d (X.treeLinks (G.sig 0)).length) {I : Type*} [Fintype I] (c : I → ℂ)
    (J : I → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (lam : ℝ × ℝ) (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) × α) : ℂ :=
  ∑ i, c i * treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ (ν u.2) (J i) (C i)) S lam u.1

theorem stronglyMeasurable_treeFiltProfile {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) {L : ℝ}
    (hL : 0 < L) (δ γ : ℝ) (ψ : Fin (X.treeLinks (G.sig 0)).length → ℝ → ℂ) {α : Type} [MeasurableSpace α]
    {ν : α → PairedMomentum d (X.treeLinks (G.sig 0)).length} (hν : Measurable ν)
    {I : Type*} [Fintype I] (c : I → ℂ) (J : I → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, StronglyMeasurable (Function.uncurry (C i)))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (Function.uncurry (treeFiltProfile hX L δ γ ψ ν c J C S)) := by
  unfold treeFiltProfile
  refine Finset.stronglyMeasurable_fun_sum _ (fun i _ => ?_)
  refine StronglyMeasurable.const_mul ?_ (c i)
  exact stronglyMeasurable_treeNormalizedScalar_param hX
    (fun a lam β γ' z => filtShiftedSymbol L δ γ ψ (ν a) (J i) (C i) lam β γ' z)
    (fun z => stronglyMeasurable_shifted (fun lam β γ' z => filtCellSymbol L δ γ ψ z β γ' (J i) (C i) lam)
      z (stronglyMeasurable_filtCellSymbol_joint hL δ γ ψ (J i) (hC i) z) hν) S

theorem norm_treeFiltProfile_le {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) (L δ γ : ℝ)
    (ψ : Fin (X.treeLinks (G.sig 0)).length → ℝ → ℂ)
    {α : Type} (ν : α → PairedMomentum d (X.treeLinks (G.sig 0)).length)
    {I : Type*} [Fintype I] (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (J : I → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (E : I → (ℝ × ℝ) → ℝ) (hpE : ∀ i lam, 0 ≤ E i lam) (lam : ℝ × ℝ)
    (hEnv : ∀ i, ∀ (z : (Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (G.sig 0)).length → Mom d),
      ‖filtCellSymbol L δ γ ψ z β γ' (J i) (C i) lam‖ ≤ E i lam)
    (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) × α) :
    ‖treeFiltProfile hX L δ γ ψ ν c J C S lam u‖ ≤
      ∑ i, treeSpectralFrequencyLoss X (G.sig 0) * E i lam := by
  unfold treeFiltProfile
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have hh := treeNormalizedScalar_norm_le hX (filtShiftedSymbol L δ γ ψ (ν u.2) (J i) (C i)) S zero_le_one
    (hpE i lam) lam (fun z β γ' => by
      have h1 := hEnv i z (shiftL β (ν u.2) 0) (shiftL γ' (ν u.2) 1)
      have h2 : (0:ℝ) ≤ (∑ j, ‖β j‖) + (∑ j, ‖γ' j‖) := by positivity
      calc ‖filtShiftedSymbol L δ γ ψ (ν u.2) (J i) (C i) lam β γ' z‖ ≤ E i lam := h1
        _ ≤ 1 * (1 + ((∑ j, ‖β j‖) + (∑ j, ‖γ' j‖))) * E i lam := by nlinarith [hpE i lam]) u.1
  rw [one_mul] at hh
  have hl : 0 ≤ treeSpectralFrequencyLoss X (G.sig 0) * E i lam :=
    mul_nonneg (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X _)) (hpE i lam)
  calc ‖c i‖ * ‖treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ (ν u.2) (J i) (C i)) S lam u.1‖
      ≤ 1 * (treeSpectralFrequencyLoss X (G.sig 0) * E i lam) :=
        mul_le_mul (hc i) hh (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The D5-weighted kernel as an iterated presentation / leaf-cell integral. -/
theorem tree_filt_kernel_eq_inner {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hwf : X.wf = true) (h0 : ∀ a, LG.layer a = 0) (hd : 3 ≤ d) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (hδ : 0 < δ)
    {Binput Ccover : ℝ} (hBi : 0 ≤ Binput) (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal Binput)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    {I : Type*} [Fintype I] (c : I → ℂ)
    (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i))
    (hH : ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      RA1Leafwise.treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s = fun g =>
      RA1Leafwise.treeWickArrayWeight g * ∑ i, c i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
        (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s)
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (Mf : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) {Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hφ : ∀ j u, ‖FiltSrc.treeLinkFilt hX F Fu ann Mf Mu j u‖ ≤ Bφ)
    {θ : ℝ} (hθ : 0 ≤ θ) (E : I → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam)) < ⊤)
    (hEnv : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (LG.garden.sig 0)).length → Mom d),
      ‖filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) (FiltSrc.treeLinkFilt hX F Fu ann Mf Mu)) z β γ' (J i) (C i)
        lam‖ ≤ E i lam)
    (Jst : ℕ) (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sset, IncTop.StarPresented Jst (ω a) (cω a))
    (t : Fin 2 → ℝ) (hs : 0 ≤ t 1) (hst : t 1 < t 0) (ht : t 0 ≤ 1) (k : Mom d) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t 0) (t 1) k (fun _ => 0) 0 (d5Mult Sset ω F ann Mf Fu Mu) =
      ∫ a, ((IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).at k).amplitude a *
        ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u *
          pairedInverseProfile (fun lam => treeFiltProfile hX L δ γ
            (profFilt (L^(2*γ)*(2*δ)) (FiltSrc.treeLinkFilt hX F Fu ann Mf Mu))
            (IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).base.frequency
            (fun i => LG.garden.zeta * c i) J C S lam (u, a)) t ∂treeLeafCellMeasure S
        ∂(IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).base.μ := by
  set Gm := IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX) with hGm
  have htv : (![t 0, t 1] : Fin 2 → ℝ) = t := by funext i; fin_cases i <;> rfl
  rw [kernelLeavesW_tree_filt_eq hX hwf h0 (by omega) hL γ δ (K := 40*d) (M := 40*d) (by omega) (by omega) H hf
    Jst Sset ω cω hpres F ann Mf Fu Mu hφ hs hst ht k]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  have hinner := tree_filt_inner_mixture hX h0 c J C hC hL γ δ (t 0) (t 1) hδ (hH _ _ hs hst ht)
    (K := 40*d) (M := 40*d) (by omega) (by omega) hBi H hf S hcover hS
    (FiltSrc.treeLinkFilt hX F Fu ann Mf Mu) hBφ hφ hθ E hmE hpE hfE hEnv LG.garden.zeta k
    (Gm.base.frequency a)
  rw [htv] at hinner
  dsimp only
  rw [IncTop.RootMeasure.at_amplitude, mul_assoc, hinner]
  simp only [treeFiltProfile]
  ring

/-- **The D5-weighted layer-zero tree kernel is the presentation × leaf-cell mixture on the time box.** -/
theorem tree_filt_kernel_eq_ext {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hwf : X.wf = true) (h0 : ∀ a, LG.layer a = 0) (hd : 3 ≤ d) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (hδ : 0 < δ)
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
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (Mf : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) {Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hφ : ∀ j u, ‖FiltSrc.treeLinkFilt hX F Fu ann Mf Mu j u‖ ≤ Bφ)
    {θ : ℝ} (hθ : 0 ≤ θ) (E : I → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam)) < ⊤)
    (hEnv : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (LG.garden.sig 0)).length → Mom d),
      ‖filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) (FiltSrc.treeLinkFilt hX F Fu ann Mf Mu)) z β γ' (J i) (C i)
        lam‖ ≤ E i lam)
    (Jst : ℕ) (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sset, IncTop.StarPresented Jst (ω a) (cω a))
    (t : Fin 2 → ℝ) (hs : 0 ≤ t 1) (hst : t 1 < t 0) (ht : t 0 ≤ 1) (k : Mom d) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t 0) (t 1) k (fun _ => 0) 0 (d5Mult Sset ω F ann Mf Fu Mu) =
      ∫ u, ((IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).at k).amplitude u.2 *
        rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u.1 *
        (unitSquareCutoff t * pairedInverseProfile (fun lam => treeFiltProfile hX L δ γ
          (profFilt (L^(2*γ)*(2*δ)) (FiltSrc.treeLinkFilt hX F Fu ann Mf Mu))
          (IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).base.frequency
          (fun i => LG.garden.zeta * c i) J C S lam u) t)
        ∂(treeLeafCellMeasure S).prod (IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX)).base.μ := by
  set Gm := IncTop.starRootMeasure Jst Sset ω cω hpres (IncTop.treeRow hX) with hGm
  set ψ := profFilt (L^(2*γ)*(2*δ)) (FiltSrc.treeLinkFilt hX F Fu ann Mf Mu) with hψ
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hbox : ∀ i, t i ∈ Icc (0:ℝ) 1 := by
    intro i
    fin_cases i
    · exact ⟨hs.trans hst.le, ht⟩
    · exact ⟨hs, hst.le.trans ht⟩
  rw [tree_filt_kernel_eq_inner hX hwf h0 hd hL γ δ hδ hBi H hf S hcover hS c J C hC hH F ann Mf Fu Mu hBφ hφ hθ
    E hmE hpE hfE hEnv Jst Sset ω cω hpres t hs hst ht k]
  have hiE (i : I) : Integrable (E i) := by
    refine ⟨(hmE i).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hpE i))]
    refine lt_of_le_of_lt (lintegral_mono fun lam => ?_) (hfE i)
    exact le_mul_of_one_le_left bot_le (one_le_wL hθ lam)
  have hmP := stronglyMeasurable_treeFiltProfile hX hLp δ γ ψ Gm.base.frequency_measurable
    (fun i => LG.garden.zeta * c i) J C (fun i => (hC i).meas) S
  have hiSum : Integrable (fun lam => ∑ i, treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam) :=
    integrable_finsetSum _ (fun i _ => (hiE i).const_mul _)
  have hpip (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) × _) :
      ‖pairedInverseProfile (fun lam => treeFiltProfile hX L δ γ ψ Gm.base.frequency
        (fun i => LG.garden.zeta * c i) J C S lam u) t‖ ≤
        ∫ lam, ∑ i, treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam := by
    unfold pairedInverseProfile
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hiSum ?_
    filter_upwards [ae_all_iff.mpr hEnv] with lam hlam
    simpa only [norm_mul, norm_e2, mul_one] using
      norm_treeFiltProfile_le hX L δ γ ψ Gm.base.frequency _ hc J C S E hpE lam hlam u
  have hmpip := (stronglyMeasurable_treePairedProfile (fun lam u => treeFiltProfile hX L δ γ ψ Gm.base.frequency
    (fun i => LG.garden.zeta * c i) J C S lam u) hmP).comp_measurable
      ((measurable_const (a := t)).prodMk measurable_id)
  have hrA : Integrable (fun u => rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S)
      k u) (treeLeafCellMeasure S) := by
    have hh := integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar (RA1Leafwise.treeInputFunctionsL LG H)
      (K := 40*d) (M := 40*d) (by omega) (by omega) hBi hf S hS (fun _ => (1:ℂ)) stronglyMeasurable_const
      (D := 1) (fun _ => by simp) k
    simpa only [mul_one] using hh
  have hfub := fubini_amp_mixture (treeLeafCellMeasure S) Gm.base.μ _ hrA _ (Gm.at k).amplitude_integrable
    (fun u => unitSquareCutoff t * pairedInverseProfile (fun lam => treeFiltProfile hX L δ γ ψ Gm.base.frequency
      (fun i => LG.garden.zeta * c i) J C S lam u) t) hmpip.aestronglyMeasurable (fun u => by
        rw [unitSquareCutoff_eq_one hbox, one_mul]; exact hpip u)
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun a => ?_)) hfub
  dsimp only
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp only
  rw [unitSquareCutoff_eq_one hbox, one_mul]

/-- **The norm of the filtered tree extension.** -/
theorem tree_filt_ext_norm_le {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hd : 3 ≤ d) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) {Binput Ccover : ℝ} (hBi : 0 ≤ Binput)
    (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal Binput)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ → ℂ)
    {I : Type*} [Fintype I] (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, StronglyMeasurable (Function.uncurry (C i)))
    {θ : ℝ} (hθ : 0 ≤ θ) (E : I → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam)) < ⊤)
    (hEnv : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (LG.garden.sig 0)).length → Mom d),
      ‖filtCellSymbol L δ γ ψ z β γ' (J i) (C i) lam‖ ≤ E i lam)
    {α : Type} [MeasurableSpace α] (Gm : RootMeasure d (X.treeLinks (LG.garden.sig 0)).length α)
    (hfin : Gm.momentMass (30*d) < ⊤) :
    Fourier.mixedFourierNorm θ (30*d) 0 (fun t k =>
      ∫ u, (Gm.at k).amplitude u.2 *
        rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u.1 *
        (unitSquareCutoff t * pairedInverseProfile (fun lam => treeFiltProfile hX L δ γ ψ Gm.base.frequency
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
  have hmP := stronglyMeasurable_treeFiltProfile hX hLp δ γ ψ Gm.base.frequency_measurable c J C hC S
  let Bs : (ℝ × ℝ) → ℝ≥0∞ := fun lam =>
    ENNReal.ofReal (∑ i, treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam)
  have hmB : Measurable Bs := ENNReal.measurable_ofReal.comp
    (Finset.measurable_sum _ (fun i _ => measurable_const.mul (hmE i)))
  have hbound (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) × α) :
      ∀ᵐ lam : ℝ × ℝ, ‖treeFiltProfile hX L δ γ ψ Gm.base.frequency c J C S lam u‖ₑ ≤ Bs lam := by
    filter_upwards [ae_all_iff.mpr hEnv] with lam hlam
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_treeFiltProfile_le hX L δ γ ψ Gm.base.frequency c hc J C S E hpE lam
      hlam u)
  have hfB : (∫⁻ lam, wL θ lam * Bs lam) < ⊤ := by
    have he : (∫⁻ lam, wL θ lam * Bs lam) =
        ∑ i, ENNReal.ofReal (treeSpectralFrequencyLoss X (LG.garden.sig 0)) *
          ∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam) :=
      lintegral_wL_ofReal_sum θ _ (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X _)) E hmE hpE
    rw [he]
    exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfE i))
  have hiA (u : (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) × α) :
      Integrable (fun lam => treeFiltProfile hX L δ γ ψ Gm.base.frequency c J C S lam u) :=
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
      treeFiltProfile hX L δ γ ψ Gm.base.frequency c J C S lam u) t)
    (stronglyMeasurable_treePairedProfile (fun lam u => treeFiltProfile hX L δ γ ψ Gm.base.frequency c J C S lam u)
      hmP)
    (fun u => integrable_mul_pairedInverseProfile integrable_unitSquareCutoff (hiA u)) hH
    (fun u => eLpNorm_treePairedProfile_one_le (hiA u) (hbound u)) hfin
  refine hmain.trans (mul_le_mul' le_rfl ?_)
  exact mixedFourierNorm00_pairedProfile_le hθ integrable_unitSquareCutoff hiA hmB hbound

/-- The D5 filter on a tree link is a product of at most four good factors in energy coordinates. -/
theorem tree_linkFilt_filtMul {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) {μ : ℝ}
    (hμ : 0 < μ) (hM : ∀ b ∈ F, 1 ≤ μ * M b / 2) (hMu : ∀ b ∈ Fu, 1 ≤ μ * Mu b / 2)
    (j : Fin (X.treeLinks (G.sig 0)).length) :
    FiltMul d (Kfilt d) 4 (profFilt μ (FiltSrc.treeLinkFilt hX F Fu ann M Mu) j) := by
  have h := filtMul_linkFiltWeight (d := d) (FiltSrc.treeLinkBlock hX j) F Fu ann M Mu hμ hM hMu
  refine h.mono ?_
  have h1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := F) (s₂ := FiltSrc.treeLinkBlock hX j))
  have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := Fu) (s₂ := FiltSrc.treeLinkBlock hX j))
  have h3 := FiltSrc.card_treeLinkBlock_le hX j
  omega

/-- **Layer-zero paired trees with star weights and both filter layers in `X^{θ,30d,0}`.** -/
theorem exists_tree_filt_bound_theta (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8) {Binput : ℝ} (hBi : 0 ≤ Binput) :
    ∃ Ck : ℝ, 1 ≤ Ck ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ X : RegChain, X.wf = true → X.size = 2*n →
      ∀ (LG : LayeredGarden 1), X.DecodesTree LG.garden → (∀ a, LG.layer a = 0) →
      ∀ H : LGSpine.LeafProfiles 1 d,
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.addrFam H z) ≤ ENNReal.ofReal Binput) →
      ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, L ≤ Mu b) →
      Fourier.mixedRestrictionNorm θ (30*d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts.val 0) (ts.val 1) k.val
          (fun _ => 0) 0 (d5Mult Sset ω F ann M Fu Mu)) ≤
        ENNReal.ofReal (Ck*(Ck*δ)^n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
  classical
  let Cbase := max 1 |CTη η|
  have hCbase : 1 ≤ Cbase := le_max_left _ _
  obtain ⟨Bfl, hBfl1, -, hBflT⟩ := FiltSrc.exists_linkFilt_bound
  obtain ⟨Kr,Cw,hKr,hCw,henv⟩ := filt_symbol_envelope hd hγ hη0 hη hηγ hθ0 hθ
    (Agev := ClassJR.A1) A1_nonneg hCbase (one_le_Kfilt d) 4
  obtain ⟨Ccover,hCcover,hcover⟩ := actual_tree_augmented_uniform_cell_cover d (by omega)
  let a := rootLocalOverlapConstant d
  let b := treeRootLeafDerivativeConstant d (30*d)
  let p := leafMomentLocalizationConstant d (30*d+1) (40*d)*treeAugmentedInputBound d (40*d) (40*d) Binput
  let Hc := ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff
  have ha : 0 ≤ a := (rootLocalOverlapConstant_pos d).le
  have hb : 0 ≤ b := treeRootLeafDerivativeConstant_nonneg d (30*d)
  have hp : 0 ≤ p := by
    apply mul_nonneg
    · unfold leafMomentLocalizationConstant
      exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg _))
    · exact (treeAugmentedInputBound_pos d (40*d) (40*d) Binput).le
  have hH : Hc < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (timeFourierNorm_unitSquareCutoff_lt_top _)
  obtain ⟨Ck,hCk,hbudget⟩ := RA1Leafwise.tree_error_budget_absorption ha hb hCcover.le hp
    (by norm_num : (0:ℝ) ≤ 2) hKr.le (zero_le_one.trans hCw) Hc hH
  have hR0 : 0 < rootJetConstant (30*d) := IncTop.rootJetConstant_pos _
  set Cf := Ck * max 1 (rootJetConstant (30*d)) with hCf
  have hCf1 : 1 ≤ Cf := one_le_mul_of_one_le_of_one_le hCk (le_max_left _ _)
  refine ⟨Cf, hCf1, fun Aorder => ?_⟩
  obtain ⟨L₁,henv⟩ := henv Aorder
  refine ⟨max L₁ 4,?_⟩
  intro L hL δ hδ hδ1 n hn hnlog X hwf hsize LG hX h0 H hF Sset ω cω hpres F ann Mf hMf Fu Mu hMu
  have hL4 : 4 ≤ L := (le_max_right L₁ 4).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδp : 0 < δ := by have := (Real.rpow_pos_of_pos hLp (-(η/2))).trans_le hδ; linarith
  set m := (X.treeLinks (LG.garden.sig 0)).length with hmdef
  have hlen : m = n := by
    have hh := chain_linksAt_length X (LG.garden.sig 0) ((0:Fin 1),[])
    change (X.treeLinks (LG.garden.sig 0)).length*2=X.size at hh
    omega
  have hmpos : 0 < m := by omega
  have hmlog : (m:ℝ) ≤ Real.log L^Aorder := by rw [hlen]; exact hnlog
  obtain ⟨C,hC,_hlead,hphase⟩ := RA1Leafwise.actual_tree_physical_phase_profiles_classified hη0
    (by linarith : η ≤ 2) (le_refl ClassJR.A1) X hwf (LG.garden.sig 0)
  choose S hS hcov using hcover LG.garden X hX
  let I := (ClassJR.chosenSet ((toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)))).powerset
  let J := fun Z : I => treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val
  let cZ := fun Z : I => (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)
  have hcZ (Z : I) : ‖LG.garden.zeta * cZ Z‖ ≤ 1 := by
    rw [norm_mul, tree_garden_zeta_norm, one_mul]
    exact tree_coefficient_weight_norm_le Z.val
  have hexp : 2*X.size+1=4*m+1 := by omega
  have hCs (Z : I) : SRep (1-η/8) (η/4) (1-η/2) ClassJR.A1 (Cbase^(4*m+1)) (C Z) := by
    apply tree_SRep_mono_mass (hC Z) A1_nonneg
    rw [hexp]
    exact tree_literal_coefficient_mass_le (CTη η) _
  have hE (Z : I) := henv L ((le_max_left _ _).trans hL) δ hδ hδ1 m hmpos hmlog (J Z) (C Z) (hCs Z)
  choose E hmE hpE hbE hgE using hE
  set P0 : ℝ := 2*(Kr*δ)^m with hP0
  have hP0n : 0 ≤ P0 := by positivity
  have hmE' (Z : I) : Measurable (fun lam => P0 * E Z lam) := measurable_const.mul (hmE Z)
  have hpE' (Z : I) (lam : ℝ × ℝ) : 0 ≤ P0 * E Z lam := mul_nonneg hP0n (hpE Z lam)
  have hwE (Z : I) : (∫⁻ lam, wL θ lam * ENNReal.ofReal (P0 * E Z lam)) ≤
      ENNReal.ofReal P0 * ENNReal.ofReal Cw ^ m := by
    have he : (∫⁻ lam, wL θ lam * ENNReal.ofReal (P0 * E Z lam)) =
        ENNReal.ofReal P0 * ∫⁻ lam, wL θ lam * ENNReal.ofReal (E Z lam) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun lam => ?_
      rw [ENNReal.ofReal_mul hP0n]
      ring
    rw [he]
    exact mul_le_mul' le_rfl (hbE Z)
  have hfE' (Z : I) : (∫⁻ lam, wL θ lam * ENNReal.ofReal (P0 * E Z lam)) < ⊤ :=
    (hwE Z).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
  set φ := FiltSrc.treeLinkFilt hX F Fu ann Mf Mu with hφdef
  have hφ : ∀ j u, ‖φ j u‖ ≤ Bfl := fun j u => hBflT hX F Fu ann Mf Mu j u
  have hμ'0 : 0 < L^(2*γ)*(2*δ) := mul_pos (Real.rpow_pos_of_pos hLp _) (by linarith)
  set ψ := profFilt (L^(2*γ)*(2*δ)) φ with hψdef
  have hψ : ∀ j, FiltMul d (Kfilt d) 4 (ψ j) := fun j =>
    tree_linkFilt_filtMul hX F Fu ann Mf Mu hμ'0
      (fun b hb => filt_scale_ge_one hL4 hγ.1.le hη hδ (hMf b hb))
      (fun b hb => filt_scale_ge_one hL4 hγ.1.le hη hδ (hMu b hb)) j
  have hEnv' (Z : I) : ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin m × Fin 2) → Fin d → ℤ) (β γ' : Fin m → Mom d),
      ‖filtCellSymbol L δ γ ψ z β γ' (J Z) (C Z) lam‖ ≤ P0 * E Z lam := by
    filter_upwards [hgE Z] with lam hlam z β γ'
    exact hlam z β γ' ψ hψ
  have hH' : ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      RA1Leafwise.treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s = fun g =>
      RA1Leafwise.treeWickArrayWeight g * ∑ Z : I, cZ Z * ∫ lam, resProfile (J Z) (fun Ω => C Z (ofLp Ω) lam)
        (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s := by
    intro t s hs hst ht
    funext g
    unfold RA1Leafwise.treeOriginalArrayCoefficient RA1Leafwise.treeOriginalLatticeCoefficient
      RA1Leafwise.treeWickArrayWeight
    rw [hphase d L γ δ LG rfl h0 hX t s hs hst ht 0 (fun p => if p.2=0 then g.1 p.1 else g.2 p.1)]
    simp only [ite_true, show (1:Fin 2) ≠ 0 by decide, ite_false, Complex.ofReal_prod]
    rfl
  have hf : ∀ b, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.treeInputFunctionsL LG H b) ≤
      ENNReal.ofReal Binput := fun _ => hF _
  set Gm := IncTop.starRootMeasure (30*d) Sset ω cω hpres (IncTop.treeRow hX) with hGm
  have hmom : Gm.momentMass (30*d) ≤ ∏ a ∈ Sset, ENNReal.ofReal (cω a) :=
    IncTop.starRootMeasure_momentMass_le (30*d) Sset ω cω hpres (IncTop.treeRow hX)
  have hfin : Gm.momentMass (30*d) < ⊤ :=
    hmom.trans_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))
  -- the extension
  have hbox (t : timeBoxGt 0 0) :
      ((t.val 0∈Set.Icc (0:ℝ) 1) ∧ (t.val 1∈Set.Icc (0:ℝ) 1)) ∧ t.val 1<t.val 0 := by
    simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using t.property
  let Ext : (Fin 2 → ℝ) → Mom d → ℂ := fun t k =>
    ∫ u, (Gm.at k).amplitude u.2 *
      rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u.1 *
      (unitSquareCutoff t * pairedInverseProfile (fun lam => treeFiltProfile hX L δ γ ψ Gm.base.frequency
        (fun Z => LG.garden.zeta * cZ Z) J C S lam u) t) ∂(treeLeafCellMeasure S).prod Gm.base.μ
  refine (Fourier.mixedRestrictionNorm_le_extension Ext (fun t k => (tree_filt_kernel_eq_ext hX hwf h0 hd hL1 γ δ
    hδp hBi H hf S hcov hS cZ hcZ J C (fun Z => (hC Z).reg) hH' F ann Mf Fu Mu (zero_le_one.trans hBfl1) hφ hθ0
    (fun Z lam => P0 * E Z lam) hmE' hpE' hfE' hEnv'
    (30*d) Sset ω cω hpres t.val (hbox t).1.2.1 (hbox t).2 (hbox t).1.1.2 k.val).symm)).trans ?_
  refine (tree_filt_ext_norm_le hX hd hL1 γ δ hBi H hf S hS ψ (fun Z => LG.garden.zeta * cZ Z) hcZ J C
    (fun Z => (hC Z).reg.meas) hθ0 (fun Z lam => P0 * E Z lam) hmE' hpE' hfE' hEnv' Gm hfin).trans ?_
  -- arithmetic
  set loss := treeSpectralFrequencyLoss X (LG.garden.sig 0) with hloss
  have hloss1 : 1 ≤ loss := one_le_treeSpectralFrequencyLoss X _
  have hcardI : Fintype.card I = 2^m := tree_coefficient_subset_count X (LG.garden.sig 0)
  have hint : (∫⁻ lam, wL θ lam * ENNReal.ofReal (∑ Z : I, loss * (P0 * E Z lam))) ≤
      (2:ℝ≥0∞)^m * (ENNReal.ofReal (2*(Kr*δ)^m*loss) * (ENNReal.ofReal 1 * (2*ENNReal.ofReal Cw^m))) := by
    rw [lintegral_wL_ofReal_sum θ loss (zero_le_one.trans hloss1) _ hmE' hpE']
    calc (∑ Z : I, ENNReal.ofReal loss * ∫⁻ lam, wL θ lam * ENNReal.ofReal (P0 * E Z lam))
        ≤ ∑ _Z : I, ENNReal.ofReal loss * (ENNReal.ofReal P0 * ENNReal.ofReal Cw ^ m) :=
          Finset.sum_le_sum fun Z _ => mul_le_mul' le_rfl (hwE Z)
      _ = (2:ℝ≥0∞)^m * (ENNReal.ofReal loss * (ENNReal.ofReal P0 * ENNReal.ofReal Cw ^ m)) := by
          rw [Finset.sum_const, Finset.card_univ, hcardI, nsmul_eq_mul]
          norm_num
      _ ≤ _ := by
          rw [ENNReal.ofReal_one, one_mul, hP0, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2*(Kr*δ)^m)]
          have h2 : (1:ℝ≥0∞) ≤ 2 := by norm_num
          calc (2:ℝ≥0∞)^m * (ENNReal.ofReal loss * (ENNReal.ofReal (2*(Kr*δ)^m) * ENNReal.ofReal Cw ^ m))
              = (2:ℝ≥0∞)^m * (ENNReal.ofReal (2*(Kr*δ)^m) * ENNReal.ofReal loss * (1 * ENNReal.ofReal Cw ^ m)) := by
                ring
            _ ≤ _ := by gcongr
  have hcard : Fintype.card (TPlus LG.garden) + 1 = 2*m+1 := by rw [tree_input_count hX]
  have hb2 := hbudget m δ loss 1 hδp.le (zero_le_one.trans hloss1)
    (RA1Leafwise.treeSpectralFrequencyLoss_le_geometric X (LG.garden.sig 0)) zero_le_one
  rw [hcard]
  calc (ENNReal.ofReal a * (ENNReal.ofReal (rootJetConstant (30*d)) *
        ((ENNReal.ofReal b * (ENNReal.ofReal (Ccover^m) * ENNReal.ofReal p^(2*m+1))) *
          Gm.momentMass (30*d)))) *
        (ENNReal.ofReal (2^θ) * Fourier.timeFourierNorm θ unitSquareCutoff *
          ∫⁻ lam, wL θ lam * ENNReal.ofReal (∑ Z : I, loss * (P0 * E Z lam)))
      ≤ (ENNReal.ofReal a * (ENNReal.ofReal (rootJetConstant (30*d)) *
        ((ENNReal.ofReal b * (ENNReal.ofReal (Ccover^m) * ENNReal.ofReal p^(2*m+1))) *
          ∏ a ∈ Sset, ENNReal.ofReal (cω a)))) *
        (Hc * ((2:ℝ≥0∞)^m * (ENNReal.ofReal (2*(Kr*δ)^m*loss) * (ENNReal.ofReal 1 * (2*ENNReal.ofReal Cw^m))))) := by
        gcongr
    _ = ((ENNReal.ofReal a*(ENNReal.ofReal b*(ENNReal.ofReal (Ccover^m)*ENNReal.ofReal p^(2*m+1)))) *
          (Hc*(ENNReal.ofReal (2*(Kr*δ)^m*loss)*((2:ℝ≥0∞)^m*(ENNReal.ofReal 1*(2*ENNReal.ofReal Cw^m)))))) *
        (ENNReal.ofReal (rootJetConstant (30*d)) * ∏ a ∈ Sset, ENNReal.ofReal (cω a)) := by ring
    _ ≤ ENNReal.ofReal (Ck*(Ck*δ)^m*1) *
        (ENNReal.ofReal (rootJetConstant (30*d)) * ∏ a ∈ Sset, ENNReal.ofReal (cω a)) :=
        mul_le_mul' hb2 le_rfl
    _ = ENNReal.ofReal (Ck*(Ck*δ)^m*rootJetConstant (30*d)) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
        rw [mul_one, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Cf*(Cf*δ)^n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
        rw [← hlen]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have hM1 : 1 ≤ max 1 (rootJetConstant (30*d)) := le_max_left _ _
        have hMR : rootJetConstant (30*d) ≤ max 1 (rootJetConstant (30*d)) := le_max_right _ _
        have hCk0 : 0 ≤ Ck := zero_le_one.trans hCk
        have h1 : (Ck*δ)^m ≤ (Cf*δ)^m := by
          apply pow_le_pow_left₀ (by positivity)
          rw [hCf]
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCk0 hM1) hδp.le
        calc Ck*(Ck*δ)^m*rootJetConstant (30*d) ≤ Ck*(Cf*δ)^m*max 1 (rootJetConstant (30*d)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 hCk0) hMR hR0.le (by positivity)
          _ = Cf*(Cf*δ)^m := by rw [hCf]; ring

end WaveTurbulence.Flower.FiltCoh
