/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.ZeroStar
public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleStarBound
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeKernelReindex
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalCellExpansion
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhaseRootIndependent
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalPhaseProfiles
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeBoundedSourceAgreement
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeFiniteProfileMixture
public import WaveTurbulence.Foundations.RegAsymp.TreeRootPairedProfile
public import WaveTurbulence.Foundations.Incoh.RootAmplitudeMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootJets

/-! # FILT-COH (c2): the exact identities of a star-weighted layer-zero paired tree

* `arrayChar`, `halfCellAmplitude_arrayChar`, `treeProfileArrayScalar_char`: a lattice character on the tree's link
  arrays is absorbed by the half-cell amplitude (modulations `β + ν₀`, `γ' + ν₁`).
* `kernelLeavesW_tree_lattice`: main's tree lattice reindexing (`treeLeaves_treeLatticeEquiv`,
  `treeLeaves_eq_original_lattice_source`) with an arbitrary decoration multiplier.
* `star_swap`: a presentation-valued lattice multiplier becomes a mixture of lattice characters (generic form of
  `couple_star_swap`).
* `star_rootAmplitudeMixture_le`: INC-TOP's `mixedFourierNorm_rootProductRootMixture_le` (sha256 in COPIED-SHA256SUMS)
  for main's root partition (`Incoh.mixedFourierNorm_rootAmplitudeMixture_le`).
* `stronglyMeasurable_rootChar_treeRootLeafAmplitude_jets`: jets of the root-modulated moving-root leaf amplitude
  (main's `stronglyMeasurable_treeRootLeafAmplitude_derivative` with INC-TOP's root-modulated jets lemma). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure rootChar rootJetConstant)
open scoped ENNReal

variable {d : ℕ}

section Char
variable {n : ℕ}

/-- The lattice character of a pair of link arrays. -/
@[expose] def arrayChar (ν : PairedMomentum d n) (L : ℝ)
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) : ℂ :=
  (Real.fourierChar (∑ j, (inner ℝ (ν (j,0)) (latticePoint L (g.1 j)) +
    inner ℝ (ν (j,1)) (latticePoint L (g.2 j)))) : ℂ)

theorem norm_arrayChar (ν : PairedMomentum d n) (L : ℝ)
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) : ‖arrayChar ν L g‖ = 1 := Circle.norm_coe _

theorem fourierChar_pairedLattice (ν : PairedMomentum d n) (L : ℝ) (p : (Fin n × Fin 2) → Fin d → ℤ) :
    (Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) =
      arrayChar ν L ((fun j => p (j,0)), (fun j => p (j,1))) := by
  unfold arrayChar
  congr 2
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  rfl

/-- The lattice character is absorbed by the half-cell amplitude. -/
theorem halfCellAmplitude_arrayChar (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (ν : PairedMomentum d n) (L : ℝ) (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) :
    halfCellAmplitude z β γ' (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) *
      arrayChar ν L g =
    halfCellAmplitude z (shiftL β ν 0) (shiftL γ' ν 1)
      (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) := by
  have he : ∀ s : ℝ, (Real.fourierChar s : ℂ) = WeylSums.e s := fun _ => rfl
  unfold arrayChar halfCellAmplitude shiftL
  simp only [Circle.smul_def, he, inner_add_left, WeylSums.e_add, WeylSums.e_sum, smul_eq_mul,
    Finset.prod_mul_distrib]
  ring

/-- **The tree profile scalar with a character-twisted weight is the scalar at shifted modulations.** -/
theorem treeProfileArrayScalar_char (L μ : ℝ) (W : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) (ν : PairedMomentum d n) :
    treeProfileArrayScalar L μ (fun g => arrayChar ν L g * W g) z β γ' J C lam =
      treeProfileArrayScalar L μ W z (shiftL β ν 0) (shiftL γ' ν 1) J C lam := by
  unfold treeProfileArrayScalar treeHalfCellLatticeScalar
  refine tsum_congr fun g => ?_
  rw [← halfCellAmplitude_arrayChar]
  ring

end Char

/-- Main's tree reindexing with an arbitrary multiplier. -/
theorem kernelLeavesW_treeLatticeEquiv (L γ δ : ℝ) (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (H : LGSpine.LeafProfiles 1 d) (t s : ℝ) (k : Mom d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 m =
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
          m (cosetDecoration LG.garden L k
            (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j,0),p (j,1)))).val) *
          (((∏ j, linkWickFactor (p (j,0)) (p (j,1))):ℂ) *
            phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s
              (cosetDecoration LG.garden L k
                (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j,0),p (j,1)))).val) *
            ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k
              (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j,0),p (j,1)))).val ℓ.toNode):ℂ)) := by
  unfold Flower.Stage1W.kernelLeavesW
  congr 1
  refine ((IncohInst.treeLatticeEquiv hX d).symm.tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro p
  have hdec : ((IncohInst.treeLatticeEquiv hX d).symm p).val =
      (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j,0),p (j,1)))).val := rfl
  rw [hdec]
  congr 1
  rw [tree_epsDec_eq_linkWickFactor hX (treeDecOfParams hX (0 : Fin d → ℤ) _).property.1]
  simp only [tree_xNode_decOfParams, tree_yNode_decOfParams, Complex.ofReal_prod]

/-- **Main's original lattice source identity of a tree with an arbitrary multiplier.** -/
theorem kernelLeavesW_tree_lattice (L γ δ : ℝ) (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (H : LGSpine.LeafProfiles 1 d) (t s : ℝ) (k : Mom d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 m =
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
          m (cosetDecoration LG.garden L k
            (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j,0),p (j,1)))).val) *
          (RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s k p *
            (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
              (fun j i => latticePoint L (p (j,i)))) := by
  rw [kernelLeavesW_treeLatticeEquiv L γ δ LG hX H t s k m]
  congr 1
  apply tsum_congr
  intro p
  congr 1
  rw [RA1Leafwise.tree_sourceLeafWeight_eqL hX H k]
  unfold RA1Leafwise.treeOriginalLatticeCoefficient
  rw [tree_decOfParams_eq_coset hX L k (fun j => (p (j,0),p (j,1)))]

/-- **Star weight ↦ presentation mixture of lattice characters** (generic form of `couple_star_swap`). -/
theorem star_swap {n : ℕ} {α : Type} [MeasurableSpace α] (G : RootMeasure d n α) (L : ℝ) (k : Mom d)
    (V : ((Fin n × Fin 2) → Fin d → ℤ) → ℂ) (hV : ∀ p, V p = (G.at k).value (pairedLattice L p))
    (c g : ((Fin n × Fin 2) → Fin d → ℤ) → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1) (hg : Summable (fun p => ‖g p‖))
    (A : ℂ) :
    A * ∑' p, V p * (c p * g p) =
      ∫ a, G.base.amplitude a * rootChar (G.root a) k *
        (A * ∑' p, ((Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ) * c p) * g p)
        ∂G.base.μ := by
  classical
  let F : ((Fin n × Fin 2) → Fin d → ℤ) → α → ℂ := fun p a =>
    G.base.amplitude a * rootChar (G.root a) k *
      (Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ) * (c p * g p)
  have hnorm : ∀ p a, ‖F p a‖ ≤ ‖G.base.amplitude a‖ * ‖g p‖ := by
    intro p a
    simp only [F, norm_mul, IncTop.norm_rootChar, Circle.norm_coe, mul_one]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hc p)) (norm_nonneg _)
  have hFm : ∀ p, AEStronglyMeasurable (F p) G.base.μ := by
    intro p
    have h1 : Measurable (fun a => rootChar (G.root a) k) := IncTop.measurable_rootChar G.root_measurable k
    have h2 : Measurable (fun a => (Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ)) := by
      have hc' : Continuous (fun v : PairedMomentum d n =>
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
  have hval : ∀ p, V p * (c p * g p) = ∫ a, F p a ∂G.base.μ := by
    intro p
    rw [hV p, IncTop.RootMeasure.at_value, ← integral_mul_const]
  simp_rw [hval]
  rw [integral_tsum_of_summable_integral_norm hFi hFs, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [F]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  ring

/-- **Root-character mixtures of main's moving-root amplitudes** (INC-TOP's tree form, main's root partition). -/
theorem star_rootAmplitudeMixture_le {r N n : ℕ} {U : Type*} [MeasurableSpace U] (μ : Measure U) [SFinite μ]
    {α : Type} [MeasurableSpace α] (G : RootMeasure d n α)
    (θ : ℝ) (B : (Fin d → ℤ) → Mom d → U → ℂ) (v : (Fin d → ℤ) → U → ℝ)
    (hz : ∀ q k u, treeRootCutoff q k = 0 → B q k u = 0)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u))
    (hm : ∀ q j, j ≤ N → ∀ k, StronglyMeasurable (fun u : U × α =>
      iteratedFDeriv ℝ j (fun k => rootChar (G.root u.2) k * B q k u.1) k))
    (hv : ∀ q, Integrable (v q) μ) (hvm : ∀ q, Measurable (v q)) (hvn : ∀ q u, 0 ≤ v q u)
    (hb : ∀ q j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => B q k u) k‖ ≤ v q u)
    {Z : ℝ≥0∞} (hmass : ∀ q, (∫⁻ u, ENNReal.ofReal (v q u) ∂μ) ≤ Z)
    (K : (Fin r → ℝ) → U × α → ℂ)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × (U × α) => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => K t u) 1 ≤ H)
    (hfin : G.momentMass N < ⊤) :
    Fourier.mixedFourierNorm θ N 0
      (fun t k => ∫ u, (G.at k).amplitude u.2 * rootAmplitudeSum B k u.1 * K t u
        ∂μ.prod G.base.μ) ≤
        (ENNReal.ofReal (rootLocalOverlapConstant d) *
          (ENNReal.ofReal (rootJetConstant N) * (Z * G.momentMass N))) *
          Fourier.mixedFourierNorm00 θ K := by
  let B' := fun q k (u : U × α) => G.base.amplitude u.2 * (rootChar (G.root u.2) k * B q k u.1)
  let m := fun a : α => (1 + ‖G.root a‖) ^ N * ‖G.base.amplitude a‖
  let v' := fun q (u : U × α) => rootJetConstant N * m u.2 * v q u.1
  have hC := (IncTop.rootJetConstant_pos N).le
  have hBB (q : Fin d → ℤ) (u : U × α) : ContDiff ℝ N (fun k => rootChar (G.root u.2) k * B q k u.1) :=
    ((contDiff_momentumModulation (G.root u.2)).of_le (by exact_mod_cast le_top)).mul (hB q u.1)
  have hs (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      iteratedFDeriv ℝ j (fun k => B' q k u) k =
        G.base.amplitude u.2 • iteratedFDeriv ℝ j (fun k => rootChar (G.root u.2) k * B q k u.1) k :=
    IncTop.iteratedFDeriv_mul_amplitude _ _ ((hBB q u).of_le (by exact_mod_cast hj)) k
  have hm' (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      StronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => B' q k u) k) := by
    simp_rw [hs q j hj k]
    exact (G.amplitude_measurable.comp measurable_snd).stronglyMeasurable.smul (hm q j hj k)
  have hmint : Integrable m G.base.μ := G.integrable_momentDensity N hfin
  have hv' (q : Fin d → ℤ) : Integrable (v' q) (μ.prod G.base.μ) := by
    have h := (hv q).mul_prod hmint
    refine (h.const_mul (rootJetConstant N)).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [v']
    ring
  have hvm' (q : Fin d → ℤ) : Measurable (v' q) :=
    (measurable_const.mul ((G.measurable_momentDensity N).comp measurable_snd)).mul
      ((hvm q).comp measurable_fst)
  have hvn' (q : Fin d → ℤ) (u : U × α) : 0 ≤ v' q u :=
    mul_nonneg (mul_nonneg hC (by positivity)) (hvn _ _)
  have hb' (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      ‖iteratedFDeriv ℝ j (fun k => B' q k u) k‖ ≤ v' q u := by
    rw [hs q j hj k u, norm_smul]
    have hl := IncTop.norm_iteratedFDeriv_rootChar_mul_le (W := 0) (G.root u.2) (hB q u.1) hj
      (fun i hi k => by simpa only [pow_zero, one_mul] using hb q i hi k u.1) k
    simp only [pow_zero, one_mul] at hl
    calc
      _ ≤ ‖G.base.amplitude u.2‖ * (rootJetConstant N * (1 + ‖G.root u.2‖) ^ N * v q u.1) :=
        mul_le_mul_of_nonneg_left hl (norm_nonneg _)
      _ = v' q u := by simp only [v', m]; ring
  have hmz (q : Fin d → ℤ) : ∫⁻ u, ENNReal.ofReal (v' q u) ∂μ.prod G.base.μ ≤
      ENNReal.ofReal (rootJetConstant N) * (Z * G.momentMass N) := by
    have he := IncTop.lintegral_rootEnvelope_eq μ G N (v q) (hvm q) (hvn q)
    simp only [v', m] at he ⊢
    rw [he]
    exact mul_le_mul' le_rfl (mul_le_mul' (hmass q) le_rfl)
  have heq (t : Fin r → ℝ) (k : Mom d) :
      (∫ u, (G.at k).amplitude u.2 * rootAmplitudeSum B k u.1 * K t u ∂μ.prod G.base.μ) =
        ∫ u, rootAmplitudeSum B' k u * K t u ∂μ.prod G.base.μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [rootAmplitudeSum, B', IncTop.RootMeasure.at_amplitude, tsum_mul_left]
    ring
  simp_rw [heq]
  exact mixedFourierNorm_rootAmplitudeMixture_le (N := N) (μ.prod G.base.μ) θ B' v'
    (fun q k u hq => by simp only [B']; rw [hz q k u.1 hq, mul_zero, mul_zero])
    (fun q u => by simpa only [smul_eq_mul] using (hBB q u).const_smul (G.base.amplitude u.2))
    hm' hv' hvm' hvn' hb' hmz K hK hiK hH hphys

/-- Jets of the root-modulated moving-root leaf amplitude are jointly measurable. -/
theorem stronglyMeasurable_rootChar_treeRootLeafAmplitude_jets {n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {α : Type} [MeasurableSpace α] {Ξ : α → Mom d} (hΞ : Measurable Ξ)
    (q : Fin d → ℤ) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun u : (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) × α =>
      iteratedFDeriv ℝ j (fun k => rootChar (Ξ u.2) k * treeRootLeafAmplitude f S q k u.1) k) := by
  obtain ⟨Bq,hBq,hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  let g := appendRootInput f (treeRootPartition q)
  have hcoef (cell : SourceCellIndex S) : Continuous (treeLeafSpectrum g cell.1) := by
    unfold treeLeafSpectrum
    apply continuous_finsetProd
    intro a _
    have hi := Fourier.integrable_of_timeFourierNorm_lt_top
      ((timeFourierNorm_leafCell_le hK hBq.le (hq a) (cell.1 a)).trans_lt ENNReal.ofReal_lt_top)
    exact (Fourier.timeFourier_continuous hi).comp (continuous_apply a)
  let v := fun α : Fin (m+1) → Fin d → ℝ => ∑ a, (toLp 2 (α a):Mom d)
  have hv : Continuous v := by unfold v; fun_prop
  let c := fun (cell : SourceCellIndex S) (α : Fin (m+1) → Fin d → ℝ) =>
    ((((1+∑ a, ‖(toLp 2 (α a):Mom d)‖):ℝ):ℂ)*treeLeafSpectrum g cell.1 α)
  have hc (cell : SourceCellIndex S) : Continuous (c cell) := by
    have := hcoef cell
    dsimp only [c]
    fun_prop
  let ψ := fun (cell : SourceCellIndex S) (k : Mom d) => treeRootCutoff q k * sourceRootMask cell.1 k
  have hψ (cell : SourceCellIndex S) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ cell) :=
    (contDiff_treeRootCutoff q).mul (contDiff_sourceRootMask cell.1)
  have he (u : (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) × α) :
      (fun k => rootChar (Ξ u.2) k * treeRootLeafAmplitude f S q k u.1) =
        fun k => rootChar (Ξ u.2) k * (ψ u.1.1 k * (c u.1.1 u.1.2 *
          (Real.fourierChar (inner ℝ (v u.1.2) k):ℂ))) := by
    funext k
    simp only [treeRootLeafAmplitude, treeRootLeafModulation, maskedModulation, ψ, c, v, g]
    ring
  simp_rw [he]
  exact IncTop.stronglyMeasurable_rootChar_modulated_jets ψ hψ c hc v hv Ξ hΞ k j

end WaveTurbulence.Flower.FiltCoh
