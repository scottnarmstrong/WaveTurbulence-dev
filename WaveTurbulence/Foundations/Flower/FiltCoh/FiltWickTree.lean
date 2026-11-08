/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltOracleCouple
public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarExt

/-! # FILT-COH (d2f): the filtered identities of a star-weighted layer-zero paired tree

* `star_swap_w`: a lattice multiplier `value · w` (presentation value times a bounded weight) becomes a mixture of
  weighted lattice characters (FiltCoh's `star_swap` with the weight);
* `kernelLeavesW_tree_filt_eq`: the D5-weighted tree kernel (`d5Mult`, FILT-SRC's `tree_starFiltWeight_eq`) is the
  presentation integral of root characters times the filtered, character-twisted lattice source sum;
* `tree_filt_inner_eq`: that sum is main's moving-root mixture of tree profile scalars with the weight
  `∏_j φ_j(⟨x_j, y_j⟩) · treeWickArrayWeight` at shifted modulations;
* `tree_filt_inner_mixture`: with the physical normalization pushed in, a mixture of shifted FILTERED physical
  symbols (`filtCellSymbol_eq_tree`), exchanges from a uniform integrable envelope.
Proofs adapted from FiltCoh's `TreeStarId`, `TreeStarMix`, `TreeStarInner` (this area). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure rootChar rootJetConstant)
open scoped ENNReal

variable {d : ℕ}

attribute [-instance] WaveTurbulence.Mole.instFintypePositionCode

/-- **Weighted presentation swap.** -/
theorem star_swap_w {n : ℕ} {α : Type} [MeasurableSpace α] (G : RootMeasure d n α) (L : ℝ) (k : Mom d)
    (V w : ((Fin n × Fin 2) → Fin d → ℤ) → ℂ) (hV : ∀ p, V p = (G.at k).value (pairedLattice L p) * w p)
    (c g : ((Fin n × Fin 2) → Fin d → ℤ) → ℂ) {D : ℝ} (hc : ∀ p, ‖w p * c p‖ ≤ D)
    (hg : Summable (fun p => ‖g p‖)) (A : ℂ) :
    A * ∑' p, V p * (c p * g p) =
      ∫ a, G.base.amplitude a * rootChar (G.root a) k *
        (A * ∑' p, (((Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ) * w p) * c p)
          * g p) ∂G.base.μ := by
  classical
  let F : ((Fin n × Fin 2) → Fin d → ℤ) → α → ℂ := fun p a =>
    G.base.amplitude a * rootChar (G.root a) k *
      (Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ) * ((w p * c p) * g p)
  have hnorm : ∀ p a, ‖F p a‖ ≤ ‖G.base.amplitude a‖ * (D * ‖g p‖) := by
    intro p a
    simp only [F, norm_mul, IncTop.norm_rootChar, Circle.norm_coe, mul_one]
    have h2 := hc p
    rw [norm_mul] at h2
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (norm_nonneg _)
  have hFm : ∀ p, AEStronglyMeasurable (F p) G.base.μ := by
    intro p
    have h1 : Measurable (fun a => rootChar (G.root a) k) := IncTop.measurable_rootChar G.root_measurable k
    have h2 : Measurable (fun a => (Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ)) := by
      have hc' : Continuous (fun v : PairedMomentum d n =>
          (Real.fourierChar (inner ℝ v (pairedLattice L p)) : ℂ)) := by fun_prop
      exact hc'.measurable.comp G.base.frequency_measurable
    exact (((G.amplitude_measurable.mul h1).mul h2).mul measurable_const).aestronglyMeasurable
  have hFi : ∀ p, Integrable (F p) G.base.μ := fun p =>
    (G.base.amplitude_integrable.norm.mul_const (D * ‖g p‖)).mono' (hFm p) (ae_of_all _ (hnorm p))
  have hFs : Summable (fun p => ∫ a, ‖F p a‖ ∂G.base.μ) := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun a => norm_nonneg _) (fun p => ?_)
      ((hg.mul_left D).mul_left (∫ a, ‖G.base.amplitude a‖ ∂G.base.μ))
    rw [← integral_mul_const]
    exact integral_mono (hFi p).norm (G.base.amplitude_integrable.norm.mul_const _) (hnorm p)
  have hval : ∀ p, V p * (c p * g p) = ∫ a, F p a ∂G.base.μ := by
    intro p
    rw [hV p, IncTop.RootMeasure.at_value, ← integral_mul_const, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [F]
    ring
  simp_rw [hval]
  rw [integral_tsum_of_summable_integral_norm hFi hFs, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [F]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  ring

/-- **The D5-weighted tree kernel as a presentation mixture of filtered lattice sums.** -/
theorem kernelLeavesW_tree_filt_eq {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hwf : X.wf = true) (h0 : ∀ a, LG.layer a = 0) (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ)
    {K M : ℕ} {B : ℝ} (hK : d+1 ≤ K) (hM : 2*d ≤ M) (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm K M (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal B)
    (J : ℕ) (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sset, IncTop.StarPresented J (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (Mf : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) {Bφ : ℝ}
    (hφ : ∀ j u, ‖FiltSrc.treeLinkFilt hX F Fu ann Mf Mu j u‖ ≤ Bφ)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) (k : Mom d) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 (d5Mult Sset ω F ann Mf Fu Mu) =
      ∫ a, (IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX)).base.amplitude a *
          rootChar ((IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX)).root a) k *
        ((coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
          ∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
            (((Real.fourierChar (inner ℝ
              ((IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX)).base.frequency a)
                (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L (FiltSrc.treeLinkFilt hX F Fu ann Mf Mu) p) *
              RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p) *
            (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
              (fun j i => latticePoint L (p (j,i))))
        ∂(IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX)).base.μ := by
  set Gm := IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX) with hGm
  rw [kernelLeavesW_tree_lattice L γ δ LG hX H t s k]
  have hroot (p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ) :
      RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s k p =
        RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p :=
    RA1Leafwise.treeOriginalLatticeCoefficient_root_independent L γ δ LG hX hwf h0 hs hst ht p k 0
  simp_rw [hroot]
  have hc : ∀ p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
      ‖FiltSrc.arrayFiltWeight L (FiltSrc.treeLinkFilt hX F Fu ann Mf Mu) p *
      RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p‖ ≤ Bφ^(X.treeLinks (LG.garden.sig 0)).length := by
    intro p
    rw [norm_mul]
    have h1 := FiltSrc.norm_arrayFiltWeight_le L _ hφ p
    have h2 := RA1Leafwise.treeOriginalLatticeCoefficient_norm_le L γ δ LG hX h0 t s 0 p
    calc _ ≤ Bφ^(X.treeLinks (LG.garden.sig 0)).length * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := mul_one _
  exact star_swap_w Gm L k _ _ (fun p => FiltSrc.tree_starFiltWeight_eq hX J Sset ω cω hpres L k F Fu ann Mf Mu p)
    _ _ hc ((treeCarrier hX).summable_norm_treeSourceLeafWeight_lattice hd _ hL hK hM hf k) _

/-- The array filter of separated link arrays. -/
@[expose] def treeArrFilt {n : ℕ} (L : ℝ) (φ : Fin n → ℝ → ℂ)
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) : ℂ :=
  ∏ j, φ j (inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))

theorem norm_treeArrFilt_le {n : ℕ} (L : ℝ) (φ : Fin n → ℝ → ℂ) {B : ℝ} (hB : ∀ j u, ‖φ j u‖ ≤ B)
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) : ‖treeArrFilt L φ g‖ ≤ B ^ n := by
  rw [treeArrFilt, norm_prod]
  calc
    _ ≤ ∏ _i : Fin n, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hB i _)
    _ = B ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem treeProfileArrayScalar_char_filt {n : ℕ} (L μ : ℝ) (φ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) (ν : PairedMomentum d n) :
    treeProfileArrayScalar L μ (fun g => arrayChar ν L g * (treeArrFilt L φ g * RA1Leafwise.treeWickArrayWeight g))
        z β γ' J C lam =
      treeProfileArrayScalar L μ (fun g => treeArrFilt L φ g * RA1Leafwise.treeWickArrayWeight g)
        z (shiftL β ν 0) (shiftL γ' ν 1) J C lam :=
  treeProfileArrayScalar_char L μ _ z β γ' J C lam ν

/-- **The filtered, twisted tree source sum is a moving-root mixture at shifted modulations.** -/
theorem tree_filt_inner_eq {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (h0 : ∀ a, LG.layer a = 0)
    {I : Type*} [Fintype I] (c : I → ℂ) (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i)) {L : ℝ} (hL : 1 ≤ L) (μ γ δ t s : ℝ)
    (hH : RA1Leafwise.treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s = fun g =>
      RA1Leafwise.treeWickArrayWeight g * ∑ i, c i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
        (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s)
    {K M : ℕ} {B Ccover : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm K M (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    (k : Mom d) (ν : PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length)
    (φ : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ → ℂ) {Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hφ : ∀ j u, ‖φ j u‖ ≤ Bφ) :
    ∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
        (((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L φ p) *
          RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p) *
        (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
          (fun j i => latticePoint L (p (j,i))) =
      ∑ i, c i * ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX
          (fun lam β γ' z => treeProfileArrayScalar L μ (fun g => treeArrFilt L φ g * RA1Leafwise.treeWickArrayWeight g)
            z (shiftL β ν 0) (shiftL γ' ν 1) (J i) (C i) lam) S lam u) ![t,s] ∂treeLeafCellMeasure S := by
  let Hν : ((Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ) × (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ)) → ℂ := fun g =>
    arrayChar ν L g * (treeArrFilt L φ g * RA1Leafwise.treeOriginalArrayCoefficient L γ δ LG hX t s g)
  have hBn : 0 ≤ Bφ^(X.treeLinks (LG.garden.sig 0)).length := pow_nonneg hBφ _
  have hHν : ∀ g, ‖Hν g‖ ≤ Bφ^(X.treeLinks (LG.garden.sig 0)).length := fun g => by
    simp only [Hν, norm_mul, norm_arrayChar, one_mul]
    calc _ ≤ Bφ^(X.treeLinks (LG.garden.sig 0)).length * 1 := mul_le_mul (norm_treeArrFilt_le L φ hφ g)
          (RA1Leafwise.treeOriginalArrayCoefficient_norm_le L γ δ LG hX h0 t s g) (norm_nonneg _) hBn
      _ = _ := mul_one _
  have hsrc := tree_bounded_mixture_eq_source hX hL Hν hBn hHν (RA1Leafwise.treeInputFunctionsL LG H) hK hM hB hf
    S hcover hS k
  let E := (linkLatticeArrayEquiv (Fin (X.treeLinks (LG.garden.sig 0)).length) (Fin d → ℤ)).trans
    (Equiv.arrowProdEquivProdArrow (Fin (X.treeLinks (LG.garden.sig 0)).length) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ))
  have hEs (g : (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ) × (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ)) :
      E.symm g = fun p => if p.2 = 0 then g.1 p.1 else g.2 p.1 := rfl
  have hstep : (∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
        (((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L φ p) *
          RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p) *
        (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
          (fun j i => latticePoint L (p (j,i)))) =
      ∑' g, Hν g * (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) := by
    refine (E.symm.tsum_eq _).symm.trans (tsum_congr fun g => ?_)
    rw [hEs g, fourierChar_pairedLattice]
    have hx : (fun j i => latticePoint L ((fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 => if p.2 = 0 then g.1 p.1 else g.2 p.1) (j,i))) =
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) := by
      funext j i
      fin_cases i <;> rfl
    rw [hx]
    have hfl : FiltSrc.arrayFiltWeight L φ (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 => if p.2 = 0 then g.1 p.1 else g.2 p.1) =
        treeArrFilt L φ g := by
      unfold FiltSrc.arrayFiltWeight treeArrFilt FiltLink.linkBilinear
      simp
    rw [hfl]
    simp only [Hν]
    rw [← mul_assoc (arrayChar ν L g)]
    rfl
  rw [hstep, ← hsrc]
  let Wν : ((Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ) × (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ)) → ℂ := fun g =>
    arrayChar ν L g * (treeArrFilt L φ g * RA1Leafwise.treeWickArrayWeight g)
  have hWν : ∀ g, ‖Wν g‖ ≤ Bφ^(X.treeLinks (LG.garden.sig 0)).length := fun g => by
    simp only [Wν, norm_mul, norm_arrayChar, one_mul]
    calc _ ≤ Bφ^(X.treeLinks (LG.garden.sig 0)).length * 1 := mul_le_mul (norm_treeArrFilt_le L φ hφ g)
          (RA1Leafwise.treeWickArrayWeight_norm_le g) (norm_nonneg _) hBn
      _ = _ := mul_one _
  have hHW : Hν = fun g => Wν g * ∑ i, c i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
      (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*
        e2 lam ((![t,s] : Fin 2 → ℝ) 0) ((![t,s] : Fin 2 → ℝ) 1) := by
    funext g
    simp only [Hν, Wν, hH]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hHW, tree_leaf_mixture_finite_profiles hX hL μ Wν hBn hWν c J C hC (RA1Leafwise.treeInputFunctionsL LG H)
    hK hM hB hf S hS ![t,s] k]
  simp only [Wν, treeProfileArrayScalar_char_filt]

/-- The shifted filtered physical symbol family. -/
@[expose] def filtShiftedSymbol {n : ℕ} (L δ γ : ℝ) (ψ : Fin n → ℝ → ℂ) (ν : PairedMomentum d n)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) :
    (ℝ × ℝ) → (Fin n → Mom d) → (Fin n → Mom d) → ((Fin n × Fin 2) → Fin d → ℤ) → ℂ :=
  fun lam β γ' z => filtCellSymbol L δ γ ψ z (shiftL β ν 0) (shiftL γ' ν 1) J C lam

theorem stronglyMeasurable_filtShiftedSymbol {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (ψ : Fin n → ℝ → ℂ)
    (ν : PairedMomentum d n) (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      filtShiftedSymbol L δ γ ψ ν J C p.1 p.2.1 p.2.2 z) :=
  stronglyMeasurable_shift_fixed (fun lam β γ' z => filtCellSymbol L δ γ ψ z β γ' J C lam) z
    (stronglyMeasurable_filtCellSymbol_joint hL δ γ ψ J hC z) ν

theorem treeFiltWeight_profFilt {n : ℕ} {L δ γ : ℝ} (hμ : L^(2*γ)*(2*δ) ≠ 0) (φ : Fin n → ℝ → ℂ) :
    treeFiltWeight (d := d) L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) =
      fun g => treeArrFilt L φ g * RA1Leafwise.treeWickArrayWeight g := by
  funext g
  unfold treeFiltWeight treeArrFilt profFilt
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  exact mul_div_cancel_left₀ _ hμ

/-- **The filtered tree source sum as one moving-root mixture of shifted filtered physical symbols.** -/
theorem tree_filt_inner_mixture {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (h0 : ∀ a, LG.layer a = 0)
    {I : Type*} [Fintype I] (c : I → ℂ) (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i)) {L : ℝ} (hL : 1 ≤ L) (γ δ t s : ℝ) (hδ : 0 < δ)
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
    (φ : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ → ℂ) {Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hφ : ∀ j u, ‖φ j u‖ ≤ Bφ)
    {θ : ℝ} (hθ : 0 ≤ θ) (E : I → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam)) < ⊤)
    (hEnv : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin (X.treeLinks (LG.garden.sig 0)).length → Mom d),
      ‖filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) z β γ' (J i) (C i) lam‖ ≤ E i lam)
    (ζ : ℂ) (k : Mom d) (ν : PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) :
    (coupling d L γ δ : ℂ)^LG.garden.order * ζ *
      ∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
        (((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L φ p) *
          RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p) *
        (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
          (fun j i => latticePoint L (p (j,i))) =
      ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u *
        pairedInverseProfile (fun lam => ∑ i, (ζ * c i) *
          treeNormalizedScalar hX (filtShiftedSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) ν (J i) (C i)) S lam u)
            ![t,s]
        ∂treeLeafCellMeasure S := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hμ0 : L^(2*γ)*(2*δ) ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hLp _) (by linarith)).ne'
  set ψ := profFilt (L^(2*γ)*(2*δ)) φ with hψdef
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*(X.treeLinks (LG.garden.sig 0)).length):ℝ):ℂ)
  have hinner := tree_filt_inner_eq hX h0 c J C hC hL (2*δ*L^(2*γ)) γ δ t s hH hK hM hB H hf S hcover hS k ν
    φ hBφ hφ
  rw [hinner]
  -- normalization: the filtered physical symbol is `q` times the filtered tree profile scalar
  have hR (i : I) (lam : ℝ × ℝ) (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S lam u =
        q * treeNormalizedScalar hX (fun lam β γ' z => treeProfileArrayScalar L (2*δ*L^(2*γ))
          (fun g => treeArrFilt L φ g * RA1Leafwise.treeWickArrayWeight g) z (shiftL β ν 0) (shiftL γ' ν 1)
            (J i) (C i) lam) S lam u := by
    unfold treeNormalizedScalar filtShiftedSymbol
    rw [filtCellSymbol_eq_tree L δ γ ψ, hψdef, treeFiltWeight_profFilt hμ0 φ, mul_div_assoc]
  -- measurability and integrability of every shifted symbol
  have hmR (i : I) : StronglyMeasurable (Function.uncurry
      (treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S)) :=
    stronglyMeasurable_treeNormalizedScalar hX _
      (fun z => stronglyMeasurable_filtShiftedSymbol hLp δ γ ψ ν (J i) (hC i).meas z) S
  have hbd (i : I) (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      ∀ᵐ lam : ℝ × ℝ, ‖treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S lam u‖ ≤
        treeSpectralFrequencyLoss X (LG.garden.sig 0) * E i lam := by
    filter_upwards [hEnv i] with lam hlam
    have hh := treeNormalizedScalar_norm_le hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S zero_le_one
      (hpE i lam) lam (fun z β γ' => by
        have h1 := hlam z (shiftL β ν 0) (shiftL γ' ν 1)
        have h2 : (0:ℝ) ≤ (∑ j, ‖β j‖) + (∑ j, ‖γ' j‖) := by positivity
        calc ‖filtShiftedSymbol L δ γ ψ ν (J i) (C i) lam β γ' z‖ ≤ E i lam := h1
          _ ≤ 1 * (1 + ((∑ j, ‖β j‖) + (∑ j, ‖γ' j‖))) * E i lam := by
              nlinarith [hpE i lam]) u
    simpa only [one_mul] using hh
  have hiLam (i : I) (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      Integrable (fun lam => treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S lam u) := by
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
  have hiU (i : I) (tt : Fin 2 → ℝ) :
      Integrable (fun u => rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S lam u) tt)
        (treeLeafCellMeasure S) := by
    have hm' : StronglyMeasurable (fun u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ) =>
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S lam u) tt) := by
      have he2 : StronglyMeasurable (fun p : ((ℝ × ℝ) ×
          (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ))) =>
          e2 p.1 (tt 0) (tt 1)) :=
        (continuous_e2.measurable.comp
          (measurable_fst.prodMk (measurable_const (a := ((tt 0, tt 1) : ℝ × ℝ))))).stronglyMeasurable
      have hpre : StronglyMeasurable (fun p : ((ℝ × ℝ) ×
          (SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ))) =>
          treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S p.1 p.2 * e2 p.1 (tt 0) (tt 1)) :=
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
  have horder : LG.garden.order = 2*(X.treeLinks (LG.garden.sig 0)).length := tree_order_eq_twice_links hX
  have hcq : (coupling d L γ δ : ℂ)^LG.garden.order = q := by
    rw [horder]
    simp only [q, coupling, Complex.ofReal_pow]
  rw [hcq]
  have hsum (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      pairedInverseProfile (fun lam => ∑ i, (ζ * c i) *
        treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S lam u) ![t,s] =
      ∑ i, (ζ * c i) * pairedInverseProfile (fun lam =>
        treeNormalizedScalar hX (filtShiftedSymbol L δ γ ψ ν (J i) (C i)) S lam u) ![t,s] := by
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
