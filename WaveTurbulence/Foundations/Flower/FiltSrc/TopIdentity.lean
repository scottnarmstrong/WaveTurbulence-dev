/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Source
public import WaveTurbulence.Foundations.Flower.IncTop.Top.TopIdentity

/-! # D5b-1 FILT-SRC: filtered weighted leafwise kernels are the filtered weighted raw operators (`TopIdentity`)

Twin of INC-TOP's `Top/TopIdentity` (copied by source, sha256 in COPIED-SHA256SUMS). INC-TOP's premise
`hW : m (coset p) = F.value (pairedLattice L p)` becomes
`hW' : m (coset p) = F.value (pairedLattice L p) * arrayFiltWeight L φ p` (D5B-MAP K1; discharged for the D5 multiplier
by `Identity.couple_starFiltWeight_eq` / `tree_starFiltWeight_eq`), and the raw operators are the filtered ones of
`Source.lean`. Main's `IncohLeafwise` summand identities are reused unchanged: they do not see the multiplier
(D5B-MAP §5.3 item 6 checked: the multiplier is factored out before them, as in INC-TOP). The Fubini bound gains
`Bφ ^ n` (`‖φ i u‖ ≤ Bφ`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise WaveTurbulence.Flower.Stage1W
open WaveTurbulence.Flower.IncTop WaveTurbulence.Flower.FiltLink

/-- Filtered weighted source Fubini: the original lattice input mass (times `Bφ ^ n`) suffices. -/
theorem integral_weightedSourceTimeIntegrand_eq_tsumFilt {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {Bφ : ℝ}
    (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) :
    (∫ t in I, (MomentumTreeData.weightedSourceTimeIntegrandFilt (P := P)) F ζ L γ δ Q φ f k t) =
      ∑' p : (Fin n × Fin 2) → Fin d → ℤ, ∫ t in I,
        F.value (pairedLattice L p) * sourceTemporalPhaseFilt L γ δ Q φ p t *
          ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))) := by
  let μ := (volume : Measure (Fin n → Fin 2 → ℝ)).restrict I
  have hfinite : μ Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hI).trans_lt
      ((isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top)
  let : IsFiniteMeasure μ := ⟨hfinite⟩
  let W := fun p : (Fin n × Fin 2) → Fin d → ℤ =>
    ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))
  let G := fun p t => F.value (pairedLattice L p) * sourceTemporalPhaseFilt L γ δ Q φ p t * W p
  have hi (p) : Integrable (G p) μ := by
    have h := ((integrableOn_sourceTemporalPhaseFilt L γ δ Q φ p hI).const_mul
      (F.value (pairedLattice L p))).mul_const (W p)
    exact h
  have hnorm (p) (t : Fin n → Fin 2 → ℝ) : ‖G p t‖ ≤
      F.mass * Bφ ^ n * ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖ := by
    simp only [G, W, norm_mul, Circle.norm_coe, one_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (F.norm_value_le _)
      (norm_sourceTemporalPhase_leFilt L γ δ Q φ hφ p t) (norm_nonneg _) F.mass_nonneg) (norm_nonneg _)
  have hsum : Summable (fun p => ∫ t, ‖G p t‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun p => integral_nonneg (fun _ => norm_nonneg _))
      (fun p => ?_) ((hs.mul_left (F.mass * Bφ ^ n)).mul_left (μ.real Set.univ))
    have hle := integral_mono (hi p).norm (integrable_const
      (F.mass * Bφ ^ n * ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) (hnorm p)
    simpa only [integral_const, smul_eq_mul] using hle
  exact (integral_tsum_of_summable_integral_norm hi hsum).symm

/-- Weighted two-root couple identity, filtered (conditional on `hW'` and summability). -/
theorem coupleLeavesW_eq_weightedRaw_of_summableFilt {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    {d : ℕ} (L γ δ : ℝ) (H : LeafProfiles 2 d) (k : Mom d) (ts : Fin 2 → ℝ)
    (mw : (GNode LG.garden.tree → Mom d) → ℂ) {α : Type*} [MeasurableSpace α]
    (F : Cut2A.SpatialMeasure (PairedMomentum d Q.links.length) α)
    (φ : Fin Q.links.length → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (hW : ∀ p : Fin Q.links.length × Fin 2 → Fin d → ℤ,
      mw (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        F.value (pairedLattice L p) * arrayFiltWeight L φ p)
    (hs : Summable (fun p : Fin Q.links.length × Fin 2 → Fin d → ℤ =>
      ‖(coupleCarrier hQ).sourceLeafWeight (coupleInputFunctionsL LG H) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 mw =
      (MomentumTreeData.weightedSourceCoupleKernelFilt (P := (coupleCarrier hQ))) F (gardenCircle LG.garden)
        (coupleRootCoordinates hQ hb) L γ δ (coupleLayerLinks LG hQ) φ (coupleInternalLinkDomain LG hQ) (coupleInputFunctionsL LG H) ts k := by
  let I := coupleInternalLinkDomain LG hQ ∩ (coupleRootCoordinates hQ hb).rootCut ts
  have hbox : I ⊆ Set.univ.pi (fun j => linkBox (coupleLayerLinks (d := d) LG hQ j)) :=
    Set.inter_subset_left.trans (coupleInternalLinkDomain_subset_boxes d hQ)
  unfold kernelLeavesW
  rw [couple_upperTimes_eqL ts, couple_order_eq_twice_links hQ]
  rw [← (coupleLatticeEquiv hQ d).symm.tsum_eq]
  change (coupling d L γ δ : ℂ) ^ (2 * Q.links.length) * LG.garden.zeta *
    (∑' p : Fin Q.links.length × Fin 2 → Fin d → ℤ,
      mw (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ((epsDec LG.garden (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun b => ts b.1.1) 0) 0
          (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1
          (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1
            ℓ.toNode) : ℂ))) = _
  simp_rw [couple_summand_eq_linkIntegralL hQ hb L γ δ H k ts, hW]
  unfold MomentumTreeData.weightedSourceCoupleKernelFilt MomentumTreeData.weightedSourceIntegralFilt
  rw [integral_weightedSourceTimeIntegrand_eq_tsumFilt (coupleCarrier hQ) F (gardenCircle LG.garden) L γ δ
    (coupleLayerLinks LG hQ) φ hφ I hbox (coupleInputFunctionsL LG H) k hs]
  rw [Complex.ofReal_pow]
  unfold coupling
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [gardenCircle_coe, sourceTemporalPhaseFilt_eq]
  ring

/-- Weighted one-root couple identity, filtered (conditional on `hW'` and summability). -/
theorem coupleLeavesW_eq_weightedOneClock_of_summableFilt {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hn : 1 ≤ Q.links.length) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
    (hwidth : ∀ b : GBranch LG.garden.tree, b.1.1 = a)
    {d : ℕ} (L γ δ : ℝ) (H : LeafProfiles 2 d) (k : Mom d) (ts : Fin 2 → ℝ)
    (mw : (GNode LG.garden.tree → Mom d) → ℂ) {α : Type*} [MeasurableSpace α]
    (F : Cut2A.SpatialMeasure (PairedMomentum d Q.links.length) α)
    (φ : Fin Q.links.length → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (hW : ∀ p : Fin Q.links.length × Fin 2 → Fin d → ℤ,
      mw (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        F.value (pairedLattice L p) * arrayFiltWeight L φ p)
    (hs : Summable (fun p : Fin Q.links.length × Fin 2 → Fin d → ℤ =>
      ‖(coupleCarrier hQ).sourceLeafWeight (coupleInputFunctionsL LG H) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 mw =
      weightedSourceOneClockKernelFilt (coupleCarrier hQ) F (gardenCircle LG.garden)
        (oneClockSelection Q.links.length hn ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩) a) a
        L γ δ (coupleLayerLinks LG hQ) φ (coupleInternalLinkDomain LG hQ) (coupleInputFunctionsL LG H) ts k := by
  let I := coupleInternalLinkDomain LG hQ ∩
    (oneClockSelection Q.links.length hn ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩) a).oneClockCut a (ts a)
  have hbox : I ⊆ Set.univ.pi (fun j => linkBox (coupleLayerLinks (d := d) LG hQ j)) :=
    Set.inter_subset_left.trans (coupleInternalLinkDomain_subset_boxes d hQ)
  unfold kernelLeavesW
  rw [couple_upperTimes_eqL ts, couple_order_eq_twice_links hQ]
  rw [← (coupleLatticeEquiv hQ d).symm.tsum_eq]
  change (coupling d L γ δ : ℂ) ^ (2 * Q.links.length) * LG.garden.zeta *
    (∑' p : Fin Q.links.length × Fin 2 → Fin d → ℤ,
      mw (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ((epsDec LG.garden (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun b => ts b.1.1) 0) 0
          (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1
          (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1
            ℓ.toNode) : ℂ))) = _
  simp_rw [couple_summand_eq_oneRootIntegralL hQ hn a hb hwidth L γ δ H k ts, hW]
  unfold weightedSourceOneClockKernelFilt MomentumTreeData.weightedSourceIntegralFilt
  rw [integral_weightedSourceTimeIntegrand_eq_tsumFilt (coupleCarrier hQ) F (gardenCircle LG.garden) L γ δ
    (coupleLayerLinks LG hQ) φ hφ I hbox (coupleInputFunctionsL LG H) k hs]
  rw [Complex.ofReal_pow]
  unfold coupling
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [gardenCircle_coe, sourceTemporalPhaseFilt_eq]
  ring

/-- Weighted paired-tree identity, filtered (conditional on `hW'` and summability). -/
theorem treeLeavesW_eq_weightedRaw_of_summableFilt {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX)
    {d : ℕ} (L γ δ : ℝ) (H : LeafProfiles 1 d) (k : Mom d) (ts : Fin 2 → ℝ)
    (mw : (GNode LG.garden.tree → Mom d) → ℂ) {α : Type*} [MeasurableSpace α]
    (F : Cut2A.SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (φ : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (hW : ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      mw (cosetDecoration LG.garden L k
        (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        F.value (pairedLattice L p) * arrayFiltWeight L φ p)
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 mw =
      (MomentumTreeData.weightedSourceTreeKernelFilt (P := (treeCarrier hX))) F (gardenCircle LG.garden) C.rootCoordinates
        L γ δ (treeLayerLinks LG hX) φ (actualTreeFibers (d := d) LG hX C).timeDomain
        (treeInputFunctionsL LG H) ts k := by
  let I := (actualTreeFibers (d := d) LG hX C).timeDomain ∩ C.rootCoordinates.causalRootCut ts
  have hbox : I ⊆ Set.univ.pi (fun j => linkBox (treeLayerLinks (d := d) LG hX j)) :=
    Set.inter_subset_left.trans (actualTreeFibers (d := d) LG hX C).timeDomain_subset_linkBoxes
  unfold kernelLeavesW
  rw [tree_order_eq_twice_links hX]
  rw [← (treeLatticeEquiv hX d).symm.tsum_eq]
  change (coupling d L γ δ : ℂ) ^ (2 * (X.treeLinks (LG.garden.sig 0)).length) * LG.garden.zeta *
    (∑' p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      mw (cosetDecoration LG.garden L k
        (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ((epsDec LG.garden (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => ts 0) (ts 1)) (ts 1)
          (cosetDecoration LG.garden L k
            (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1
          (cosetDecoration LG.garden L k
            (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 ℓ.toNode) : ℂ))) = _
  simp_rw [tree_summand_eq_linkIntegralL hX C L γ δ H k ts, hW]
  unfold MomentumTreeData.weightedSourceTreeKernelFilt MomentumTreeData.weightedSourceIntegralFilt
  rw [integral_weightedSourceTimeIntegrand_eq_tsumFilt (treeCarrier hX) F (gardenCircle LG.garden) L γ δ
    (treeLayerLinks LG hX) φ hφ I hbox (treeInputFunctionsL LG H) k hs]
  rw [Complex.ofReal_pow]
  unfold coupling
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [gardenCircle_coe, sourceTemporalPhaseFilt_eq]
  ring

end WaveTurbulence.Flower.FiltSrc
