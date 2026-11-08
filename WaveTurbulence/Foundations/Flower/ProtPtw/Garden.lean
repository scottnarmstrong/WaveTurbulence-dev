/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Chain
public import WaveTurbulence.Foundations.Flower.ProtCut.Time
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.TreeSummandIdentity

/-! # D6a PROT-PTW: the protected tree kernel as a free-time integral of the link integrand

For a paired tree, any designated branches `fix`, any upper clocks `up`, any lone-port time `s`, and any decoration
multiplier `m` which on link arrays is a spatial-measure value times per-link weights (`hW`), `kernelProt` is
`c^{2n}` times the free-time integral, over its literal domain `protDom`, of the weighted link integrand
`arrayIntegrand` read at the branch times (IncohInst's clock reindexing, pointwise). The lattice sum and the time
integral are exchanged once, with the leaf-summability premise of INC-TOP. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Links
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs

variable {d : ℕ} {LG : LayeredGarden 1} {X : RegChain}

/-- The weighted link integrand of a paired tree, read at garden branch times. -/
def treeIntegrand (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α] (L γ δ : ℝ)
    (H : LeafProfiles 1 d) (k : Mom d)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) (x : GBranch LG.garden.tree → ℝ) : ℂ :=
  arrayIntegrand (treeCarrier hX) F (gardenCircle LG.garden) L γ δ (treeLayerLinks LG hX) ψ
    (treeInputFunctionsL LG H) k ((treeClockEquiv hX).symm x)

/-- The pointwise summand identity: decoration summand at branch times = link-array summand at link times. -/
theorem tree_summand_pointwise (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α] (L γ δ : ℝ)
    (H : LeafProfiles 1 d) (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ)
    (hW : ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      m (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        F.value (pairedLattice L p) * arrayWeight ψ p)
    (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) (x : GBranch LG.garden.tree → ℝ) :
    LG.garden.zeta * (m (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ)
        (fun j => (p (j, 0), p (j, 1)))).1) *
      ((epsDec LG.garden (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
        phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k
          (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) x *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k
          (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 ℓ.toNode) : ℂ))) =
      F.value (pairedLattice L p) * arrayWeight ψ p *
        sourceTemporalPhase L γ δ (treeLayerLinks LG hX) p ((treeClockEquiv hX).symm x) *
        ((gardenCircle LG.garden : ℂ) * (treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k
          (fun i j => latticePoint L (p (i, j)))) := by
  have ht := tree_temporalSource_eq hX L γ δ k p ((treeClockEquiv hX).symm x)
  rw [MeasurableEquiv.apply_symm_apply] at ht
  have hl : (treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k
      (fun i j => latticePoint L (p (i, j))) = ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k
        (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 ℓ.toNode) : ℂ) := by
    rw [IncohLeafwise.tree_sourceLeafWeight_eqL hX H k]
    have he := tree_decOfParams_eq_coset hX L k (fun j => (p (j, 0), p (j, 1)))
    apply Finset.prod_congr rfl
    intro ℓ _
    exact congrArg (fun v : Mom d => (H ℓ.1 v : ℂ)) (congrFun he ℓ.toNode)
  rw [hW p, hl, ← ht, gardenCircle_coe]
  ring

/-- **The garden identity.** -/
theorem kernelProt_tree_eq_integral (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α]
    {L : ℝ} (_hL : 0 < L) (γ δ : ℝ) (H : LeafProfiles 1 d) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k : Mom d)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) {Bψ : ℝ} (hBψ : 0 ≤ Bψ)
    (hψ : ∀ i q, ‖ψ i q‖ ≤ Bψ)
    (hW : ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      m (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        F.value (pairedLattice L p) * arrayWeight ψ p)
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))‖)) :
    kernelProt L γ δ LG H m up s fix k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ (2 * (X.treeLinks (LG.garden.sig 0)).length) *
        ∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
          (protDom LG up s fix).indicator (treeIntegrand hX L γ δ H k F ψ) (LG.garden.extendFix fix τ) := by
  rw [kernelProt_eq_tsum, tree_order_eq_twice_links hX, ← (treeLatticeEquiv hX d).symm.tsum_eq, mul_assoc]
  congr 1
  let lw := fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
    (treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))
  let gx := fun (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) (x : GBranch LG.garden.tree → ℝ) =>
    F.value (pairedLattice L p) * arrayWeight ψ p *
      sourceTemporalPhase L γ δ (treeLayerLinks LG hX) p ((treeClockEquiv hX).symm x) *
        ((gardenCircle LG.garden : ℂ) * lw p)
  let g := fun (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ) =>
    (protDom LG up s fix).indicator (gx p) (LG.garden.extendFix fix τ)
  have hsummand (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) :
      LG.garden.zeta * protSummand L γ δ LG H m up s fix k ((treeLatticeEquiv hX d).symm p) = ∫ τ, g p τ := by
    have hκ : ((treeLatticeEquiv hX d).symm p).1 =
        (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 := rfl
    unfold protSummand protTime
    rw [hκ]
    rw [← integral_const_mul, ← integral_mul_const, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro τ
    dsimp only [g]
    by_cases hτ : LG.garden.extendFix fix τ ∈ protDom LG up s fix
    · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ]
      exact tree_summand_pointwise hX L γ δ H k m F ψ hW p (LG.garden.extendFix fix τ)
    · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ]
      ring
  have hBm : MeasurableSet (freeBox LG fix) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hint1 : Integrable ((freeBox LG fix).indicator (1 : ({b : GBranch LG.garden.tree //
      fix b = none} → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff hBm]
    exact integrableOn_const (by rw [volume_freeBox]; exact ENNReal.one_ne_top)
  have hgx (p) (x) : ‖gx p x‖ ≤ F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖ := by
    have h1 := F.norm_value_le (pairedLattice L p)
    have h2 := norm_arrayWeight_le ψ hBψ hψ p
    have h3 := norm_sourceTemporalPhase_le_one L γ δ (treeLayerLinks LG hX) p ((treeClockEquiv hX).symm x)
    simp only [gx, norm_mul, Circle.norm_coe, one_mul]
    calc _ ≤ F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * 1 * ‖lw p‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) F.mass_nonneg) h3
            (norm_nonneg _) (mul_nonneg F.mass_nonneg (pow_nonneg hBψ _))) (norm_nonneg _)
      _ = _ := by ring
  have hgb (p) (τ) : ‖g p τ‖ ≤ F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖ * (freeBox LG fix).indicator 1 τ := by
    dsimp only [g]
    by_cases hτ : LG.garden.extendFix fix τ ∈ protDom LG up s fix
    · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem (protDom_subset_freeBox LG up s fix τ hτ),
        Pi.one_apply, mul_one]
      exact hgx p _
    · rw [Set.indicator_of_notMem hτ, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg F.mass_nonneg (pow_nonneg hBψ _)) (norm_nonneg _))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hmeas (p) : Measurable (g p) := by
    show Measurable ((protDom LG up s fix).indicator (gx p) ∘ LG.garden.extendFix fix)
    refine Measurable.comp ?_ (measurable_extendFix _ _)
    refine Measurable.indicator ?_ (measurableSet_protDom LG up s fix)
    exact (measurable_const.mul ((continuous_sourceTemporalPhase L γ δ _ p).measurable.comp
      (treeClockEquiv hX).symm.measurable)).mul measurable_const
  have hi (p) : Integrable (g p) :=
    (hint1.const_mul (F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖)).mono' (hmeas p).aestronglyMeasurable
      (Filter.Eventually.of_forall (hgb p))
  have hn (p) : (∫ τ, ‖g p τ‖) ≤ F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖ := by
    calc (∫ τ, ‖g p τ‖) ≤ ∫ τ, F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖ * (freeBox LG fix).indicator 1 τ :=
          integral_mono (hi p).norm (hint1.const_mul _) (hgb p)
      _ = F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖ := by
          rw [integral_const_mul, integral_indicator_one hBm, Measure.real, volume_freeBox,
            ENNReal.toReal_one, mul_one]
  have hsum : Summable (fun p => ∫ τ, ‖g p τ‖) :=
    ((hs.mul_left (F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length))).of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun p => (hn p).trans_eq (by ring))
  rw [← tsum_mul_left]
  simp_rw [hsummand]
  rw [(hasSum_integral_of_summable_integral_norm hi hsum).tsum_eq]
  apply integral_congr_ae
  apply ae_of_all
  intro τ
  dsimp only [g]
  by_cases hτ : LG.garden.extendFix fix τ ∈ protDom LG up s fix
  · simp only [Set.indicator_of_mem hτ]
    rfl
  · simp only [Set.indicator_of_notMem hτ, tsum_zero]

end WaveTurbulence.Flower.ProtPtw
