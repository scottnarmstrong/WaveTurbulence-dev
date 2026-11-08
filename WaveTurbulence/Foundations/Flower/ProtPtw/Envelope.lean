/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Garden
public import WaveTurbulence.Foundations.ApproxNT.Products

/-! # D6a PROT-PTW: integrating the envelope over the remaining times (o82 Prop 14.2, last step)

"Take its absolute value, enlarge the remaining time domain to the product of its original unit intervals, and apply
(14.1) pair by pair." Three measure-theoretic steps:
- `lintegral_fill`: integrating over a subset of the branch times (pins, the selected time removed) a function of those
  times only equals integrating over all branch times (the others range over unit intervals);
- `lintegral_tree_links`: over all branch times, the IncohInst clock reindexing turns the unit box into the product of
  the link boxes and a product of per-link functions integrates to the product of their link masses;
- `lintegral_arrayEnvelope`: Tonelli for the envelope (star measure, cells, spectral variables). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A

/-! ### Filling and unit boxes -/

/-- Fill the coordinates outside `keep` with `y`. -/
def fill {ι : Type*} (keep : ι → Prop) [DecidablePred keep] (y : ι → ℝ) (τ : {i // keep i} → ℝ) : ι → ℝ :=
  fun i => if h : keep i then τ ⟨i, h⟩ else y i

/-- The unit box with lower corner `lo`. -/
def unitBox {ι : Type*} (lo : ι → ℝ) : Set (ι → ℝ) := Set.pi univ fun i => Icc (lo i) (lo i + 1)

theorem measurableSet_unitBox {ι : Type*} [Fintype ι] (lo : ι → ℝ) : MeasurableSet (unitBox lo) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem volume_unitBox {ι : Type*} [Fintype ι] (lo : ι → ℝ) : volume (unitBox lo) = 1 := by
  unfold unitBox
  rw [volume_pi_pi]
  simp only [Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_one, Finset.prod_const_one]

theorem measurable_fill {ι : Type*} (keep : ι → Prop) [DecidablePred keep] (y : ι → ℝ) :
    Measurable (fill keep y) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold fill
  by_cases h : keep i
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

/-- **Dummy integration.** -/
theorem lintegral_fill {ι : Type*} [Fintype ι] (keep : ι → Prop) [DecidablePred keep] (lo y : ι → ℝ)
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) (hdep : ∀ x x' : ι → ℝ, (∀ i, keep i → x i = x' i) → f x = f x') :
    ∫⁻ τ : {i // keep i} → ℝ, (unitBox fun i => lo i.1).indicator 1 τ * f (fill keep y τ) =
      ∫⁻ x : ι → ℝ, (unitBox lo).indicator 1 x * f x := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) keep
  have hp := (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℝ)) keep).symm e
  conv_rhs => rw [volume_pi]
  rw [← hp.lintegral_comp_emb e.symm.measurableEmbedding]
  have hpt (z : ({i // keep i} → ℝ) × ({i // ¬keep i} → ℝ)) :
      (unitBox lo).indicator 1 (e.symm z) * f (e.symm z) =
        ((unitBox fun i => lo i.1).indicator 1 z.1 * f (fill keep y z.1)) *
          (unitBox fun i : {i // ¬keep i} => lo i.1).indicator 1 z.2 := by
    have hf' : f (e.symm z) = f (fill keep y z.1) := by
      apply hdep
      intro i hi
      simp [e, fill, hi, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
    rw [hf']
    have hmem : e.symm z ∈ unitBox lo ↔ z.1 ∈ (unitBox fun i => lo i.1) ∧
        z.2 ∈ (unitBox fun i : {i // ¬keep i} => lo i.1) := by
      simp only [unitBox, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro h
        refine ⟨fun i => ?_, fun i => ?_⟩
        · have := h i.1
          simpa [e, i.2, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd] using this
        · have := h i.1
          simpa [e, i.2, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd] using this
      · rintro ⟨h1, h2⟩ i
        by_cases hi : keep i
        · simpa [e, hi, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd] using h1 ⟨i, hi⟩
        · simpa [e, hi, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd] using h2 ⟨i, hi⟩
    by_cases h1 : z.1 ∈ (unitBox fun i => lo i.1) <;>
      by_cases h2 : z.2 ∈ (unitBox fun i : {i // ¬keep i} => lo i.1) <;>
      simp [Set.indicator, h1, h2, hmem]
  simp_rw [hpt]
  rw [lintegral_prod_mul (f := fun τ => (unitBox fun i => lo i.1).indicator 1 τ * f (fill keep y τ))
    (g := fun σ => (unitBox fun i : {i // ¬keep i} => lo i.1).indicator 1 σ)
    (((measurable_one.indicator (measurableSet_unitBox _)).mul
      (hf.comp (measurable_fill keep y))).aemeasurable)
    (measurable_one.indicator (measurableSet_unitBox _)).aemeasurable]
  have hv := volume_unitBox (fun i : {i // ¬keep i} => lo i.1)
  rw [volume_pi] at hv
  rw [lintegral_indicator_one (measurableSet_unitBox _), hv, mul_one]
  rfl

/-! ### The link product over all branch times -/

variable {d : ℕ} {LG : LayeredGarden 1} {X : RegChain}

/-- The layer unit box of all branch times. -/
def layerBox (LG : LayeredGarden 1) : Set (GBranch LG.garden.tree → ℝ) :=
  unitBox fun b => (LG.layer b.toNode : ℝ)

theorem mem_layerBox_clock (hX : X.DecodesTree LG.garden) (t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ) :
    treeClockEquiv hX t ∈ layerBox LG ↔ ∀ i, t i ∈ linkBox (treeLayerLinks (d := d) LG hX i) := by
  simp only [layerBox, unitBox, linkBox, treeLayerLinks, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  constructor
  · intro h i
    refine ⟨fun e => ?_, fun e => ?_⟩ <;> fin_cases e <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      first
      | exact (h (treeLinkBranch hX i 0)).1.trans_eq (treeClockEquiv_apply hX t i 0)
      | exact (h (treeLinkBranch hX i 1)).1.trans_eq (treeClockEquiv_apply hX t i 1)
      | exact (treeClockEquiv_apply hX t i 0).symm.trans_le (h (treeLinkBranch hX i 0)).2
      | exact (treeClockEquiv_apply hX t i 1).symm.trans_le (h (treeLinkBranch hX i 1)).2
  · intro h b
    obtain ⟨v, rfl⟩ := (treeLinkEquiv hX).surjective b
    rw [treeClockEquiv_link]
    obtain ⟨i, e⟩ := v
    have h1 := (h i).1 e
    have h2 := (h i).2 e
    fin_cases e <;> exact ⟨h1, h2⟩

/-- **Product of link masses.** -/
theorem lintegral_tree_links (hX : X.DecodesTree LG.garden)
    (g : Fin (X.treeLinks (LG.garden.sig 0)).length → (Fin 2 → ℝ) → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : GBranch LG.garden.tree → ℝ, (layerBox LG).indicator 1 x * ∏ i, g i ((treeClockEquiv hX).symm x i) =
      ∏ i, ∫⁻ s in linkBox (treeLayerLinks (d := d) LG hX i), g i s := by
  rw [← (measurePreserving_treeClockEquiv hX).lintegral_comp_emb (treeClockEquiv hX).measurableEmbedding]
  have hpt (t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ) :
      (layerBox LG).indicator 1 (treeClockEquiv hX t) * ∏ i, g i ((treeClockEquiv hX).symm (treeClockEquiv hX t) i) =
        ∏ i, (linkBox (treeLayerLinks (d := d) LG hX i)).indicator (g i) (t i) := by
    rw [MeasurableEquiv.symm_apply_apply]
    by_cases ht : ∀ i, t i ∈ linkBox (treeLayerLinks (d := d) LG hX i)
    · rw [Set.indicator_of_mem ((mem_layerBox_clock hX t).2 ht), Pi.one_apply, one_mul]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (ht i) _).symm
    · push Not at ht
      obtain ⟨i, hi⟩ := ht
      rw [Set.indicator_of_notMem (fun h => hi ((mem_layerBox_clock (d := d) hX t).1 h i)), zero_mul]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [hpt]
  have hm (i) : Measurable ((linkBox (treeLayerLinks (d := d) LG hX i)).indicator (g i)) :=
    (hg i).indicator measurableSet_Icc
  rw [volume_pi, ApproxNT.lintegral_fintype_prod_eq_prod _ hm]
  exact Finset.prod_congr rfl fun i _ => lintegral_indicator measurableSet_Icc _

/-! ### Tonelli for the envelope, and the amplitude masses -/

variable {n m w : ℕ}

/-- **Envelope integral.** Any per-(star frequency, cell, spectral variable) bound `R` of the time integral of the link
product majorant gives the time integral of the envelope, with the star-measure mass and the cell spectral mass. -/
theorem lintegral_arrayEnvelope_le {T : Type*} [MeasurableSpace T] (μτ : Measure T) [SFinite μτ]
    {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (ψ : Fin n → LPair d → ℂ) (f : Fin m → Mom d → ℂ)
    {K M : ℕ} {B : ℝ} (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (k : Mom d) (G : Fin n → (Fin 2 → ℝ) → LayerLink d → ℝ≥0∞) (tf : T → Fin n → Fin 2 → ℝ)
    (hG : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, Measurable (fun v : T × α × (LocalizedCellIndex n m → Fin d → ℝ) =>
      ∏ i, G i (tf v.1 i) (cellLinks P F Q z v.2.1 v.2.2 i)))
    {R : ℝ≥0∞} (hR : ∀ z a ξ, ∫⁻ τ, ∏ i, G i (tf τ i) (cellLinks P F Q z a ξ i) ∂μτ ≤ R) :
    ∫⁻ τ, arrayEnvelope P F ζ L γ δ Q ψ f S k G (tf τ) ∂μτ ≤
      ENNReal.ofReal F.mass * (ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
        ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) * R := by
  let Bu := fun (u : SourceCellIndex S) (ξ : LocalizedCellIndex n m → Fin d → ℝ) =>
    ‖localizedSpectralReference (n := n) f u.1 ξ‖ₑ
  have hBu (u : SourceCellIndex S) : Measurable (Bu u) :=
    (continuous_localizedSpectralReferenceSpatial f u.1 hK hB h).measurable.enorm
  let Hu := fun (u : SourceCellIndex S) (τ : T) (a : α) (ξ : LocalizedCellIndex n m → Fin d → ℝ) =>
    ∏ i, G i (tf τ i) (cellLinks P F Q u.2.val a ξ i)
  have hint (u : SourceCellIndex S) : Measurable (fun q : (T × α) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      Bu u q.2 * Hu u q.1.1 q.1.2 q.2) :=
    ((hBu u).comp measurable_snd).mul ((hG u.2.val).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hΦ : Measurable (fun q : T × α => ∑' u : SourceCellIndex S, ∫⁻ ξ, Bu u ξ * Hu u q.1 q.2 ξ) :=
    Measurable.tsum fun u => (hint u).lintegral_prod_right'
  have hA : AEMeasurable (fun a => ‖F.amplitude a‖ₑ) F.μ := F.amplitude_integrable.aestronglyMeasurable.enorm
  have henv (τ : T) : arrayEnvelope P F ζ L γ δ Q ψ f S k G (tf τ) =
      ∫⁻ a, ‖F.amplitude a‖ₑ * (∑' u : SourceCellIndex S, ∫⁻ ξ, Bu u ξ * Hu u τ a ξ) ∂F.μ := by
    unfold arrayEnvelope
    simp_rw [MomentumTreeData.enorm_sourceSpectralAmplitudeSpatial]
    rfl
  simp_rw [henv]
  rw [lintegral_lintegral_swap (hA.comp_snd.mul hΦ.aemeasurable)]
  have hin (a : α) : ∫⁻ τ, ‖F.amplitude a‖ₑ * (∑' u : SourceCellIndex S, ∫⁻ ξ, Bu u ξ * Hu u τ a ξ) ∂μτ ≤
      ‖F.amplitude a‖ₑ * ((∑' u : SourceCellIndex S, ∫⁻ ξ, Bu u ξ) * R) := by
    have hΦa : Measurable (fun τ => ∑' u : SourceCellIndex S, ∫⁻ ξ, Bu u ξ * Hu u τ a ξ) :=
      hΦ.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_const_mul (‖F.amplitude a‖ₑ) hΦa]
    apply mul_le_mul' le_rfl
    have hua (u : SourceCellIndex S) : Measurable (fun τ => ∫⁻ ξ, Bu u ξ * Hu u τ a ξ) :=
      (hint u).lintegral_prod_right'.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_tsum fun u => (hua u).aemeasurable, ← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro u
    have hsw : Measurable (fun p : T × (LocalizedCellIndex n m → Fin d → ℝ) => Bu u p.2 * Hu u p.1 a p.2) :=
      ((hBu u).comp measurable_snd).mul
        ((hG u.2.val).comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
    rw [lintegral_lintegral_swap hsw.aemeasurable, ← lintegral_mul_const R (hBu u)]
    apply lintegral_mono
    intro ξ
    dsimp only
    have hτ : Measurable (fun τ => Hu u τ a ξ) :=
      (hG u.2.val).comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))
    rw [lintegral_const_mul (Bu u ξ) hτ]
    exact mul_le_mul' le_rfl (hR u.2.val a ξ)
  have hmass : (∑' u : SourceCellIndex S, ∫⁻ ξ, Bu u ξ) ≤ ENNReal.ofReal (C ^ n) *
      (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m * ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) := by
    rw [tsum_sourceCellIndex S (fun c => ∫⁻ ξ, ‖localizedSpectralReference (n := n) f c ξ‖ₑ),
      ← lintegral_sourceCellMeasure S _ (fun c => (continuous_localizedSpectralReferenceSpatial f c hK hB h).measurable.enorm)]
    exact lintegral_sourceCellMeasure_reference_leSpatial S hS f hK hM hB h
  have hFm : ∫⁻ a, ‖F.amplitude a‖ₑ ∂F.μ = ENNReal.ofReal F.mass := by
    rw [SpatialMeasure.mass, ofReal_integral_norm_eq_lintegral_enorm F.amplitude_integrable]
  calc _ ≤ ∫⁻ a, ‖F.amplitude a‖ₑ * ((∑' u : SourceCellIndex S, ∫⁻ ξ, Bu u ξ) * R) ∂F.μ := lintegral_mono hin
    _ = (∫⁻ a, ‖F.amplitude a‖ₑ ∂F.μ) * ((∑' u : SourceCellIndex S, ∫⁻ ξ, Bu u ξ) * R) :=
        lintegral_mul_const'' _ hA
    _ ≤ _ := by
        rw [hFm, mul_assoc]
        exact mul_le_mul' le_rfl (mul_le_mul' hmass le_rfl)

end WaveTurbulence.Flower.ProtPtw
