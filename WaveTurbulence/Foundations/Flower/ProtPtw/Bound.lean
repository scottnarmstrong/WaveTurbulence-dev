/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Envelope

/-! # D6a PROT-PTW: the pointwise bound with exceptional links (o82 Prop 14.2, (14.5))

The exceptional links `E` (those carrying a pinned or deleted time) are bounded by their trivial supremum
`c_i (5L)^{2d}`; every other link keeps its absolute pair mass `M_i` (Lemma 14.1). The time domain is enlarged to the
product of unit intervals; the deleted times are not integrated. Abstract in the kept coordinates `keep`/fill values
`y`, so that the pinned kernel (`keep = free`) and the selected faces (`keep = free \ {v}`) are both instances. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs

variable {d n m w : ℕ}

/-- The per-link majorant: trivial supremum on exceptional links, the absolute link factor otherwise. -/
def supG (L γ δ : ℝ) (E : Finset (Fin n)) (cE : Fin n → ℝ) (ψ : Fin n → LPair d → ℂ) :
    Fin n → (Fin 2 → ℝ) → LayerLink d → ℝ≥0∞ :=
  fun i s A => if i ∈ E then ENNReal.ofReal (cE i * (5 * L) ^ (2 * d)) else ‖genLinkTimeFactor L γ δ A (ψ i) s‖ₑ

theorem supG_ge {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (E : Finset (Fin n)) (cE : Fin n → ℝ) (ψ : Fin n → LPair d → ℂ)
    (hcE : ∀ i ∈ E, 0 ≤ cE i ∧ ∀ q, ‖ψ i q‖ ≤ cE i) (i : Fin n) (s : Fin 2 → ℝ) (A : LayerLink d) :
    ‖genLinkTimeFactor L γ δ A (ψ i) s‖ₑ ≤ supG L γ δ E cE ψ i s A := by
  unfold supG
  split_ifs with hi
  · rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_genLinkTimeFactor_le hL γ δ A (ψ i) (hcE i hi).1 (hcE i hi).2 s)
  · exact le_rfl

theorem genLinkTimeFactor_cellLinks {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (F : SpatialMeasure (PairedMomentum d n) α) (Q : Fin n → LayerLink d) (L γ δ : ℝ)
    (ψ : LPair d → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ) (i : Fin n) (a : α)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (t : Fin 2 → ℝ) :
    genLinkTimeFactor L γ δ (cellLinks P F Q z a ξ i) ψ t =
      genLinkLatticeSum L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1))
        { leftCenter := halfCellCenter (z (i, 0)), rightCenter := halfCellCenter (z (i, 1)),
          leftShift := P.spectralShift ξ (some (i, 0)) + F.frequency a (i, 0),
          rightShift := P.spectralShift ξ (some (i, 1)) + F.frequency a (i, 1) } ψ := by
  simp only [genLinkTimeFactor, cellLinks, MomentumTreeData.spectralLinksSpatial, spatialFrequencyLinks]

theorem measurable_genLinkTimeFactor_cellLinks {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (F : SpatialMeasure (PairedMomentum d n) α) (Q : Fin n → LayerLink d) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (ψ : LPair d → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ) (i : Fin n) :
    Measurable (fun v : (Fin 2 → ℝ) × α × (LocalizedCellIndex n m → Fin d → ℝ) =>
      genLinkTimeFactor L γ δ (cellLinks P F Q z v.2.1 v.2.2 i) ψ v.1) := by
  have hc : Continuous (fun v : (Fin 2 → ℝ) × PairedMomentum d n × (LocalizedCellIndex n m → Fin d → ℝ) =>
      genLinkLatticeSum L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (v.1 0 - v.1 1))
        { leftCenter := halfCellCenter (z (i, 0)), rightCenter := halfCellCenter (z (i, 1)),
          leftShift := P.spectralShift v.2.2 (some (i, 0)) + v.2.1 (i, 0),
          rightShift := P.spectralShift v.2.2 (some (i, 1)) + v.2.1 (i, 1) } ψ) :=
    continuous_genLinkLatticeSum_shifts hL _ _ ψ (by fun_prop)
      (by unfold MomentumTreeData.spectralShift; fun_prop) (by unfold MomentumTreeData.spectralShift; fun_prop)
  have he : (fun v : (Fin 2 → ℝ) × α × (LocalizedCellIndex n m → Fin d → ℝ) =>
      genLinkTimeFactor L γ δ (cellLinks P F Q z v.2.1 v.2.2 i) ψ v.1) =
      (fun v : (Fin 2 → ℝ) × PairedMomentum d n × (LocalizedCellIndex n m → Fin d → ℝ) =>
        genLinkLatticeSum L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (v.1 0 - v.1 1))
          { leftCenter := halfCellCenter (z (i, 0)), rightCenter := halfCellCenter (z (i, 1)),
            leftShift := P.spectralShift v.2.2 (some (i, 0)) + v.2.1 (i, 0),
            rightShift := P.spectralShift v.2.2 (some (i, 1)) + v.2.1 (i, 1) } ψ) ∘
        (fun v => (v.1, F.frequency v.2.1, v.2.2)) := by
    funext v
    exact genLinkTimeFactor_cellLinks P F Q L γ δ ψ z i v.2.1 v.2.2 v.1
  rw [he]
  exact hc.measurable.comp (measurable_fst.prodMk ((F.frequency_measurable.comp measurable_snd.fst).prodMk
    measurable_snd.snd))

theorem linkBox_eq_of_layers {A A' : LayerLink d} (h1 : A.leftLayer = A'.leftLayer)
    (h2 : A.rightLayer = A'.rightLayer) : linkBox A = linkBox A' := by
  unfold linkBox; rw [h1, h2]

theorem volume_linkBox (A : LayerLink d) : volume (linkBox A) = 1 := by
  unfold linkBox
  rw [Real.volume_Icc_pi]
  simp [Fin.prod_univ_two]

variable {LG : LayeredGarden 1} {X : RegChain}

/-- The time integral of the per-link majorants over the kept coordinates: the product of the link masses, with
exceptional links at their trivial supremum. -/
theorem lintegral_links_le (hX : X.DecodesTree LG.garden) {L : ℝ} (hLp : 0 < L) (γ δ : ℝ)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ)
    (E : Finset (Fin (X.treeLinks (LG.garden.sig 0)).length)) (cE : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ)
    (Mi : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ≥0∞)
    (hMi : ∀ i ∉ E, ∀ A : LayerLink d, A.leftLayer = (treeLayerLinks (d := d) LG hX i).leftLayer →
      A.rightLayer = (treeLayerLinks (d := d) LG hX i).rightLayer →
      ∫⁻ s in linkBox A, ‖genLinkTimeFactor L γ δ A (ψ i) s‖ₑ ≤ Mi i)
    (keep : GBranch LG.garden.tree → Prop) [DecidablePred keep] (y : GBranch LG.garden.tree → ℝ)
    (hkeep : ∀ i ∉ E, ∀ e, keep (treeLinkBranch hX i e))
    (A : Fin (X.treeLinks (LG.garden.sig 0)).length → LayerLink d)
    (hA1 : ∀ i, (A i).leftLayer = (treeLayerLinks (d := d) LG hX i).leftLayer)
    (hA2 : ∀ i, (A i).rightLayer = (treeLayerLinks (d := d) LG hX i).rightLayer) :
    ∫⁻ τ : {b // keep b} → ℝ, (unitBox fun b => (LG.layer b.1.toNode : ℝ)).indicator 1 τ *
        ∏ i, supG L γ δ E cE ψ i ((treeClockEquiv hX).symm (fill keep y τ) i) (A i) ≤
      ∏ i, (if i ∈ E then ENNReal.ofReal (cE i * (5 * L) ^ (2 * d)) else Mi i) := by
  let g := fun (i : Fin (X.treeLinks (LG.garden.sig 0)).length) (s : Fin 2 → ℝ) => supG L γ δ E cE ψ i s (A i)
  have hg (i) : Measurable (g i) := by
    dsimp only [g]
    unfold supG
    by_cases hi : i ∈ E
    · simp only [hi, ite_true]; exact measurable_const
    · simp only [hi, ite_false]
      exact (continuous_genLinkTimeFactor hLp γ δ _ (ψ i)).measurable.enorm
  have hdep : ∀ x x' : GBranch LG.garden.tree → ℝ, (∀ b, keep b → x b = x' b) →
      (∏ i, g i ((treeClockEquiv hX).symm x i)) = ∏ i, g i ((treeClockEquiv hX).symm x' i) := by
    intro x x' hxx
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ E
    · simp only [g, supG, hi, ite_true]
    · congr 1
      funext e
      have h1 := treeClockEquiv_apply hX ((treeClockEquiv hX).symm x) i e
      have h2 := treeClockEquiv_apply hX ((treeClockEquiv hX).symm x') i e
      rw [MeasurableEquiv.apply_symm_apply] at h1 h2
      rw [← h1, ← h2]
      exact hxx _ (hkeep i hi e)
  have hfm : Measurable (fun x : GBranch LG.garden.tree → ℝ => ∏ i, g i ((treeClockEquiv hX).symm x i)) :=
    Finset.measurable_prod _ fun i _ => (hg i).comp ((measurable_pi_apply i).comp (treeClockEquiv hX).symm.measurable)
  calc _ = ∫⁻ x : GBranch LG.garden.tree → ℝ, (layerBox LG).indicator 1 x * ∏ i, g i ((treeClockEquiv hX).symm x i) :=
        lintegral_fill keep (fun b => (LG.layer b.toNode : ℝ)) y _ hfm hdep
    _ = ∏ i, ∫⁻ s in linkBox (treeLayerLinks (d := d) LG hX i), g i s := lintegral_tree_links hX g hg
    _ ≤ _ := by
        apply Finset.prod_le_prod fun i _ => ?_
        by_cases hi : i ∈ E
        · simp only [g, supG, hi, ite_true]
          rw [setLIntegral_const, volume_linkBox, mul_one]
        · simp only [g, supG, hi, ite_false]
          rw [linkBox_eq_of_layers (A := treeLayerLinks (d := d) LG hX i) (A' := A i) (hA1 i).symm (hA2 i).symm]
          exact hMi i hi _ (hA1 i) (hA2 i)

/-- **The core bound** in the kept coordinates. -/
theorem lintegral_keep_envelope_le (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α]
    {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (H : LeafProfiles 1 d) (k : Mom d)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ)
    {K M : ℕ} {B : ℝ} (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (treeInputFunctionsL LG H a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (Links.TPlus LG.garden)) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ (X.treeLinks (LG.garden.sig 0)).length)
    (E : Finset (Fin (X.treeLinks (LG.garden.sig 0)).length)) (cE : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ)
    (Mi : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ≥0∞)
    (hMi : ∀ i ∉ E, ∀ A : LayerLink d, A.leftLayer = (treeLayerLinks (d := d) LG hX i).leftLayer →
      A.rightLayer = (treeLayerLinks (d := d) LG hX i).rightLayer →
      ∫⁻ s in linkBox A, ‖genLinkTimeFactor L γ δ A (ψ i) s‖ₑ ≤ Mi i)
    (keep : GBranch LG.garden.tree → Prop) [DecidablePred keep] (y : GBranch LG.garden.tree → ℝ)
    (hkeep : ∀ i ∉ E, ∀ e, keep (treeLinkBranch hX i e)) :
    ∫⁻ τ : {b // keep b} → ℝ, (unitBox fun b => (LG.layer b.1.toNode : ℝ)).indicator 1 τ *
        arrayEnvelope (treeCarrier hX) F (gardenCircle LG.garden) L γ δ (treeLayerLinks LG hX) ψ
          (treeInputFunctionsL LG H) S k (supG L γ δ E cE ψ) ((treeClockEquiv hX).symm (fill keep y τ)) ≤
      ENNReal.ofReal F.mass * (ENNReal.ofReal (C ^ (X.treeLinks (LG.garden.sig 0)).length) *
        (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ Fintype.card (Links.TPlus LG.garden) *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * (X.treeLinks (LG.garden.sig 0)).length))) *
        ∏ i, (if i ∈ E then ENNReal.ofReal (cE i * (5 * L) ^ (2 * d)) else Mi i) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  set Q := treeLayerLinks (d := d) LG hX
  let tf := fun τ : {b // keep b} → ℝ => (treeClockEquiv hX).symm (fill keep y τ)
  have hbox : MeasurableSet (unitBox fun b : {b // keep b} => (LG.layer b.1.toNode : ℝ)) := measurableSet_unitBox _
  have hlhs : (∫⁻ τ : {b // keep b} → ℝ, (unitBox fun b => (LG.layer b.1.toNode : ℝ)).indicator 1 τ *
        arrayEnvelope (treeCarrier hX) F (gardenCircle LG.garden) L γ δ Q ψ
          (treeInputFunctionsL LG H) S k (supG L γ δ E cE ψ) (tf τ)) =
      ∫⁻ τ, arrayEnvelope (treeCarrier hX) F (gardenCircle LG.garden) L γ δ Q ψ
          (treeInputFunctionsL LG H) S k (supG L γ δ E cE ψ) (tf τ)
        ∂(volume.restrict (unitBox fun b : {b // keep b} => (LG.layer b.1.toNode : ℝ))) := by
    rw [← lintegral_indicator hbox]
    apply lintegral_congr
    intro τ
    by_cases hτ : τ ∈ (unitBox fun b : {b // keep b} => (LG.layer b.1.toNode : ℝ)) <;>
      simp [Set.indicator, hτ]
  rw [hlhs]
  -- the per-link majorants are measurable
  have hGm (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ) :
      Measurable (fun v : ({b // keep b} → ℝ) × α × (LocalizedCellIndex (X.treeLinks (LG.garden.sig 0)).length
          (Fintype.card (Links.TPlus LG.garden)) → Fin d → ℝ) =>
        ∏ i, supG L γ δ E cE ψ i (tf v.1 i) (cellLinks (treeCarrier hX) F Q z v.2.1 v.2.2 i)) := by
    refine Finset.measurable_prod _ fun i _ => ?_
    unfold supG
    by_cases hi : i ∈ E
    · simp only [hi, ite_true]; exact measurable_const
    · simp only [hi, ite_false]
      have htf : Measurable (fun τ : {b // keep b} → ℝ => tf τ i) :=
        (measurable_pi_apply i).comp ((treeClockEquiv hX).symm.measurable.comp (measurable_fill keep y))
      exact ((measurable_genLinkTimeFactor_cellLinks (treeCarrier hX) F Q hLp γ δ (ψ i) z i).comp
        ((htf.comp measurable_fst).prodMk measurable_snd)).enorm
  refine lintegral_arrayEnvelope_le _ (treeCarrier hX) F (gardenCircle LG.garden) L γ δ Q ψ _ hK hM hB hf S hS k
    (supG L γ δ E cE ψ) tf hGm ?_
  intro z a ξ
  rw [← lintegral_indicator hbox]
  have hcong : ((unitBox fun b : {b // keep b} => (LG.layer b.1.toNode : ℝ)).indicator fun τ =>
      ∏ i, supG L γ δ E cE ψ i (tf τ i) (cellLinks (treeCarrier hX) F Q z a ξ i)) =
      fun τ => (unitBox fun b : {b // keep b} => (LG.layer b.1.toNode : ℝ)).indicator 1 τ *
        ∏ i, supG L γ δ E cE ψ i ((treeClockEquiv hX).symm (fill keep y τ) i) (cellLinks (treeCarrier hX) F Q z a ξ i) := by
    funext τ
    by_cases hτ : τ ∈ (unitBox fun b : {b // keep b} => (LG.layer b.1.toNode : ℝ)) <;> simp [Set.indicator, hτ, tf]
  rw [hcong]
  exact lintegral_links_le hX hLp γ δ ψ E cE Mi hMi keep y hkeep _ (fun _ => rfl) (fun _ => rfl)

end WaveTurbulence.Flower.ProtPtw
