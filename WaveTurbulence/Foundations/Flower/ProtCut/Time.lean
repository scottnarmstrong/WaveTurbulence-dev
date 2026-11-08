/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Spine.PL234Draft.LeafSummable

/-! # D2c PROT-CUT: the free-time integral of `kernelProt`

* `protDom`, `protTime`, `protSummand`: the time domain, the free-time integral at one decoration and the
  summand of `kernelProt` (`kernelProt_eq_tsum` is `rfl`).
* `integral_arrow_equiv`, `integral_sum_mul`: transport of a function-space integral along an equivalence of
  index types, and the product of integrals over a sum of index types.
* `norm_protTime_le_one`, `integrable_protIntegrand`: the integrand lives in a unit cube.
* **`protTime_pin`**: integrating out one free branch `a` (the pin identity in the direction
  `free = ∫ du pinned at u`), with the explicit constraint set `pinSet`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtCut

open WaveTurbulence.Flower.ProtDefs

variable {w d : ℕ}

/-- The time domain of `kernelProt`: frozen `kDomainFix` and the lone-port lower time. -/
def protDom (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) : Set (GBranch LG.garden.tree → ℝ) :=
  kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s < τ b}

/-- The free-time integral of `kernelProt` at the momenta `K`. -/
def protTime (L γ δ : ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) : ℂ :=
  ∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
    (protDom LG up s fix).indicator (phaseProd L γ δ LG.garden K) (LG.garden.extendFix fix τ)

/-- The summand of `kernelProt` at one integer decoration. -/
def protSummand (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) : ℂ :=
  m (cosetDecoration LG.garden L k₀ κ.1) *
    ((epsDec LG.garden κ.1 : ℂ) * protTime L γ δ LG up s fix (cosetDecoration LG.garden L k₀ κ.1) *
      ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))

theorem kernelProt_eq_tsum (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG H m up s fix k₀ nroot nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, protSummand L γ δ LG H m up s fix k₀ κ := by
  unfold kernelProt protSummand protTime protDom
  simp only [mul_assoc]

/-! ### Function-space integrals -/

/-- Transport of a function-space integral along an equivalence of the index types. -/
theorem integral_arrow_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (G : (β → ℝ) → ℂ) :
    ∫ σ : α → ℝ, G (fun b => σ (e.symm b)) = ∫ τ : β → ℝ, G τ := by
  have hΦ := measurePreserving_arrowCongr' (fun _ : α => (volume : Measure ℝ))
    (fun _ : β => (volume : Measure ℝ)) e (MeasurableEquiv.refl ℝ) fun _ => MeasurePreserving.id volume
  have := hΦ.integral_comp' (f := MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ)) G
  exact this

/-- The integral over a sum of index types of a product of a function of each part. -/
theorem integral_sum_mul {α β : Type*} [Fintype α] [Fintype β] (f : (α → ℝ) → ℂ) (g : (β → ℝ) → ℂ) :
    ∫ τ : α ⊕ β → ℝ, f (fun a => τ (Sum.inl a)) * g (fun b => τ (Sum.inr b)) =
      (∫ x : α → ℝ, f x) * ∫ y : β → ℝ, g y := by
  have hΦ : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)) volume volume :=
    volume_measurePreserving_sumPiEquivProdPi _
  have := hΦ.integral_comp' (fun z : (α → ℝ) × (β → ℝ) => f z.1 * g z.2)
  rw [← integral_prod_mul f g]
  exact this

/-! ### Measurability and the unit cube -/

theorem measurable_extendFix (G : Garden w) (fix : GBranch G.tree → Option ℝ) :
    Measurable (G.extendFix fix) := by
  refine measurable_pi_iff.2 fun b => ?_
  unfold Garden.extendFix
  split
  · exact measurable_const
  · exact measurable_pi_apply _

theorem measurableSet_imp {α : Type*} [MeasurableSpace α] (q : Prop) {S : Set α}
    (hS : MeasurableSet S) : MeasurableSet {x | q → x ∈ S} := by
  by_cases hq : q
  · simpa [hq] using hS
  · simp [hq]

theorem measurableSet_protDom (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) : MeasurableSet (protDom LG up s fix) := by
  classical
  unfold protDom kDomainFix
  refine MeasurableSet.inter ?_ ?_
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun b => ?_
    rw [Set.ofPred_and]
    refine MeasurableSet.inter ?_ ?_
    · refine measurableSet_imp _ ?_
      refine (measurableSet_lt measurable_const (measurable_pi_apply b)).inter
        ((measurableSet_lt (measurable_pi_apply b) measurable_const).inter
          ((measurableSet_lt measurable_const (measurable_pi_apply b)).inter
            (measurableSet_lt (measurable_pi_apply b) measurable_const)))
    · rw [Set.ofPred_forall]
      refine MeasurableSet.iInter fun b' => ?_
      refine measurableSet_imp _ (measurableSet_imp _ ?_)
      exact measurableSet_lt (measurable_pi_apply b') (measurable_pi_apply b)
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun b => measurableSet_imp _ (measurableSet_imp _ ?_)
    exact measurableSet_lt measurable_const (measurable_pi_apply b)

theorem continuous_phaseProd (L γ δ : ℝ) (G : Garden w) (K : GNode G.tree → Mom d) :
    Continuous (phaseProd L γ δ G K) := by
  unfold phaseProd
  refine continuous_finsetProd _ fun b _ => ?_
  refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
  exact Complex.continuous_ofReal.comp (continuous_const.mul (continuous_apply b))

theorem norm_phaseProd (L γ δ : ℝ) (G : Garden w) (K : GNode G.tree → Mom d)
    (τ : GBranch G.tree → ℝ) : ‖phaseProd L γ δ G K τ‖ = 1 := by
  unfold phaseProd
  rw [norm_prod]
  exact Finset.prod_eq_one fun b _ => Complex.norm_exp_ofReal_mul_I _

/-- The unit cube of the free times. -/
def freeBox (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ) :
    Set ({b : GBranch LG.garden.tree // fix b = none} → ℝ) :=
  Set.pi Set.univ fun b => Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)

theorem volume_freeBox (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ) :
    volume (freeBox LG fix) = 1 := by
  unfold freeBox
  rw [volume_pi_pi]
  simp only [Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_one, prod_const_one]

theorem extendFix_free (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) (b : {b : GBranch G.tree // fix b = none}) :
    G.extendFix fix τ b.1 = τ b := by
  unfold Garden.extendFix
  split
  · rename_i v h
    exact absurd (h.symm.trans b.2) (by simp)
  · rfl

theorem extendFix_some (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) {b : GBranch G.tree} {v : ℝ} (h : fix b = some v) :
    G.extendFix fix τ b = v := by
  unfold Garden.extendFix
  split
  · rename_i v' h'
    rw [h] at h'
    exact (Option.some.inj h').symm
  · rename_i h'
    rw [h] at h'
    exact absurd h' (by simp)

theorem protDom_subset_freeBox (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ)
    (h : LG.garden.extendFix fix τ ∈ protDom LG up s fix) : τ ∈ freeBox LG fix := by
  intro b _
  have hb := (h.1 b.1).1 b.2
  rw [extendFix_free] at hb
  exact ⟨hb.1.le, hb.2.1.le⟩

/-- The integrand of `protTime`. -/
def protIntegrand (L γ δ : ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d)
    (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ) : ℂ :=
  (protDom LG up s fix).indicator (phaseProd L γ δ LG.garden K) (LG.garden.extendFix fix τ)

theorem norm_protIntegrand_le (L γ δ : ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d)
    (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ) :
    ‖protIntegrand L γ δ LG up s fix K τ‖ ≤ (freeBox LG fix).indicator 1 τ := by
  unfold protIntegrand
  by_cases hD : LG.garden.extendFix fix τ ∈ protDom LG up s fix
  · rw [Set.indicator_of_mem hD, Set.indicator_of_mem (protDom_subset_freeBox LG up s fix τ hD),
      norm_phaseProd]
    rfl
  · rw [Set.indicator_of_notMem hD, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem measurable_protIntegrand (L γ δ : ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    Measurable (protIntegrand L γ δ LG up s fix K) := by
  unfold protIntegrand
  exact ((continuous_phaseProd L γ δ LG.garden K).measurable.indicator
    (measurableSet_protDom LG up s fix)).comp (measurable_extendFix _ _)

theorem integrable_protIntegrand (L γ δ : ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    Integrable (protIntegrand L γ δ LG up s fix K) := by
  have hBm : MeasurableSet (freeBox LG fix) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hint : Integrable ((freeBox LG fix).indicator (1 : ({b : GBranch LG.garden.tree //
      fix b = none} → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff hBm]
    exact integrableOn_const (by rw [volume_freeBox]; exact ENNReal.one_ne_top)
  exact hint.mono' (measurable_protIntegrand L γ δ LG up s fix K).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_protIntegrand_le L γ δ LG up s fix K))

theorem norm_protTime_le_one (L γ δ : ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    ‖protTime L γ δ LG up s fix K‖ ≤ 1 := by
  have hBm : MeasurableSet (freeBox LG fix) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hint : Integrable ((freeBox LG fix).indicator (1 : ({b : GBranch LG.garden.tree //
      fix b = none} → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff hBm]
    exact integrableOn_const (by rw [volume_freeBox]; exact ENNReal.one_ne_top)
  have h := norm_integral_le_of_norm_le hint
    (Filter.Eventually.of_forall (norm_protIntegrand_le L γ δ LG up s fix K))
  rw [integral_indicator_one hBm, measureReal_def, volume_freeBox, ENNReal.toReal_one] at h
  exact h

end WaveTurbulence.Flower.ProtCut
