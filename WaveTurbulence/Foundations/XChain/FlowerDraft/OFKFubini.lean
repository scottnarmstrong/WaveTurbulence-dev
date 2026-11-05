/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.OFKFlower

/-!
# O-FK, part 4: Fubini at the flower parent

* `integral_eq_integral_glueTime`: `∫ τ H(τ) = ∫ ds ∫ dτ' H(t_{c₀} := s, τ')`.
* `timeIntG_flowerData`: the time integral of a decoration of `F.toTree`, with `b` at the flower, is
  `∫_p^t W_κ(s) b_{κ_𝔣}(s)^{ζ_𝔣} ∏_{ℓ≠𝔣} a_{κ_ℓ}(p)^{ζ_ℓ} ds`. Here `W_κ(s)` is the time integral of TARGET's
  kernel, with `t_{𝔣^pr} := s`.
* Bounds and measurability of the summands `flowerSummand` in the flower-parent time `s`.
  The assembly (`fOp_kernel_rep'`) is in `OFK-Rep.lean`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

variable (L γ δ : ℝ) {d : ℕ}

/-! ## Signs -/

theorem pow_count_flowerPath : ∀ F : FTree, ((-1 : ℤˣ) ^ (F.flowerPath.count 1)) = F.sign
  | .flower => by simp [flowerPath, sign]
  | .node i F T₁ T₂ => by
    have ih := pow_count_flowerPath F
    fin_cases i <;> simp [flowerPath, sign, pow_succ, ih, mul_comm]

theorem treeSign_flowerLeaf (F : FTree) : treeSign F.toTree F.flowerLeaf.toNode = F.sign := by
  show (1 : ℤˣ) * (-1) ^ (F.flowerPath.count 1) = F.sign
  rw [one_mul, pow_count_flowerPath]

/-! ## Splitting off one branching time -/

section Glue

variable {T : TTree}

open Classical in
/-- `t_{c₀} := s`; the other branching times from `τ'`. -/
noncomputable def glueTime (c₀ : GBranch (single T)) (s : ℝ) (τ' : {c : GBranch (single T) // c ≠ c₀} → ℝ) :
    GBranch (single T) → ℝ :=
  fun c => if h : c = c₀ then s else τ' ⟨c, h⟩

theorem glueTime_self (c₀ : GBranch (single T)) (s : ℝ) (τ' : {c : GBranch (single T) // c ≠ c₀} → ℝ) :
    glueTime c₀ s τ' c₀ = s := by
  simp [glueTime]

theorem glueTime_ne (c₀ : GBranch (single T)) (s : ℝ) (τ' : {c : GBranch (single T) // c ≠ c₀} → ℝ)
    {c : GBranch (single T)} (h : c ≠ c₀) : glueTime c₀ s τ' c = τ' ⟨c, h⟩ := by
  simp [glueTime, h]

theorem continuous_glueTime (c₀ : GBranch (single T)) :
    Continuous fun z : ℝ × ({c : GBranch (single T) // c ≠ c₀} → ℝ) => glueTime c₀ z.1 z.2 := by
  refine continuous_pi fun c => ?_
  unfold glueTime
  split_ifs with h
  · exact continuous_fst
  · exact (continuous_apply _).comp continuous_snd

open Classical in
/-- `ℝ^{𝒩} ≃ ℝ × ℝ^{𝒩 ∖ {c₀}}`. -/
noncomputable def splitAt (c₀ : GBranch (single T)) :
    (GBranch (single T) → ℝ) ≃ᵐ ℝ × ({c : GBranch (single T) // c ≠ c₀} → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : GBranch (single T) => ℝ) (· = c₀)).trans
    ((MeasurableEquiv.funUnique {c : GBranch (single T) // c = c₀} ℝ).prodCongr (MeasurableEquiv.refl _))

theorem splitAt_symm_apply (c₀ : GBranch (single T)) (z : ℝ × ({c : GBranch (single T) // c ≠ c₀} → ℝ)) :
    (splitAt c₀).symm z = glueTime c₀ z.1 z.2 := rfl

open Classical in
theorem measurePreserving_splitAt (c₀ : GBranch (single T)) :
    MeasurePreserving (splitAt c₀) volume ((volume : Measure ℝ).prod volume) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd
    (fun _ : GBranch (single T) => (volume : Measure ℝ)) (· = c₀)
  have h2 := measurePreserving_funUnique (volume : Measure ℝ) {c : GBranch (single T) // c = c₀}
  refine (h2.prod (MeasurePreserving.id _)).comp ?_
  convert h1 using 3

/-- **Fubini at one branching time.** -/
theorem integral_eq_integral_glueTime (c₀ : GBranch (single T)) {H : (GBranch (single T) → ℝ) → ℂ}
    (hH : Integrable H) : ∫ τ, H τ = ∫ s, ∫ τ', H (glueTime c₀ s τ') := by
  have hE := MeasurePreserving.symm (splitAt c₀) (measurePreserving_splitAt c₀)
  have hint : Integrable (fun z : ℝ × ({c : GBranch (single T) // c ≠ c₀} → ℝ) => H (glueTime c₀ z.1 z.2))
      ((volume : Measure ℝ).prod volume) :=
    (hE.integrable_comp_emb (splitAt c₀).symm.measurableEmbedding).2 hH
  rw [← hE.integral_comp' H]
  exact integral_prod _ hint

end Glue

/-! ## The flower parent -/

section Flower

variable {F : FTree}

theorem parTime_flowerLeaf (hF : F ≠ flower) (τ : GBranch (single F.toTree) → ℝ) (t : ℝ) :
    parTime τ t F.flowerLeaf = τ (F.flowerParent hF) := by
  have h : F.flowerLeaf.1.2 ≠ [] := flowerPath_ne_nil hF
  unfold parTime
  simp only [h, ↓reduceDIte]
  rfl

/-- The leaf factor away from the flower. -/
noncomputable def restProd (F : FTree) (aP : (Fin d → ℤ) → ℂ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    ℂ :=
  ∏ ℓ ∈ Finset.univ.erase F.flowerLeaf, zpowSign (treeSign F.toTree ℓ.toNode) (aP (κ ℓ.toNode))

/-- The input factor `b_{k'}(s)^{ζ_𝔣}`. -/
noncomputable def inFac {p : ℕ} (F : FTree) (b : ArrI p d) (s : ℝ) (k' : Fin d → ℤ) : ℂ :=
  zpowSign F.sign (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')

/-- The time integral of TARGET's kernel, with `t_{𝔣^pr} := s`. -/
noncomputable def flowerTimeInt (p : ℕ) (F : FTree) (hF : F ≠ flower)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) (t s : ℝ) : ℂ :=
  ∫ τ' : {c : GBranch (single F.toTree) // c ≠ F.flowerParent hF} → ℝ,
    (treeTimeDomain F.toTree p t).indicator (phaseFn L γ δ F.toTree κ) (glueTime (F.flowerParent hF) s τ')

theorem flowerKernel_eq (hF : F ≠ flower) (p : ℕ) (aP : (Fin d → ℤ) → ℂ) (t s : ℝ) (k k' : Fin d → ℤ) :
    flowerKernel L γ δ p F aP t s k k' = treePrefactor L γ δ d F.toTree *
      ∑' κ : FlowerDecoration F d k k',
        epsProd F.toTree κ.1.1 * flowerTimeInt L γ δ p F hF κ.1.1 t s * restProd F aP κ.1.1 := by
  simp only [flowerKernel, hF, ↓reduceDIte]
  rfl

theorem leafFactorG_flowerData (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) (κ : GNode (single F.toTree) → (Fin d → ℤ))
    (τ : GBranch (single F.toTree) → ℝ) (t : ℝ) :
    leafFactorG F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ τ t =
      inFac F b (τ (F.flowerParent hF)) (κ F.flowerLeaf.toNode) * restProd F aP κ := by
  unfold leafFactorG restProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ F.flowerLeaf)]
  congr 1
  · rw [treeSign_flowerLeaf, parTime_flowerLeaf hF]
    simp only [flowerData, LeafData.mark_B_self]
    rfl
  · refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    simp only [flowerData, LeafData.mark_B_ne _ _ _ _ (Finset.ne_of_mem_erase hℓ)]
    rfl

/-- **The time integral with `b` at the flower, by Fubini at the flower parent.** -/
theorem timeIntG_flowerData (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) (κ : GNode (single F.toTree) → (Fin d → ℤ)) {t : ℝ}
    (ht : (p : ℝ) ≤ t) :
    timeIntG L γ δ F.toTree κ (flowerData F (LeafIn.ofGood hb) haP) p t =
      ∫ s in (p : ℝ)..t, flowerTimeInt L γ δ p F hF κ t s *
        (inFac F b s (κ F.flowerLeaf.toNode) * restProd F aP κ) := by
  unfold timeIntG
  rw [integral_eq_integral_glueTime (F.flowerParent hF) (integrable_timeIntegrandG L γ δ _ κ _ p t)]
  have hpt : ∀ s, ∫ τ', (treeTimeDomain F.toTree p t).indicator (fun τ => phaseFn L γ δ F.toTree κ τ *
      leafFactorG F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ τ t) (glueTime (F.flowerParent hF) s τ') =
      flowerTimeInt L γ δ p F hF κ t s * (inFac F b s (κ F.flowerLeaf.toNode) * restProd F aP κ) := by
    intro s
    unfold flowerTimeInt
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun τ' => ?_)
    by_cases h : glueTime (F.flowerParent hF) s τ' ∈ treeTimeDomain F.toTree p t
    · simp only [Set.indicator_of_mem h, leafFactorG_flowerData hF p haP hb, glueTime_self]
    · simp only [Set.indicator_of_notMem h, zero_mul]
  simp only [hpt]
  rw [intervalIntegral.integral_of_le ht, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro s hs
  have : flowerTimeInt L γ δ p F hF κ t s = 0 := by
    unfold flowerTimeInt
    refine (integral_congr_ae (ae_of_all _ fun τ' => ?_)).trans (integral_zero _ _)
    refine Set.indicator_of_notMem (fun hmem => hs ?_) _
    have := hmem (F.flowerParent hF)
    rw [glueTime_self] at this
    exact ⟨this.1, this.2.1.le⟩
  rw [this, zero_mul]

/-! ### Bounds and measurability -/

/-- The volume of the box of the other branching times. -/
noncomputable def boxVolW (p : ℕ) (F : FTree) (hF : F ≠ flower) (t : ℝ) : ℝ :=
  volume.real (Set.pi univ fun _ : {c : GBranch (single F.toTree) // c ≠ F.flowerParent hF} =>
    Icc (p : ℝ) t)

theorem boxVolW_nonneg (hF : F ≠ flower) (p : ℕ) (t : ℝ) : 0 ≤ boxVolW p F hF t := measureReal_nonneg

theorem norm_flowerTimeInt_le (hF : F ≠ flower) (p : ℕ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) (t s : ℝ) :
    ‖flowerTimeInt L γ δ p F hF κ t s‖ ≤ boxVolW p F hF t := by
  set Box : Set ({c : GBranch (single F.toTree) // c ≠ F.flowerParent hF} → ℝ) :=
    Set.pi univ fun _ => Icc (p : ℝ) t
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBc : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
  have h := norm_integral_le_of_norm_le (μ := volume)
    (f := fun τ' => (treeTimeDomain F.toTree p t).indicator (phaseFn L γ δ F.toTree κ)
      (glueTime (F.flowerParent hF) s τ'))
    (g := Box.indicator fun _ => (1 : ℝ))
    ((integrable_indicator_iff hBm).2 (integrableOn_const hBc.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun τ' => by
      by_cases hD : glueTime (F.flowerParent hF) s τ' ∈ treeTimeDomain F.toTree p t
      · have hτ : τ' ∈ Box := fun c _ => by
          have := hD c.1
          rw [glueTime_ne _ _ _ c.2] at this
          exact ⟨this.1.le, this.2.1.le⟩
        rw [Set.indicator_of_mem hD, Set.indicator_of_mem hτ, norm_phaseFn]
      · rw [Set.indicator_of_notMem hD, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  rw [integral_indicator hBm, setIntegral_const, smul_eq_mul, mul_one] at h
  exact h

theorem stronglyMeasurable_flowerTimeInt (hF : F ≠ flower) (p : ℕ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) (t : ℝ) :
    StronglyMeasurable fun s => flowerTimeInt L γ δ p F hF κ t s := by
  have hG : StronglyMeasurable fun z : ℝ × ({c : GBranch (single F.toTree) // c ≠ F.flowerParent hF} → ℝ) =>
      (treeTimeDomain F.toTree p t).indicator (phaseFn L γ δ F.toTree κ) (glueTime (F.flowerParent hF) z.1 z.2) :=
    ((continuous_phaseFn L γ δ _ κ).stronglyMeasurable.indicator
      (measurableSet_treeTimeDomain _ _ _)).comp_measurable (continuous_glueTime _).measurable
  exact hG.integral_prod_right' (ν := volume)

theorem continuous_inFac {p : ℕ} {b : ArrI p d} (hb : Good p b) (k' : Fin d → ℤ) :
    Continuous fun s => inFac F b s k' :=
  (continuous_zpowSign _).comp (hb.iccExtend k')

theorem norm_rest_inFac_le (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {b : ArrI p d}
    (hb : Good p b) (κ : GNode (single F.toTree) → (Fin d → ℤ)) (s : ℝ) :
    ‖restProd F aP κ‖ * ‖inFac F b s (κ F.flowerLeaf.toNode)‖ ≤
      leafBound F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ := by
  unfold leafBound
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ F.flowerLeaf),
    mul_comm (‖restProd F aP κ‖)]
  have h1 : (flowerData F (LeafIn.ofGood hb) haP).U F.flowerLeaf = (LeafIn.ofGood hb).U :=
    LeafData.mark_U_self _ _ _ _
  have h2 : ∀ ℓ ∈ Finset.univ.erase F.flowerLeaf,
      (flowerData F (LeafIn.ofGood hb) haP).U ℓ (κ ℓ.toNode) = ‖aP (κ ℓ.toNode)‖ := fun ℓ hℓ => by
    rw [flowerData, LeafData.mark_U_ne _ _ _ _ (Finset.ne_of_mem_erase hℓ)]
    rfl
  rw [Finset.prod_congr rfl h2, h1]
  refine mul_le_mul ?_ (le_of_eq ?_) (norm_nonneg _) ((LeafIn.ofGood hb).nonneg _)
  · unfold inFac
    rw [norm_zpowSign]
    exact (LeafIn.ofGood hb).bound _ _
  · unfold restProd
    rw [norm_prod]
    simp only [norm_zpowSign]

/-! ### The summands -/

/-- The summand of a decoration, as a function of the flower-parent time. -/
noncomputable def flowerSummand (p : ℕ) (F : FTree) (hF : F ≠ flower) (aP : (Fin d → ℤ) → ℂ) (b : ArrI p d)
    (t : ℝ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) (s : ℝ) : ℂ :=
  epsProd F.toTree κ * flowerTimeInt L γ δ p F hF κ t s * restProd F aP κ * inFac F b s (κ F.flowerLeaf.toNode)

theorem norm_flowerSummand_le (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) (t : ℝ)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) (s : ℝ) :
    ‖flowerSummand L γ δ p F hF aP b t κ s‖ ≤
      boxVolW p F hF t * leafBound F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ := by
  unfold flowerSummand
  rw [norm_mul, norm_mul, norm_mul, mul_assoc]
  calc ‖epsProd F.toTree κ‖ * ‖flowerTimeInt L γ δ p F hF κ t s‖ *
        (‖restProd F aP κ‖ * ‖inFac F b s (κ F.flowerLeaf.toNode)‖)
      ≤ 1 * boxVolW p F hF t * leafBound F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ := by
        exact mul_le_mul (mul_le_mul (norm_epsProd_le _ _) (norm_flowerTimeInt_le L γ δ hF p κ t s)
          (norm_nonneg _) zero_le_one) (norm_rest_inFac_le p haP hb κ s)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg zero_le_one (boxVolW_nonneg hF p t))
    _ = _ := by ring

theorem stronglyMeasurable_flowerSummand (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ} {b : ArrI p d}
    (hb : Good p b) (t : ℝ)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    StronglyMeasurable fun s => flowerSummand L γ δ p F hF aP b t κ s := by
  unfold flowerSummand
  exact ((stronglyMeasurable_const.mul (stronglyMeasurable_flowerTimeInt L γ δ hF p κ t)).mul
    stronglyMeasurable_const).mul (continuous_inFac hb _).stronglyMeasurable

theorem integrableOn_flowerSummand (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) (t : ℝ)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    IntegrableOn (fun s => flowerSummand L γ δ p F hF aP b t κ s) (Ioc (p : ℝ) t) :=
  Measure.integrableOn_of_bounded
    (M := boxVolW p F hF t * leafBound F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ)
    measure_Ioc_lt_top.ne (stronglyMeasurable_flowerSummand L γ δ hF p hb t κ).aestronglyMeasurable
    (ae_of_all _ fun s => norm_flowerSummand_le L γ δ hF p haP hb t κ s)

theorem integral_flowerSummand (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) {t : ℝ} (ht : (p : ℝ) ≤ t)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    ∫ s in (p : ℝ)..t, flowerSummand L γ δ p F hF aP b t κ s =
      epsProd F.toTree κ * timeIntG L γ δ F.toTree κ (flowerData F (LeafIn.ofGood hb) haP) p t := by
  rw [timeIntG_flowerData L γ δ hF p haP hb κ ht, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [flowerSummand]
  ring

end Flower

end WaveTurbulence.SysAPI
