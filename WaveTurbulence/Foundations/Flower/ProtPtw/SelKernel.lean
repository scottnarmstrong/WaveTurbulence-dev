/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Select

/-! # D6a PROT-PTW: the kernel with one selected time, pointwise (o82 Prop 14.2 with `a = 1`)

Split the selected free time `t_v` off the free times (Fubini); its section of the literal domain is an interval
(`ordConnected_section`), so its integral is the difference of the antiderivative integrand at the two endpoints
(`integral_Ioo_treeIntegrand`); each endpoint value is bounded by the envelope in which the selected link is
exceptional, independently of `t_v`; re-merge `t_v` as a dummy unit interval and apply the core bound. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links

/-! ### Splitting off one coordinate -/

section Split
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance uniqueNotNe (v : ι) : Unique {i : ι // ¬i ≠ v} where
  default := ⟨v, by simp⟩
  uniq := fun ⟨i, hi⟩ => Subtype.ext (not_not.mp hi)

/-- The measurable equivalence `(τ', x) ↦` (put `x` at coordinate `v` and `τ'` elsewhere). -/
def joinEquiv (v : ι) : ({i // i ≠ v} → ℝ) × ℝ ≃ᵐ (ι → ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.funUnique {i // ¬i ≠ v} ℝ).symm).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ≠ v)).symm

/-- Put `x` at coordinate `v` and `τ'` elsewhere. -/
def join (v : ι) (τ' : {i // i ≠ v} → ℝ) (x : ℝ) : ι → ℝ := joinEquiv v (τ', x)

omit [Fintype ι] in
theorem join_apply_self (v : ι) (τ' : {i // i ≠ v} → ℝ) (x : ℝ) : join v τ' x v = x := by
  simp [join, joinEquiv, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  rfl

omit [Fintype ι] in
theorem join_apply_ne (v : ι) (τ' : {i // i ≠ v} → ℝ) (x : ℝ) {i : ι} (h : i ≠ v) :
    join v τ' x i = τ' ⟨i, h⟩ := by
  simp [join, joinEquiv, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h]
  rfl

omit [Fintype ι] in
theorem join_eq_update (v : ι) (τ' : {i // i ≠ v} → ℝ) (x : ℝ) :
    join v τ' x = Function.update (join v τ' 0) v x := by
  funext i
  by_cases h : i = v
  · subst h; rw [Function.update_self, join_apply_self]
  · rw [Function.update_of_ne h, join_apply_ne v τ' x h, join_apply_ne v τ' 0 h]

theorem pi_fintype_irrel {κ : Type*} (i1 i2 : Fintype κ) (μ : κ → Measure ℝ) :
    @Measure.pi κ (fun _ => ℝ) i1 _ μ = @Measure.pi κ (fun _ => ℝ) i2 _ μ := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

theorem measurePreserving_joinEquiv (v : ι) : MeasurePreserving (joinEquiv v) (volume.prod volume) volume := by
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℝ)) (· ≠ v)).symm
  have h3 := (volume_preserving_funUnique {i // ¬i ≠ v} ℝ).symm
  have h2 : MeasurePreserving (Prod.map id (MeasurableEquiv.funUnique {i // ¬i ≠ v} ℝ).symm)
      ((Measure.pi fun _ : {i // i ≠ v} => (volume : Measure ℝ)).prod volume)
      ((Measure.pi fun _ : {i // i ≠ v} => (volume : Measure ℝ)).prod
        (Measure.pi fun _ : {i // ¬i ≠ v} => (volume : Measure ℝ))) :=
    (MeasurePreserving.id _).prod (by
      convert h3
      exact pi_fintype_irrel _ _ _)
  rw [volume_pi]
  exact h1.comp h2

theorem integral_split (v : ι) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (ι → ℝ) → E)
    (hf : Integrable f) : ∫ τ, f τ = ∫ τ' : {i // i ≠ v} → ℝ, ∫ x : ℝ, f (join v τ' x) := by
  have h := (measurePreserving_joinEquiv v).integral_comp (joinEquiv v).measurableEmbedding f
  rw [← h, integral_prod (fun z => f (joinEquiv v z))
    ((measurePreserving_joinEquiv v).integrable_comp_of_integrable hf)]
  rfl

theorem lintegral_split (v : ι) (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ τ, f τ = ∫⁻ τ' : {i // i ≠ v} → ℝ, ∫⁻ x : ℝ, f (join v τ' x) := by
  have h := (measurePreserving_joinEquiv v).lintegral_comp_emb (joinEquiv v).measurableEmbedding f
  rw [← h, lintegral_prod (fun z => f (joinEquiv v z)) (hf.comp (joinEquiv v).measurable).aemeasurable]
  rfl

end Split

/-! ### Regularity of the tree integrand -/

variable {d : ℕ} {LG : LayeredGarden 1} {X : RegChain}

theorem continuous_treeIntegrand_bound (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α] (L γ δ : ℝ)
    (H : LeafProfiles 1 d) (k : Mom d)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) {Bψ : ℝ} (hBψ : 0 ≤ Bψ)
    (hψ : ∀ i q, ‖ψ i q‖ ≤ Bψ)
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))‖)) :
    Continuous (treeIntegrand hX L γ δ H k F ψ) ∧ ∀ x, ‖treeIntegrand hX L γ δ H k F ψ x‖ ≤
      F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ∑' p : Fin (X.treeLinks (LG.garden.sig 0)).length ×
        Fin 2 → Fin d → ℤ, ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k
          (fun i j => latticePoint L (p (i, j)))‖ := by
  let lw := fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
    (treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))
  let fp := fun (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ)
      (t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ) =>
    F.value (pairedLattice L p) * arrayWeight ψ p * sourceTemporalPhase L γ δ (treeLayerLinks LG hX) p t *
      ((gardenCircle LG.garden : ℂ) * lw p)
  have hb (p) (t) : ‖fp p t‖ ≤ F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖ := by
    have h1 := F.norm_value_le (pairedLattice L p)
    have h2 := norm_arrayWeight_le ψ hBψ hψ p
    have h3 := norm_sourceTemporalPhase_le_one L γ δ (treeLayerLinks (d := d) LG hX) p t
    simp only [fp, norm_mul, Circle.norm_coe, one_mul]
    calc _ ≤ F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * 1 * ‖lw p‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) F.mass_nonneg) h3
            (norm_nonneg _) (mul_nonneg F.mass_nonneg (pow_nonneg hBψ _))) (norm_nonneg _)
      _ = _ := by ring
  have hsum := hs.mul_left (F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length)
  constructor
  · have hc : Continuous (fun t => ∑' p, fp p t) :=
      continuous_tsum (fun p => by
        have := continuous_sourceTemporalPhase L γ δ (treeLayerLinks (d := d) LG hX) p
        simp only [fp]; fun_prop) hsum (fun p t => hb p t)
    have hcl : Continuous (treeClockEquiv hX).symm := by
      have he : ⇑(treeClockEquiv hX).symm = fun g i e => g (treeLinkBranch hX i e) :=
        funext fun g => funext fun i => funext fun e => treeClockEquiv_symm_apply hX g i e
      rw [he]; fun_prop
    exact hc.comp hcl
  · intro x
    unfold treeIntegrand arrayIntegrand
    refine (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => hb p _))).trans ?_
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun p => hb p _) (hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => hb p _)) hsum

/-! ### The section of the domain in one free time -/

theorem ordConnected_section (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (g : GBranch LG.garden.tree → ℝ) (v : GBranch LG.garden.tree) :
    (Set.ofPred fun x => Function.update g v x ∈ protDom LG up s fix).OrdConnected := by
  refine ⟨fun x hx z hz y hy => ?_⟩
  obtain ⟨⟨hx1, hx2⟩, hz1⟩ := And.intro hx hz
  simp only [Set.mem_ofPred_eq, protDom, kDomainFix, Set.mem_inter_iff] at hx hz ⊢
  obtain ⟨⟨hxa, hxb⟩, ⟨hza, hzb⟩⟩ := And.intro hx hz
  refine ⟨fun b => ⟨fun hb => ?_, fun b' hb' hfr => ?_⟩, fun b hb hfr => ?_⟩
  · have h1 := (hxa b).1 hb
    have h3 := (hza b).1 hb
    by_cases hbv : b = v
    · subst hbv
      simp only [Function.update_self] at h1 h3 ⊢
      exact ⟨h1.1.trans_le hy.1, hy.2.trans_lt h3.2.1, h1.2.2.1.trans_le hy.1, hy.2.trans_lt h3.2.2.2⟩
    · simpa only [Function.update_of_ne hbv] using h1
  · have h1 := (hxa b).2 b' hb' hfr
    have h3 := (hza b).2 b' hb' hfr
    by_cases hb'v : b' = v
    · by_cases hbv : b = v
      · subst hb'v; subst hbv
        simp only [Function.update_self] at h1
        exact absurd h1 (lt_irrefl _)
      · subst hb'v
        simp only [Function.update_self, Function.update_of_ne hbv] at h3 ⊢
        exact hy.2.trans_lt h3
    · by_cases hbv : b = v
      · subst hbv
        simp only [Function.update_self, Function.update_of_ne hb'v] at h1 ⊢
        exact h1.trans_le hy.1
      · simpa only [Function.update_of_ne hbv, Function.update_of_ne hb'v] using h1
  · have h1 := hxb b hb hfr
    by_cases hbv : b = v
    · subst hbv
      simp only [Function.update_self] at h1 ⊢
      exact h1.trans_le hy.1
    · simpa only [Function.update_of_ne hbv] using h1

theorem section_subset_Icc (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (g : GBranch LG.garden.tree → ℝ) {v : GBranch LG.garden.tree} (hv : fix v = none) :
    (Set.ofPred fun x => Function.update g v x ∈ protDom LG up s fix) ⊆
      Icc (LG.layer v.toNode : ℝ) (LG.layer v.toNode + 1) := by
  intro x hx
  have h := (hx.1 v).1 hv
  simp only [Function.update_self] at h
  exact ⟨h.1.le, h.2.1.le⟩

/-- **The selected-time integral**: bounded by twice any bound of the antiderivative integrand on the line. -/
theorem enorm_integral_section_le (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α] {L : ℝ}
    (hL : 0 < L) (γ δ : ℝ) (H : LeafProfiles 1 d) (k : Mom d)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) {Bψ : ℝ} (hBψ : 0 ≤ Bψ)
    (hψ : ∀ i q, ‖ψ i q‖ ≤ Bψ) (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2)
    (hann : ∀ q, selFreq (X := X) (LG := LG) L γ δ (treeLayerLinks LG hX) j ev q = 0 → ψ j q = 0)
    {Bψ' : ℝ} (hBψ' : 0 ≤ Bψ') (hψ' : ∀ i q, ‖selWeight L γ δ (treeLayerLinks LG hX) j ev ψ i q‖ ≤ Bψ')
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))‖))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (hv : fix (treeLinkBranch hX j ev) = none) (g : GBranch LG.garden.tree → ℝ) {R : ℝ≥0∞}
    (hR : ∀ x, ‖treeIntegrand hX L γ δ H k F (selWeight L γ δ (treeLayerLinks LG hX) j ev ψ)
      (Function.update g (treeLinkBranch hX j ev) x)‖ₑ ≤ R) :
    ‖∫ x : ℝ, (protDom LG up s fix).indicator (treeIntegrand hX L γ δ H k F ψ)
      (Function.update g (treeLinkBranch hX j ev) x)‖ₑ ≤ 2 * R := by
  set v := treeLinkBranch hX j ev
  set S := Set.ofPred fun x => Function.update g v x ∈ protDom LG up s fix
  have hS : MeasurableSet S := (ordConnected_section up s fix g v).measurableSet
  have hind : (fun x => (protDom LG up s fix).indicator (treeIntegrand hX L γ δ H k F ψ) (Function.update g v x)) =
      S.indicator (fun x => treeIntegrand hX L γ δ H k F ψ (Function.update g v x)) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show Function.update g v x ∈ protDom LG up s fix from hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show Function.update g v x ∉ protDom LG up s fix from hx)]
  rw [hind, integral_indicator hS]
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he, Measure.restrict_empty, integral_zero_measure, enorm_zero]; exact bot_le
  have hbdd := section_subset_Icc up s fix g hv
  have hbb : BddBelow S := ⟨_, fun x hx => (hbdd hx).1⟩
  have hba : BddAbove S := ⟨_, fun x hx => (hbdd hx).2⟩
  have hab : sInf S ≤ sSup S := csInf_le_csSup hne hbb hba
  have hIoo : Ioo (sInf S) (sSup S) ⊆ S := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := exists_lt_of_csInf_lt hne hy.1
    obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne hy.2
    exact (ordConnected_section up s fix g v).out hx hz ⟨hxy.le, hyz.le⟩
  have hIcc : S ⊆ Icc (sInf S) (sSup S) := fun x hx => ⟨csInf_le hbb hx, le_csSup hba hx⟩
  have hae : S =ᵐ[volume] Ioo (sInf S) (sSup S) :=
    (hIcc.eventuallyLE.trans Ioo_ae_eq_Icc.symm.le).antisymm hIoo.eventuallyLE
  rw [setIntegral_congr_set hae, integral_Ioo_treeIntegrand hX hL γ δ H k F ψ hBψ hψ j ev hann hBψ' hψ' hs g hab]
  calc _ ≤ ‖treeIntegrand hX L γ δ H k F (selWeight L γ δ (treeLayerLinks LG hX) j ev ψ) (Function.update g v (sSup S))‖ₑ +
        ‖treeIntegrand hX L γ δ H k F (selWeight L γ δ (treeLayerLinks LG hX) j ev ψ) (Function.update g v (sInf S))‖ₑ :=
        enorm_sub_le
    _ ≤ R + R := add_le_add (hR _) (hR _)
    _ = 2 * R := (two_mul R).symm

end WaveTurbulence.Flower.ProtPtw
