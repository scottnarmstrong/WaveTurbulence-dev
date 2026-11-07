/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.CoarseBlockST
public import WaveTurbulence.Foundations.Spine.Assembly3
/-! # FLOWER-P5: the class-sum bound for the spliced kernel with stubs (copy-and-thread of `Assembly3`)

Same proof as `splicedKernel_le_classes`: the stubs lie in no ladder block, so the block integral runs over the
free clocks (`prod_block_integral_free`) and the pointwise fibre bound is unchanged. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.CoarseSpliced Finset MeasureTheory Set
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem splicedKernelST_le_classes (hP : G.IsPlain) (D : SplicedKernelDataST G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (S : ι → Finset (GBranch G.tree))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hfree : ∀ i, ∀ v ∈ S i, D.fix v = none) (hH : ∀ i, Disjoint (S i) D.hinges)
    {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (hc : 0 < ‖(coupling d L γ δ : ℂ)‖) (b : ι → ℝ)
    (hb : ∀ (z₀ : GenDecoration G d roots 0)
        (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1))),
        (∀ i ζ, ζ ∉ T i → ladderWeight D.toSplicedKernelData (S i) L γ η base ζ.1.1 = 0) → ∀ i,
        ‖(coupling d L γ δ : ℂ)‖ ^ ((S i).card - 1) *
          ∫ s in LadderDecay.timeBox G D.layer (S i), ‖Lam D.toSplicedKernelData S L γ η δ base z₀ T i s‖ ≤ b i)
    (hk : ∑ i, ((S i).card - 1) ≤ G.order) :
    ‖splicedKernelST G D L γ η δ base roots‖ ≤
      ‖(coupling d L γ δ : ℂ)‖ ^ (G.order - ∑ i, ((S i).card - 1)) *
        ((((finite_momAmp_support G hP D.toSplicedKernelData hD hL γ η base roots).toFinset.image (kappa S)).card : ℕ) : ℝ) *
        ∏ i, b i := by
  set hfin := finite_momAmp_support G hP D.toSplicedKernelData hD hL γ η base roots with hfin_def
  set Zsupp := hfin.toFinset with hZs
  have hZ : ∀ z : GenDecoration G d roots 0, splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 ≠ 0 → z ∈ Zsupp :=
    fun z hz => hfin.mem_toFinset.mpr hz
  refine (splicedKernelST_norm_le D γ η δ base roots Zsupp hZ).trans ?_
  by_cases hne : Nonempty (GenDecoration G d roots 0)
  swap
  · have hZe : Zsupp = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro z; exact (hne ⟨z⟩).elim
    rw [hZe]
    simp only [Finset.sum_empty, norm_zero, MeasureTheory.integral_zero, mul_zero, Finset.image_empty,
      Finset.card_empty, Nat.cast_zero, zero_mul]
    exact le_rfl
  set 𝒞 := Zsupp.image (kappa S) with h𝒞
  have hrep : ∀ c ∈ 𝒞, ∃ z ∈ Zsupp, kappa S z = c := fun c hc => Finset.mem_image.mp hc
  choose! rep hrep1 hrep2 using hrep
  -- supports of the local weights
  have hTfin : ∀ c, ∀ i, Set.Finite {ζ : ↥(localLadderDecorations G (S i) roots (bondIndex G (rep c).1)) |
      ladderWeight D.toSplicedKernelData (S i) L γ η base ζ.1.1 ≠ 0} :=
    fun c i => weight_support_finite hP hL base D.toSplicedKernelData hD (S i) γ η roots (bondIndex G (rep c).1)
  let T : ∀ c, ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G (rep c).1)) :=
    fun c i => (hTfin c i).toFinset
  have hT : ∀ c i ζ, ζ ∉ T c i → ladderWeight D.toSplicedKernelData (S i) L γ η base ζ.1.1 = 0 := by
    intro c i ζ hζ
    by_contra h
    exact hζ ((hTfin c i).mem_toFinset.mpr h)
  -- pointwise bound
  have hpt : ∀ t : GBranch G.tree → ℝ,
      ‖∑ z ∈ Zsupp, splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 * globalPhase D.toSplicedKernelData L γ δ base z.1 t‖ ≤
        ∑ c ∈ 𝒞, ∏ i, ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i (fun v : S i => t v.1)‖ := by
    intro t
    rw [← Finset.sum_fiberwise_of_maps_to (s := Zsupp) (t := 𝒞) (g := kappa S)
      (fun z hz => Finset.mem_image_of_mem _ hz)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c hc' => ?_))
    apply fibre_norm_le hP D.toSplicedKernelData hD S hS hH hL γ η δ base roots (rep c)
      (Zsupp.filter (fun z => kappa S z = c))
    · intro z hz hm
      rw [Finset.mem_filter]
      refine ⟨hZ z hm, ?_⟩
      rw [← hrep2 c hc']
      exact (kappa_eq_iff S z (rep c)).mpr hz
    · intro z hz
      rw [Finset.mem_filter] at hz
      exact (kappa_eq_iff S z (rep c)).mp (hz.2.trans (hrep2 c hc').symm)
    · exact hT c
  -- continuity
  have hcont1 : Continuous (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
      ‖∑ z ∈ Zsupp, splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 * globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)‖) :=
    (continuous_finsetSum _ (fun z _ => continuous_const.mul
      ((continuous_globalPhase D.toSplicedKernelData L γ δ base z.1).comp (continuous_extendFix D.fix)))).norm
  have hcontLam : ∀ c i, Continuous (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
      ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i (fun v : S i => G.extendFix D.fix τ v.1)‖) := by
    intro c i
    exact ((continuous_Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i).comp
      (continuous_pi (fun v => (continuous_apply v.1).comp (continuous_extendFix D.fix)))).norm
  have hcont2 : ∀ c, Continuous (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
      ∏ i, ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i (fun v : S i => G.extendFix D.fix τ v.1)‖) :=
    fun c => continuous_finsetProd _ (fun i _ => hcontLam c i)
  have hint1 : IntegrableOn (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
      ‖∑ z ∈ Zsupp, splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 * globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)‖)
      (freeBox G D.layer D.fix) :=
    hcont1.continuousOn.integrableOn_compact (isCompact_freeBox G D.layer D.fix)
  have hint2 : ∀ c, IntegrableOn (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
      ∏ i, ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i (fun v : S i => G.extendFix D.fix τ v.1)‖)
      (freeBox G D.layer D.fix) :=
    fun c => (hcont2 c).continuousOn.integrableOn_compact (isCompact_freeBox G D.layer D.fix)
  -- integrate
  have hmono : ∫ τ in freeBox G D.layer D.fix,
      ‖∑ z ∈ Zsupp, splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 * globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)‖ ≤
      ∑ c ∈ 𝒞, ∏ i, ∫ s in LadderDecay.timeBox G D.layer (S i), ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i s‖ := by
    calc _ ≤ ∫ τ in freeBox G D.layer D.fix,
          ∑ c ∈ 𝒞, ∏ i, ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i (fun v : S i => G.extendFix D.fix τ v.1)‖ :=
        integral_mono hint1 (integrable_finsetSum _ (fun c _ => hint2 c)) (fun τ => hpt (G.extendFix D.fix τ))
      _ = ∑ c ∈ 𝒞, ∫ τ in freeBox G D.layer D.fix,
          ∏ i, ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i (fun v : S i => G.extendFix D.fix τ v.1)‖ :=
        integral_finsetSum _ (fun c _ => hint2 c)
      _ = _ := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        exact prod_block_integral_free D.layer D.fix S hfree
          (fun i s => ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i s‖) univ
          (fun i _ j _ hij => hS i j hij)
  -- the ladder bounds
  have hLb : ∀ c ∈ 𝒞, ∀ i, ∫ s in LadderDecay.timeBox G D.layer (S i), ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i s‖ ≤
      b i / ‖(coupling d L γ δ : ℂ)‖ ^ ((S i).card - 1) := by
    intro c _ i
    rw [le_div_iff₀ (pow_pos hc _), mul_comm]
    exact hb (rep c) (T c) (hT c) i |>.trans' (le_of_eq (by ring))
  have hnn : ∀ c ∈ 𝒞, ∀ i, 0 ≤ ∫ s in LadderDecay.timeBox G D.layer (S i), ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i s‖ :=
    fun c _ i => setIntegral_nonneg (isCompact_timeBox G D.layer (S i)).measurableSet (fun _ _ => norm_nonneg _)
  have hprod : ∀ c ∈ 𝒞, ∏ i, ∫ s in LadderDecay.timeBox G D.layer (S i), ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i s‖ ≤
      ∏ i, (b i / ‖(coupling d L γ δ : ℂ)‖ ^ ((S i).card - 1)) :=
    fun c hc' => by
      gcongr with i hi
      exact hLb c hc' i
  have hsum : ∑ c ∈ 𝒞, ∏ i, ∫ s in LadderDecay.timeBox G D.layer (S i), ‖Lam D.toSplicedKernelData S L γ η δ base (rep c) (T c) i s‖ ≤
      (𝒞.card : ℝ) * ∏ i, (b i / ‖(coupling d L γ δ : ℂ)‖ ^ ((S i).card - 1)) := by
    calc _ ≤ ∑ _c ∈ 𝒞, ∏ i, (b i / ‖(coupling d L γ δ : ℂ)‖ ^ ((S i).card - 1)) :=
          Finset.sum_le_sum hprod
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_left (hmono.trans hsum) (by positivity) |>.trans (le_of_eq ?_)
  -- arithmetic
  set cc := ‖(coupling d L γ δ : ℂ)‖ with hcc
  have hprodb : ∏ i, (b i / cc ^ ((S i).card - 1)) = (∏ i, b i) / cc ^ (∑ i, ((S i).card - 1)) := by
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hprodb]
  have hn : cc ^ G.order = cc ^ (G.order - ∑ i, ((S i).card - 1)) * cc ^ (∑ i, ((S i).card - 1)) := by
    rw [← pow_add]; congr 1; omega
  rw [hn]
  have hpos : 0 < cc ^ (∑ i, ((S i).card - 1)) := pow_pos hc _
  field_simp


end WaveTurbulence.FlowerP5
