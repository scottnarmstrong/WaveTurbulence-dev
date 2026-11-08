/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Face
public import WaveTurbulence.Foundations.Flower.FinalMKFine.Kernel
public import WaveTurbulence.Foundations.Spine.Support
import Mathlib.Tactic

/-! # LB-RESTORE-2 (ruling R187): constant lower bounds reduce to pins

The marked time integral `splicedTimeIntegralMK` runs over `splicedTimeDomainFix ∩ splicedLBDomain lb`. A lower
bound `x < t_b` at a FREE atom `b` is removed by Fubini at `b`: pinning `b` at `r` and integrating `r` over the window
`lbWin` (`x < r`, the layer box of `b`, the root time and the pinned neighbours of `b`):
`K(D) = ∫ r, lbWin.indicator (fun r => K(D[b ↦ r, lb b ↦ none])) r` (`splicedKernelMK_eq_integral_pin`).
A lower bound at a PINNED atom is a constant `0/1` factor (`splicedKernelMK_pinned_lb`). By induction on the
lower-bounded atoms (`norm_kernelMK_le_of_pinLB`): `‖K(D)‖ ≤ B` as soon as `‖K‖ ≤ B` for every `lb`-free data whose
pins extend `D`'s by pins of the lower-bounded atoms inside their layer windows (`PinsLB`). The window has length
`≤ 1`, so no constant is lost. Used by C4 (`FineSplicedAtMK`, the pinned atoms are exceptional) and D7 (SelRes). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace WaveTurbulence.Flower.FinalMKFine
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.SelRes (pin phaseF norm_phaseF continuous_phaseF restOK slotA mem_dom_update
  mem_dom_pin_update integral_pin_eq integral_extendFix_split' integrable_extendFix_split' integrable_of_closed_box
  extendFix_fixSel_pinned)
open WaveTurbulence.Flower.FlFace (fixSel extendFix_of_none extendFix_of_some measurable_extendFix')

variable {w d : ℕ} {G : Garden w}

/-! ## The lower-bound-aware pinned time transform -/

theorem measurableSet_splicedLBDomain (lb : GBranch G.tree → Option ℝ) :
    MeasurableSet (splicedLBDomain (G := G) lb) := by
  have e : splicedLBDomain (G := G) lb = ⋂ v, {t : GBranch G.tree → ℝ | ∀ x, lb v = some x → x < t v} := by
    ext t; simp [splicedLBDomain]
  rw [e]
  refine MeasurableSet.iInter fun v => ?_
  rcases h : lb v with _ | x0
  · simp
  · have e2 : {t : GBranch G.tree → ℝ | ∀ x, some x0 = some x → x < t v} = (fun t => t v) ⁻¹' Ioi x0 := by
      ext t; simp
    rw [e2]
    exact measurableSet_Ioi.preimage (measurable_pi_apply v)

/-- The pinned time transform over the pinned domain intersected with the lower bounds. -/
def fourierLB (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix lb : GBranch G.tree → Option ℝ) (α : GBranch G.tree → ℝ) : ℂ :=
  ∫ τ : {b : GBranch G.tree // fix b = none} → ℝ,
    (splicedTimeDomainFix G layer rootTime fix ∩ splicedLBDomain lb).indicator (phaseF α) (G.extendFix fix τ)

theorem integrable_domLB (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix lb : GBranch G.tree → Option ℝ)
    (α : GBranch G.tree → ℝ) :
    Integrable fun τ : {x : GBranch G.tree // fix x = none} → ℝ =>
      (splicedTimeDomainFix G layer rootTime fix ∩ splicedLBDomain lb).indicator (phaseF α) (G.extendFix fix τ) :=
  integrable_of_closed_box (G.extendFix fix) (measurable_extendFix' fix) _
    ((WaveTurbulence.FlowerP5.measurableSet_splicedTimeDomainFix G layer rootTime fix).inter
      (measurableSet_splicedLBDomain lb)) _ (continuous_phaseF α).measurable
    (fun t => (norm_phaseF α t).le) (fun i => (layer i.1 : ℝ))
    (fun τ hτ i => by
      have h := (hτ.1.1 i.1 i.2).1
      rw [extendFix_of_none fix τ i.1 i.2] at h
      exact ⟨h.1, h.2⟩)

/-- The lower-bound-aware transform has modulus at most one (unit phases on a subset of the unit box). -/
theorem norm_fourierLB_le_one (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix lb : GBranch G.tree → Option ℝ) (α : GBranch G.tree → ℝ) :
    ‖fourierLB G layer rootTime fix lb α‖ ≤ 1 := by
  unfold fourierLB
  set B : Set ({x : GBranch G.tree // fix x = none} → ℝ) :=
    Set.pi univ fun i => Icc (layer i.1 : ℝ) (layer i.1 + 1) with hB
  have hBm : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hvol : volume B = 1 := by
    rw [hB, volume_pi_pi]
    simp [Real.volume_Icc]
  have hint : Integrable (B.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const (by rw [hvol]; simp))
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => norm_nonneg _) hint
    (Filter.Eventually.of_forall fun τ => ?_)).trans ?_
  · show ‖(splicedTimeDomainFix G layer rootTime fix ∩ splicedLBDomain lb).indicator (phaseF α)
      (G.extendFix fix τ)‖ ≤ _
    by_cases h : G.extendFix fix τ ∈ splicedTimeDomainFix G layer rootTime fix ∩ splicedLBDomain lb
    · have hτ : τ ∈ B := Set.mem_univ_pi.2 fun i => by
        have := (h.1.1 i.1 i.2).1
        rwa [extendFix_of_none fix τ i.1 i.2] at this
      rw [indicator_of_mem h, indicator_of_mem hτ, norm_phaseF]
    · rw [indicator_of_notMem h, norm_zero]; exact indicator_nonneg (fun _ _ => zero_le_one) τ
  · rw [integral_indicator_const _ hBm]; simp [Measure.real, hvol]

/-- The marked time integral is `fourierLB` at the decoration's frequency. -/
theorem splicedTimeIntegralMK_eq_LB (G : Garden w) (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) :
    splicedTimeIntegralMK G D L γ δ base z =
      fourierLB G D.layer D.rootTime D.fix D.lb (splicedFrequency G D.toSplicedKernelData L γ δ base z) := by
  unfold splicedTimeIntegralMK fourierLB
  congr 1
  funext τ
  have h : (fun t : GBranch G.tree → ℝ => phaseProd L γ δ G (cosetDecoration G L base z) t *
      ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I)) =
      phaseF (splicedFrequency G D.toSplicedKernelData L γ δ base z) := by
    funext t
    exact phase_mul_eq G D.toSplicedKernelData L γ δ base z t
  rw [h]

/-- The marked kernel as a finite sum of amplitudes times `fourierLB` (any `lb`). -/
theorem splicedKernelMK_eq_sumLB (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) :
    splicedKernelMK G D L γ η δ base roots =
      (coupling d L γ δ : ℂ) ^ G.order *
        ∑ z ∈ (CoarseSpliced.finite_momAmp_support G hP D.toSplicedKernelData hD hL γ η base roots).toFinset,
          ampMK G D L γ η base z.1 *
            fourierLB G D.layer D.rootTime D.fix D.lb (splicedFrequency G D.toSplicedKernelData L γ δ base z.1) := by
  unfold splicedKernelMK
  congr 1
  have hterm : ∀ z : GenDecoration G d roots 0,
      D.atomW (cosetDecoration G L base z.1) *
        (splicedEpsilon G D.hinges z.1 : ℂ) * (splicedGapIndicator G D.toSplicedKernelData L γ η base z.1 : ℂ) *
        (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) *
        D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z.1 x.1)) *
        splicedTimeIntegralMK G D L γ δ base z.1 =
      ampMK G D L γ η base z.1 *
        fourierLB G D.layer D.rootTime D.fix D.lb (splicedFrequency G D.toSplicedKernelData L γ δ base z.1) := by
    intro z
    rw [splicedTimeIntegralMK_eq_LB]
    unfold ampMK splicedMomentumAmplitude
    ring
  simp_rw [hterm]
  rw [tsum_eq_sum]
  intro z hz
  have h0 : splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 = 0 := by
    by_contra h; exact hz ((Set.Finite.mem_toFinset _).2 h)
  have : ampMK G D L γ η base z.1 = 0 := by unfold ampMK; rw [h0, mul_zero]
  rw [this, zero_mul]

/-! ## A lower bound at a pinned atom: a constant factor -/

theorem fourierLB_pinned (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix lb : GBranch G.tree → Option ℝ)
    (α : GBranch G.tree → ℝ) {b : GBranch G.tree} {r₀ x : ℝ} (hb : fix b = some r₀) (hx : lb b = some x) :
    fourierLB G layer rootTime fix lb α =
      if x < r₀ then fourierLB G layer rootTime fix (Function.update lb b none) α else 0 := by
  unfold fourierLB
  have hval : ∀ τ : {b : GBranch G.tree // fix b = none} → ℝ, G.extendFix fix τ b = r₀ :=
    fun τ => extendFix_of_some fix τ b hb
  split_ifs with hxr
  · refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    dsimp only
    have hmem : G.extendFix fix τ ∈ splicedLBDomain lb ↔
        G.extendFix fix τ ∈ splicedLBDomain (Function.update lb b none) := by
      simp only [splicedLBDomain, Set.mem_ofPred_eq]
      constructor
      · intro h v y hv
        by_cases hvb : v = b
        · subst hvb; simp at hv
        · rw [Function.update_of_ne hvb] at hv; exact h v y hv
      · intro h v y hv
        by_cases hvb : v = b
        · subst hvb; rw [hx] at hv; cases hv; rw [hval τ]; exact hxr
        · exact h v y (by rwa [Function.update_of_ne hvb])
    by_cases hm : G.extendFix fix τ ∈ splicedTimeDomainFix G layer rootTime fix
    · by_cases hl : G.extendFix fix τ ∈ splicedLBDomain lb
      · rw [indicator_of_mem (Set.mem_inter hm hl), indicator_of_mem (Set.mem_inter hm (hmem.1 hl))]
      · rw [indicator_of_notMem (fun h => hl h.2), indicator_of_notMem (fun h => hl (hmem.2 h.2))]
    · rw [indicator_of_notMem (fun h => hm h.1), indicator_of_notMem (fun h => hm h.1)]
  · have h0 : ∀ τ : {b : GBranch G.tree // fix b = none} → ℝ,
        (splicedTimeDomainFix G layer rootTime fix ∩ splicedLBDomain lb).indicator (phaseF α)
          (G.extendFix fix τ) = 0 := by
      intro τ
      refine indicator_of_notMem (fun h => hxr ?_) _
      have := h.2 b x hx
      rwa [hval τ] at this
    simp only [h0, integral_zero]

/-! ## A lower bound at a free atom: Fubini at the atom -/

/-- The window of a lower-bounded free atom `b`: above `x`, inside the layer box of `b`, below its root time, above
its pinned children and below its pinned parent. -/
def lbWin (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (b : GBranch G.tree) (x : ℝ) : Set ℝ :=
  {r | x < r ∧ (layer b : ℝ) ≤ r ∧ r ≤ layer b + 1 ∧ r < rootTime b.1.1 ∧
    (∀ c, c.IsChildOf b → ∀ s, fix c = some s → s < r) ∧ ∀ u, b.IsChildOf u → ∀ s, fix u = some s → r < s}

theorem lbWin_subset (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (b : GBranch G.tree) (x : ℝ) : lbWin layer rootTime fix b x ⊆ Icc (layer b : ℝ) (layer b + 1) :=
  fun _ hr => ⟨hr.2.1, hr.2.2.1⟩

theorem mem_LB_update (lb : GBranch G.tree → Option ℝ) {b : GBranch G.tree} {x : ℝ} (hx : lb b = some x)
    (Y : GBranch G.tree → ℝ) (r : ℝ) :
    Function.update Y b r ∈ splicedLBDomain lb ↔
      x < r ∧ Function.update Y b r ∈ splicedLBDomain (Function.update lb b none) := by
  simp only [splicedLBDomain, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨by simpa using h b x hx, fun v y hv => ?_⟩
    by_cases hvb : v = b
    · subst hvb; simp at hv
    · rw [Function.update_of_ne hvb] at hv; exact h v y hv
  · rintro ⟨h1, h2⟩ v y hv
    by_cases hvb : v = b
    · subst hvb; rw [hx] at hv; cases hv; simpa using h1
    · exact h2 v y (by rwa [Function.update_of_ne hvb])

/-- The slot of `b` splits into the window conditions on pinned neighbours and the free-neighbour order. -/
theorem mem_slotA_iff (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (b : GBranch G.tree) (X : GBranch G.tree → ℝ) (hX : ∀ y s, fix y = some s → X y = s) (r : ℝ) :
    r ∈ slotA layer rootTime b X ↔
      ((layer b : ℝ) ≤ r ∧ r ≤ layer b + 1 ∧ r < rootTime b.1.1 ∧
        (∀ c, c.IsChildOf b → ∀ s, fix c = some s → s < r) ∧ ∀ u, b.IsChildOf u → ∀ s, fix u = some s → r < s) ∧
      (∀ c, c.IsChildOf b → fix c = none → X c < r) ∧ ∀ u, b.IsChildOf u → fix u = none → r < X u := by
  simp only [slotA, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, hc, hp⟩
    refine ⟨⟨h1, h2, h3, fun c hcb s hs => ?_, fun u hbu s hs => ?_⟩, fun c hcb _ => hc c hcb,
      fun u hbu _ => hp u hbu⟩
    · rw [← hX c s hs]; exact hc c hcb
    · rw [← hX u s hs]; exact hp u hbu
  · rintro ⟨⟨h1, h2, h3, hc, hp⟩, hcf, hpf⟩
    refine ⟨h1, h2, h3, fun c hcb => ?_, fun u hbu => ?_⟩
    · rcases hfc : fix c with _ | s
      · exact hcf c hcb hfc
      · rw [hX c s hfc]; exact hc c hcb s hfc
    · rcases hfu : fix u with _ | s
      · exact hpf u hbu hfu
      · rw [hX u s hfu]; exact hp u hbu s hfu

/-- The pointwise identity behind Fubini at a lower-bounded free atom. -/
theorem mem_domLB_update_iff (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix lb : GBranch G.tree → Option ℝ)
    {b : GBranch G.tree} (hb : fix b = none) {x : ℝ} (hx : lb b = some x) (X : GBranch G.tree → ℝ)
    (hX : ∀ y s, fix y = some s → X y = s) (r : ℝ) :
    Function.update X b r ∈ splicedTimeDomainFix G layer rootTime fix ∩ splicedLBDomain lb ↔
      r ∈ lbWin layer rootTime fix b x ∧
        Function.update X b r ∈
          splicedTimeDomainFix G layer rootTime (pin fix b r) ∩ splicedLBDomain (Function.update lb b none) := by
  rw [Set.mem_inter_iff, Set.mem_inter_iff, mem_dom_update layer rootTime fix b hb X r,
    mem_dom_pin_update layer rootTime fix b X r, mem_slotA_iff layer rootTime fix b X hX r, mem_LB_update lb hx]
  simp only [lbWin, Set.mem_ofPred_eq]
  tauto

theorem fourierLB_free (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix lb : GBranch G.tree → Option ℝ)
    (α : GBranch G.tree → ℝ) {b : GBranch G.tree} (hb : fix b = none) {x : ℝ} (hx : lb b = some x) :
    fourierLB G layer rootTime fix lb α =
      ∫ r, (lbWin layer rootTime fix b x).indicator
        (fun r => fourierLB G layer rootTime (pin fix b r) (Function.update lb b none) α) r ∧
    Integrable fun r => (lbWin layer rootTime fix b x).indicator
        (fun r => fourierLB G layer rootTime (pin fix b r) (Function.update lb b none) α) r := by
  set F : (GBranch G.tree → ℝ) → ℂ :=
    (splicedTimeDomainFix G layer rootTime fix ∩ splicedLBDomain lb).indicator (phaseF α) with hF
  have hint := integrable_domLB (G := G) layer rootTime fix lb α
  have hpin : ∀ ρ : {y : GBranch G.tree // fixSel fix {b} y = none} → ℝ, ∀ y s, fix y = some s →
      G.extendFix (fixSel fix {b}) ρ y = s :=
    extendFix_fixSel_pinned fix {b} (by simpa using hb)
  have hpt : ∀ r : ℝ, (∫ ρ : {y : GBranch G.tree // fixSel fix {b} y = none} → ℝ,
      F (Function.update (G.extendFix (fixSel fix {b}) ρ) b r)) =
      (lbWin layer rootTime fix b x).indicator
        (fun r => fourierLB G layer rootTime (pin fix b r) (Function.update lb b none) α) r := by
    intro r
    by_cases hr : r ∈ lbWin layer rootTime fix b x
    · rw [indicator_of_mem hr]
      unfold fourierLB
      rw [integral_pin_eq fix b r]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
      have hiff := mem_domLB_update_iff layer rootTime fix lb hb hx _ (hpin ρ) r
      simp only [hF]
      by_cases hm : Function.update (G.extendFix (fixSel fix {b}) ρ) b r ∈
          splicedTimeDomainFix G layer rootTime fix ∩ splicedLBDomain lb
      · rw [indicator_of_mem hm, indicator_of_mem (hiff.1 hm).2]
      · rw [indicator_of_notMem hm, indicator_of_notMem (fun h => hm (hiff.2 ⟨hr, h⟩))]
    · rw [indicator_of_notMem hr]
      have h0 : ∀ ρ : {y : GBranch G.tree // fixSel fix {b} y = none} → ℝ,
          F (Function.update (G.extendFix (fixSel fix {b}) ρ) b r) = 0 := fun ρ =>
        indicator_of_notMem (fun h => hr ((mem_domLB_update_iff layer rootTime fix lb hb hx _ (hpin ρ) r).1 h).1) _
      simp only [h0, integral_zero]
  refine ⟨?_, ?_⟩
  · unfold fourierLB
    rw [integral_extendFix_split' fix b hb F hint]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  · exact (integrable_extendFix_split' fix b hb F hint).congr (Filter.Eventually.of_forall hpt)

/-! ## The kernel -/

/-- `b` pinned at `r`, its lower bound dropped. -/
def pinLBData (D : SplicedKernelDataMK G d) (b : GBranch G.tree) (r : ℝ) : SplicedKernelDataMK G d :=
  { D with fix := pin D.fix b r, lb := Function.update D.lb b none }

/-- The lower bound of `b` dropped. -/
def dropLBData (D : SplicedKernelDataMK G d) (b : GBranch G.tree) : SplicedKernelDataMK G d :=
  { D with lb := Function.update D.lb b none }

/-- New pins, no lower bounds. -/
def pinData (D : SplicedKernelDataMK G d) (fix' : GBranch G.tree → Option ℝ) : SplicedKernelDataMK G d :=
  { D with fix := fix', lb := fun _ => none }

theorem splicedKernelMK_pinned_lb (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) {b : GBranch G.tree} {r₀ x : ℝ} (hb : D.fix b = some r₀) (hx : D.lb b = some x) :
    splicedKernelMK G D L γ η δ base roots =
      if x < r₀ then splicedKernelMK G (dropLBData D b) L γ η δ base roots else 0 := by
  rw [splicedKernelMK_eq_sumLB hP D hD hL, splicedKernelMK_eq_sumLB hP (dropLBData D b) hD hL]
  split_ifs with hxr
  · congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [fourierLB_pinned _ _ _ _ _ hb hx, ite_eq_left_of_eq_true _ _ (eq_true hxr)]
    rfl
  · rw [Finset.sum_eq_zero fun z _ => by rw [fourierLB_pinned _ _ _ _ _ hb hx, ite_eq_right_of_eq_false _ _ (eq_false hxr), mul_zero],
    mul_zero]

theorem splicedKernelMK_eq_integral_pin (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) {b : GBranch G.tree} {x : ℝ} (hb : D.fix b = none) (hx : D.lb b = some x) :
    splicedKernelMK G D L γ η δ base roots =
      ∫ r, (lbWin D.layer D.rootTime D.fix b x).indicator
        (fun r => splicedKernelMK G (pinLBData D b r) L γ η δ base roots) r ∧
    Integrable fun r => (lbWin D.layer D.rootTime D.fix b x).indicator
        (fun r => splicedKernelMK G (pinLBData D b r) L γ η δ base roots) r := by
  set W := lbWin D.layer D.rootTime D.fix b x with hW
  set Zs := (CoarseSpliced.finite_momAmp_support G hP D.toSplicedKernelData hD hL γ η base roots).toFinset
  set c : ℂ := (coupling d L γ δ : ℂ) ^ G.order
  set α : GenDecoration G d roots 0 → GBranch G.tree → ℝ :=
    fun z => splicedFrequency G D.toSplicedKernelData L γ δ base z.1
  set f : GenDecoration G d roots 0 → ℝ → ℂ := fun z => W.indicator
    (fun r => fourierLB G D.layer D.rootTime (pin D.fix b r) (Function.update D.lb b none) (α z))
  have hfree := fun z => fourierLB_free D.layer D.rootTime D.fix D.lb (α z) hb hx
  have hpt : ∀ r, W.indicator (fun r => splicedKernelMK G (pinLBData D b r) L γ η δ base roots) r =
      c * ∑ z ∈ Zs, ampMK G D L γ η base z.1 * f z r := by
    intro r
    by_cases hr : r ∈ W
    · rw [indicator_of_mem hr, splicedKernelMK_eq_sumLB hP (pinLBData D b r) hD hL]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [f, indicator_of_mem hr]
      rfl
    · rw [indicator_of_notMem hr]
      simp only [f, indicator_of_notMem hr, mul_zero, Finset.sum_const_zero]
  have hint : ∀ z ∈ Zs, Integrable fun r => ampMK G D L γ η base z.1 * f z r :=
    fun z _ => (hfree z).2.const_mul _
  refine ⟨?_, ?_⟩
  · rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, integral_finsetSum _ hint,
      splicedKernelMK_eq_sumLB hP D hD hL]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_const_mul, (hfree z).1]
  · exact ((integrable_finsetSum _ hint).const_mul c).congr
      (Filter.Eventually.of_forall fun r => (hpt r).symm)

/-! ## The reduction -/

/-- Pins extending `D`'s by pins of lower-bounded atoms inside their layer windows. -/
def PinsLB (D : SplicedKernelDataMK G d) (fix' : GBranch G.tree → Option ℝ) : Prop :=
  (∀ b, D.lb b = none → fix' b = D.fix b) ∧
  ∀ b, (D.lb b).isSome → fix' b = D.fix b ∨ ∃ r, fix' b = some r ∧ (D.layer b : ℝ) ≤ r ∧ r ≤ D.layer b + 1

theorem PinsLB.self (D : SplicedKernelDataMK G d) : PinsLB D D.fix :=
  ⟨fun _ _ => rfl, fun _ _ => Or.inl rfl⟩

/-- The lower-bounded atoms. -/
def lbSet (D : SplicedKernelDataMK G d) : Finset (GBranch G.tree) := univ.filter fun b => (D.lb b).isSome

theorem mem_lbSet {D : SplicedKernelDataMK G d} {v : GBranch G.tree} : v ∈ lbSet D ↔ (D.lb v).isSome := by
  simp [lbSet]

theorem pinData_of_lbSet_empty (D : SplicedKernelDataMK G d) (h : lbSet D = ∅) : pinData D D.fix = D := by
  have hlb : D.lb = fun _ => none := by
    funext b
    by_contra hb
    have : b ∈ lbSet D := mem_lbSet.2 (Option.isSome_iff_ne_none.2 hb)
    rw [h] at this; simp at this
  cases D
  simp only [pinData] at hlb ⊢
  rw [hlb]

theorem lbSet_dropLB (D : SplicedKernelDataMK G d) {b : GBranch G.tree} (hb : b ∈ lbSet D) :
    lbSet (dropLBData D b) = (lbSet D).erase b := by
  ext v
  rw [mem_lbSet, Finset.mem_erase, mem_lbSet]
  by_cases hvb : v = b
  · subst hvb; simp [dropLBData]
  · simp [dropLBData, hvb]

theorem lbSet_pinLB (D : SplicedKernelDataMK G d) {b : GBranch G.tree} (hb : b ∈ lbSet D) (r : ℝ) :
    lbSet (pinLBData D b r) = (lbSet D).erase b := by
  ext v
  rw [mem_lbSet, Finset.mem_erase, mem_lbSet]
  by_cases hvb : v = b
  · subst hvb; simp [pinLBData]
  · simp [pinLBData, hvb]

/-- **Lower bounds reduce to pins.** If every `lb`-free data whose pins extend `D`'s by pins of the lower-bounded
atoms inside their layer windows has kernel norm `≤ B`, then so does `D`. -/
theorem norm_kernelMK_le_of_pinLB (hP : G.IsPlain) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (B : ℝ) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (hB : ∀ fix', PinsLB D fix' → ‖splicedKernelMK G (pinData D fix') L γ η δ base roots‖ ≤ B) :
    ‖splicedKernelMK G D L γ η δ base roots‖ ≤ B := by
  suffices key : ∀ n : ℕ, ∀ D : SplicedKernelDataMK G d, (lbSet D).card ≤ n →
      SplicedAmplitudeBounds G D.toSplicedKernelData →
      (∀ fix', PinsLB D fix' → ‖splicedKernelMK G (pinData D fix') L γ η δ base roots‖ ≤ B) →
      ‖splicedKernelMK G D L γ η δ base roots‖ ≤ B from key _ D le_rfl hD hB
  intro n
  induction n with
  | zero =>
    intro D hn _ hB
    have h0 : lbSet D = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hn)
    have := hB D.fix (PinsLB.self D)
    rwa [pinData_of_lbSet_empty D h0] at this
  | succ n ih =>
    intro D hn hD hB
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB D.fix (PinsLB.self D))
    rcases (lbSet D).eq_empty_or_nonempty with h0 | ⟨b, hbS⟩
    · have := hB D.fix (PinsLB.self D)
      rwa [pinData_of_lbSet_empty D h0] at this
    have hbS' := mem_lbSet.1 hbS
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hbS'
    have hcard : ((lbSet D).erase b).card ≤ n := by
      rw [Finset.card_erase_of_mem hbS]; omega
    rcases hfb : D.fix b with _ | r₀
    · -- a free lower-bounded atom: Fubini at `b`
      obtain ⟨heq, hint⟩ := splicedKernelMK_eq_integral_pin hP D hD hL γ η δ base roots hfb hx
      set W := lbWin D.layer D.rootTime D.fix b x with hW
      have hbnd : ∀ r ∈ W, ‖splicedKernelMK G (pinLBData D b r) L γ η δ base roots‖ ≤ B := by
        intro r hr
        refine ih (pinLBData D b r) (by rw [lbSet_pinLB D hbS r]; exact hcard) hD fun fix' hP' => ?_
        have e : pinData (pinLBData D b r) fix' = pinData D fix' := rfl
        rw [e]
        refine hB fix' ⟨fun v hv => ?_, fun v hv => ?_⟩
        · have hvb : v ≠ b := fun h => by rw [h, hx] at hv; exact absurd hv (by simp)
          have := hP'.1 v (by simp [pinLBData, Function.update_of_ne hvb, hv])
          rw [this]; simp [pinLBData, pin, Function.update_of_ne hvb]
        · by_cases hvb : v = b
          · subst hvb
            have := hP'.1 v (by simp [pinLBData])
            refine Or.inr ⟨r, by rw [this]; simp [pinLBData, pin], hr.2.1, hr.2.2.1⟩
          · have h2 := hP'.2 v (by simpa [pinLBData, Function.update_of_ne hvb] using hv)
            simp only [pinLBData, pin, Function.update_of_ne hvb] at h2
            exact h2
      rw [heq]
      have hle : ∀ r, ‖W.indicator (fun r => splicedKernelMK G (pinLBData D b r) L γ η δ base roots) r‖ ≤
          (Icc (D.layer b : ℝ) (D.layer b + 1)).indicator (fun _ => B) r := by
        intro r
        by_cases hr : r ∈ W
        · rw [indicator_of_mem hr, indicator_of_mem (lbWin_subset _ _ _ _ _ hr)]
          exact hbnd r hr
        · rw [indicator_of_notMem hr, norm_zero]
          exact indicator_nonneg (fun _ _ => hB0) r
      have hIcc : Integrable ((Icc (D.layer b : ℝ) (D.layer b + 1)).indicator (fun _ : ℝ => B)) :=
        (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
      refine (norm_integral_le_of_norm_le hIcc (Filter.Eventually.of_forall hle)).trans ?_
      rw [integral_indicator_const _ measurableSet_Icc]
      simp
    · -- a pinned lower-bounded atom: a constant factor
      rw [splicedKernelMK_pinned_lb hP D hD hL γ η δ base roots hfb hx]
      split_ifs with hxr
      · refine ih (dropLBData D b) (by rw [lbSet_dropLB D hbS]; exact hcard) hD fun fix' hP' => ?_
        have e : pinData (dropLBData D b) fix' = pinData D fix' := rfl
        rw [e]
        refine hB fix' ⟨fun v hv => ?_, fun v hv => ?_⟩
        · have hvb : v ≠ b := fun h => by rw [h, hx] at hv; exact absurd hv (by simp)
          exact hP'.1 v (by simp [dropLBData, Function.update_of_ne hvb, hv])
        · by_cases hvb : v = b
          · subst hvb; exact Or.inl (hP'.1 v (by simp [dropLBData]))
          · exact hP'.2 v (by simpa [dropLBData, Function.update_of_ne hvb] using hv)
      · rw [norm_zero]; exact hB0

end WaveTurbulence.Flower.FinalMKFine
