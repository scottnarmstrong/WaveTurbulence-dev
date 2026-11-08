/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RDom
public import WaveTurbulence.Foundations.Vine.B.TimeDomain
public import WaveTurbulence.Foundations.FlowerTop.Port.FixLemmas

/-! # B3s-HELPER3 B2 (1): the relaxed open spliced domain and the shift lemmas of the VINE-B♯ split

* `openSbR G layer tt fix`: main's `VineB.openSb` RELAXED (windows and root bound at free atoms only, the parent order
  for pairs with a free member); `openSbR_none`, `measurableSet_openSbR`;
* `boxSbR`, `fixMeasure_boxSbR_le`, `openSbR_subset_boxSbR`, `splicedTimeDomainFix_subset_boxSbR`;
* `indicator_splicedTimeDomainFix_ae_openSbR`: main's closed relaxed domain `splicedTimeDomainFix` and `openSbR` agree
  `fixMeasure fix`-a.e. (free coordinates avoid the window endpoints a.e.; pinned coordinates are unconstrained in
  both, so no condition on the pins is needed);
* `eventually_openSb_shift_iff`: `openSb` at the shifted `τ - ε • α` is eventually `openSbR` at `τ`;
* `clLocalClock_shift`, `parentClock_clLocal_shift`, **`eventually_clLocalTimeDomain_shift_iff`**: V5's local unit domain
  at shifted exterior clocks is eventually the local domain at the unshifted clocks (every constraint has a free
  interior member; the lower boundary constraints need the interior lower joint to differ from a pinned clock). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology Set MeasureTheory
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine
  WaveTurbulence.VineB TTree

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-! ## The relaxed open spliced domain -/

/-- **The relaxed open spliced domain**: open layer windows and the root bound at free atoms, the parent order for every
parent–child pair with a free member. -/
def openSbR (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ) :
    Set (GBranch G.tree → ℝ) :=
  {τ | (∀ c, fix c = none → (layer c : ℝ) < τ c ∧ τ c < layer c + 1) ∧
    (∀ v u, v.IsChildOf u → (fix v = none ∨ fix u = none) → τ v < τ u) ∧ ∀ v, fix v = none → τ v < tt v.1.1}

theorem openSbR_none (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ) :
    openSbR G layer tt (fun _ => none) = openSb G layer tt := by
  ext τ
  simp only [openSbR, openSb, Set.mem_ofPred_eq, true_or, forall_const]

theorem measurableSet_openSbR (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) : MeasurableSet (openSbR G layer tt fix) := by
  have he : openSbR G layer tt fix =
      (⋂ c, ({τ : GBranch G.tree → ℝ | fix c = none → (layer c : ℝ) < τ c} ∩
        {τ | fix c = none → τ c < (layer c : ℝ) + 1})) ∩
      ((⋂ v, ⋂ u, {τ : GBranch G.tree → ℝ | (v.IsChildOf u ∧ (fix v = none ∨ fix u = none)) → τ v < τ u}) ∩
        ⋂ v, {τ : GBranch G.tree → ℝ | fix v = none → τ v < tt v.1.1}) := by
    ext τ
    simp only [openSbR, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, and_imp]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun c => ⟨fun h => (h1 c h).1, fun h => (h1 c h).2⟩, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun c h => ⟨(h1 c).1 h, (h1 c).2 h⟩, h2, h3⟩
  rw [he]
  refine (MeasurableSet.iInter fun c => (measurableSet_imp_lt _ measurable_const (measurable_pi_apply c)).inter
    (measurableSet_imp_lt _ (measurable_pi_apply c) measurable_const)).inter
    ((MeasurableSet.iInter fun v => MeasurableSet.iInter fun u =>
      measurableSet_imp_lt _ (measurable_pi_apply v) (measurable_pi_apply u)).inter
    (MeasurableSet.iInter fun v => measurableSet_imp_lt _ (measurable_pi_apply v) measurable_const))

/-! ## Lower bounds (ruling R187) -/

/-- The lower-bound domain: `x < t v` whenever `lb v = some x` (a copy of the body of `splicedLBDomain`). -/
def lbDomR {tree : Fin w → TTree} (lb : GBranch tree → Option ℝ) : Set (GBranch tree → ℝ) :=
  {t | ∀ v x, lb v = some x → x < t v}

theorem lbDomR_none {tree : Fin w → TTree} : lbDomR (fun _ : GBranch tree => (none : Option ℝ)) = Set.univ := by
  ext t
  simp [lbDomR]

theorem measurableSet_lbDomR {tree : Fin w → TTree} (lb : GBranch tree → Option ℝ) :
    MeasurableSet (lbDomR lb) := by
  have he : lbDomR lb = ⋂ v, {t : GBranch tree → ℝ | ∀ x, lb v = some x → x < t v} := by
    ext t
    simp [lbDomR]
  rw [he]
  refine MeasurableSet.iInter fun v => ?_
  rcases lb v with _ | x0
  · have : {t : GBranch tree → ℝ | ∀ x, (none : Option ℝ) = some x → x < t v} = Set.univ := by
      ext t
      simp
    rw [this]
    exact MeasurableSet.univ
  · have : {t : GBranch tree → ℝ | ∀ x, some x0 = some x → x < t v} = {t | x0 < t v} := by
      ext t
      simp
    rw [this]
    exact measurableSet_lt measurable_const (measurable_pi_apply v)

/-! ## The relaxed box -/

/-- The relaxed box: free coordinates in their closed layer windows, pinned coordinates unconstrained. -/
def boxSbR {G : Garden w} (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ) :
    Set (GBranch G.tree → ℝ) :=
  Set.pi Set.univ fun c => (fix c).elim (Set.Icc (layer c : ℝ) (layer c + 1)) fun _ => Set.univ

theorem measurableSet_boxSbR {G : Garden w} (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ) :
    MeasurableSet (boxSbR layer fix) := by
  refine MeasurableSet.univ_pi fun c => ?_
  rcases fix c with _ | v
  · exact measurableSet_Icc
  · exact MeasurableSet.univ

theorem fixMeasure_boxSbR_le {G : Garden w} (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ) :
    MkSlots.fixMeasure fix (boxSbR layer fix) ≤ 1 := by
  rw [boxSbR, MkSlots.fixMeasure, Measure.pi_pi]
  refine Finset.prod_le_one fun v _ => ?_
  rcases fix v with _ | x
  · simp [MkSlots.fixFactor, Real.volume_Icc]
  · simp [MkSlots.fixFactor]

theorem mem_boxSbR_of {G : Garden w} {layer : GBranch G.tree → ℕ} {fix : GBranch G.tree → Option ℝ}
    {τ : GBranch G.tree → ℝ} (h : ∀ c, fix c = none → τ c ∈ Set.Icc (layer c : ℝ) (layer c + 1)) :
    τ ∈ boxSbR layer fix := by
  intro c _
  show τ c ∈ (fix c).elim (Set.Icc (layer c : ℝ) (layer c + 1)) fun _ => Set.univ
  rcases hc : fix c with _ | v
  · exact h c hc
  · exact Set.mem_univ _

theorem openSbR_subset_boxSbR (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) : openSbR G layer tt fix ⊆ boxSbR layer fix := fun _ h =>
  mem_boxSbR_of fun c hc => ⟨(h.1 c hc).1.le, (h.1 c hc).2.le⟩

theorem splicedTimeDomainFix_subset_boxSbR (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) : splicedTimeDomainFix G layer tt fix ⊆ boxSbR layer fix := fun _ h =>
  mem_boxSbR_of fun c hc => (h.1 c hc).1

theorem fixMeasure_openSbR_le (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) : MkSlots.fixMeasure fix (openSbR G layer tt fix) ≤ 1 :=
  (measure_mono (openSbR_subset_boxSbR G layer tt fix)).trans (fixMeasure_boxSbR_le layer fix)

/-! ## Closed and open relaxed domains agree a.e. -/

/-- **`splicedTimeDomainFix` and `openSbR` agree `fixMeasure fix`-a.e.**, for every pins. -/
theorem ae_mem_splicedTimeDomainFix_iff_openSbR (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) :
    ∀ᵐ τ ∂(MkSlots.fixMeasure fix), τ ∈ splicedTimeDomainFix G layer tt fix ↔ τ ∈ openSbR G layer tt fix := by
  have hae : ∀ᵐ τ ∂(MkSlots.fixMeasure fix), ∀ c, fix c = none → τ c ≠ (layer c : ℝ) ∧ τ c ≠ (layer c : ℝ) + 1 := by
    rw [ae_all_iff]
    intro c
    by_cases hc : fix c = none
    · filter_upwards [ae_ne_of_free fix hc (layer c : ℝ), ae_ne_of_free fix hc ((layer c : ℝ) + 1)] with τ h1 h2 _
      exact ⟨h1, h2⟩
    · exact ae_of_all _ fun τ h => absurd h hc
  filter_upwards [hae] with τ hτ
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun c hc => ⟨lt_of_le_of_ne (h1 c hc).1.1 (hτ c hc).1.symm,
      lt_of_le_of_ne (h1 c hc).1.2 (hτ c hc).2⟩, h2, fun v hv => (h1 v hv).2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun c hc => ⟨⟨(h1 c hc).1.le, (h1 c hc).2.le⟩, h3 c hc⟩, h2⟩

/-- The same with the lower bounds. -/
theorem ae_mem_splicedTimeDomainFix_lb_iff (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix lb : GBranch G.tree → Option ℝ) :
    ∀ᵐ τ ∂(MkSlots.fixMeasure fix), τ ∈ splicedTimeDomainFix G layer tt fix ∩ lbDomR lb ↔
      τ ∈ openSbR G layer tt fix ∩ lbDomR lb := by
  filter_upwards [ae_mem_splicedTimeDomainFix_iff_openSbR G layer tt fix] with τ h
  exact and_congr h Iff.rfl

theorem indicator_ae_eq_of_ae_iff {α E : Type*} [MeasurableSpace α] [Zero E] {μ : Measure α} {s t : Set α}
    (h : ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t) (f : α → E) : s.indicator f =ᵐ[μ] t.indicator f := by
  filter_upwards [h] with x hx
  by_cases hs : x ∈ s
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hx.1 hs)]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (fun h' => hs (hx.2 h'))]

/-! ## The shift lemma for `openSb` -/

section Atoms

variable {P : Prop}

theorem window2_iff (L t a : ℝ) (hfree : P → a = 0) (hpin : ¬ P → 0 < a ∧ L < t ∧ t ≤ L + 1) :
    ((L < t ∨ (L = t ∧ a < 0)) ∧ (t < L + 1 ∨ (t = L + 1 ∧ 0 < a))) ↔ (P → L < t ∧ t < L + 1) := by
  by_cases hP : P
  · have h0 := hfree hP
    subst h0
    simp only [lt_self_iff_false, and_false, or_false, hP, true_implies]
  · obtain ⟨hapos, h1, h2⟩ := hpin hP
    simp only [hP, false_implies, iff_true]
    refine ⟨Or.inl h1, ?_⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hapos⟩

theorem top_iff (t c a : ℝ) (hfree : P → a = 0) (hpin : ¬ P → 0 < a ∧ t ≤ c) :
    (t < c ∨ (t = c ∧ 0 < a)) ↔ (P → t < c) := by
  by_cases hP : P
  · have h0 := hfree hP
    subst h0
    simp only [lt_self_iff_false, and_false, or_false, hP, true_implies]
  · obtain ⟨hapos, h1⟩ := hpin hP
    simp only [hP, false_implies, iff_true]
    rcases lt_or_eq_of_le h1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hapos⟩

end Atoms

/-- **The shift lemma for the open spliced domain.** For a `τ` whose pinned coordinates lie in their (half-open) windows
and below the root times, satisfy the pinned–pinned order in the shifted sense, and differ from every free coordinate,
`openSb` contains `τ - ε • α` for all small `ε > 0` iff `τ ∈ openSbR`. -/
theorem eventually_openSb_shift_iff (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (α τ : GBranch G.tree → ℝ)
    (hα0 : ∀ c, fix c = none → α c = 0) (hα : ∀ c, 0 ≤ α c) (hαpos : ∀ c, fix c ≠ none → 0 < α c)
    (hgen : ∀ x y, fix x = none → fix y ≠ none → τ x ≠ τ y)
    (hwin : ∀ c, fix c ≠ none → (layer c : ℝ) < τ c ∧ τ c ≤ layer c + 1)
    (htop : ∀ c, fix c ≠ none → τ c ≤ tt c.1.1)
    (hedge : ∀ v u, v.IsChildOf u → fix v ≠ none → fix u ≠ none → τ v < τ u ∨ (τ v = τ u ∧ α u < α v)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), (fun c => τ c - ε * α c) ∈ openSb G layer tt) ↔ τ ∈ openSbR G layer tt fix := by
  simp only [openSb, openSbR, Set.mem_ofPred_eq]
  rw [Filter.eventually_and, Filter.eventually_and, Filter.eventually_all, Filter.eventually_all,
    Filter.eventually_all]
  refine and_congr (forall_congr' fun c => ?_) (and_congr (forall_congr' fun v => ?_) (forall_congr' fun v => ?_))
  · rw [Filter.eventually_and, evLt_const_left, evLt_const_right]
    exact window2_iff (P := fix c = none) _ _ _ (hα0 c) (fun h => ⟨hαpos c h, (hwin c h).1, (hwin c h).2⟩)
  · rw [Filter.eventually_all]
    refine forall_congr' fun u => ?_
    rw [Filter.eventually_imp_distrib_left]
    refine forall_congr' fun hvu => ?_
    rw [evLt_iff]
    exact clock_iff (P := fix v = none) (Q := fix u = none) (τ v) (τ u) (α v) (α u) (hα v) (hα u) (hα0 v)
      (hαpos v) (hα0 u) (fun hv hu => (hgen u v hu hv).symm) (fun hv hu => hedge v u hvu hv hu)
  · rw [evLt_const_right]
    exact top_iff (P := fix v = none) _ _ _ (hα0 v) (fun h => ⟨hαpos v h, htop v h⟩)

/-! ## The shift lemma for V5's local unit domain -/

section Local

variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clLocalClock_shift (R : CLRegionData G U a b) (t tα : Fin 3 → ℝ) (τ : CLInternalTime R) (ε : ℝ)
    (v : GBranch G.tree) :
    clLocalClock R (fun i => t i - ε * tα i) τ v = clLocalClock R t τ v - ε * clLocalClock R tα 0 v := by
  unfold clLocalClock
  split_ifs <;> simp

theorem clLocalClock_nonneg (R : CLRegionData G U a b) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (ht : ∀ i, 0 ≤ t i) (hτ : ∀ v, 0 ≤ τ v) (v : GBranch G.tree) : 0 ≤ clLocalClock R t τ v := by
  unfold clLocalClock
  split_ifs
  · exact ht 0
  · exact hτ _
  · exact ht 1
  · exact ht 2
  · exact le_refl 0

theorem clLocalClock_interior_zero (R : CLRegionData G U a b) (t : Fin 3 → ℝ) (hb : b ≠ a) (hbU : b ∈ U) :
    clLocalClock R t 0 b = 0 :=
  clLocalClock_internal R t 0 ⟨b, Finset.mem_erase.mpr ⟨hb, hbU⟩⟩

theorem parentClock_clLocal_shift (R : CLRegionData G U a b) (t tα : Fin 3 → ℝ) (τ : CLInternalTime R) (ε : ℝ)
    (x : GNode G.tree) :
    parentClock (t 0 - ε * tα 0) (clLocalClock R (fun i => t i - ε * tα i) τ) x =
      parentClock (t 0) (clLocalClock R t τ) x - ε * parentClock (tα 0) (clLocalClock R tα 0) x := by
  unfold parentClock
  cases nodeToSlot x with
  | inl j => rfl
  | inr y => exact clLocalClock_shift R t tα τ ε y.1

theorem parentClock_nonneg' {tree : Fin w → TTree} (top : ℝ) (f : GBranch tree → ℝ) (x : GNode tree)
    (htop : 0 ≤ top) (hf : ∀ v, 0 ≤ f v) : 0 ≤ parentClock top f x := by
  unfold parentClock
  cases nodeToSlot x with
  | inl j => exact htop
  | inr y => exact hf y.1

theorem mem_clLocalTimeDomain_shift_iff (R : CLRegionData G U a b) (layer : GBranch G.tree → ℕ)
    (t tα : Fin 3 → ℝ) (τ : CLInternalTime R) (hb0 : clLocalClock R tα 0 b = 0) (ε : ℝ) :
    τ ∈ clLocalTimeDomain R layer (fun i => t i - ε * tα i) ↔
      (∀ v : ↥(clInteriorBranches R), (layer v.1 : ℝ) < τ v ∧ τ v < layer v.1 + 1 ∧ 0 < τ v ∧
        τ v < parentClock (t 0) (clLocalClock R t τ) v.1.toNode -
          ε * parentClock (tα 0) (clLocalClock R tα 0) v.1.toNode) ∧
      ((b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching →
        t 1 - ε * tα 1 < clLocalClock R t τ b) ∧
      ((b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching →
        t 2 - ε * tα 2 < clLocalClock R t τ b) := by
  have e1 := parentClock_clLocal_shift R t tα τ ε
  have e2 : clLocalClock R (fun i => t i - ε * tα i) τ b = clLocalClock R t τ b := by
    rw [clLocalClock_shift, hb0, mul_zero, sub_zero]
  simp only [clLocalTimeDomain, Set.mem_ofPred_eq, e1, e2]

/-- **The shift lemma for V5's local unit domain.** Shifting the exterior clocks down by `ε • tα` (`tα ≥ 0`) does not
change the local domain for small `ε > 0`, provided the lower joint is interior (`hb0`) and differs from a shifted
lower boundary clock (`hg1`, `hg2`). -/
theorem eventually_clLocalTimeDomain_shift_iff (R : CLRegionData G U a b) (layer : GBranch G.tree → ℕ)
    (t tα : Fin 3 → ℝ) (τ : CLInternalTime R) (hα : ∀ i, 0 ≤ tα i) (hb0 : clLocalClock R tα 0 b = 0)
    (hg1 : 0 < tα 1 → t 1 ≠ clLocalClock R t τ b) (hg2 : 0 < tα 2 → t 2 ≠ clLocalClock R t τ b) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), τ ∈ clLocalTimeDomain R layer (fun i => t i - ε * tα i)) ↔
      τ ∈ clLocalTimeDomain R layer t := by
  rw [Filter.eventually_congr (Filter.Eventually.of_forall (mem_clLocalTimeDomain_shift_iff R layer t tα τ hb0))]
  have hY : ∀ x, 0 ≤ parentClock (tα 0) (clLocalClock R tα 0) x := fun x =>
    parentClock_nonneg' _ _ x (hα 0) (clLocalClock_nonneg R tα 0 hα (fun _ => le_refl 0))
  simp only [Filter.eventually_and, Filter.eventually_all, Filter.eventually_const, evLt_const_left, evLt_const_right, clLocalTimeDomain, Set.mem_ofPred_eq]
  refine and_congr (forall_congr' fun v => ?_) (and_congr (imp_congr_right fun _ => ?_)
    (imp_congr_right fun _ => ?_))
  · have := not_lt.mpr (hY v.1.toNode)
    simp only [this, and_false, or_false]
  · constructor
    · rintro (h | ⟨h, hpos⟩)
      · exact h
      · exact absurd h (hg1 hpos)
    · exact Or.inl
  · constructor
    · rintro (h | ⟨h, hpos⟩)
      · exact h
      · exact absurd h (hg2 hpos)
    · exact Or.inl

end Local

end WaveTurbulence.Flower.MkSlotsB
