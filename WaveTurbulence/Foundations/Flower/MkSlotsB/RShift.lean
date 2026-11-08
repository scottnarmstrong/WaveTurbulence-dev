/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RDefs

/-! # B3s-HELPER3: the shift method

A relaxed domain at a time vector `τ` is the unpinned domain at the shifted vector `τ - ε • α` for every small `ε > 0`,
where `α` vanishes at free coordinates and is positive (and larger for deeper branches) at pinned ones. The basic fact:
`x - ε a < y - ε b` holds for all small `ε > 0` iff `x < y`, or `x = y` and `b < a` (`evLt_iff`). So an unpinned
constraint between two pinned coordinates with equal values survives the shift when the lower one is shifted more,
and a constraint between a free and a pinned coordinate is the strict one as soon as the two values differ.

* `evLt_iff`, `evLt_const_left`, `evLt_const_right`;
* **`eventually_kDomain_shift_iff`**: shifted `kDomain` (shifted clocks) ↔ `kDomainR`;
* `parentClockWith_shift`, **`eventually_coreTimeDomainW_shift_iff`**: shifted `coreTimeDomainW` ↔ `coreTimeDomainWR`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology Set
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree

namespace WaveTurbulence.Flower.MkSlotsB

/-! ## Eventual comparison of shifted reals -/

theorem eventually_pos_nhdsGT : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin

/-- **Eventual comparison of shifted reals.** -/
theorem evLt_iff (x y a b : ℝ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), x - ε * a < y - ε * b) ↔ (x < y ∨ (x = y ∧ b < a)) := by
  constructor
  · intro h
    by_contra hn
    simp only [not_or, not_and, not_lt] at hn
    obtain ⟨h1, h2⟩ := hn
    rcases lt_or_eq_of_le h1 with hlt | heq
    · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), y - ε * b < x - ε * a :=
        ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hlt)
      obtain ⟨ε, h3, h4⟩ := (h.and (hc.filter_mono nhdsWithin_le_nhds)).exists
      linarith
    · have hab := h2 heq.symm
      obtain ⟨ε, h3, h4⟩ := (h.and eventually_pos_nhdsGT).exists
      have : ε * a ≤ ε * b := mul_le_mul_of_nonneg_left hab h4.le
      rw [heq] at h3
      linarith
  · rintro (h | ⟨rfl, h⟩)
    · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), x - ε * a < y - ε * b :=
        ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using h)
      exact hc.filter_mono nhdsWithin_le_nhds
    · filter_upwards [eventually_pos_nhdsGT] with ε hε
      have : ε * b < ε * a := mul_lt_mul_of_pos_left h hε
      linarith

theorem evLt_const_left (c y b : ℝ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), c < y - ε * b) ↔ (c < y ∨ (c = y ∧ b < 0)) := by
  have h := evLt_iff c y 0 b
  simp only [mul_zero, sub_zero] at h
  exact h

theorem evLt_const_right (x a c : ℝ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), x - ε * a < c) ↔ (x < c ∨ (x = c ∧ 0 < a)) := by
  have h := evLt_iff x c a 0
  simp only [mul_zero, sub_zero] at h
  exact h

/-! ## Atomwise comparisons -/

section Atoms

variable {P Q : Prop}

/-- A window constraint. -/
theorem window_iff (L t a : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) (hfree : P → a = 0) (hpin : ¬ P → 0 < a ∧ L < t ∧ t ≤ L + 1) :
    ((L < t ∨ (L = t ∧ a < 0)) ∧ (t < L + 1 ∨ (t = L + 1 ∧ 0 < a)) ∧ (0 < t ∨ (0 = t ∧ a < 0))) ↔
      (P → L < t ∧ t < L + 1 ∧ 0 < t) := by
  by_cases hP : P
  · have h0 := hfree hP
    subst h0
    simp only [lt_self_iff_false, and_false, or_false, hP, true_implies]
  · obtain ⟨hapos, h1, h2⟩ := hpin hP
    simp only [hP, false_implies, iff_true]
    refine ⟨Or.inl h1, ?_, Or.inl (by linarith)⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hapos⟩

/-- A comparison of a branch with a clock (upper, or a lower clock read from the other side). -/
theorem clock_iff (t u a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hfree : P → a = 0) (hpos : ¬ P → 0 < a)
    (hQ : Q → c = 0) (hgen : ¬ P → Q → t ≠ u) (hpp : ¬ P → ¬ Q → t < u ∨ (t = u ∧ c < a)) :
    (t < u ∨ (t = u ∧ c < a)) ↔ ((P ∨ Q) → t < u) := by
  by_cases hP : P
  · have h0 := hfree hP
    subst h0
    have : ¬ c < 0 := not_lt.mpr hc
    simp only [this, and_false, or_false, hP, true_or, true_implies]
  · by_cases hq : Q
    · have h0 := hQ hq
      subst h0
      have hne := hgen hP hq
      simp only [hP, hq, or_true, true_implies]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact h
        · exact absurd h hne
      · exact Or.inl
    · simp only [hP, hq, or_self, false_implies, iff_true]
      exact hpp hP hq

/-- A lower-clock comparison (the clock below, the branch above). -/
theorem lower_iff (s t a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hfree : P → a = 0)
    (hQ : Q → c = 0) (hgen : P → ¬ Q → s ≠ t) (hpp : ¬ P → ¬ Q → s < t ∨ (s = t ∧ a < c)) :
    (s < t ∨ (s = t ∧ a < c)) ↔ ((P ∨ Q) → s < t) := by
  by_cases hq : Q
  · have h0 := hQ hq
    subst h0
    have : ¬ a < 0 := not_lt.mpr ha
    simp only [this, and_false, or_false, hq, or_true, true_implies]
  · by_cases hP : P
    · have h0 := hfree hP
      subst h0
      have hne := hgen hP hq
      simp only [hP, true_or, true_implies]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact h
        · exact absurd h hne
      · exact Or.inl
    · simp only [hP, hq, or_self, false_implies, iff_true]
      exact hpp hP hq

end Atoms

/-! ## The relaxed kernel domain is the shifted unpinned domain -/

variable {w : ℕ}

/-- **The shift lemma for kernel domains.** For a time vector `τ` whose pinned coordinates lie in their windows, satisfy
the pinned–pinned constraints in the shifted sense, and differ from every free coordinate (and from free clocks), the
unpinned `kDomain` with shifted clocks contains `τ - ε • α` for all small `ε > 0` iff `τ` is in the relaxed domain. -/
theorem eventually_kDomain_shift_iff (LG : LayeredGarden w) (up upα : GBranch LG.garden.tree → ℝ) (s sα : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (upFree : GBranch LG.garden.tree → Prop) (sFree : Prop)
    (α τ : GBranch LG.garden.tree → ℝ)
    (hα0 : ∀ b, fix b = none → α b = 0) (hα : ∀ b, 0 ≤ α b) (hαpos : ∀ b, fix b ≠ none → 0 < α b)
    (hupα : ∀ b, 0 ≤ upα b) (hupF : ∀ b, upFree b → upα b = 0) (hsα : 0 ≤ sα) (hsF : sFree → sα = 0)
    (hgen : ∀ x y, fix x = none → fix y ≠ none → τ x ≠ τ y)
    (hwin : ∀ b, fix b ≠ none → (LG.layer b.toNode : ℝ) < τ b ∧ τ b ≤ LG.layer b.toNode + 1)
    (hupP : ∀ b, fix b ≠ none → ¬ upFree b → τ b < up b ∨ (τ b = up b ∧ upα b < α b))
    (hupG : ∀ b, fix b ≠ none → upFree b → τ b ≠ up b)
    (hedge : ∀ b b', b'.IsChildOf b → fix b' ≠ none → fix b ≠ none → τ b' < τ b ∨ (τ b' = τ b ∧ α b < α b'))
    (hlowP : ∀ b, LG.garden.IsLoneParent b → fix b ≠ none → ¬ sFree → s < τ b ∨ (s = τ b ∧ α b < sα))
    (hlowG : ∀ b, LG.garden.IsLoneParent b → fix b = none → ¬ sFree → s ≠ τ b) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), (fun b => τ b - ε * α b) ∈ kDomain LG (fun b => up b - ε * upα b) (s - ε * sα)) ↔
      τ ∈ kDomainR LG up s fix upFree sFree := by
  simp only [kDomain, kDomainR, Set.mem_ofPred_eq]
  rw [Filter.eventually_all]
  refine forall_congr' fun b => ?_
  simp only [Filter.eventually_and, Filter.eventually_all, evLt_iff,
    evLt_const_left, evLt_const_right]
  have hL : (0 : ℝ) ≤ LG.layer b.toNode := Nat.cast_nonneg _
  have hW := window_iff (P := fix b = none) (LG.layer b.toNode) (τ b) (α b) hL (hα b) (hα0 b)
    (fun h => ⟨hαpos b h, (hwin b h).1, (hwin b h).2⟩)
  have hU := clock_iff (P := fix b = none) (Q := upFree b) (τ b) (up b) (α b) (upα b) (hα b) (hupα b) (hα0 b)
    (hαpos b) (hupF b) (hupG b) (hupP b)
  have hE : (∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → (τ b' < τ b ∨ (τ b' = τ b ∧ α b < α b'))) ↔
      (∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b) := by
    refine forall_congr' fun b' => forall_congr' fun hb' => ?_
    exact clock_iff (P := fix b' = none) (Q := fix b = none) (τ b') (τ b) (α b') (α b) (hα b') (hα b) (hα0 b')
      (hαpos b') (hα0 b) (fun h1 h2 => (hgen b b' h2 h1).symm) (fun h1 h2 => hedge b b' hb' h1 h2)
  have hLo : (LG.garden.IsLoneParent b → (s < τ b ∨ (s = τ b ∧ α b < sα))) ↔
      (LG.garden.IsLoneParent b → (fix b = none ∨ sFree) → s < τ b) := by
    refine forall_congr' fun hl => ?_
    exact lower_iff (P := fix b = none) (Q := sFree) s (τ b) (α b) sα (hα b) hsα (hα0 b) hsF
      (fun h1 h2 => hlowG b hl h1 h2) (fun h1 h2 => hlowP b hl h1 h2)
  rw [← hW, ← hU, ← hE, ← hLo]
  simp only [and_assoc]

/-! ## The relaxed core domain is the shifted unpinned core domain -/

theorem parentClockWith_shift {tree : Fin w → TTree} (top : Fin w → ℝ) (τ α : GBranch tree → ℝ) (ε : ℝ)
    (a : GNode tree) :
    parentClockWith top (fun b => τ b - ε * α b) a = parentClockWith top τ a - ε * parentClockWith 0 α a := by
  unfold parentClockWith
  cases nodeToSlot a with
  | inl j => simp
  | inr x => rfl

theorem parentClockWith_zero_nonneg {tree : Fin w → TTree} (α : GBranch tree → ℝ) (hα : ∀ b, 0 ≤ α b)
    (a : GNode tree) : 0 ≤ parentClockWith 0 α a := by
  unfold parentClockWith
  cases nodeToSlot a with
  | inl j => simp
  | inr x => exact hα x.1

/-- A free parent clock is a free branch time. -/
theorem clockFree_spec {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) (a : GNode tree)
    (h : clockFree fix a) : ∃ c : GBranch tree, fix c = none ∧ ∀ (top : Fin w → ℝ) (τ : GBranch tree → ℝ),
      parentClockWith top τ a = τ c := by
  unfold clockFree at h
  unfold parentClockWith
  revert h
  cases nodeToSlot a with
  | inl j => exact fun h => h.elim
  | inr x => exact fun h => ⟨x.1, h, fun _ _ => rfl⟩

/-- **The shift lemma for the core domain.** -/
theorem eventually_coreTimeDomainW_shift_iff {tree : Fin w → TTree} (layer : GBranch tree → ℕ) (top : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ) (α τ : GBranch tree → ℝ)
    (hα0 : ∀ b, fix b = none → α b = 0) (hα : ∀ b, 0 ≤ α b) (hαpos : ∀ b, fix b ≠ none → 0 < α b)
    (hgen : ∀ x y, fix x = none → fix y ≠ none → τ x ≠ τ y)
    (hwin : ∀ b, fix b ≠ none → (layer b : ℝ) < τ b ∧ τ b ≤ layer b + 1)
    (hclk : ∀ b, fix b ≠ none → ¬ clockFree fix b.toNode →
      τ b < parentClockWith top τ b.toNode ∨
        (τ b = parentClockWith top τ b.toNode ∧ parentClockWith 0 α b.toNode < α b)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), (fun b => τ b - ε * α b) ∈ coreTimeDomainW layer top) ↔
      τ ∈ coreTimeDomainWR layer top fix := by
  simp only [coreTimeDomainW, coreTimeDomainWR, Set.mem_ofPred_eq, parentClockWith_shift]
  rw [Filter.eventually_all]
  refine forall_congr' fun b => ?_
  simp only [Filter.eventually_and, evLt_iff, evLt_const_left, evLt_const_right]
  have hL : (0 : ℝ) ≤ layer b := Nat.cast_nonneg _
  have hW := window_iff (P := fix b = none) (layer b) (τ b) (α b) hL (hα b) (hα0 b)
    (fun h => ⟨hαpos b h, (hwin b h).1, (hwin b h).2⟩)
  have hC := clock_iff (P := fix b = none) (Q := clockFree fix b.toNode) (τ b) (parentClockWith top τ b.toNode)
    (α b) (parentClockWith 0 α b.toNode) (hα b) (parentClockWith_zero_nonneg α hα _) (hα0 b) (hαpos b)
    (fun hq => by
      obtain ⟨c, hc, hpc⟩ := clockFree_spec fix b.toNode hq
      rw [hpc]; exact hα0 c hc)
    (fun hP hq => by
      obtain ⟨c, hc, hpc⟩ := clockFree_spec fix b.toNode hq
      rw [hpc top τ]; exact (hgen c b hc hP).symm)
    (hclk b)
  rw [← hW, ← hC]
  simp only [and_assoc]

end WaveTurbulence.Flower.MkSlotsB
