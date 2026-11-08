/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBR1

/-! # B3s-HELPER3 B2 (2): the relaxed domain split of VINE-B♯

Main's `VineB.SpliceShape.dom_iff` splits the unpinned skeleton domain `coreTimeDomainW` of the glued times into the
open spliced domain `openSb` of the `G_sb` times and V5's local unit domains. Its RELAXED twin, for pins `fixS` on the
skeleton branches with the unit interiors unpinned (`hU`) and the pin hypotheses `RelaxPinsS` (pins in their half-open
windows, below the upper times, monotone along ancestry):

  `Φ.glueTime hd τ' τs ∈ coreTimeDomainWR layerS tt fixS ↔
     τ' ∈ openSbR Gsb (layerS ∘ Φ.br) tt (fixS ∘ Φ.br) ∧ ∀ j, τs j ∈ clLocalTimeDomain (regionOf (blk j)) layerS (Φ.clocks τ' j)`

for every `(τ', τs)` whose glued time vector is on the pinned slice with free times off the pins (`PinnedAt`, a full
set). Proof by the shift method: with `α := alphaOf fixS` (zero on unit interiors by `hU`),
`Φ.glueTime hd (τ' - ε • α ∘ Φ.br) τs = Φ.glueTime hd τ' τs - ε • α` (`glueTime_shift`); the left side is the
eventual unpinned membership of the shifted vector (`eventually_coreTimeDomainW_shift_iff`), main's `dom_iff` applies
at every `ε`, and the two factors are eventually the relaxed ones (`eventually_openSb_shift_iff`, with the structural
fact `br_isAncB_of_isChildOf`; `eventually_clLocalTimeDomain_shift_iff` with `Φ.clocks` linear in `τ'`).

With lower bounds `lbS` absent on unit interiors (ruling R187) the split gains the conjunct
`glueTime ∈ lbDomR lbS ↔ τ' ∈ lbDomR (lbS ∘ Φ.br)` (`mem_lbDomR_glue_iff`, exact). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology Set MeasureTheory
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.LGSpine WaveTurbulence.VineB WaveTurbulence.RedSplice TTree

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-! ## Pin hypotheses on branch-layered trees -/

/-- **The pin hypotheses of the relaxed VINE-B♯** (on a branch layering): pins in their half-open layer windows and
below the upper time of their tree, monotone along ancestry. -/
structure RelaxPinsS {tree : Fin w → TTree} (layer : GBranch tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ) : Prop where
  val : ∀ b v, fix b = some v → (layer b : ℝ) < v ∧ v ≤ layer b + 1 ∧ v ≤ tt b.1.1
  mono : ∀ x y v v', fix x = some v → fix y = some v' → IsAncB y x → v ≤ v'

theorem PinnedAt.val_of_ne {ι : Type*} {fix : ι → Option ℝ} {τ : ι → ℝ} (hτ : PinnedAt fix τ) {b : ι}
    (hb : fix b ≠ none) : ∃ v, fix b = some v ∧ τ b = v := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
  exact ⟨v, hv, hτ.pin b v hv⟩

theorem isChildOf_of_toNode_eq {tree : Fin w → TTree} {b c : GBranch tree} {i : Fin 3}
    (h : b.toNode = c.child i) : b.IsChildOf c :=
  ⟨congrArg (fun x : GNode tree => x.1.1) h, i, congrArg (fun x : GNode tree => x.1.2) h⟩

/-- **The shift lemma for the core domain under the pin hypotheses** (any branch-layered tree). -/
theorem eventually_coreTimeDomainW_shift_iff_of_pins {tree : Fin w → TTree} (layer : GBranch tree → ℕ)
    (tt : Fin w → ℝ) (fix : GBranch tree → Option ℝ) (hP : RelaxPinsS layer tt fix) (τ : GBranch tree → ℝ)
    (hτ : PinnedAt fix τ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), (fun b => τ b - ε * alphaOf fix b) ∈ coreTimeDomainW layer tt) ↔
      τ ∈ coreTimeDomainWR layer tt fix := by
  refine eventually_coreTimeDomainW_shift_iff layer tt fix (alphaOf fix) τ (fun b h => alphaOf_none h)
    (alphaOf_nonneg fix) (fun b h => alphaOf_pos h) hτ.gen
    (fun b hb => by
      obtain ⟨v, hv, hτv⟩ := hτ.val_of_ne hb
      rw [hτv]
      exact ⟨(hP.val b v hv).1, (hP.val b v hv).2.1⟩)
    (fun b hb hcf => ?_)
  obtain ⟨v, hv, hτv⟩ := hτ.val_of_ne hb
  rcases hs : nodeToSlot b.toNode with j | ⟨c, i⟩
  · have hpc : parentClockWith tt τ b.toNode = tt j := by unfold parentClockWith; rw [hs]
    have hpa : parentClockWith 0 (alphaOf fix) b.toNode = 0 := by unfold parentClockWith; rw [hs]; rfl
    have hle := (hP.val b v hv).2.2
    rw [show b.1.1 = j from index_of_slot_root b.toNode j hs] at hle
    rw [hpc, hpa, hτv]
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, alphaOf_pos hb⟩
  · have hc : fix c ≠ none := by
      intro h; apply hcf; unfold clockFree; rw [hs]; exact h
    obtain ⟨v', hv', hτv'⟩ := hτ.val_of_ne hc
    have hpc : parentClockWith tt τ b.toNode = τ c := by unfold parentClockWith; rw [hs]
    have hpa : parentClockWith 0 (alphaOf fix) b.toNode = alphaOf fix c := by unfold parentClockWith; rw [hs]
    have hanc : IsAncB c b := IsAncB.of_isChildOf (isChildOf_of_toNode_eq (node_eq_child_of_slot b.toNode c i hs))
    have hm := hP.mono b c v v' hv hv' hanc
    rw [hpc, hpa, hτv, hτv']
    rcases lt_or_eq_of_le hm with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, alphaOf_lt hanc hc hb⟩

/-! ## The splice: structure and linearity -/

variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)
set_option linter.unusedSectionVars false

/-- **A `G_sb` child is a strict descendant in the skeleton**: a child of a non-hinge is the image child, a child of a
hinge `u1^j` is a boundary node of unit `j`, a strict descendant of `u1^j`. -/
theorem br_isAncB_of_isChildOf {v u : GBranch Gsb.tree} (h : v.IsChildOf u) : IsAncB (Φ.br u) (Φ.br v) := by
  obtain ⟨h1, i, hi⟩ := h
  have hv : v.toNode = u.child i := Subtype.ext (Prod.ext h1 hi)
  have hn : (Φ.br v).toNode = Φ.node (u.child i) := by rw [Φ.br_node, hv]
  rcases Φ.node_child_parent u i with ⟨hh, -⟩ | ⟨j, hj, hcr⟩
  · rw [Φ.child u i hh] at hn
    exact IsAncB.of_isChildOf (isChildOf_of_toNode_eq hn)
  · rw [← hn] at hcr
    have hd := crown_desc (blk j) hcr
    have hne := crown_ne_upper (blk j) hcr
    rw [← hj] at hd hne
    obtain ⟨l, hl⟩ := hd.2
    refine ⟨hd.1, l, fun hl0 => hne ?_, hl.symm⟩
    rw [hl0, List.append_nil] at hl
    exact Subtype.ext (Prod.ext hd.1.symm hl.symm)

/-- The glued time vector of a shifted `G_sb` vector is the shifted glued vector (the shift vanishes on the unit
interiors). -/
theorem glueTime_shift (hd : Disj blk) (fixS : GBranch S.tree → Option ℝ)
    (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) (ε : ℝ) :
    Φ.glueTime hd (fun c => τ' c - ε * alphaOf fixS (Φ.br c)) τs =
      fun v => Φ.glueTime hd τ' τs v - ε * alphaOf fixS v := by
  funext v
  rcases hs : Φ.branchSplit hd v with c | ⟨j, x⟩
  · have hv : v = Φ.br c := (Φ.branchSplit hd).injective (hs.trans (Φ.branchSplit_br hd c).symm)
    subst hv
    rw [Φ.glueTime_br, Φ.glueTime_br]
  · have hv : v = x.1 := (Φ.branchSplit hd).injective (hs.trans (Φ.branchSplit_inter hd j x).symm)
    subst hv
    rw [Φ.glueTime_inter, Φ.glueTime_inter, alphaOf_none (hU j x.1 x.2), mul_zero, sub_zero]

theorem extTime_shift (τ' α : GBranch Gsb.tree → ℝ) (ε : ℝ) :
    Φ.extTime (fun c => τ' c - ε * α c) = fun v => Φ.extTime τ' v - ε * Φ.extTime α v := by
  funext v
  unfold SpliceShape.extTime
  split_ifs <;> simp

theorem clBranchClock_shift {G : Garden w} (τ α : GBranch G.tree → ℝ) (ε : ℝ) (x : GNode G.tree) :
    clBranchClock (fun v => τ v - ε * α v) x = clBranchClock τ x - ε * clBranchClock α x := by
  unfold clBranchClock
  split_ifs <;> simp

theorem clExternalTimes_shift {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G U a b) (τ α : GBranch G.tree → ℝ) (ε : ℝ) :
    clExternalTimes R (fun v => τ v - ε * α v) = fun i => clExternalTimes R τ i - ε * clExternalTimes R α i := by
  funext i
  fin_cases i
  · rfl
  · exact clBranchClock_shift τ α ε _
  · exact clBranchClock_shift τ α ε _

theorem clocks_shift (τ' α : GBranch Gsb.tree → ℝ) (ε : ℝ) (j : J) :
    Φ.clocks (fun c => τ' c - ε * α c) j = fun i => Φ.clocks τ' j i - ε * Φ.clocks α j i := by
  unfold SpliceShape.clocks
  rw [extTime_shift, clExternalTimes_shift]

theorem extTime_nonneg (α : GBranch Gsb.tree → ℝ) (hα : ∀ c, 0 ≤ α c) (v : GBranch S.tree) :
    0 ≤ Φ.extTime α v := by
  unfold SpliceShape.extTime
  split_ifs
  · exact hα _
  · exact le_refl 0

theorem clBranchClock_nonneg {G : Garden w} (α : GBranch G.tree → ℝ) (hα : ∀ v, 0 ≤ α v) (x : GNode G.tree) :
    0 ≤ clBranchClock α x := by
  unfold clBranchClock
  split_ifs
  · exact hα _
  · exact le_refl 0

theorem clocks_nonneg (α : GBranch Gsb.tree → ℝ) (hα : ∀ c, 0 ≤ α c) (j : J) (i : Fin 3) :
    0 ≤ Φ.clocks α j i := by
  have h := extTime_nonneg Φ α hα
  fin_cases i
  · exact h _
  · exact clBranchClock_nonneg _ h _
  · exact clBranchClock_nonneg _ h _

theorem extTime_alpha_ret (fixS : GBranch S.tree → Option ℝ) {v : GBranch S.tree} (hv : Ret blk v.toNode) :
    Φ.extTime (fun c => alphaOf fixS (Φ.br c)) v = alphaOf fixS v := by
  obtain ⟨c, rfl⟩ := Φ.exists_br hv
  rw [Φ.extTime_br]

/-! ## The two eventual factors -/

theorem upper_ne_lower (j : J) : (blk j).lower ≠ (blk j).upper := fun h => (blk j).isBlock.2.2.2.1 h.symm

theorem lower_mem_inter (j : J) : (blk j).lower ∈ inter blk j :=
  mem_inter.mpr ⟨lower_mem _, upper_ne_lower j⟩

/-- The lower boundary clocks: the shifted clock differs from the (free) lower joint. -/
theorem clocks_lower_gen (hd : Disj blk) (fixS : GBranch S.tree → Option ℝ)
    (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) (hτ : PinnedAt fixS (Φ.glueTime hd τ' τs)) (j : J)
    (i : Fin 3) (x : GNode S.tree) (hx : x ∈ crownSet (blk j))
    (hc : Φ.clocks τ' j i = clBranchClock (Φ.extTime τ') x)
    (hcα : Φ.clocks (fun c => alphaOf fixS (Φ.br c)) j i =
      clBranchClock (Φ.extTime (fun c => alphaOf fixS (Φ.br c))) x) :
    0 < Φ.clocks (fun c => alphaOf fixS (Φ.br c)) j i →
      Φ.clocks τ' j i ≠ clLocalClock (regionOf (blk j)) (Φ.clocks τ' j) (τs j) (blk j).lower := by
  intro hpos
  rw [hcα] at hpos
  rw [hc, Φ.clLocalClock_glue hd τ' τs j (lower_mem _)]
  unfold clBranchClock at hpos ⊢
  split_ifs at hpos ⊢ with hb
  · have hr : Ret blk (GBranch.toNode (⟨x.1, hb⟩ : GBranch S.tree)) := ret_crown hd j hx
    rw [extTime_alpha_ret Φ fixS hr] at hpos
    have hpin : fixS ⟨x.1, hb⟩ ≠ none := fun h => by rw [alphaOf_none h] at hpos; exact lt_irrefl _ hpos
    rw [← Φ.glueTime_ret hd τ' τs hr]
    exact fun h => hτ.gen _ _ (hU j _ (lower_mem_inter j)) hpin h.symm
  · exact (lt_irrefl _ hpos).elim

/-- The unit factor: the local domain at the shifted exterior clocks is eventually the local domain. -/
theorem unit_eventually_iff (hd : Disj blk) (layerS : GBranch S.tree → ℕ) (fixS : GBranch S.tree → Option ℝ)
    (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) (hτ : PinnedAt fixS (Φ.glueTime hd τ' τs)) (j : J) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), τs j ∈ clLocalTimeDomain (regionOf (blk j)) layerS
        (Φ.clocks (fun c => τ' c - ε * alphaOf fixS (Φ.br c)) j)) ↔
      τs j ∈ clLocalTimeDomain (regionOf (blk j)) layerS (Φ.clocks τ' j) := by
  simp_rw [clocks_shift]
  refine eventually_clLocalTimeDomain_shift_iff (regionOf (blk j)) layerS (Φ.clocks τ' j)
    (Φ.clocks (fun c => alphaOf fixS (Φ.br c)) j) (τs j)
    (clocks_nonneg Φ _ (fun c => alphaOf_nonneg _ _) j)
    (clLocalClock_interior_zero _ _ (upper_ne_lower j) (lower_mem _))
    (clocks_lower_gen Φ hd fixS hU τ' τs hτ j 1 _ (Or.inr (Or.inl rfl)) rfl rfl)
    (clocks_lower_gen Φ hd fixS hU τ' τs hτ j 2 _ (Or.inr (Or.inr rfl)) rfl rfl)

theorem br_index (c : GBranch Gsb.tree) : (Φ.br c).1.1 = c.1.1 := by
  have := Φ.tree_eq c.toNode
  rw [← Φ.br_node] at this
  exact this

/-- The `G_sb` factor: `openSb` at the shifted `G_sb` times is eventually `openSbR`. -/
theorem openSb_eventually_iff (hd : Disj blk) (layerS : GBranch S.tree → ℕ) (tt : Fin w → ℝ)
    (fixS : GBranch S.tree → Option ℝ) (hP : RelaxPinsS layerS tt fixS) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) (hτ : PinnedAt fixS (Φ.glueTime hd τ' τs)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), (fun c => τ' c - ε * alphaOf fixS (Φ.br c)) ∈
        openSb Gsb (fun c => layerS (Φ.br c)) tt) ↔
      τ' ∈ openSbR Gsb (fun c => layerS (Φ.br c)) tt (fun c => fixS (Φ.br c)) := by
  have hpin : ∀ c, fixS (Φ.br c) ≠ none → ∃ v, fixS (Φ.br c) = some v ∧ τ' c = v := fun c hc => by
    obtain ⟨v, hv, h⟩ := hτ.val_of_ne hc
    exact ⟨v, hv, by rw [← h, Φ.glueTime_br]⟩
  refine eventually_openSb_shift_iff Gsb _ tt _ (fun c => alphaOf fixS (Φ.br c)) τ'
    (fun c h => alphaOf_none h) (fun c => alphaOf_nonneg _ _) (fun c h => alphaOf_pos h)
    (fun x y hx hy => by
      have := hτ.gen _ _ hx hy
      rwa [Φ.glueTime_br, Φ.glueTime_br] at this)
    (fun c hc => by
      obtain ⟨v, hv, h⟩ := hpin c hc
      rw [h]
      exact ⟨(hP.val _ v hv).1, (hP.val _ v hv).2.1⟩)
    (fun c hc => by
      obtain ⟨v, hv, h⟩ := hpin c hc
      rw [h, ← br_index Φ c]
      exact (hP.val _ v hv).2.2)
    (fun v u hvu hv hu => ?_)
  obtain ⟨x, hx, h1⟩ := hpin v hv
  obtain ⟨y, hy, h2⟩ := hpin u hu
  have hanc := br_isAncB_of_isChildOf Φ hvu
  have hm := hP.mono _ _ x y hx hy hanc
  rw [h1, h2]
  rcases lt_or_eq_of_le hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, alphaOf_lt hanc hu hv⟩

/-! ## The relaxed domain split -/

/-- **The relaxed domain split of VINE-B♯** (relaxed `VineB.SpliceShape.dom_iff`). -/
theorem mem_coreTimeDomainWR_glue_iff (hd : Disj blk) (layerS : GBranch S.tree → ℕ) (tt : Fin w → ℝ)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hP : RelaxPinsS layerS tt fixS) (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j)))
    (hτ : PinnedAt fixS (Φ.glueTime hd τ' τs)) :
    Φ.glueTime hd τ' τs ∈ coreTimeDomainWR layerS tt fixS ↔
      τ' ∈ openSbR Gsb (fun c => layerS (Φ.br c)) tt (fun c => fixS (Φ.br c)) ∧
        ∀ j, τs j ∈ clLocalTimeDomain (regionOf (blk j)) layerS (Φ.clocks τ' j) := by
  have hset : ∀ ε : ℝ, (fun b => Φ.glueTime hd τ' τs b - ε * alphaOf fixS b) ∈ coreTimeDomainW layerS tt ↔
      (fun c => τ' c - ε * alphaOf fixS (Φ.br c)) ∈ openSb Gsb (fun c => layerS (Φ.br c)) tt ∧
        ∀ j, τs j ∈ clLocalTimeDomain (regionOf (blk j)) layerS
          (Φ.clocks (fun c => τ' c - ε * alphaOf fixS (Φ.br c)) j) := fun ε => by
    rw [← glueTime_shift Φ hd fixS hU τ' τs ε]
    exact Φ.dom_iff hd layerS tt _ τs
  rw [← eventually_coreTimeDomainW_shift_iff_of_pins layerS tt fixS hP _ hτ,
    Filter.eventually_congr (Filter.Eventually.of_forall hset), Filter.eventually_and, Filter.eventually_all]
  exact and_congr (openSb_eventually_iff Φ hd layerS tt fixS hP τ' τs hτ)
    (forall_congr' fun j => unit_eventually_iff Φ hd layerS fixS hU τ' τs hτ j)

/-- The lower bounds of the glued times are the lower bounds of the `G_sb` times (no lower bound at a unit
interior). -/
theorem mem_lbDomR_glue_iff (hd : Disj blk) (lbS : GBranch S.tree → Option ℝ)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) :
    Φ.glueTime hd τ' τs ∈ lbDomR lbS ↔ τ' ∈ lbDomR (fun c => lbS (Φ.br c)) := by
  constructor
  · intro h c x hx
    have := h (Φ.br c) x hx
    rwa [Φ.glueTime_br] at this
  · intro h v x hx
    rcases ret_or_interior (blk := blk) v.toNode with hr | ⟨j, h1, h2⟩
    · obtain ⟨c, rfl⟩ := Φ.exists_br hr
      rw [Φ.glueTime_br]
      exact h c x hx
    · have hm : v ∈ inter blk j := mem_inter.mpr ⟨(branch_real_iff _ _).mp h1, fun he => h2 (by rw [he])⟩
      rw [hlbU j v hm] at hx
      exact absurd hx (by simp)

/-- **The relaxed domain split with lower bounds** (ruling R187). -/
theorem mem_coreTimeDomainWR_lb_glue_iff (hd : Disj blk) (layerS : GBranch S.tree → ℕ) (tt : Fin w → ℝ)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS layerS tt fixS) (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j)))
    (hτ : PinnedAt fixS (Φ.glueTime hd τ' τs)) :
    Φ.glueTime hd τ' τs ∈ coreTimeDomainWR layerS tt fixS ∩ lbDomR lbS ↔
      τ' ∈ openSbR Gsb (fun c => layerS (Φ.br c)) tt (fun c => fixS (Φ.br c)) ∩ lbDomR (fun c => lbS (Φ.br c)) ∧
        ∀ j, τs j ∈ clLocalTimeDomain (regionOf (blk j)) layerS (Φ.clocks τ' j) := by
  rw [Set.mem_inter_iff, Set.mem_inter_iff, mem_coreTimeDomainWR_glue_iff Φ hd layerS tt fixS hU hP τ' τs hτ,
    mem_lbDomR_glue_iff Φ hd lbS hlbU τ' τs]
  tauto

end WaveTurbulence.Flower.MkSlotsB
