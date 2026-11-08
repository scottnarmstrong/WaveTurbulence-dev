/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLeaves
public import WaveTurbulence.Foundations.Flower.MkSlotsW.PRedM

/-! # B3s-HELPER3 (B1): the relaxed reduction specializes to the unpinned-domain one (`_one`)

When every constraint that the relaxed domains drop holds strictly at the pinned values — pins strictly inside their
layer windows and strictly below the upper times, and STRICTLY monotone along ancestry (`StrictPins`; α's pins, at
most one per tree, satisfy it vacuously in the monotonicity part) — the relaxed and the unpinned domains agree on the
pinned slices of the garden, the core and every native slot. Then, with unit slot weights `Θs ≡ 1`, the relaxed
reduction `kernelLeaves_skeleton_reduction_selNWFMR` is, statement for statement,
`MkSlotsW.kernelLeaves_skeleton_reduction_selNWFM` (`kernelLeaves_skeleton_reduction_selNWFMR_one`).

(Non-strict equal pins — β's `dParent`/`dChild` — are exactly the case where the unpinned domains are empty on the
pinned slice and only the relaxed statement is meaningful.)

* `mem_kDomainR_iff_kDomain`, `mem_coreTimeDomainWR_iff`: relaxed = unpinned when the dropped constraints hold;
* `StrictPins`, `StrictPins.relax`;
* `kernelLeavesSelNWFMR_one_eq`, `slotFnGWFR_one_eq`, **`kernelLeaves_skeleton_reduction_selNWFMR_one`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsB
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots WaveTurbulence.LGSpine

variable {w : ℕ}

/-! ### Relaxed = unpinned when the dropped constraints hold -/

theorem mem_kDomainR_iff_kDomain (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (upFree : GBranch LG.garden.tree → Prop) (sFree : Prop)
    (τ : GBranch LG.garden.tree → ℝ)
    (hwin : ∀ b, fix b ≠ none → (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧ 0 < τ b)
    (hup : ∀ b, fix b ≠ none → ¬ upFree b → τ b < up b)
    (hedge : ∀ b b', b'.IsChildOf b → fix b' ≠ none → fix b ≠ none → τ b' < τ b)
    (hlow : ∀ b, LG.garden.IsLoneParent b → fix b ≠ none → ¬ sFree → s < τ b) :
    τ ∈ kDomainR LG up s fix upFree sFree ↔ τ ∈ kDomain LG up s := by
  constructor
  · intro h b
    obtain ⟨h1, h2, h3, h4⟩ := h b
    have hw : (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧ 0 < τ b := by
      by_cases hb : fix b = none
      · exact h1 hb
      · exact hwin b hb
    refine ⟨hw.1, hw.2.1, hw.2.2, ?_, fun b' hc => ?_, fun hl => ?_⟩
    · by_cases hb : fix b = none
      · exact h2 (Or.inl hb)
      · by_cases hu : upFree b
        · exact h2 (Or.inr hu)
        · exact hup b hb hu
    · by_cases hb' : fix b' = none
      · exact h3 b' hc (Or.inl hb')
      · by_cases hb : fix b = none
        · exact h3 b' hc (Or.inr hb)
        · exact hedge b b' hc hb' hb
    · by_cases hb : fix b = none
      · exact h4 hl (Or.inl hb)
      · by_cases hs : sFree
        · exact h4 hl (Or.inr hs)
        · exact hlow b hl hb hs
  · intro h b
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h b
    exact ⟨fun _ => ⟨h1, h2, h3⟩, fun _ => h4, fun b' hb' _ => h5 b' hb', fun hl _ => h6 hl⟩

theorem mem_coreTimeDomainWR_iff {tree : Fin w → TTree} (layer : GBranch tree → ℕ) (top : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ) (τ : GBranch tree → ℝ)
    (hwin : ∀ b, fix b ≠ none → (layer b : ℝ) < τ b ∧ τ b < layer b + 1 ∧ 0 < τ b)
    (hclk : ∀ b, fix b ≠ none → ¬ clockFree fix b.toNode → τ b < parentClockWith top τ b.toNode) :
    τ ∈ coreTimeDomainWR layer top fix ↔ τ ∈ coreTimeDomainW layer top := by
  constructor
  · intro h b
    obtain ⟨h1, h2⟩ := h b
    have hw : (layer b : ℝ) < τ b ∧ τ b < layer b + 1 ∧ 0 < τ b := by
      by_cases hb : fix b = none
      · exact h1 hb
      · exact hwin b hb
    refine ⟨hw.1, hw.2.1, hw.2.2, ?_⟩
    by_cases hb : fix b = none
    · exact h2 (Or.inl hb)
    · by_cases hc : clockFree fix b.toNode
      · exact h2 (Or.inr hc)
      · exact hclk b hb hc
  · intro h b
    obtain ⟨h1, h2, h3, h4⟩ := h b
    exact ⟨fun _ => ⟨h1, h2, h3⟩, fun _ => h4⟩

/-! ### Strict pins -/

/-- Pins strictly inside their windows, strictly below the upper time of their tree, strictly monotone along
ancestry. -/
structure StrictPins {tree : Fin w → TTree} (layer : GNode tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ) : Prop where
  val : ∀ b v, fix b = some v → (layer b.toNode : ℝ) < v ∧ v < layer b.toNode + 1 ∧ v < tt b.1.1
  smono : ∀ x y v v', fix x = some v → fix y = some v' → IsAncB y x → v < v'

theorem StrictPins.relax {tree : Fin w → TTree} {layer : GNode tree → ℕ} {tt : Fin w → ℝ}
    {fix : GBranch tree → Option ℝ} (h : StrictPins layer tt fix) : RelaxPins layer tt fix :=
  ⟨fun b v hv => ⟨(h.val b v hv).1, (h.val b v hv).2.1.le, (h.val b v hv).2.2.le⟩,
    fun x y v v' hx hy ha => (h.smono x y v v' hx hy ha).le⟩

/-- α-type pins (`MkSlots.AdmissiblePins` with the upper times `tt`, and no two pinned branches comparable — e.g. at
most one pin per tree) are strict. -/
theorem StrictPins.of_admissible (LG : LayeredGarden w) (tt : Fin w → ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (hA : AdmissiblePins LG (fun b => tt b.1.1) fix)
    (hnc : ∀ x y : GBranch LG.garden.tree, IsAncB y x → fix x = none ∨ fix y = none) :
    StrictPins LG.layer tt fix := by
  refine ⟨fun b v hv => ⟨(hA.val b v hv).1, (hA.val b v hv).2.1, (hA.val b v hv).2.2.2⟩, fun x y v v' hx hy ha => ?_⟩
  rcases hnc x y ha with h | h
  · rw [h] at hx; exact absurd hx (by simp)
  · rw [h] at hy; exact absurd hy (by simp)

/-- The pinned slice. -/
def OnSlice {ι : Type*} (fix : ι → Option ℝ) (τ : ι → ℝ) : Prop := ∀ b v, fix b = some v → τ b = v

theorem ae_onSlice {ι : Type*} [Fintype ι] (fix : ι → Option ℝ) : ∀ᵐ τ ∂(fixMeasure fix), OnSlice fix τ := by
  filter_upwards [ae_pinnedAt fix] with τ h
  exact h.pin

/-! ### The slices of a reconstruction -/

section Recon

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (tt : Fin w → ℝ) (fixG : GBranch (D.forest hS) → Option ℝ)

theorem slice_val {ι : Type*} {fix : ι → Option ℝ} {τ : ι → ℝ} (hτ : OnSlice fix τ) {b : ι} (hb : fix b ≠ none) :
    ∃ v, fix b = some v ∧ τ b = v := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
  exact ⟨v, hv, hτ b v hv⟩

/-- A pinned branch strictly below a clock that is not free. -/
theorem clock_lt_of_strict (hP : StrictPins layer tt fixG) {τS : GBranch S.tree → ℝ}
    (hτS : OnSlice (fixCore D hS fixG) τS) (a : GNode S.tree) (x : GBranch (D.forest hS)) (v : ℝ)
    (hx : fixG x = some v)
    (hidx : ∀ j, nodeToSlot a = .inl j → x.1.1 = j)
    (hanc : ∀ c i, nodeToSlot a = .inr (c, i) → IsAncB (D.coreBranch hS c) x)
    (hcf : ¬ clockFree (fixCore D hS fixG) a) :
    v < parentClockWith tt τS a := by
  rcases hs : nodeToSlot a with j | ⟨c, i⟩
  · have hpc : parentClockWith tt τS a = tt j := by unfold parentClockWith; rw [hs]
    have hlt := (hP.val x v hx).2.2
    rw [hidx j hs] at hlt
    rw [hpc]
    exact hlt
  · have hc : fixCore D hS fixG c ≠ none := by
      intro h; apply hcf; unfold clockFree; rw [hs]; exact h
    obtain ⟨v', hv', hτv'⟩ := slice_val hτS hc
    have hpc : parentClockWith tt τS a = τS c := by unfold parentClockWith; rw [hs]
    rw [hpc, hτv']
    exact hP.smono _ _ v v' hx hv' (hanc c i hs)

theorem garden_slice_iff (hP : StrictPins layer tt fixG) (τ : GBranch (D.forest hS) → ℝ) (hτ : OnSlice fixG τ) :
    τ ∈ kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG ↔
      τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) 0 := by
  have e := kDomainR_eq_kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG
  refine (Eq.to_iff (congrArg (fun A => τ ∈ A) e.symm)).trans ?_
  have hplain := D.garden_plain hS
  refine mem_kDomainR_iff_kDomain (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) 0 fixG
    (fun _ => False) False τ (fun b hb => ?_) (fun b hb _ => ?_) (fun b b' hbb hb' hb => ?_)
    (fun b hl => (not_loneParent_of_plain (D.garden hS) hplain b hl).elim)
  · obtain ⟨v, hv, hτv⟩ := slice_val hτ hb
    have := hP.val b v hv
    show (layer b.toNode : ℝ) < τ b ∧ τ b < layer b.toNode + 1 ∧ 0 < τ b
    rw [hτv]
    exact ⟨this.1, this.2.1, lt_of_le_of_lt (Nat.cast_nonneg _) this.1⟩
  · obtain ⟨v, hv, hτv⟩ := slice_val hτ hb
    show τ b < tt b.1.1
    rw [hτv]
    exact (hP.val b v hv).2.2
  · obtain ⟨v, hv, hτv⟩ := slice_val hτ hb
    obtain ⟨v', hv', hτv'⟩ := slice_val hτ hb'
    rw [hτv, hτv']
    exact hP.smono _ _ v' v hv' hv (IsAncB.of_isChildOf hbb)

theorem core_slice_iff (hP : StrictPins layer tt fixG) (τS : GBranch S.tree → ℝ)
    (hτ : OnSlice (fixCore D hS fixG) τS) :
    τS ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt (fixCore D hS fixG) ↔
      τS ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt := by
  refine mem_coreTimeDomainWR_iff _ _ _ τS (fun b hb => ?_) (fun b hb hcf => ?_)
  · obtain ⟨v, hv, hτv⟩ := slice_val hτ hb
    have := hP.val _ v hv
    rw [hτv]
    exact ⟨this.1, this.2.1, lt_of_le_of_lt (Nat.cast_nonneg _) this.1⟩
  · obtain ⟨v, hv, hτv⟩ := slice_val hτ hb
    rw [hτv]
    exact clock_lt_of_strict D hS layer tt fixG hP hτ b.toNode (D.coreBranch hS b) v hv
      (fun j hj => (coreBranch_index D hS b).trans (index_of_slot_root _ j hj))
      (fun c i hci => coreBranch_isAncB D hS c i b (node_eq_child_of_slot _ c i hci)) hcf

theorem native_slice_iff (hP : StrictPins layer tt fixG) (τS : GBranch S.tree → ℝ)
    (hτS : OnSlice (fixCore D hS fixG) τS) (s : ReplacementSlot S) (t : NativeTimeBlock D s)
    (ht : OnSlice (fixNative D hS fixG s) t) :
    t ∈ nativeDomainWR D hS layer hLayer tt τS fixG s ↔ t ∈ nativeDomainW D hS layer hLayer tt τS s := by
  cases s with
  | inl p =>
    have hp : (nativeCoupleLayered D hS layer hLayer p).garden.IsPlain :=
      Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS) (nativeCoupleForest D hS p)
        (nativeCoupleForest_closed D hS p)
    refine mem_kDomainR_iff_kDomain (nativeCoupleLayered D hS layer hLayer p)
      (fun q => nativeCoupleUpperW D hS tt τS p q.1.1) 0 (fixNative D hS fixG (.inl p))
      (fun q => clockFree (fixCore D hS fixG) (coupleLeafNode hS p q.1.1)) False t (fun q hq => ?_)
      (fun q hq hcf => ?_) (fun q q' hqq hq' hq => ?_) (fun q hl => (not_loneParent_of_plain _ hp q hl).elim)
    · obtain ⟨v, hv, htv⟩ := slice_val ht hq
      have := hP.val (coupleContextBranch D hS p q) v hv
      show (layer (coupleContextBranch D hS p q).toNode : ℝ) < t q ∧
        t q < (layer (coupleContextBranch D hS p q).toNode : ℝ) + 1 ∧ 0 < t q
      rw [htv]
      exact ⟨this.1, this.2.1, lt_of_le_of_lt (Nat.cast_nonneg _) this.1⟩
    · obtain ⟨v, hv, htv⟩ := slice_val ht hq
      show t q < nativeCoupleUpperW D hS tt τS p q.1.1
      rw [htv, nativeCoupleUpperW_eq]
      exact clock_lt_of_strict D hS layer tt fixG hP hτS _ (coupleContextBranch D hS p q) v hv
        (fun j hj => (coupleBranch_index D hS p q).trans (index_of_slot_root _ j hj))
        (fun c i hci => coupleBranch_isAncB D hS p q c i (node_eq_child_of_slot _ c i hci)) hcf
    · obtain ⟨v, hv, htv⟩ := slice_val ht hq
      obtain ⟨v', hv', htv'⟩ := slice_val ht hq'
      rw [htv, htv']
      exact hP.smono _ _ v' v hv' hv (IsAncB.of_isChildOf (coupleBranch_isChildOf D hS p q q' hqq))
  | inr b =>
    refine mem_kDomainR_iff_kDomain (nativeChainLayered D hS layer hLayer b)
      (fun _ => parentClockWith tt τS b.toNode) (τS b) (fixNative D hS fixG (.inr b))
      (fun _ => clockFree (fixCore D hS fixG) b.toNode) (fixCore D hS fixG b = none) t (fun q hq => ?_)
      (fun q hq hcf => ?_) (fun q q' hqq hq' hq => ?_) (fun q hl hq hsF => ?_)
    · obtain ⟨v, hv, htv⟩ := slice_val ht hq
      have := hP.val (chainContextBranch D hS b ⟨q.1.2, q.2⟩) v hv
      show (layer (chainContextBranch D hS b ⟨q.1.2, q.2⟩).toNode : ℝ) < t q ∧
        t q < (layer (chainContextBranch D hS b ⟨q.1.2, q.2⟩).toNode : ℝ) + 1 ∧ 0 < t q
      rw [htv]
      exact ⟨this.1, this.2.1, lt_of_le_of_lt (Nat.cast_nonneg _) this.1⟩
    · obtain ⟨v, hv, htv⟩ := slice_val ht hq
      show t q < parentClockWith tt τS b.toNode
      rw [htv]
      exact clock_lt_of_strict D hS layer tt fixG hP hτS _ (chainContextBranch D hS b ⟨q.1.2, q.2⟩) v hv
        (fun j hj => (chainBranch_index D hS b _).trans (index_of_slot_root _ j hj))
        (fun c i hci => chainBranch_isAncB D hS b _ c i (node_eq_child_of_slot _ c i hci)) hcf
    · obtain ⟨v, hv, htv⟩ := slice_val ht hq
      obtain ⟨v', hv', htv'⟩ := slice_val ht hq'
      rw [htv, htv']
      exact hP.smono _ _ v' v hv' hv (IsAncB.of_isChildOf (chainBranch_isChildOf D hS b q q' hqq))
    · have hb : fixCore D hS fixG b ≠ none := hsF
      obtain ⟨v, hv, htv⟩ := slice_val ht hq
      obtain ⟨v', hv', hτv'⟩ := slice_val hτS hb
      show τS b < t q
      rw [htv, hτv']
      exact hP.smono _ _ v' v hv' hv (chainLone_isAncB D hS b q hl)

end Recon

/-! ### Unit slot weights and strict pins: the unpinned-domain statement -/

section One

variable {w d : ℕ}

theorem kernelNodeWR_one_eq (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Dom : Set (GBranch LG.garden.tree → ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (fix : GBranch LG.garden.tree → Option ℝ) (h : ∀ τ, OnSlice fix τ → (τ ∈ Dom ↔ τ ∈ kDomain LG up s)) :
    kernelNodeWR L γ δ LG A m Dom k₀ nroot nfl (fun _ => 1) fix = kernelNodeWF L γ δ LG A m up s k₀ nroot nfl fix := by
  unfold kernelNodeWR kernelNodeWF
  congr 1
  refine tsum_congr fun κ => ?_
  rw [mul_one]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [ae_onSlice fix] with τ hτ
  by_cases h1 : τ ∈ kDomain LG up s
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem ((h τ hτ).mpr h1)]
  · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h' => h1 ((h τ hτ).mp h'))]

theorem kernelLeavesSelNWFMR_one_eq (L γ δ : ℝ) {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (H : LeafProfiles w d) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration (D.garden hS) d nroot nfl → Prop) (m : (GNode (D.forest hS) → Mom d) → ℂ)
    (Θg : GenDecoration (D.garden hS) d nroot nfl → ℂ) (fixG : GBranch (D.forest hS) → Option ℝ)
    (hP : StrictPins layer tt fixG) :
    kernelLeavesSelNWFMR L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) k₀ nroot nfl sel m
        Θg fixG =
      MkSlotsW.kernelLeavesSelNWFM L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ nroot
        nfl sel m Θg fixG := by
  unfold kernelLeavesSelNWFMR MkSlotsW.kernelLeavesSelNWFM
  congr 1
  refine tsum_congr fun κ => ?_
  split_ifs
  · congr 4
    refine integral_congr_ae ?_
    filter_upwards [ae_onSlice fixG] with τ hτ
    have hg := garden_slice_iff D hS layer hLayer tt fixG hP τ hτ
    by_cases h1 : τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) 0
    · rw [Set.indicator_of_mem h1]
      exact Set.indicator_of_mem (hg.mpr h1) _
    · rw [Set.indicator_of_notMem h1]
      exact Set.indicator_of_notMem (fun h' => h1 (hg.mp h')) _
  · rfl

theorem nativeKernelValue_one_eq {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τS : GBranch S.tree → ℝ)
    (fixG : GBranch (D.forest hS) → Option ℝ) (hP : StrictPins layer tt fixG)
    (hτS : OnSlice (fixCore D hS fixG) τS) (s : ReplacementSlot S) :
    nativeKernelValueNWR D hS L γ δ A W (fun _ _ _ => 1) layer hLayer tt k₀ κ τS fixG s =
      nativeKernelValueNWF D hS L γ δ A W layer hLayer tt k₀ κ τS fixG s := by
  cases s with
  | inl p =>
    exact kernelNodeWR_one_eq L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (nativeDomainWR D hS layer hLayer tt τS fixG (.inl p))
      (fun q => nativeCoupleUpperW D hS tt τS p q.1.1) 0
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0 (fixNative D hS fixG (.inl p))
      (fun t ht => native_slice_iff D hS layer hLayer tt fixG hP τS hτS (.inl p) t ht)
  | inr b =>
    exact kernelNodeWR_one_eq L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a)) (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (nativeDomainWR D hS layer hLayer tt τS fixG (.inr b))
      (fun _ => parentClockWith tt τS b.toNode) (τS b) (k₀ + latticePoint L (κ b.toNode)) (fun _ => 0) 0
      (fixNative D hS fixG (.inr b))
      (fun t ht => native_slice_iff D hS layer hLayer tt fixG hP τS hτS (.inr b) t ht)

/-- **`_one`: unit slot weights and strict pins give the unpinned-domain reduction.** The statement is exactly
`MkSlotsW.kernelLeaves_skeleton_reduction_selNWFM`, derived from the relaxed reduction
`kernelLeaves_skeleton_reduction_selNWFMR` (the left-hand sides agree on the pinned slice of the garden, the
integrands of the right-hand sides on the pinned slice of the core, slot by slot). -/
theorem kernelLeaves_skeleton_reduction_selNWFMR_one {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (fixG : GBranch (D.forest hS) → Option ℝ)
    (hP : StrictPins layer tt fixG)
    (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ) (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    MkSlotsW.kernelLeavesSelNWFM L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z))
        (fun κ => Θ (collapseGenDecoration D hS κ)) fixG =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              ((∏ s, MkSlots.slotFnNWF D hS L γ δ H W layer hLayer fixG s (Represents.slotTs hS tt τ s)
                (k₀ + latticePoint L (κ.1 (Represents.slotNode hS s)))) * Θ κ)) τ
            ∂(fixMeasure (fixCore D hS fixG))
          else 0 := by
  have hB := kernelLeaves_skeleton_reduction_selNWFMR D hS L γ δ H W Cw hCw hW layer hLayer tt k₀ n nfl hH selSk
    fixG hP.relax Θ CΘ hΘ (fun _ _ _ => 1) 1 (fun _ _ _ => by simp)
  simp only [Finset.prod_const_one, mul_one] at hB
  refine (kernelLeavesSelNWFMR_one_eq L γ δ D hS H layer hLayer tt k₀ n nfl _ _ _ fixG hP).symm.trans
    (hB.trans ?_)
  congr 1
  refine tsum_congr fun κ => ?_
  split_ifs
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_onSlice (fixCore D hS fixG)] with τ hτ
    have hprod : (∏ s, slotFnGWFR D hS L γ δ H W (fun _ _ _ => 1) layer hLayer fixG s (Represents.slotTs hS tt τ s)
        (k₀ + latticePoint L (κ.1 (Represents.slotNode hS s)))) =
        ∏ s, MkSlots.slotFnNWF D hS L γ δ H W layer hLayer fixG s (Represents.slotTs hS tt τ s)
          (k₀ + latticePoint L (κ.1 (Represents.slotNode hS s))) := by
      rw [prod_slotFnGWFR, prod_slotFnNWF]
      unfold reducedStarProductLeavesNWF
      exact Finset.prod_congr rfl fun s _ =>
        nativeKernelValue_one_eq D hS L γ δ (fun a => H a.1) W layer hLayer tt k₀ κ.1 τ fixG hP hτ s
    have hc := core_slice_iff D hS layer tt fixG hP τ hτ
    by_cases h1 : τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hc.mpr h1), hprod]
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h' => h1 (hc.mp h'))]
  · rfl

end One

end WaveTurbulence.Flower.MkSlotsB
