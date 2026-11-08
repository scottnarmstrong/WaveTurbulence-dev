/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLbDom

/-! # B3s-HELPER3 (B1, ruling R187): the relaxed domain identity with core lower bounds (assembly)

**`mem_kDomainFix_reconstruction_iff_lb`**: on the pinned slice (`PinnedAt`), under `RelaxPins`, `LbSound` and
`LbComplete`,
`τ ∈ kDomainFix (layeredReconstruction …) (fun b => tt b.1.1) fixG ↔
   nativeCoreClock τ ∈ coreTimeDomainWR … (fixCore fixG) ∩ lbDomC lbC ∧ ∀ s, nativeTimeRestriction τ s ∈ nativeDomainWRL … s`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology Set MeasureTheory
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (tt : Fin w → ℝ) (fixG : GBranch (D.forest hS) → Option ℝ)

theorem clockFree_iff_exists {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) (a : GNode tree) :
    clockFree fix a ↔ ∃ c i, nodeToSlot a = .inr (c, i) ∧ fix c = none := by
  unfold clockFree
  rcases nodeToSlot a with j | ⟨c, i⟩
  · simp
  · exact ⟨fun h => ⟨c, i, rfl, h⟩, fun ⟨c', i', h1, h2⟩ => by
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h1; rw [h1.1]; exact h2⟩

theorem parentClockWith_of_slot {tree : Fin w → TTree} (top : Fin w → ℝ) (τ : GBranch tree → ℝ) (a : GNode tree)
    (c : GBranch tree) (i : Fin 3) (h : nodeToSlot a = .inr (c, i)) : parentClockWith top τ a = τ c := by
  unfold parentClockWith; rw [h]

/-- The clock constraints of the pinned branches of one slot, from the lower bounds (induction on the depth). -/
theorem native_clock_of_lb (hP : RelaxPins layer tt fixG) (lbC : GBranch S.tree → Option ℝ)
    (hLC : LbComplete D hS fixG lbC) (τ : GBranch (D.forest hS) → ℝ) (hτ : PinnedAt fixG τ)
    (hlb : nativeCoreClock D hS τ ∈ lbDomC lbC) (s : ReplacementSlot S)
    (hs : nativeTimeRestriction D hS τ s ∈ nativeDomainWRL D hS layer hLayer tt fixG (nativeCoreClock D hS τ) s) :
    nativeTimeRestriction D hS τ s ∈ nativeDomainWR D hS layer hLayer tt (nativeCoreClock D hS τ) fixG s := by
  cases s with
  | inl p =>
    refine (mem_kDomainR_iff_noClock _ _ _ _ _ _ _).2 ⟨hs, fun q hq hu => ?_⟩
    refine pinned_below_clock _ _ _ _ _ _ hs (fun q => clockFree (MkSlots.fixCore D hS fixG)
      (coupleLeafNode hS p q.1.1)) (fun b b' hbb' h => by rw [← hbb'.1]; exact h)
      (fun b b' hbb' => by show nativeCoupleUpperW D hS tt _ p b'.1.1 = nativeCoupleUpperW D hS tt _ p b.1.1
                           rw [hbb'.1])
      (fun b v hv => hτ.pin _ v hv)
      (fun b b' v v' hbb' hv' hv => hP.mono _ _ v' v hv' hv
        (IsAncB.of_isChildOf (coupleBranch_isChildOf D hS p b b' hbb')))
      (fun b v hu hb hv => ?_) _ q rfl hu hq
    obtain ⟨c, i, hci, hc⟩ := (clockFree_iff_exists _ _).1 hu
    obtain ⟨x, hx, hvx⟩ := hLC (.inl p) b v c i hb hv (node_eq_child_of_slot _ c i hci) hc
    show v < nativeCoupleUpperW D hS tt (nativeCoreClock D hS τ) p b.1.1
    rw [nativeCoupleUpperW_eq, parentClockWith_of_slot tt _ _ c i hci]
    exact lt_of_le_of_lt hvx (hlb c x hx)
  | inr b =>
    refine (mem_kDomainR_iff_noClock _ _ _ _ _ _ _).2 ⟨hs, fun q hq hu => ?_⟩
    refine pinned_below_clock _ _ _ _ _ _ hs (fun _ => clockFree (MkSlots.fixCore D hS fixG) b.toNode)
      (fun _ _ _ h => h) (fun _ _ _ => rfl)
      (fun q v hv => hτ.pin _ v hv)
      (fun q q' v v' hqq' hv' hv => hP.mono _ _ v' v hv' hv
        (IsAncB.of_isChildOf (chainBranch_isChildOf D hS b q q' hqq')))
      (fun q v hu hq hv => ?_) _ q rfl hu hq
    obtain ⟨c, i, hci, hc⟩ := (clockFree_iff_exists _ _).1 hu
    obtain ⟨x, hx, hvx⟩ := hLC (.inr b) q v c i hq hv (node_eq_child_of_slot _ c i hci) hc
    show v < parentClockWith tt (nativeCoreClock D hS τ) b.toNode
    rw [parentClockWith_of_slot tt _ _ c i hci]
    exact lt_of_le_of_lt hvx (hlb c x hx)

/-- **The relaxed domain identity with core lower bounds** (R187). -/
theorem mem_kDomainFix_reconstruction_iff_lb (hP : RelaxPins layer tt fixG) (lbC : GBranch S.tree → Option ℝ)
    (hLS : LbSound D hS fixG lbC) (hLC : LbComplete D hS fixG lbC) (τ : GBranch (D.forest hS) → ℝ)
    (hτ : PinnedAt fixG τ) :
    τ ∈ kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG ↔
      nativeCoreClock D hS τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt
          (MkSlots.fixCore D hS fixG) ∩ lbDomC lbC ∧
        ∀ s, nativeTimeRestriction D hS τ s ∈ nativeDomainWRL D hS layer hLayer tt fixG (nativeCoreClock D hS τ) s := by
  rw [mem_kDomainFix_reconstruction_iff D hS layer hLayer tt fixG hP τ hτ]
  constructor
  · rintro ⟨hc, hn⟩
    refine ⟨⟨hc, fun c x hx => ?_⟩, fun s => ?_⟩
    · obtain ⟨s, q, i, htop, hq, hcl, hcf⟩ := hLS c x hx
      have hu : clockFree (MkSlots.fixCore D hS fixG) (nativeClockNode D hS s q) := by
        rw [hcl, clockFree_child]; exact hcf
      have hk := hn s
      cases s with
      | inl p =>
        have h := ((mem_kDomainR_iff_noClock _ _ _ _ _ _ _).1 hk).2 q (by rw [hq]; simp) hu
        have hv : nativeTimeRestriction D hS τ (.inl p) q = x := hτ.pin _ x hq
        rw [hv, nativeCoupleUpperW_eq] at h
        have hcl' : coupleLeafNode hS p q.1.1 = c.child i := hcl
        rw [hcl', parentClockWith_child] at h
        exact h
      | inr b =>
        have h := ((mem_kDomainR_iff_noClock _ _ _ _ _ _ _).1 hk).2 q (by rw [hq]; simp) hu
        have hv : nativeTimeRestriction D hS τ (.inr b) q = x := hτ.pin _ x hq
        rw [hv] at h
        have hcl' : b.toNode = c.child i := hcl
        rw [hcl', parentClockWith_child] at h
        exact h
    · cases s with
      | inl p => exact ((mem_kDomainR_iff_noClock _ _ _ _ _ _ _).1 (hn (.inl p))).1
      | inr b => exact ((mem_kDomainR_iff_noClock _ _ _ _ _ _ _).1 (hn (.inr b))).1
  · rintro ⟨⟨hc, hlb⟩, hn⟩
    exact ⟨hc, fun s => native_clock_of_lb D hS layer hLayer tt fixG hP lbC hLC τ hτ hlb s (hn s)⟩

end WaveTurbulence.Flower.MkSlotsB
