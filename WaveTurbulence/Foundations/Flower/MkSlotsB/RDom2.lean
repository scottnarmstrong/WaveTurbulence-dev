/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RDom

/-! # B3s-HELPER3: the relaxed time-domain identity of a reconstruction (native slots, assembly)

* `couple_eventually_iff`, `chain_eventually_iff`: the native slot domains at the shifted time vector are eventually
  the relaxed native domains `nativeDomainWR`;
* **`mem_kDomainFix_reconstruction_iff`**: the relaxed twin of main's `nativeTimeDomain_reconstructionW`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology Set MeasureTheory
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (tt : Fin w → ℝ) (fixG : GBranch (D.forest hS) → Option ℝ)

/-- A pinned branch below a clock that is not free. -/
theorem clock_pinned_cases {τ : GBranch (D.forest hS) → ℝ} (hP : RelaxPins layer tt fixG) (hτ : PinnedAt fixG τ)
    (a : GNode S.tree) (x : GBranch (D.forest hS)) (hx : fixG x ≠ none)
    (hidx : ∀ j, nodeToSlot a = .inl j → x.1.1 = j)
    (hanc : ∀ c i, nodeToSlot a = .inr (c, i) → IsAncB (D.coreBranch hS c) x)
    (hcf : ¬ clockFree (MkSlots.fixCore D hS fixG) a) :
    τ x < parentClockWith tt (nativeCoreClock D hS τ) a ∨
      (τ x = parentClockWith tt (nativeCoreClock D hS τ) a ∧
        parentClockWith 0 (fun c => alphaOf fixG (D.coreBranch hS c)) a < alphaOf fixG x) := by
  obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ hx
  rcases hs : nodeToSlot a with j | ⟨c, i⟩
  · have hpc : parentClockWith tt (nativeCoreClock D hS τ) a = tt j := by unfold parentClockWith; rw [hs]
    have hpa : parentClockWith 0 (fun c => alphaOf fixG (D.coreBranch hS c)) a = 0 := by
      unfold parentClockWith; rw [hs]; rfl
    have hle := (hP.val x v hv).2.2
    rw [hidx j hs] at hle
    rw [hpc, hpa, hτv]
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, alphaOf_pos hx⟩
  · have hc : MkSlots.fixCore D hS fixG c ≠ none := by
      intro h; apply hcf; unfold clockFree; rw [hs]; exact h
    obtain ⟨v', hv', hτv'⟩ := pinned_val D hS hτ hc
    have hpc : parentClockWith tt (nativeCoreClock D hS τ) a = τ (D.coreBranch hS c) := by
      unfold parentClockWith; rw [hs]; rfl
    have hpa : parentClockWith 0 (fun c => alphaOf fixG (D.coreBranch hS c)) a = alphaOf fixG (D.coreBranch hS c) := by
      unfold parentClockWith; rw [hs]
    have ha := hanc c i hs
    have hm := hP.mono _ _ v v' hv hv' ha
    rw [hpc, hpa, hτv, hτv']
    rcases lt_or_eq_of_le hm with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, alphaOf_lt ha hc hx⟩

theorem clockFree_ne {τ : GBranch (D.forest hS) → ℝ} (hτ : PinnedAt fixG τ) (a : GNode S.tree)
    (x : GBranch (D.forest hS)) (hx : fixG x ≠ none) (hcf : clockFree (MkSlots.fixCore D hS fixG) a) :
    τ x ≠ parentClockWith tt (nativeCoreClock D hS τ) a := by
  obtain ⟨c, hc, hpc⟩ := clockFree_spec _ a hcf
  rw [hpc]
  exact (hτ.gen _ _ hc hx).symm

theorem clockFree_alpha (a : GNode S.tree) (hcf : clockFree (MkSlots.fixCore D hS fixG) a) :
    parentClockWith 0 (fun c => alphaOf fixG (D.coreBranch hS c)) a = 0 := by
  obtain ⟨c, hc, hpc⟩ := clockFree_spec _ a hcf
  rw [hpc]
  exact alphaOf_none hc

/-- The native couple step. -/
theorem couple_eventually_iff (hP : RelaxPins layer tt fixG) (τ : GBranch (D.forest hS) → ℝ) (hτ : PinnedAt fixG τ)
    (p : SourcePair S) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), nativeTimeRestriction D hS (fun b => τ b - ε * alphaOf fixG b) (.inl p) ∈
        nativeDomainW D hS layer hLayer tt (nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b)) (.inl p)) ↔
      nativeTimeRestriction D hS τ (.inl p) ∈ nativeDomainWR D hS layer hLayer tt (nativeCoreClock D hS τ) fixG (.inl p) := by
  set LGc := nativeCoupleLayered D hS layer hLayer p
  set τS := nativeCoreClock D hS τ
  set αS : GBranch S.tree → ℝ := fun c => alphaOf fixG (D.coreBranch hS c) with hαS
  have hset : ∀ ε : ℝ, (nativeTimeRestriction D hS (fun b => τ b - ε * alphaOf fixG b) (.inl p) ∈
        nativeDomainW D hS layer hLayer tt (nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b)) (.inl p)) ↔
      (fun q : GBranch LGc.garden.tree => nativeCoupleClock D hS τ p q - ε * alphaOf fixG (coupleContextBranch D hS p q))
        ∈ kDomain LGc (fun q => parentClockWith tt τS (coupleLeafNode hS p q.1.1) -
          ε * parentClockWith 0 αS (coupleLeafNode hS p q.1.1)) (0 - ε * 0) := by
    intro ε
    have hu : (fun q : GBranch LGc.garden.tree =>
        nativeCoupleUpperW D hS tt (nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b)) p q.1.1) =
        fun q => parentClockWith tt τS (coupleLeafNode hS p q.1.1) -
          ε * parentClockWith 0 αS (coupleLeafNode hS p q.1.1) := by
      funext q
      rw [nativeCoupleUpperW_eq]
      exact parentClockWith_shift tt τS αS ε _
    rw [mul_zero, sub_zero]
    show _ ∈ kDomain LGc (fun q => nativeCoupleUpperW D hS tt
      (nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b)) p q.1.1) 0 ↔ _
    rw [hu]
    exact Iff.rfl
  rw [Filter.eventually_congr (Filter.Eventually.of_forall hset)]
  have hup : (fun q : GBranch LGc.garden.tree => nativeCoupleUpperW D hS tt τS p q.1.1) =
      fun q => parentClockWith tt τS (coupleLeafNode hS p q.1.1) := by
    funext q; exact nativeCoupleUpperW_eq D hS tt τS p q.1.1
  show _ ↔ nativeCoupleClock D hS τ p ∈ kDomainR LGc (fun q => nativeCoupleUpperW D hS tt τS p q.1.1) 0
    (MkSlots.fixNative D hS fixG (.inl p)) (fun q => clockFree (MkSlots.fixCore D hS fixG) (coupleLeafNode hS p q.1.1))
    False
  rw [hup]
  have hp : LGc.garden.IsPlain :=
    Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS) (nativeCoupleForest D hS p)
      (nativeCoupleForest_closed D hS p)
  exact eventually_kDomain_shift_iff LGc _ _ 0 0 (MkSlots.fixNative D hS fixG (.inl p)) _ False
    (fun q => alphaOf fixG (coupleContextBranch D hS p q)) (nativeCoupleClock D hS τ p)
    (fun q h => alphaOf_none h) (fun q => alphaOf_nonneg _ _) (fun q h => alphaOf_pos h)
    (fun q => parentClockWith_zero_nonneg αS (fun c => alphaOf_nonneg _ _) _)
    (fun q hq => clockFree_alpha D hS fixG _ hq) (le_refl 0) (fun h => h.elim)
    (fun x y hx hy => hτ.gen _ _ hx hy)
    (fun q hq => by
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ (b := coupleContextBranch D hS p q) hq
      have := hP.val _ v hv
      show (layer (coupleContextBranch D hS p q).toNode : ℝ) < τ (coupleContextBranch D hS p q) ∧
        τ (coupleContextBranch D hS p q) ≤ (layer (coupleContextBranch D hS p q).toNode : ℝ) + 1
      rw [hτv]
      exact ⟨this.1, this.2.1⟩)
    (fun q hq hcf => clock_pinned_cases D hS layer tt fixG hP hτ (coupleLeafNode hS p q.1.1)
      (coupleContextBranch D hS p q) hq
      (fun j hj => (coupleBranch_index D hS p q).trans (index_of_slot_root _ j hj))
      (fun c i hci => coupleBranch_isAncB D hS p q c i (node_eq_child_of_slot _ c i hci)) hcf)
    (fun q hq hcf => clockFree_ne D hS tt fixG hτ _ _ hq hcf)
    (fun q q' hqq hq' hq => by
      have ha := IsAncB.of_isChildOf (coupleBranch_isChildOf D hS p q q' hqq)
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ (b := coupleContextBranch D hS p q) hq
      obtain ⟨v', hv', hτv'⟩ := pinned_val D hS hτ (b := coupleContextBranch D hS p q') hq'
      have hm := hP.mono _ _ v' v hv' hv ha
      show τ (coupleContextBranch D hS p q') < τ (coupleContextBranch D hS p q) ∨
        (τ (coupleContextBranch D hS p q') = τ (coupleContextBranch D hS p q) ∧ _)
      rw [hτv, hτv']
      rcases lt_or_eq_of_le hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, alphaOf_lt ha hq hq'⟩)
    (fun q hl => (not_loneParent_of_plain _ hp q hl).elim)
    (fun q hl => (not_loneParent_of_plain _ hp q hl).elim)

/-- The native chain step. -/
theorem chain_eventually_iff (hP : RelaxPins layer tt fixG) (τ : GBranch (D.forest hS) → ℝ) (hτ : PinnedAt fixG τ)
    (b : GBranch S.tree) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), nativeTimeRestriction D hS (fun b => τ b - ε * alphaOf fixG b) (.inr b) ∈
        nativeDomainW D hS layer hLayer tt (nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b)) (.inr b)) ↔
      nativeTimeRestriction D hS τ (.inr b) ∈ nativeDomainWR D hS layer hLayer tt (nativeCoreClock D hS τ) fixG (.inr b) := by
  set LGt := nativeChainLayered D hS layer hLayer b
  set τS := nativeCoreClock D hS τ
  set αS : GBranch S.tree → ℝ := fun c => alphaOf fixG (D.coreBranch hS c) with hαS
  have hset : ∀ ε : ℝ, (nativeTimeRestriction D hS (fun b => τ b - ε * alphaOf fixG b) (.inr b) ∈
        nativeDomainW D hS layer hLayer tt (nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b)) (.inr b)) ↔
      (fun q : GBranch LGt.garden.tree => nativeChainClock D hS τ b q -
          ε * alphaOf fixG (chainContextBranch D hS b ⟨q.1.2, q.2⟩))
        ∈ kDomain LGt (fun _ => parentClockWith tt τS b.toNode - ε * parentClockWith 0 αS b.toNode)
          (τS b - ε * αS b) := by
    intro ε
    have hu : (fun _ : GBranch LGt.garden.tree =>
        parentClockWith tt (nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b)) b.toNode) =
        fun _ => parentClockWith tt τS b.toNode - ε * parentClockWith 0 αS b.toNode := by
      funext q
      exact parentClockWith_shift tt τS αS ε _
    show _ ∈ kDomain LGt (fun _ => parentClockWith tt
      (nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b)) b.toNode) (τS b - ε * αS b) ↔ _
    rw [hu]
    exact Iff.rfl
  rw [Filter.eventually_congr (Filter.Eventually.of_forall hset)]
  show _ ↔ nativeChainClock D hS τ b ∈ kDomainR LGt (fun _ => parentClockWith tt τS b.toNode) (τS b)
    (MkSlots.fixNative D hS fixG (.inr b)) (fun _ => clockFree (MkSlots.fixCore D hS fixG) b.toNode)
    (MkSlots.fixCore D hS fixG b = none)
  exact eventually_kDomain_shift_iff LGt _ _ _ _ (MkSlots.fixNative D hS fixG (.inr b)) _ _
    (fun q => alphaOf fixG (chainContextBranch D hS b ⟨q.1.2, q.2⟩)) (nativeChainClock D hS τ b)
    (fun q h => alphaOf_none h) (fun q => alphaOf_nonneg _ _) (fun q h => alphaOf_pos h)
    (fun q => parentClockWith_zero_nonneg αS (fun c => alphaOf_nonneg _ _) _)
    (fun q hq => clockFree_alpha D hS fixG _ hq) (alphaOf_nonneg _ _) (fun h => alphaOf_none h)
    (fun x y hx hy => hτ.gen _ _ hx hy)
    (fun q hq => by
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ (b := chainContextBranch D hS b ⟨q.1.2, q.2⟩) hq
      have := hP.val _ v hv
      show (layer (chainContextBranch D hS b ⟨q.1.2, q.2⟩).toNode : ℝ) < τ (chainContextBranch D hS b ⟨q.1.2, q.2⟩) ∧
        τ (chainContextBranch D hS b ⟨q.1.2, q.2⟩) ≤
          (layer (chainContextBranch D hS b ⟨q.1.2, q.2⟩).toNode : ℝ) + 1
      rw [hτv]
      exact ⟨this.1, this.2.1⟩)
    (fun q hq hcf => clock_pinned_cases D hS layer tt fixG hP hτ b.toNode
      (chainContextBranch D hS b ⟨q.1.2, q.2⟩) hq
      (fun j hj => (chainBranch_index D hS b _).trans (index_of_slot_root _ j hj))
      (fun c i hci => chainBranch_isAncB D hS b _ c i (node_eq_child_of_slot _ c i hci)) hcf)
    (fun q hq hcf => clockFree_ne D hS tt fixG hτ _ _ hq hcf)
    (fun q q' hqq hq' hq => by
      have ha := IsAncB.of_isChildOf (chainBranch_isChildOf D hS b q q' hqq)
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ (b := chainContextBranch D hS b ⟨q.1.2, q.2⟩) hq
      obtain ⟨v', hv', hτv'⟩ := pinned_val D hS hτ (b := chainContextBranch D hS b ⟨q'.1.2, q'.2⟩) hq'
      have hm := hP.mono _ _ v' v hv' hv ha
      show τ (chainContextBranch D hS b ⟨q'.1.2, q'.2⟩) < τ (chainContextBranch D hS b ⟨q.1.2, q.2⟩) ∨
        (τ (chainContextBranch D hS b ⟨q'.1.2, q'.2⟩) = τ (chainContextBranch D hS b ⟨q.1.2, q.2⟩) ∧ _)
      rw [hτv, hτv']
      rcases lt_or_eq_of_le hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, alphaOf_lt ha hq hq'⟩)
    (fun q hl hq hsF => by
      have hb : fixG (D.coreBranch hS b) ≠ none := hsF
      have ha := chainLone_isAncB D hS b q hl
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ (b := chainContextBranch D hS b ⟨q.1.2, q.2⟩) hq
      obtain ⟨v', hv', hτv'⟩ := pinned_val D hS hτ hb
      have hm := hP.mono _ _ v' v hv' hv ha
      show τ (D.coreBranch hS b) < τ (chainContextBranch D hS b ⟨q.1.2, q.2⟩) ∨
        (τ (D.coreBranch hS b) = τ (chainContextBranch D hS b ⟨q.1.2, q.2⟩) ∧ _)
      rw [hτv, hτv']
      rcases lt_or_eq_of_le hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, alphaOf_lt ha hq hb⟩)
    (fun q hl hq hsF => by
      have hb : fixG (D.coreBranch hS b) ≠ none := hsF
      exact (hτ.gen _ _ hq hb).symm)

/-- **The relaxed time-domain identity of a reconstruction** (relaxed `nativeTimeDomain_reconstructionW`). -/
theorem mem_kDomainFix_reconstruction_iff (hP : RelaxPins layer tt fixG) (τ : GBranch (D.forest hS) → ℝ)
    (hτ : PinnedAt fixG τ) :
    τ ∈ kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG ↔
      nativeCoreClock D hS τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt
          (MkSlots.fixCore D hS fixG) ∧
        ∀ s, nativeTimeRestriction D hS τ s ∈ nativeDomainWR D hS layer hLayer tt (nativeCoreClock D hS τ) fixG s := by
  rw [kDomainFix_iff_eventually D hS layer hLayer tt fixG hP τ hτ]
  rw [Filter.eventually_congr (Filter.Eventually.of_forall fun ε =>
    nativeTimeDomain_reconstructionW D hS layer hLayer tt (fun b => τ b - ε * alphaOf fixG b))]
  rw [Filter.eventually_and, Filter.eventually_all]
  refine and_congr (core_eventually_iff D hS layer tt fixG hP τ hτ) (forall_congr' fun s => ?_)
  cases s with
  | inl p => exact couple_eventually_iff D hS layer hLayer tt fixG hP τ hτ p
  | inr b => exact chain_eventually_iff D hS layer hLayer tt fixG hP τ hτ b

end WaveTurbulence.Flower.MkSlotsB
