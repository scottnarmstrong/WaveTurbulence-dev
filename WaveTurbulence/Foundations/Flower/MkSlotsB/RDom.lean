/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RShift
public import WaveTurbulence.Foundations.Flower.MkSlots.TopPin

/-! # B3s-HELPER3: the relaxed time-domain identity of a reconstruction

Main's `RegRedLeaf.nativeTimeDomain_reconstructionW` splits the (unpinned) time domain of a reconstructed garden into
the skeleton core domain and the native slot domains. Its relaxed twin, for pins `fixG` on the reconstructed garden:

  `τ ∈ kDomainFix (layeredReconstruction …) (fun b => tt b.1.1) fixG ↔
     nativeCoreClock τ ∈ coreTimeDomainWR … (fixCore fixG) ∧ ∀ s, nativeTimeRestriction τ s ∈ nativeDomainWR … fixG s`

for every `τ` on the pinned slice whose free times differ from the pinned values (`PinnedAt`, a `fixMeasure fixG`-full
set: `ae_pinnedAt`), under the pin hypotheses `RelaxPins` (pins in their windows and below the upper times, and
monotone along ancestry). Proof: both sides are the corresponding unpinned memberships at `τ - ε • alphaOf fixG` for
small `ε > 0` (`RShift`), and main's identity holds at every time vector.

Monotonicity is necessary (see PROGRESS.md): a non-monotone pinned pair inside a chain object breaks the
transitivity by which the core order follows from the chain constraints.

* `IsAncB`, `alphaOf`, `RelaxPins`, `PinnedAt`, `ae_pinnedAt`;
* reconstruction ancestry: `coreBranch_isAncB`, `coupleBranch_isAncB`, `chainBranch_isAncB`, `chainLone_isAncB`;
* **`mem_kDomainFix_reconstruction_iff`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology Set MeasureTheory
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-! ## Ancestry, shift weights, pin hypotheses -/

/-- `y` is a strict ancestor of `x` (same tree, proper prefix address). -/
def IsAncB {tree : Fin w → TTree} (y x : GBranch tree) : Prop :=
  y.1.1 = x.1.1 ∧ ∃ l : List (Fin 3), l ≠ [] ∧ x.1.2 = y.1.2 ++ l

theorem IsAncB.of_isChildOf {tree : Fin w → TTree} {b b' : GBranch tree} (h : b'.IsChildOf b) : IsAncB b b' := by
  obtain ⟨h1, i, hi⟩ := h
  exact ⟨h1.symm, [i], by simp, hi⟩

theorem IsAncB.length_lt {tree : Fin w → TTree} {y x : GBranch tree} (h : IsAncB y x) :
    y.1.2.length < x.1.2.length := by
  obtain ⟨-, l, hl, he⟩ := h
  rw [he, List.length_append]
  have := List.length_pos_iff_ne_nil.mpr hl
  omega

/-- The shift weights of the pins: `0` at free branches, `depth + 1` at pinned ones. -/
def alphaOf {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) (b : GBranch tree) : ℝ :=
  if fix b = none then 0 else (b.1.2.length : ℝ) + 1

theorem alphaOf_none {tree : Fin w → TTree} {fix : GBranch tree → Option ℝ} {b : GBranch tree} (h : fix b = none) :
    alphaOf fix b = 0 := by simp [alphaOf, h]

theorem alphaOf_nonneg {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) (b : GBranch tree) :
    0 ≤ alphaOf fix b := by
  unfold alphaOf
  split_ifs
  · exact le_refl 0
  · positivity

theorem alphaOf_pos {tree : Fin w → TTree} {fix : GBranch tree → Option ℝ} {b : GBranch tree} (h : fix b ≠ none) :
    0 < alphaOf fix b := by
  simp only [alphaOf, h, ite_false]
  positivity

theorem alphaOf_lt {tree : Fin w → TTree} {fix : GBranch tree → Option ℝ} {y x : GBranch tree} (h : IsAncB y x)
    (hy : fix y ≠ none) (hx : fix x ≠ none) : alphaOf fix y < alphaOf fix x := by
  simp only [alphaOf, hy, hx, ite_false]
  have := h.length_lt
  have : (y.1.2.length : ℝ) < x.1.2.length := by exact_mod_cast this
  linarith

/-- **The pin hypotheses of the relaxed reduction**: pins in their (half-open) layer windows and below the upper time
of their tree, and monotone along ancestry. -/
structure RelaxPins {tree : Fin w → TTree} (layer : GNode tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ) : Prop where
  val : ∀ b v, fix b = some v → (layer b.toNode : ℝ) < v ∧ v ≤ layer b.toNode + 1 ∧ v ≤ tt b.1.1
  mono : ∀ x y v v', fix x = some v → fix y = some v' → IsAncB y x → v ≤ v'

/-- A time vector on the pinned slice whose free times differ from the pinned times. -/
structure PinnedAt {ι : Type*} (fix : ι → Option ℝ) (τ : ι → ℝ) : Prop where
  pin : ∀ b v, fix b = some v → τ b = v
  gen : ∀ x y, fix x = none → fix y ≠ none → τ x ≠ τ y

theorem ae_ne_of_free {ι : Type*} [Fintype ι] (fix : ι → Option ℝ) {x : ι} (hx : fix x = none) (v : ℝ) :
    ∀ᵐ τ ∂(MkSlots.fixMeasure fix), τ x ≠ v := by
  rw [ae_iff]
  have : {τ : ι → ℝ | ¬ τ x ≠ v} = Function.eval x ⁻¹' ({v} : Set ℝ) := by ext τ; simp
  rw [this]
  refine Measure.pi_eval_preimage_null _ ?_
  simp only [MkSlots.fixFactor, hx, Option.elim]
  exact Real.volume_singleton

/-- **Almost every time vector is on the pinned slice with distinct free times.** -/
theorem ae_pinnedAt {ι : Type*} [Fintype ι] (fix : ι → Option ℝ) :
    ∀ᵐ τ ∂(MkSlots.fixMeasure fix), PinnedAt fix τ := by
  have h1 : ∀ᵐ τ ∂(MkSlots.fixMeasure fix), ∀ b v, fix b = some v → τ b = v := by
    rw [ae_all_iff]
    intro b
    cases hb : fix b with
    | none => exact ae_of_all _ (fun τ v h => by simp at h)
    | some v0 =>
      filter_upwards [MkSlots.ae_fixMeasure_pinned fix hb] with τ hτ v hv
      rw [hτ]
      exact Option.some.inj hv
  have h2 : ∀ᵐ τ ∂(MkSlots.fixMeasure fix), ∀ x y, fix x = none → fix y ≠ none → τ x ≠ τ y := by
    rw [ae_all_iff]
    intro x
    rw [ae_all_iff]
    intro y
    by_cases hx : fix x = none
    · cases hy : fix y with
      | none => exact ae_of_all _ (fun τ _ h => absurd rfl h)
      | some v =>
        filter_upwards [ae_ne_of_free fix hx v, MkSlots.ae_fixMeasure_pinned fix hy] with τ h h' _ _
        rw [h']
        exact h
    · exact ae_of_all _ (fun τ h => absurd h hx)
  filter_upwards [h1, h2] with τ ha hb
  exact ⟨ha, hb⟩

/-! ## Ancestry in a reconstruction -/

section Recon

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

theorem node_eq_child_of_slot {tree : Fin w → TTree} (a : GNode tree) (c : GBranch tree) (i : Fin 3)
    (h : nodeToSlot a = .inr (c, i)) : a = c.child i := by
  have := (nodeSlotEquiv tree).left_inv a
  change slotToNode tree (nodeToSlot a) = a at this
  rw [h] at this
  exact this.symm

theorem index_of_slot_root {tree : Fin w → TTree} (a : GNode tree) (j : Fin w) (h : nodeToSlot a = .inl j) :
    a.1.1 = j := by
  unfold nodeToSlot at h
  split_ifs at h
  exact Sum.inl.inj h

theorem coreBranch_index (b : GBranch S.tree) : (D.coreBranch hS b).1.1 = b.1.1 :=
  inflatedPosition_index S D.tree b.toNode

theorem coreBranch_isAncB (c : GBranch S.tree) (i : Fin 3) (b : GBranch S.tree) (hb : b.toNode = c.child i) :
    IsAncB (D.coreBranch hS c) (D.coreBranch hS b) := by
  have h1 : (D.coreBranch hS b).1 = addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath := rfl
  have h2 : (D.coreBranch hS c).1 = D.corePosition c := rfl
  rw [hb, D.core_child_position c i] at h1
  refine ⟨?_, [i] ++ (D.tree b).lonePath, by simp, ?_⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2]; simp [addrExt, List.append_assoc]

theorem nativeCoupleForest_root (p : SourcePair S) (j : Fin 2) :
    (nativeCoupleForest D hS p).root j = attachedNode D hS (coupleLeafNode hS p j) := by
  fin_cases j <;> rfl

theorem coupleBranch_index (p : SourcePair S) (q : GBranch (decodedCouple (D.couple p)).tree) :
    (coupleContextBranch D hS p q).1.1 = (coupleLeafNode hS p q.1.1).1.1 := by
  change ((nativeCoupleForest D hS p).root q.1.1).1.1 = _
  rw [nativeCoupleForest_root]
  exact inflatedPosition_index S D.tree _

theorem coupleBranch_isAncB (p : SourcePair S) (q : GBranch (decodedCouple (D.couple p)).tree) (c : GBranch S.tree)
    (i : Fin 3) (hc : coupleLeafNode hS p q.1.1 = c.child i) :
    IsAncB (D.coreBranch hS c) (coupleContextBranch D hS p q) := by
  have h1 : (coupleContextBranch D hS p q).1 =
      (((nativeCoupleForest D hS p).root q.1.1).1.1, ((nativeCoupleForest D hS p).root q.1.1).1.2 ++ q.1.2) := rfl
  have h2 : ((nativeCoupleForest D hS p).root q.1.1).1 = addrExt (D.corePosition c) [i] := by
    rw [nativeCoupleForest_root, hc]
    exact D.core_child_position c i
  have h3 : (D.coreBranch hS c).1 = D.corePosition c := rfl
  refine ⟨?_, [i] ++ q.1.2, by simp, ?_⟩
  · rw [h1, h2, h3]; rfl
  · rw [h1, h2, h3]; simp [addrExt, List.append_assoc]

theorem coupleBranch_isChildOf (p : SourcePair S) (q q' : GBranch (decodedCouple (D.couple p)).tree)
    (h : q'.IsChildOf q) : (coupleContextBranch D hS p q').IsChildOf (coupleContextBranch D hS p q) := by
  obtain ⟨h1, i, hi⟩ := h
  have e1 : (coupleContextBranch D hS p q').1 =
      (((nativeCoupleForest D hS p).root q'.1.1).1.1, ((nativeCoupleForest D hS p).root q'.1.1).1.2 ++ q'.1.2) := rfl
  have e2 : (coupleContextBranch D hS p q).1 =
      (((nativeCoupleForest D hS p).root q.1.1).1.1, ((nativeCoupleForest D hS p).root q.1.1).1.2 ++ q.1.2) := rfl
  refine ⟨?_, i, ?_⟩
  · rw [e1, e2, h1]
  · rw [e1, e2, h1, hi, List.append_assoc]

theorem chainBranch_index (b : GBranch S.tree) (q : ChainBranchPath D b) :
    (chainContextBranch D hS b q).1.1 = b.1.1 :=
  inflatedPosition_index S D.tree b.toNode

theorem chainBranch_isAncB (b : GBranch S.tree) (q : ChainBranchPath D b) (c : GBranch S.tree) (i : Fin 3)
    (hb : b.toNode = c.child i) : IsAncB (D.coreBranch hS c) (chainContextBranch D hS b q) := by
  have h1 : (chainContextBranch D hS b q).1 = addrExt (inflatedPosition S D.tree b.toNode) q.1 := rfl
  have h3 : (D.coreBranch hS c).1 = D.corePosition c := rfl
  rw [hb, D.core_child_position c i] at h1
  refine ⟨?_, [i] ++ q.1, by simp, ?_⟩
  · rw [h1, h3]; rfl
  · rw [h1, h3]; simp [addrExt, List.append_assoc]

theorem chainBranch_isChildOf (b : GBranch S.tree) (q q' : GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (h : q'.IsChildOf q) :
    (chainContextBranch D hS b ⟨q'.1.2, q'.2⟩).IsChildOf (chainContextBranch D hS b ⟨q.1.2, q.2⟩) := by
  obtain ⟨-, i, hi⟩ := h
  refine ⟨rfl, i, ?_⟩
  change (inflatedPosition S D.tree b.toNode).2 ++ q'.1.2 = ((inflatedPosition S D.tree b.toNode).2 ++ q.1.2) ++ [i]
  rw [hi, List.append_assoc]

theorem chainLone_isAncB (b : GBranch S.tree) (q : GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (hq : (decodedTree (D.tree b) (nodeSign S.sig b.1)).IsLoneParent q) :
    IsAncB (chainContextBranch D hS b ⟨q.1.2, q.2⟩) (D.coreBranch hS b) := by
  obtain ⟨ℓ, hℓ, -, i, hi⟩ := hq
  have hl := (decodesTree_lone_iff (decodedTree_decodes _ _) ℓ).mp hℓ
  have h1 : (D.coreBranch hS b).1 = addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath := rfl
  have h2 : (chainContextBranch D hS b ⟨q.1.2, q.2⟩).1 = addrExt (inflatedPosition S D.tree b.toNode) q.1.2 := rfl
  refine ⟨?_, [i], by simp, ?_⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2, ← hl, hi]; simp [addrExt, List.append_assoc]

end Recon

/-! ## The relaxed reconstruction identity -/

section Main

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (tt : Fin w → ℝ) (fixG : GBranch (D.forest hS) → Option ℝ)

theorem pinned_val {fixG : GBranch (D.forest hS) → Option ℝ} {τ : GBranch (D.forest hS) → ℝ}
    (hτ : PinnedAt fixG τ) {b : GBranch (D.forest hS)} (hb : fixG b ≠ none) : ∃ v, fixG b = some v ∧ τ b = v := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
  exact ⟨v, hv, hτ.pin b v hv⟩

/-- The garden step: `kDomainFix` of the reconstruction is the shifted unpinned `kDomain`. -/
theorem kDomainFix_iff_eventually (hP : RelaxPins layer tt fixG) (τ : GBranch (D.forest hS) → ℝ)
    (hτ : PinnedAt fixG τ) :
    τ ∈ kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG ↔
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), (fun b => τ b - ε * alphaOf fixG b) ∈
        kDomain (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) 0 := by
  have hplain := D.garden_plain hS
  have h := eventually_kDomain_shift_iff (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) (fun _ => 0)
    0 0 fixG (fun _ => False) False (alphaOf fixG) τ (fun b h => alphaOf_none h) (alphaOf_nonneg fixG)
    (fun b h => alphaOf_pos h) (fun _ => le_refl 0) (fun _ h => h.elim) (le_refl 0) (fun h => h.elim) hτ.gen
    (fun b hb => by
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ hb
      have := hP.val b v hv
      rw [hτv]
      exact ⟨this.1, this.2.1⟩)
    (fun b hb _ => by
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ hb
      have := (hP.val b v hv).2.2
      rw [hτv]
      rcases lt_or_eq_of_le this with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, alphaOf_pos hb⟩)
    (fun _ _ h => h.elim)
    (fun b b' hbb hb' hb => by
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ hb
      obtain ⟨v', hv', hτv'⟩ := pinned_val D hS hτ hb'
      have hm := hP.mono b' b v' v hv' hv (IsAncB.of_isChildOf hbb)
      rw [hτv, hτv']
      rcases lt_or_eq_of_le hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, alphaOf_lt (IsAncB.of_isChildOf hbb) hb hb'⟩)
    (fun b hl => (not_loneParent_of_plain _ hplain b hl).elim)
    (fun b hl => (not_loneParent_of_plain _ hplain b hl).elim)
  simp only [mul_zero, sub_zero] at h
  have e := kDomainR_eq_kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG
  exact (Eq.to_iff (congrArg (fun A => τ ∈ A) e.symm)).trans h.symm

/-- The core step. -/
theorem core_eventually_iff (hP : RelaxPins layer tt fixG) (τ : GBranch (D.forest hS) → ℝ) (hτ : PinnedAt fixG τ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), nativeCoreClock D hS (fun b => τ b - ε * alphaOf fixG b) ∈
        coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt) ↔
      nativeCoreClock D hS τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt
        (MkSlots.fixCore D hS fixG) := by
  have h := eventually_coreTimeDomainW_shift_iff (fun b => layer (D.coreBranch hS b).toNode) tt
    (MkSlots.fixCore D hS fixG) (fun c => alphaOf fixG (D.coreBranch hS c)) (nativeCoreClock D hS τ)
    (fun b h => alphaOf_none h) (fun b => alphaOf_nonneg fixG _) (fun b h => alphaOf_pos h)
    (fun x y hx hy => hτ.gen _ _ hx hy)
    (fun b hb => by
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ hb
      have := hP.val _ v hv
      show (layer (D.coreBranch hS b).toNode : ℝ) < τ (D.coreBranch hS b) ∧
        τ (D.coreBranch hS b) ≤ (layer (D.coreBranch hS b).toNode : ℝ) + 1
      rw [hτv]
      exact ⟨this.1, this.2.1⟩)
    (fun b hb hcf => by
      obtain ⟨v, hv, hτv⟩ := pinned_val D hS hτ hb
      rcases hs : nodeToSlot b.toNode with j | ⟨c, i⟩
      · have hpc : parentClockWith tt (nativeCoreClock D hS τ) b.toNode = tt j := by
          unfold parentClockWith; rw [hs]
        have hpa : parentClockWith 0 (fun c => alphaOf fixG (D.coreBranch hS c)) b.toNode = 0 := by
          unfold parentClockWith; rw [hs]; rfl
        have hj : b.1.1 = j := index_of_slot_root b.toNode j hs
        have hle := (hP.val _ v hv).2.2
        rw [coreBranch_index, hj] at hle
        rw [hpc, hpa]
        show τ (D.coreBranch hS b) < tt j ∨ (τ (D.coreBranch hS b) = tt j ∧ 0 < alphaOf fixG (D.coreBranch hS b))
        rw [hτv]
        rcases lt_or_eq_of_le hle with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, alphaOf_pos hb⟩
      · have hbc : b.toNode = c.child i := node_eq_child_of_slot b.toNode c i hs
        have hc : MkSlots.fixCore D hS fixG c ≠ none := by
          intro h; apply hcf; unfold clockFree; rw [hs]; exact h
        obtain ⟨v', hv', hτv'⟩ := pinned_val D hS hτ hc
        have hpc : parentClockWith tt (nativeCoreClock D hS τ) b.toNode = τ (D.coreBranch hS c) := by
          unfold parentClockWith; rw [hs]; rfl
        have hpa : parentClockWith 0 (fun c => alphaOf fixG (D.coreBranch hS c)) b.toNode =
            alphaOf fixG (D.coreBranch hS c) := by
          unfold parentClockWith; rw [hs]
        have hanc := coreBranch_isAncB D hS c i b hbc
        have hm := hP.mono _ _ v v' hv hv' hanc
        rw [hpc, hpa]
        show τ (D.coreBranch hS b) < _ ∨ (τ (D.coreBranch hS b) = _ ∧ _)
        rw [hτv, hτv']
        rcases lt_or_eq_of_le hm with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, alphaOf_lt hanc hc hb⟩)
  exact h

end Main

end WaveTurbulence.Flower.MkSlotsB
