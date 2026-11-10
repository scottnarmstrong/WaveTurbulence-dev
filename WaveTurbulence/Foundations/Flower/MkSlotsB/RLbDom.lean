/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RDom2

/-! # B3s-HELPER3 (B1, ruling R187): the relaxed domain identity with core lower bounds

Under R187 the constraint between a pinned native branch and its FREE clock leaves the slot and becomes a constant
lower bound on the clock (a core branch): the slot domains are `nativeDomainWRL` (`kDomainR` with no clock
constraint at pinned branches — the clock constraints of a pinned branch are those of D2a's `kDomainFix`), and the
core domain is `coreTimeDomainWR ∩ lbDomC lbC` (`lbDomC lbC = {τ | ∀ c x, lbC c = some x → x < τ c}`), where `lbC`
puts at the free clock `c` of a pinned slot TOP (a root of a native object) its pinned value:
* `LbSound`: every lower bound is the value of a pinned native top whose clock is the free core branch `c`;
* `LbComplete`: every pinned native top with a free clock `c` has a value at most `lbC c`.
On the pinned slice the slot constraints of the other pinned branches follow from those of the free ones, the
lower bounds and monotonicity (induction on the native depth).

* `nativeUp`, `nativeUpFree`, `nativeDomainWRL`, `lbDomC`, `LbSound`, `LbComplete`;
* **`mem_kDomainFix_reconstruction_iff_lb`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology Set MeasureTheory
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-- Constant lower bounds. -/
def lbDomC {tree : Fin w → TTree} (lb : GBranch tree → Option ℝ) : Set (GBranch tree → ℝ) :=
  {τ | ∀ c x, lb c = some x → x < τ c}

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (tt : Fin w → ℝ) (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The skeleton node whose parent clock is the upper clock of a native branch. -/
def nativeClockNode : (s : ReplacementSlot S) → NativeClockBranch D s → GNode S.tree
  | .inl p, q => coupleLeafNode hS p q.1.1
  | .inr b, _ => b.toNode

/-- **The relaxed native domains with the clock constraints of pinned branches removed** (R187). -/
def nativeDomainWRL (τ : GBranch S.tree → ℝ) : (s : ReplacementSlot S) → Set (NativeTimeBlock D s)
  | .inl p => kDomainR (nativeCoupleLayered D hS layer hLayer p) (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (MkSlots.fixNative D hS fixG (.inl p)) (fun _ => False) False
  | .inr b => kDomainR (nativeChainLayered D hS layer hLayer b) (fun _ => parentClockWith tt τ b.toNode) (τ b)
      (MkSlots.fixNative D hS fixG (.inr b)) (fun _ => False) (MkSlots.fixCore D hS fixG b = none)

/-- The native branch is a root (top) of its native object. -/
def NativeTop : (s : ReplacementSlot S) → NativeClockBranch D s → Prop
  | .inl _, q => q.1.2 = []
  | .inr _, q => q.1.2 = []

/-- **Soundness of the lower bounds**: each is the pinned value of a native top whose clock is the free branch `c`. -/
def LbSound (lbC : GBranch S.tree → Option ℝ) : Prop :=
  ∀ c x, lbC c = some x → ∃ (s : ReplacementSlot S) (q : NativeClockBranch D s) (i : Fin 3),
    NativeTop D s q ∧ MkSlots.fixNative D hS fixG s q = some x ∧ nativeClockNode D hS s q = c.child i ∧
      MkSlots.fixCore D hS fixG c = none

/-- **Completeness of the lower bounds**: a pinned native top with a free clock `c` is at most `lbC c`. -/
def LbComplete (lbC : GBranch S.tree → Option ℝ) : Prop :=
  ∀ (s : ReplacementSlot S) (q : NativeClockBranch D s) (v : ℝ) (c : GBranch S.tree) (i : Fin 3),
    NativeTop D s q → MkSlots.fixNative D hS fixG s q = some v → nativeClockNode D hS s q = c.child i →
      MkSlots.fixCore D hS fixG c = none → ∃ x, lbC c = some x ∧ v ≤ x

/-! ### The native slot constraints of pinned branches, by induction on the depth -/

/-- A non-root branch has a parent branch. -/
theorem exists_parent_branch {tree : Fin w → TTree} (q : GBranch tree) (h : q.1.2 ≠ []) :
    ∃ par : GBranch tree, q.IsChildOf par := by
  have h' : q.toNode.1.2 ≠ [] := h
  have hs : nodeToSlot q.toNode = .inr (q.toNode.parent h', q.toNode.1.2.getLast h') := by
    unfold nodeToSlot
    split_ifs with hc
    · exact absurd hc h'
    · rfl
  have he := node_eq_child_of_slot q.toNode _ _ hs
  refine ⟨q.toNode.parent h', ?_⟩
  have h1 : q.toNode.1 = ((q.toNode.parent h').child (q.toNode.1.2.getLast h')).1 := congrArg Subtype.val he
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  exact ⟨e1, q.toNode.1.2.getLast h', e2⟩

/-- The generic induction: in `kDomainR` with no pinned clock constraints, a pinned branch of a tree with a free
clock (`P`, inherited along parents) whose ancestors' values dominate stays below its (common) clock, given its top
does. -/
theorem pinned_below_clock (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (sFree : Prop) (τ : GBranch LG.garden.tree → ℝ)
    (hτ : τ ∈ kDomainR LG up s fix (fun _ => False) sFree) (P : GBranch LG.garden.tree → Prop)
    (hPpar : ∀ b b', b'.IsChildOf b → P b' → P b)
    (hupc : ∀ b b', b'.IsChildOf b → up b' = up b)
    (hpin : ∀ b v, fix b = some v → τ b = v)
    (hmono : ∀ b b' v v', b'.IsChildOf b → fix b' = some v' → fix b = some v → v' ≤ v)
    (htop : ∀ b v, P b → b.1.2 = [] → fix b = some v → v < up b) :
    ∀ (n : ℕ) (b : GBranch LG.garden.tree), b.1.2.length = n → P b → fix b ≠ none → τ b < up b := by
  intro n
  induction n with
  | zero =>
    intro b hn hPb hb
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
    rw [hpin b v hv]
    exact htop b v hPb (List.length_eq_zero_iff.mp hn) hv
  | succ n ih =>
    intro b hn hPb hb
    have hne : b.1.2 ≠ [] := fun h => by rw [h] at hn; simp at hn
    obtain ⟨par, hpar⟩ := exists_parent_branch b hne
    have hlen : par.1.2.length = n := by
      obtain ⟨-, i, hi⟩ := hpar
      have := congrArg List.length hi
      simp only [List.length_append, List.length_singleton] at this
      omega
    rw [hupc par b hpar]
    by_cases hp : fix par = none
    · exact ((hτ par).2.2.1 b hpar (Or.inr hp)).trans ((hτ par).2.1 (Or.inl hp))
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
      obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.1 hp
      have h1 := ih par hlen (hPpar par b hpar hPb) hp
      rw [hpin b v hv]
      rw [hpin par v' hv'] at h1
      exact lt_of_le_of_lt (hmono par b v' v hpar hv hv') h1

/-- The relaxed native domain is the one without pinned clock constraints plus the clock constraints of pinned
branches (pure rearrangement). -/
theorem mem_kDomainR_iff_noClock (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (upFree : GBranch LG.garden.tree → Prop) (sFree : Prop)
    (τ : GBranch LG.garden.tree → ℝ) :
    τ ∈ kDomainR LG up s fix upFree sFree ↔
      τ ∈ kDomainR LG up s fix (fun _ => False) sFree ∧ ∀ b, fix b ≠ none → upFree b → τ b < up b := by
  constructor
  · intro h
    refine ⟨fun b => ⟨(h b).1, fun hb => (h b).2.1 (Or.inl (hb.resolve_right id)), (h b).2.2.1, (h b).2.2.2⟩,
      fun b _ hu => (h b).2.1 (Or.inr hu)⟩
  · rintro ⟨h, hp⟩ b
    refine ⟨(h b).1, fun hb => ?_, (h b).2.2.1, (h b).2.2.2⟩
    by_cases hf : fix b = none
    · exact (h b).2.1 (Or.inl hf)
    · exact hp b hf (hb.resolve_left hf)

end WaveTurbulence.Flower.MkSlotsB
