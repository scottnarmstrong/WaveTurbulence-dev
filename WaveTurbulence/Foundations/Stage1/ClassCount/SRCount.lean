/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Slots2
public import WaveTurbulence.Foundations.LayerCnt.Source
import Mathlib.Tactic

/-!
# CLASSCOUNT: coherent regions and the slots they touch

* `sourceRegion_of_zero`: if the regular trees/couples attached in the region of a vine all have incoherency index `0`,
  the induced pre-layering satisfies `SourceRegion` (hypothesis of the improved `layervine` bound);
* `card_bad_region_le`: for a family of vines whose regions `T \ {x}` are pairwise disjoint, the number of vines whose
  region touches a slot with incoherency `≥ 1` is at most `2 Σ_s gs s`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree LFTwist RegRed
  WaveTurbulence.LayerCnt

variable {w : ℕ} {S : Garden w}

/-- The slots attached in the region `T \ {x}` of a vine: trees at its branches and couples with a leaf below them. -/
def regionHas (hS : S.IsPlain) (T : Finset (GBranch S.tree)) (x : GBranch S.tree) : ReplacementSlot S → Prop
  | .inr y => y ∈ T ∧ y ≠ x
  | .inl q => ∃ ℓ : GLeaf S.tree, ∃ hr : ℓ.1.2 ≠ [], pairOfLeaf S hS ℓ = q ∧
      GNode.parent ℓ.toNode hr ∈ T ∧ GNode.parent ℓ.toNode hr ≠ x

theorem cohOn_of_incohCount_zero (LG : LayeredGarden w) (L : List ((Fin w × Path) × (Fin w × Path)))
    (h : incohCount LG L = 0) : CohOn LG L := by
  intro l hl
  by_contra hne
  have : l ∈ L.filter (fun l => layerAt LG l.1 ≠ layerAt LG l.2) := by
    simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hl, hne⟩
  have h0 : (L.filter (fun l => layerAt LG l.1 ≠ layerAt LG l.2)).length = 0 := h
  rw [List.length_eq_zero_iff] at h0
  rw [h0] at this
  simp at this

/-- **Coherent regional attachments give `SourceRegion`.** -/
theorem sourceRegion_of_zero (hS : S.IsPlain) (p : ℕ) {LG : LayeredGarden w} (hc : IsCanonGC (p + 1) LG)
    (D : ReconstructionData S) (hd : D.Decodes hS LG.garden) (T : Finset (GBranch S.tree)) (x : GBranch S.tree)
    (hz : ∀ s, regionHas hS T x s → slotInc D hS LG s = 0) :
    SourceRegion S hS p T x (coreOf D hS LG) := by
  classical
  have hcan : ∃ kind, CanonicalObject p kind LG := by
    obtain ⟨hpl, hmid, hcrit⟩ := hc
    rcases hmid with ⟨h4, hirr⟩ | ⟨h2, hsig⟩
    · exact ⟨true, CanonicalObject.garden ⟨h4, hpl, hirr, hcrit⟩⟩
    · subst h2
      exact ⟨false, CanonicalObject.couple ((Canon.isCanonGC_iff_isCanonC (p + 1) LG).1 ⟨hpl, Or.inr ⟨rfl, hsig⟩, hcrit⟩)⟩
  obtain ⟨kind, hk⟩ := hcan
  refine ⟨kind, LG, D, hd, hk, ?_, ?_, ?_⟩
  · rw [coreOf_eq D hS hd]; rfl
  · intro y hy hyx
    exact cohOn_of_incohCount_zero LG _ (hz (.inr y) ⟨hy, hyx⟩)
  · intro q hq
    exact cohOn_of_incohCount_zero LG _ (hz (.inl q) hq)

theorem card_mem_le_one {I B : Type*} [Fintype I] [DecidableEq B] (e : I → Finset B)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (e i) (e i')) (z : B) :
    (Finset.univ.filter (fun i => z ∈ e i)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi i' hi'
  by_contra hne
  exact Finset.disjoint_left.1 (hdisj i i' hne) (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hi').2

theorem card_exists_mem_le {I B : Type*} [Fintype I] [DecidableEq B] (e : I → Finset B)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (e i) (e i')) (Z : Finset B) :
    (Finset.univ.filter (fun i => ∃ z ∈ Z, z ∈ e i)).card ≤ Z.card := by
  classical
  have hsub : Finset.univ.filter (fun i => ∃ z ∈ Z, z ∈ e i) ⊆
      Z.biUnion (fun z => Finset.univ.filter (fun i => z ∈ e i)) := by
    intro i hi
    obtain ⟨z, hz, hze⟩ := (Finset.mem_filter.1 hi).2
    exact Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_filter.2 ⟨Finset.mem_univ _, hze⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ z ∈ Z, (Finset.univ.filter (fun i => z ∈ e i)).card ≤ ∑ z ∈ Z, 1 :=
        Finset.sum_le_sum fun z _ => card_mem_le_one e hdisj z
    _ = Z.card := by simp

/-- The possible parents of the two leaves of a source pair. -/
noncomputable def pairParents (hS : S.IsPlain) (q : SourcePair S) : Finset (GBranch S.tree) :=
  by classical exact
    (if h : (q.firstLeaf hS).1.2 ≠ [] then {GNode.parent (q.firstLeaf hS).toNode h} else ∅) ∪
    (if h : (q.secondLeaf hS).1.2 ≠ [] then {GNode.parent (q.secondLeaf hS).toNode h} else ∅)

theorem card_pairParents_le (hS : S.IsPlain) (q : SourcePair S) : (pairParents hS q).card ≤ 2 := by
  classical
  unfold pairParents
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : ∀ (ℓ : GLeaf S.tree),
      (if h : ℓ.1.2 ≠ [] then ({GNode.parent ℓ.toNode h} : Finset (GBranch S.tree)) else ∅).card ≤ 1 := by
    intro ℓ; split_ifs <;> simp
  have := h1 (q.firstLeaf hS)
  have := h1 (q.secondLeaf hS)
  omega

theorem regionHas_pair_parent (hS : S.IsPlain) {T : Finset (GBranch S.tree)} {x : GBranch S.tree}
    {q : SourcePair S} (h : regionHas hS T x (.inl q)) : ∃ z ∈ pairParents hS q, z ∈ T.erase x := by
  classical
  obtain ⟨ℓ, hr, hq, hT, hx⟩ := h
  refine ⟨GNode.parent ℓ.toNode hr, ?_, Finset.mem_erase.2 ⟨hx, hT⟩⟩
  have he : (sourcePairAt S ℓ).1 = ℓ.1 ∨ (sourcePairAt S ℓ).2 = ℓ.1 := sourcePairAt_endpoint S ℓ
  have hq' : (q : Pair w) = sourcePairAt S ℓ := by rw [← hq]; rfl
  unfold pairParents
  rcases he with he | he
  · have hl : ℓ = q.firstLeaf hS := Subtype.ext (by show ℓ.1 = q.1.1; rw [hq']; exact he.symm)
    subst hl
    rw [Finset.mem_union]; left
    rw [dif_pos hr]; simp
  · have hl : ℓ = q.secondLeaf hS := Subtype.ext (by show ℓ.1 = q.1.2; rw [hq']; exact he.symm)
    subst hl
    rw [Finset.mem_union]; right
    rw [dif_pos hr]; simp

open Classical in
/-- **Counting the vines whose region touches an incoherent slot.** -/
theorem card_bad_region_le {I : Type*} [Fintype I] (hS : S.IsPlain) (T : I → Finset (GBranch S.tree))
    (x : I → GBranch S.tree)
    (hdisj : ∀ i i', i ≠ i' → Disjoint ((T i).erase (x i)) ((T i').erase (x i')))
    (gs : ReplacementSlot S → ℕ) :
    (Finset.univ.filter (fun i => ∃ s, regionHas hS (T i) (x i) s ∧ 1 ≤ gs s)).card ≤ 2 * ∑ s, gs s := by
  classical
  set S1 := (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => 1 ≤ gs s) with hS1
  have hmult : ∀ s, (Finset.univ.filter (fun i => regionHas hS (T i) (x i) s)).card ≤ 2 := by
    intro s
    cases s with
    | inr y =>
      have := card_mem_le_one (fun i => (T i).erase (x i)) hdisj y
      refine le_trans (le_of_eq_of_le ?_ this) (by omega)
      congr 1
      ext i
      simp [regionHas, Finset.mem_erase, and_comm]
    | inl q =>
      have := card_exists_mem_le (fun i => (T i).erase (x i)) hdisj (pairParents hS q)
      refine le_trans (Finset.card_le_card ?_) (this.trans (card_pairParents_le hS q))
      intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, regionHas_pair_parent hS (Finset.mem_filter.1 hi).2⟩
  have hsub : Finset.univ.filter (fun i => ∃ s, regionHas hS (T i) (x i) s ∧ 1 ≤ gs s) ⊆
      S1.biUnion (fun s => Finset.univ.filter (fun i => regionHas hS (T i) (x i) s)) := by
    intro i hi
    obtain ⟨s, hs, hg⟩ := (Finset.mem_filter.1 hi).2
    exact Finset.mem_biUnion.2 ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ s ∈ S1, (Finset.univ.filter (fun i => regionHas hS (T i) (x i) s)).card ≤ ∑ s ∈ S1, 2 :=
        Finset.sum_le_sum fun s _ => hmult s
    _ = 2 * S1.card := by simp [mul_comm]
    _ ≤ 2 * ∑ s, gs s := by
        refine Nat.mul_le_mul_left _ ?_
        calc S1.card = ∑ s ∈ S1, 1 := by simp
          _ ≤ ∑ s ∈ S1, gs s := Finset.sum_le_sum fun s hs => (Finset.mem_filter.1 hs).2
          _ ≤ ∑ s, gs s := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem card_fiber_le_two {I V : Type*} [Fintype I] [DecidableEq V] (T : I → Finset V) (x : I → V)
    (hx : ∀ i, x i ∈ T i) (hne : ∀ i, ((T i).erase (x i)).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint ((T i).erase (x i)) ((T i').erase (x i'))) (T0 : Finset V) :
    (Finset.univ.filter (fun i => T i = T0)).card ≤ 2 := by
  classical
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hlt
  have ha' : T a = T0 := (Finset.mem_filter.1 ha).2
  have hb' : T b = T0 := (Finset.mem_filter.1 hb).2
  have hc' : T c = T0 := (Finset.mem_filter.1 hc).2
  have hxd : ∀ i j, i ≠ j → T i = T j → x i ≠ x j := by
    intro i j hij hT hxe
    have hd := hdisj i j hij
    have : (T i).erase (x i) = (T j).erase (x j) := by rw [hT, hxe]
    rw [this] at hd
    obtain ⟨z, hz⟩ := hne j
    exact Finset.disjoint_left.1 hd hz hz
  have h1 : x c ≠ x a := fun h => hxd c a hac.symm (hc'.trans ha'.symm) h
  have h2 : x c ≠ x b := fun h => hxd c b hbc.symm (hc'.trans hb'.symm) h
  have hc0 : x c ∈ T0 := hc' ▸ hx c
  have m1 : x c ∈ (T a).erase (x a) := by rw [Finset.mem_erase, ha']; exact ⟨h1, hc0⟩
  have m2 : x c ∈ (T b).erase (x b) := by rw [Finset.mem_erase, hb']; exact ⟨h2, hc0⟩
  exact Finset.disjoint_left.1 (hdisj a b hab) m1 m2

theorem sum_le_two_mul_of_fiber {I V : Type*} [Fintype I] [DecidableEq V] (T : I → Finset V) (x : I → V)
    (hx : ∀ i, x i ∈ T i) (hne : ∀ i, ((T i).erase (x i)).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint ((T i).erase (x i)) ((T i').erase (x i')))
    (Y : Finset (Finset V)) (hY : ∀ i, T i ∈ Y) (g : Finset V → ℕ) :
    ∑ i, g (T i) ≤ 2 * ∑ T0 ∈ Y, g T0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Y) (g := T) (fun i _ => hY i)]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun T0 _ => ?_
  have : ∀ i ∈ Finset.univ.filter (fun i => T i = T0), g (T i) = g T0 := by
    intro i hi; rw [(Finset.mem_filter.1 hi).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_fiber_le_two T x hx hne hdisj T0)

end WaveTurbulence.ClassCount
