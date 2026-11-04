/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Canon.Basic

/-!
# Canonical layered gardens — the decomposition theorems (packet D3 CANON, pre-freeze)

For a set `S` of pairwise incomparable nodes and a level `q` (T Prop `canonequiv`, proof):

* (L) `layer_lt_of_canonInd`: below a set in the inductive class `CanonInd q`, all layers are `< q`;
* (C) `relCrit_of_topDecomp`: a top-level decomposition with blocks in `CanonInd q` gives the relative
  criterion at level `q`;
* (D) `topDecomp_of_relCrit`: the relative criterion (with complete pairing below `S`, flowers allowed
  if their stems lie in layer `q`) gives a top-level decomposition, with `U` the relative attachment
  nodes and blocks the classes of their linking relation.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.Canon

open TTree

namespace Rel

variable {w : ℕ} {LG : LayeredGarden w}

/-! ### Leaves below sets of nodes -/

theorem mem_leavesBelow {a : GNode LG.garden.tree} {ℓ : GLeaf LG.garden.tree} :
    ℓ ∈ a.leavesBelow ↔ a.IsDesc ℓ.toNode := by
  simp [GNode.leavesBelow]

theorem mem_leavesBelowSet {A : Finset (GNode LG.garden.tree)} {ℓ : GLeaf LG.garden.tree} :
    ℓ ∈ LG.leavesBelowSet A ↔ ∃ s ∈ A, s.IsDesc ℓ.toNode := by
  rw [LayeredGarden.leavesBelowSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, LayeredGarden.BelowSet]

theorem leavesBelowSet_pair (a a' : GNode LG.garden.tree) :
    LG.leavesBelowSet {a, a'} = a.leavesBelow ∪ a'.leavesBelow := by
  ext ℓ
  simp [mem_leavesBelowSet, mem_leavesBelow]

theorem card_leavesBelowSet {B : Finset (GNode LG.garden.tree)} (hB : Antichain LG B) :
    (LG.leavesBelowSet B).card = ∑ u ∈ B, u.leavesBelow.card := by
  classical
  have h : LG.leavesBelowSet B = B.biUnion fun u => u.leavesBelow := by
    ext ℓ
    simp [mem_leavesBelowSet, mem_leavesBelow]
  rw [h, Finset.card_biUnion]
  intro u hu u' hu' hne
  exact disjoint_leavesBelow (hB u hu u' hu' hne)

/-- A completely paired antichain has an even number of nodes (each subtree has an odd number of
leaves). -/
theorem even_card_of_cp {B : Finset (GNode LG.garden.tree)} (hB : Antichain LG B)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet B)) : Even B.card := by
  have he := even_card_of_completelyPaired LG.garden _ _ rfl hcp
  rw [card_leavesBelowSet hB] at he
  have h2 : ((∑ u ∈ B, u.leavesBelow.card : ℕ) : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff_even).2 he
  rw [Nat.cast_sum] at h2
  have hone : ∀ u ∈ B, ((u.leavesBelow.card : ℕ) : ZMod 2) = 1 := fun u _ =>
    (ZMod.natCast_eq_one_iff_odd).2 (odd_card_leavesBelow u)
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  exact (ZMod.natCast_eq_zero_iff_even).1 h2

theorem exists_of_not_topRegion {S U : Finset (GNode LG.garden.tree)} {a : GNode LG.garden.tree}
    (ha : LG.BelowSet S a) (h : ¬ LG.TopRegion S U a) : ∃ u ∈ U, u.IsDesc a ∧ u ≠ a := by
  unfold LayeredGarden.TopRegion at h
  push Not at h
  exact h ha

theorem unfold_topDecomp {fl : Bool} {q : ℕ} {sub : Finset (GNode LG.garden.tree) → Prop}
    {S : Finset (GNode LG.garden.tree)} (h : LG.TopDecomp fl q sub S) :
    ∃ U : Finset (GNode LG.garden.tree), ∃ Bp : Finpartition U, LG.TopDecompWith fl q sub S U Bp :=
  h

theorem canonInd_succ {q : ℕ} {S : Finset (GNode LG.garden.tree)} :
    LG.CanonInd (q + 1) S ↔ 4 ≤ S.card ∧ Antichain LG S ∧
      LG.garden.CompletelyPaired (LG.leavesBelowSet S) ∧ LG.IrreducibleAt S ∧
      LG.TopDecomp false q (LG.CanonInd q) S := by
  rw [LayeredGarden.CanonInd]
  rfl

theorem not_canonInd_zero {S : Finset (GNode LG.garden.tree)} : ¬ LG.CanonInd 0 S := by
  rw [LayeredGarden.CanonInd]
  exact id

/-! ### (L) Layers below the inductive class -/

theorem layer_lt_of_canonInd :
    ∀ (q : ℕ) (S : Finset (GNode LG.garden.tree)), LG.CanonInd q S →
      ∀ a, LG.BelowSet S a → LG.layer a < q := by
  intro q
  induction q with
  | zero => exact fun S h => absurd h not_canonInd_zero
  | succ q ih =>
    intro S h a ha
    obtain ⟨-, -, -, -, htd⟩ := canonInd_succ.1 h
    obtain ⟨U, Bp, h1, h2, -, h4⟩ := unfold_topDecomp htd
    by_cases htop : LG.TopRegion S U a
    · by_cases haU : a ∈ U
      · obtain ⟨B, hB, haB⟩ := Bp.exists_mem haU
        have := ih B (h4 B hB).2 a ⟨a, haB, GNode.isDesc_refl a⟩
        omega
      · rw [h2 a htop haU]
        omega
    · obtain ⟨u, hu, hua, -⟩ := exists_of_not_topRegion ha htop
      obtain ⟨B, hB, huB⟩ := Bp.exists_mem hu
      have := ih B (h4 B hB).2 a ⟨u, huB, hua⟩
      omega

/-! ### (C) The criterion from a decomposition -/

theorem relCrit_of_topDecomp (q : ℕ) :
    ∀ (S : Finset (GNode LG.garden.tree)) (fl : Bool) (U : Finset (GNode LG.garden.tree))
      (Bp : Finpartition U), Antichain LG S → LG.TopDecompWith fl q (LG.CanonInd q) S U Bp →
      RelCrit LG S q := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro S fl U Bp hS hTD
  obtain ⟨h1, h2, -, h4⟩ := hTD
  have hUac : ∀ u ∈ U, ∀ u' ∈ U, u.IsDesc u' → u = u' := fun u hu u' hu' h =>
    (h1 u' hu').2 u hu h
  have hblock : ∀ u ∈ U, ∀ a, u.IsDesc a → LG.layer a < q := by
    intro u hu a hua
    obtain ⟨B, hB, huB⟩ := Bp.exists_mem hu
    exact layer_lt_of_canonInd q B (h4 B hB).2 a ⟨u, huB, hua⟩
  have hdich : ∀ a, LG.BelowSet S a → (LG.TopRegion S U a ∧ a ∉ U) ∨ ∃ u ∈ U, u.IsDesc a := by
    intro a ha
    by_cases htop : LG.TopRegion S U a
    · by_cases haU : a ∈ U
      · exact Or.inr ⟨a, haU, GNode.isDesc_refl a⟩
      · exact Or.inl ⟨htop, haU⟩
    · obtain ⟨u, hu, hua, -⟩ := exists_of_not_topRegion ha htop
      exact Or.inr ⟨u, hu, hua⟩
  have hle : ∀ a, LG.BelowSet S a → LG.layer a ≤ q := by
    intro a ha
    rcases hdich a ha with ⟨htop, haU⟩ | ⟨u, hu, hua⟩
    · exact (h2 a htop haU).le
    · exact (hblock u hu a hua).le
  have hrpl_le : ∀ a, LG.BelowSet S a → rpl LG S q a ≤ q := by
    intro a ha
    by_cases haS : a ∈ S
    · simp [rpl, haS]
    · obtain ⟨-, hpar, hr⟩ := below_par hS ha haS (q := q)
      rw [hr]
      exact hle _ hpar
  refine ⟨hle, ?_⟩
  intro a a' ha ha' hinc hcp
  by_cases hmax : q ≤ max (LG.layer a) (LG.layer a')
  · exact (min_le_left _ _).trans ((hrpl_le a ha).trans hmax)
  push Not at hmax
  have hla : LG.layer a < q := lt_of_le_of_lt (le_max_left _ _) hmax
  have hla' : LG.layer a' < q := lt_of_le_of_lt (le_max_right _ _) hmax
  have hbelowU : ∀ x, LG.BelowSet S x → LG.layer x < q → ∃ u ∈ U, u.IsDesc x := by
    intro x hx hlx
    rcases hdich x hx with ⟨htop, hxU⟩ | h
    · exact absurd (h2 x htop hxU) hlx.ne
    · exact h
  obtain ⟨u, hu, hua⟩ := hbelowU a ha hla
  obtain ⟨u', hu', hua'⟩ := hbelowU a' ha' hla'
  obtain ⟨B, hB, huB⟩ := Bp.exists_mem hu
  obtain ⟨B', hB', hu'B'⟩ := Bp.exists_mem hu'
  have hcanonB := (h4 B hB).2
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by
    have := hblock u hu u (GNode.isDesc_refl u)
    omega⟩
  obtain ⟨hcard, hBac, hBcp, hBirr, hBtd⟩ := canonInd_succ.1 hcanonB
  -- the two nodes lie in the same block
  have hBB' : B = B' := by
    by_contra hne
    have hcpa : LG.garden.CompletelyPaired a.leavesBelow := by
      intro ℓ hℓ
      obtain ⟨hpne, hpmem⟩ := hcp ℓ (Finset.mem_union_left _ hℓ)
      refine ⟨hpne, ?_⟩
      rcases Finset.mem_union.1 hpmem with h | h
      · exact h
      · exfalso
        have hℓB : ℓ ∈ LG.leavesBelowSet B :=
          mem_leavesBelowSet.2 ⟨u, huB, hua.trans (mem_leavesBelow.1 hℓ)⟩
        obtain ⟨b, hbB, hb⟩ := mem_leavesBelowSet.1 (hBcp ℓ hℓB).2
        have hu'p : u'.IsDesc (LG.garden.pair ℓ).toNode := hua'.trans (mem_leavesBelow.1 h)
        have hbU : b ∈ U := Bp.le hB hbB
        have hbu' : b = u' := by
          rcases isDesc_total hb hu'p with h' | h'
          · exact hUac b hbU u' hu' h'
          · exact (hUac u' hu' b hbU h').symm
        exact hne (Bp.eq_of_mem_parts hB hB' (hbu' ▸ hbB) hu'B')
    exact (Nat.not_even_iff_odd.2 (odd_card_leavesBelow a))
      (even_card_of_completelyPaired LG.garden _ _ rfl hcpa)
  subst hBB'
  obtain ⟨U', Bp', hTD'⟩ := unfold_topDecomp hBtd
  have hRB := ih q' (Nat.lt_succ_self q') B false U' Bp' hBac hTD'
  have haB : LG.BelowSet B a := ⟨u, huB, hua⟩
  have ha'B : LG.BelowSet B a' := ⟨u', hu'B', hua'⟩
  have hR := hRB.2 a a' haB ha'B hinc hcp
  have hlayB : ∀ x, LG.BelowSet B x → LG.layer x < q' + 1 :=
    layer_lt_of_canonInd (q' + 1) B hcanonB
  -- outside `B`, the two relative parent layers agree
  have hagree : ∀ x, LG.BelowSet B x → x ∉ B →
      rpl LG S (q' + 1) x = rpl LG B q' x ∧ rpl LG B q' x ≤ q' := by
    intro x hxB hxnB
    obtain ⟨v, hvB, hvx⟩ := hxB
    have hvS : LG.BelowSet S v := (h1 v (Bp.le hB hvB)).1
    have hxS : x ∉ S := fun hxS => hxnB (eq_of_below_isDesc_mem hS hvS hxS hvx ▸ hvB)
    obtain ⟨-, -, hrS⟩ := below_par hS (belowSet_of_isDesc hvS hvx) hxS (q := q' + 1)
    obtain ⟨-, hparB, hrB⟩ := below_par hBac ⟨v, hvB, hvx⟩ hxnB (q := q')
    refine ⟨hrS.trans hrB.symm, ?_⟩
    rw [hrB]
    have := hlayB _ hparB
    omega
  have hrplB_mem : ∀ x ∈ B, rpl LG B q' x = q' := fun x hx => by simp [rpl, hx]
  by_cases haBm : a ∈ B <;> by_cases ha'Bm : a' ∈ B
  · exfalso
    have hne : a ≠ a' := fun h => hinc.1 (h ▸ GNode.isDesc_refl a)
    refine hBirr {a, a'} (Finset.mem_powerset.2
      (Finset.insert_subset haBm (Finset.singleton_subset_iff.2 ha'Bm)))
      ⟨a, Finset.mem_insert_self _ _⟩ ?_ ?_
    · intro h
      have := congrArg Finset.card h
      rw [Finset.card_pair hne] at this
      omega
    · rw [leavesBelowSet_pair]
      exact hcp
  · obtain ⟨he, hle'⟩ := hagree a' ha'B ha'Bm
    calc min (rpl LG S (q' + 1) a) (rpl LG S (q' + 1) a') ≤ rpl LG S (q' + 1) a' :=
          min_le_right _ _
      _ = rpl LG B q' a' := he
      _ = min (rpl LG B q' a) (rpl LG B q' a') := by
          rw [hrplB_mem a haBm]
          exact (min_eq_right hle').symm
      _ ≤ _ := hR
  · obtain ⟨he, hle'⟩ := hagree a haB haBm
    calc min (rpl LG S (q' + 1) a) (rpl LG S (q' + 1) a') ≤ rpl LG S (q' + 1) a :=
          min_le_left _ _
      _ = rpl LG B q' a := he
      _ = min (rpl LG B q' a) (rpl LG B q' a') := by
          rw [hrplB_mem a' ha'Bm]
          exact (min_eq_left hle').symm
      _ ≤ _ := hR
  · obtain ⟨he, -⟩ := hagree a haB haBm
    obtain ⟨he', -⟩ := hagree a' ha'B ha'Bm
    rw [he, he']
    exact hR

/-! ### (D) A decomposition from the criterion -/

theorem relLinked_symm {S : Finset (GNode LG.garden.tree)} {q : ℕ} {u u' : GNode LG.garden.tree}
    (h : RelLinked LG S q u u') : RelLinked LG S q u' u := by
  obtain ⟨hu, hu', ℓ, hℓ, hpℓ⟩ := h
  exact ⟨hu', hu, LG.garden.pair ℓ, hpℓ, by rw [LG.garden.pair_pair]; exact hℓ⟩

theorem topDecomp_of_relCrit (q : ℕ) :
    ∀ (S : Finset (GNode LG.garden.tree)) (fl : Bool), Antichain LG S → RelCrit LG S q →
      (∀ ℓ : GLeaf LG.garden.tree, LG.BelowSet S ℓ.toNode → LG.garden.mark ℓ = none →
        LG.BelowSet S (LG.garden.pair ℓ).toNode) →
      (∀ ℓ : GLeaf LG.garden.tree, LG.BelowSet S ℓ.toNode → LG.garden.mark ℓ ≠ none →
        fl = true ∧ LG.garden.IsFlower ℓ ∧
          ∀ c, c.IsDesc ℓ.toNode → LG.BelowSet S c → LG.layer c = q) →
      LG.TopDecomp fl q (LG.CanonInd q) S := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro S fl hS hcrit hpair hmark
  classical
  set U := relAttach LG S q with hU
  let st : Setoid (GNode LG.garden.tree) := Relation.EqvGen.setoid (RelLinked LG S q)
  refine ⟨U, Finpartition.ofSetSetoid st U, ?_, ?_, ?_, ?_⟩
  · -- (a) attachment nodes lie in the top region
    intro u hu
    exact ⟨((mem_relAttach LG).1 hu).1, fun u' hu' h => eq_of_relAttach_isDesc hS hu' hu h⟩
  · -- (b) the rest of the top region is in layer `q`
    intro a htop haU
    refine le_antisymm (hcrit.1 a htop.1) (not_lt.1 fun hlt => haU ?_)
    obtain ⟨u, hu, hua⟩ := exists_relAttach_isDesc hS hcrit.1 htop.1 hlt
    exact htop.2 u hu hua ▸ hu
  · -- (c) top leaves are paired in the top region, or flowers
    intro ℓ htop hℓU
    have hlayℓ : LG.layer ℓ.toNode = q := by
      refine le_antisymm (hcrit.1 _ htop.1) (not_lt.1 fun hlt => hℓU ?_)
      obtain ⟨u, hu, hua⟩ := exists_relAttach_isDesc hS hcrit.1 htop.1 hlt
      exact htop.2 u hu hua ▸ hu
    by_cases hm : LG.garden.mark ℓ = none
    · left
      have hpne : LG.garden.pair ℓ ≠ ℓ := fun h => ((LG.garden.pair_eq_iff ℓ).1 h) hm
      have hplay : LG.layer (LG.garden.pair ℓ).toNode = q := by
        rw [← LG.isLayering.2 ℓ]
        exact hlayℓ
      refine ⟨hpne, ⟨hpair ℓ htop.1 hm, fun u hu h => ?_⟩, fun hpU => ?_⟩
      · exfalso
        have h1 := LG.layer_le_of_isDesc h
        have h2 := ((mem_relAttach LG).1 hu).2.1
        omega
      · have := ((mem_relAttach LG).1 hpU).2.1
        omega
    · right
      exact ⟨(hmark ℓ htop.1 hm).1, (hmark ℓ htop.1 hm).2.1⟩
  · -- (d) the blocks
    intro B hB
    simp only [Finpartition.ofSetSetoid_parts, Finset.mem_image] at hB
    obtain ⟨u0, hu0, rfl⟩ := hB
    have hmemB : ∀ x, x ∈ U.filter (fun b => st.r u0 b) ↔
        x ∈ U ∧ Relation.EqvGen (RelLinked LG S q) u0 x := by
      intro x
      simp only [Finset.mem_filter]
      rfl
    set B := U.filter (fun b => st.r u0 b) with hBdef
    have hBU : B ⊆ U := Finset.filter_subset _ _
    have hu0B : u0 ∈ B := (hmemB u0).2 ⟨hu0, Relation.EqvGen.refl _⟩
    obtain ⟨hu0S, hu0q, -⟩ := (mem_relAttach LG).1 hu0
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hUlt : ∀ u ∈ U, LG.layer u < q' + 1 := fun u hu => ((mem_relAttach LG).1 hu).2.1
    have hUac : ∀ u ∈ U, ∀ u' ∈ U, u.IsDesc u' → u = u' := fun u hu u' hu' h =>
      eq_of_relAttach_isDesc hS hu hu' h
    -- leaves below `B` are unmarked
    have hunm : ∀ ℓ : GLeaf LG.garden.tree, ∀ u ∈ B, u.IsDesc ℓ.toNode → LG.garden.mark ℓ = none := by
      intro ℓ u hu hul
      by_contra hm
      have huS : LG.BelowSet S u := ((mem_relAttach LG).1 (hBU hu)).1
      have h1 := (hmark ℓ (belowSet_of_isDesc huS hul) hm).2.2 ℓ.toNode (GNode.isDesc_refl _)
        (belowSet_of_isDesc huS hul)
      have h2 := LG.layer_le_of_isDesc hul
      have h3 := hUlt u (hBU hu)
      omega
    -- the class is closed under linking
    have hclosed : ∀ x ∈ B, ∀ y, RelLinked LG S (q' + 1) x y → y ∈ B := by
      intro x hx y hxy
      exact (hmemB y).2 ⟨hxy.2.1, Relation.EqvGen.trans _ _ _ ((hmemB x).1 hx).2
        (Relation.EqvGen.rel _ _ hxy)⟩
    -- partners of leaves below `B` lie below `B`
    have hpairB : ∀ ℓ : GLeaf LG.garden.tree, ∀ u ∈ B, u.IsDesc ℓ.toNode →
        ∃ u'' ∈ B, u''.IsDesc (LG.garden.pair ℓ).toNode := by
      intro ℓ u hu hul
      have hm := hunm ℓ u hu hul
      have huS : LG.BelowSet S u := ((mem_relAttach LG).1 (hBU hu)).1
      have hpS := hpair ℓ (belowSet_of_isDesc huS hul) hm
      have hplt : LG.layer (LG.garden.pair ℓ).toNode < q' + 1 := by
        rw [← LG.isLayering.2 ℓ]
        exact lt_of_le_of_lt (LG.layer_le_of_isDesc hul) (hUlt u (hBU hu))
      obtain ⟨u'', hu'', hu''p⟩ := exists_relAttach_isDesc hS hcrit.1 hpS hplt
      exact ⟨u'', hclosed u hu u'' ⟨hBU hu, hu'', ℓ, mem_leavesBelow.2 hul,
        mem_leavesBelow.2 hu''p⟩, hu''p⟩
    have hBac : Antichain LG B := by
      intro s hs s' hs' hne
      exact ⟨fun h => hne (hUac s (hBU hs) s' (hBU hs') h),
        fun h => hne (hUac s' (hBU hs') s (hBU hs) h).symm⟩
    have hBcp : LG.garden.CompletelyPaired (LG.leavesBelowSet B) := by
      intro ℓ hℓ
      obtain ⟨u, hu, hul⟩ := mem_leavesBelowSet.1 hℓ
      have hm := hunm ℓ u hu hul
      refine ⟨fun h => ((LG.garden.pair_eq_iff ℓ).1 h) hm, ?_⟩
      obtain ⟨u'', hu'', hp⟩ := hpairB ℓ u hu hul
      exact mem_leavesBelowSet.2 ⟨u'', hu'', hp⟩
    -- irreducibility of the block
    have hBirr : LG.IrreducibleAt B := by
      intro A hA hAne hAB hAcp
      have hAB' : A ⊆ B := Finset.mem_powerset.1 hA
      -- `A` is closed under the linking relation (both directions)
      have hfwd : ∀ x y, RelLinked LG S (q' + 1) x y → x ∈ A → y ∈ A := by
        intro x y hxy hxA
        obtain ⟨-, hyU, ℓ, hℓx, hpℓy⟩ := hxy
        obtain ⟨a', ha'A, ha'p⟩ :=
          mem_leavesBelowSet.1 (hAcp ℓ (mem_leavesBelowSet.2 ⟨x, hxA, mem_leavesBelow.1 hℓx⟩)).2
        have hpy := mem_leavesBelow.1 hpℓy
        have ha'U := hBU (hAB' ha'A)
        rcases isDesc_total ha'p hpy with h | h
        · exact hUac a' ha'U y hyU h ▸ ha'A
        · exact (hUac y hyU a' ha'U h).symm ▸ ha'A
      have hinv : ∀ x y, Relation.EqvGen (RelLinked LG S (q' + 1)) x y → (x ∈ A ↔ y ∈ A) := by
        intro x y h
        induction h with
        | rel x y hxy => exact ⟨hfwd x y hxy, hfwd y x (relLinked_symm hxy)⟩
        | refl => exact Iff.rfl
        | symm x y _ ih => exact ih.symm
        | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
      apply hAB
      refine Finset.Subset.antisymm hAB' fun b hb => ?_
      obtain ⟨a0, ha0⟩ := hAne
      have h1 := ((hmemB a0).1 (hAB' ha0)).2
      have h2 := ((hmemB b).1 hb).2
      exact (hinv a0 b (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1) h2)).1 ha0
    -- the block has at least four nodes
    have hcard : 4 ≤ B.card := by
      have heven := even_card_of_cp hBac hBcp
      have hpos : B.card ≠ 0 := Finset.card_ne_zero.2 ⟨u0, hu0B⟩
      have hne2 : B.card ≠ 2 := by
        intro h2
        obtain ⟨x, y, hxy, hBxy⟩ := Finset.card_eq_two.1 h2
        have hxB : x ∈ B := by rw [hBxy]; exact Finset.mem_insert_self _ _
        have hyB : y ∈ B := by rw [hBxy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hxU := hBU hxB
        have hyU := hBU hyB
        obtain ⟨hxS, hxq, hxr⟩ := (mem_relAttach LG).1 hxU
        obtain ⟨hyS, hyq, hyr⟩ := (mem_relAttach LG).1 hyU
        have hcpxy : LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) := by
          rw [← leavesBelowSet_pair, ← hBxy]
          exact hBcp
        have := hcrit.2 x y hxS hyS (hBac x hxB y hyB hxy) hcpxy
        rw [hxr, hyr] at this
        omega
      obtain ⟨k, hk⟩ := heven
      omega
    -- the relative criterion for the block
    have hcritB : RelCrit LG B q' := by
      have hle_rpl : ∀ x, LG.BelowSet B x → rpl LG B q' x ≤ rpl LG S (q' + 1) x := by
        intro x hxB
        by_cases hxBm : x ∈ B
        · simp only [rpl, hxBm, ↓reduceIte]
          have := ((mem_relAttach LG).1 (hBU hxBm)).2.2
          unfold rpl at this
          omega
        · obtain ⟨v, hvB, hvx⟩ := hxB
          have hvS : LG.BelowSet S v := ((mem_relAttach LG).1 (hBU hvB)).1
          have hxS : x ∉ S := fun hxS => hxBm (eq_of_below_isDesc_mem hS hvS hxS hvx ▸ hvB)
          obtain ⟨-, -, hrS⟩ := below_par hS (belowSet_of_isDesc hvS hvx) hxS (q := q' + 1)
          obtain ⟨-, -, hrB⟩ := below_par hBac ⟨v, hvB, hvx⟩ hxBm (q := q')
          rw [hrS, hrB]
      refine ⟨fun x ⟨v, hvB, hvx⟩ => ?_, fun x x' hx hx' hinc hcp => ?_⟩
      · have := lt_of_le_of_lt (LG.layer_le_of_isDesc hvx) (hUlt v (hBU hvB))
        omega
      · have hxS : LG.BelowSet S x := by
          obtain ⟨v, hvB, hvx⟩ := hx
          exact belowSet_of_isDesc ((mem_relAttach LG).1 (hBU hvB)).1 hvx
        have hx'S : LG.BelowSet S x' := by
          obtain ⟨v, hvB, hvx⟩ := hx'
          exact belowSet_of_isDesc ((mem_relAttach LG).1 (hBU hvB)).1 hvx
        exact le_trans (min_le_min (hle_rpl x hx) (hle_rpl x' hx'))
          (hcrit.2 x x' hxS hx'S hinc hcp)
    refine ⟨hcard, canonInd_succ.2 ⟨hcard, hBac, hBcp, hBirr, ?_⟩⟩
    refine ih q' (Nat.lt_succ_self q') B false hBac hcritB (fun ℓ hℓ hm => ?_) (fun ℓ hℓ hm => ?_)
    · obtain ⟨u, hu, hul⟩ := hℓ
      obtain ⟨u'', hu'', hp⟩ := hpairB ℓ u hu hul
      exact ⟨u'', hu'', hp⟩
    · obtain ⟨u, hu, hul⟩ := hℓ
      exact absurd (hunm ℓ u hu hul) hm

end Rel

end WaveTurbulence.Canon
