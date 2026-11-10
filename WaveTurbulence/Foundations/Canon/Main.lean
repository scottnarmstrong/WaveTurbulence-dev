/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Canon.Decomp

/-!
# B1.11 `canonicalCharacterization` — proof (packet D3 CANON, pre-freeze)

The relative notions at `S = roots` are the global ones (`rpl = parentLayer`, `relAttach =
attachNodes`, `RelLinked = AttachLinkedOn`, `RelCrit = CanonCriterion`, `IrreducibleAt roots =
Irreducible`, complete pairing below the roots = plain). With (C) and (D) this gives parts (1), (3),
(4); part (2), uniqueness of the construction data, holds for every top-level decomposition with
blocks in the inductive class (the canonicity hypothesis of B1.11 (2) is not needed).
-/

@[expose] public section

open Finset

namespace WaveTurbulence.Canon

open TTree _root_.WaveTurbulence.Canon.Rel

variable {w : ℕ} {LG : LayeredGarden w}

/-! ### The roots -/

theorem mem_roots {a : GNode LG.garden.tree} : a ∈ LG.roots ↔ a.1.2 = [] := by
  simp only [LayeredGarden.roots, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    rfl
  · intro h
    exact ⟨a.1.1, Subtype.ext (Prod.ext rfl h.symm)⟩

theorem root_isDesc_iff {j : Fin w} {a : GNode LG.garden.tree} :
    (GNode.root LG.garden.tree j).IsDesc a ↔ j = a.1.1 :=
  ⟨fun h => h.1, fun h => ⟨h, List.nil_prefix⟩⟩

theorem belowSet_roots (a : GNode LG.garden.tree) : LG.BelowSet LG.roots a :=
  ⟨GNode.root LG.garden.tree a.1.1, Finset.mem_image_of_mem _ (Finset.mem_univ _),
    root_isDesc_iff.2 rfl⟩

theorem antichain_roots : Antichain LG LG.roots := by
  intro s hs s' hs' hne
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hs
  obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hs'
  have hjj : j ≠ j' := fun h => hne (h ▸ rfl)
  exact ⟨fun h => hjj h.1, fun h => hjj h.1.symm⟩

theorem card_roots : LG.roots.card = w := by
  rw [LayeredGarden.roots, Finset.card_image_of_injective _ (fun j j' h => congrArg
    (fun a : GNode LG.garden.tree => a.1.1) h), Finset.card_univ, Fintype.card_fin]

theorem rpl_roots (q : ℕ) (a : GNode LG.garden.tree) :
    rpl LG LG.roots q a = LG.parentLayer q a := by
  unfold rpl
  split_ifs with h
  · simp [LayeredGarden.parentLayer, mem_roots.1 h]
  · rfl

theorem relCrit_roots_iff (q : ℕ) : RelCrit LG LG.roots q ↔ LG.CanonCriterion q := by
  simp only [RelCrit, LayeredGarden.CanonCriterion, rpl_roots]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => h1 a (belowSet_roots a), fun a a' => h2 a a' (belowSet_roots a)
      (belowSet_roots a')⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a _ => h1 a, fun a a' _ _ => h2 a a'⟩

theorem leavesBelowSet_roots_sub {A : Finset (GNode LG.garden.tree)} (hA : A ⊆ LG.roots)
    {ℓ : GLeaf LG.garden.tree} :
    ℓ ∈ LG.leavesBelowSet A ↔ GNode.root LG.garden.tree ℓ.1.1 ∈ A := by
  rw [mem_leavesBelowSet]
  constructor
  · rintro ⟨s, hs, hsl⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (hA hs)
    rw [root_isDesc_iff.1 hsl] at hs
    exact hs
  · intro h
    exact ⟨_, h, root_isDesc_iff.2 rfl⟩

theorem completelyPaired_roots_iff :
    LG.garden.CompletelyPaired (LG.leavesBelowSet LG.roots) ↔ LG.garden.IsPlain := by
  constructor
  · intro h ℓ
    by_contra hm
    exact (h ℓ ((leavesBelowSet_roots_sub subset_rfl).2
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)))).1 ((LG.garden.pair_eq_iff ℓ).2 hm)
  · intro h ℓ _
    refine ⟨fun hp => ((LG.garden.pair_eq_iff ℓ).1 hp) (h ℓ), ?_⟩
    exact (leavesBelowSet_roots_sub subset_rfl).2 (Finset.mem_image_of_mem _ (Finset.mem_univ _))

theorem irreducibleAt_roots_iff : LG.IrreducibleAt LG.roots ↔ LG.garden.Irreducible := by
  classical
  constructor
  · intro h J hJ hJu hcp
    set A := J.image (GNode.root LG.garden.tree) with hAdef
    have hAr : A ⊆ LG.roots := Finset.image_subset_image (Finset.subset_univ _)
    have hmemA : ∀ j, GNode.root LG.garden.tree j ∈ A ↔ j ∈ J := by
      intro j
      simp only [hAdef, Finset.mem_image]
      refine ⟨fun ⟨j', hj', he⟩ => ?_, fun hj => ⟨j, hj, rfl⟩⟩
      have hjj : j' = j := congrArg (fun a : GNode LG.garden.tree => a.1.1) he
      exact hjj ▸ hj'
    have hleaves : LG.leavesBelowSet A = LG.garden.leavesOf J := by
      ext ℓ
      rw [leavesBelowSet_roots_sub hAr, hmemA]
      simp [Garden.leavesOf]
    refine h A (Finset.mem_powerset.2 hAr) ?_ ?_ (hleaves ▸ hcp)
    · obtain ⟨j, hj⟩ := hJ
      exact ⟨_, (hmemA j).2 hj⟩
    · intro hAeq
      apply hJu
      ext j
      simp only [Finset.mem_univ, iff_true]
      exact (hmemA j).1 (hAeq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · intro h A hA hAne hAr hcp
    have hAsub := Finset.mem_powerset.1 hA
    set J := Finset.univ.filter fun j => GNode.root LG.garden.tree j ∈ A with hJdef
    have hleaves : LG.leavesBelowSet A = LG.garden.leavesOf J := by
      ext ℓ
      rw [leavesBelowSet_roots_sub hAsub]
      simp [Garden.leavesOf, hJdef]
    refine h J ?_ ?_ (hleaves ▸ hcp)
    · obtain ⟨a, ha⟩ := hAne
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (hAsub ha)
      exact ⟨j, by simp [hJdef, ha]⟩
    · intro hJu
      apply hAr
      refine Finset.Subset.antisymm hAsub fun a ha => ?_
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
      have : j ∈ J := hJu ▸ Finset.mem_univ j
      simpa [hJdef] using this

/-! ### Part (2): uniqueness of the construction data -/

theorem uniqueness (p : ℕ) (fl : Bool) (U : Finset (GNode LG.garden.tree)) (Bp : Finpartition U)
    (hTD : LG.TopDecompWith fl p (LG.CanonInd p) LG.roots U Bp) :
    U = LG.attachNodes p ∧
      ∀ B ∈ Bp.parts, ∀ u ∈ B, ∀ u' ∈ U,
        (u' ∈ B ↔ Relation.EqvGen (LG.AttachLinkedOn p) u u') := by
  classical
  obtain ⟨h1, h2, -, h4⟩ := hTD
  have hUac : ∀ u ∈ U, ∀ u' ∈ U, u.IsDesc u' → u = u' := fun u hu u' hu' h =>
    (h1 u' hu').2 u hu h
  have hUlt : ∀ u ∈ U, ∀ a, u.IsDesc a → LG.layer a < p := by
    intro u hu a hua
    obtain ⟨B, hB, huB⟩ := Bp.exists_mem hu
    exact layer_lt_of_canonInd p B (h4 B hB).2 a ⟨u, huB, hua⟩
  have hUeq : U = LG.attachNodes p := by
    ext a
    simp only [LayeredGarden.attachNodes, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      refine ⟨hUlt a ha a (GNode.isDesc_refl a), ?_⟩
      by_cases hroot : a.1.2 = []
      · simp [LayeredGarden.parentLayer, hroot]
      · have hparTop : LG.TopRegion LG.roots U (par a) := by
          refine ⟨belowSet_roots _, fun u hu h => ?_⟩
          exfalso
          have hua : u = a := (h1 a ha).2 u hu (h.trans (par_isDesc a))
          subst hua
          exact par_ne hroot (isDesc_antisymm (par_isDesc u) h)
        have hparU : par a ∉ U := fun h => par_ne hroot ((h1 a ha).2 _ h (par_isDesc a))
        have := h2 _ hparTop hparU
        simp only [LayeredGarden.parentLayer, hroot, ↓reduceIte]
        exact this
    · rintro ⟨hlt, hpl⟩
      have htop : LG.TopRegion LG.roots U a := by
        refine ⟨belowSet_roots a, fun u hu h => ?_⟩
        by_contra hne
        have hroot := path_ne_nil_of_isDesc_of_ne h hne
        have h3 := hUlt u hu _ (isDesc_par_of_isDesc_of_ne h hne)
        simp only [LayeredGarden.parentLayer, hroot, ↓reduceIte] at hpl
        change LG.layer (par a) = p at hpl
        omega
      by_contra haU
      have := h2 a htop haU
      omega
  refine ⟨hUeq, ?_⟩
  intro B hB u hu u' hu'
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by
    have := hUlt u (Bp.le hB hu) u (GNode.isDesc_refl u)
    omega⟩
  obtain ⟨-, -, hBcp, hBirr, -⟩ := canonInd_succ.1 (h4 B hB).2
  have hBU : B ⊆ U := Bp.le hB
  -- linking preserves membership in `B`
  have hstep : ∀ x y, LG.AttachLinkedOn (p' + 1) x y → (x ∈ B ↔ y ∈ B) := by
    intro x y hxy
    obtain ⟨hxA, hyA, ℓ, hℓx, hpy⟩ := hxy
    rw [← hUeq] at hxA hyA
    constructor
    · intro hxB
      obtain ⟨b, hbB, hb⟩ := mem_leavesBelowSet.1
        (hBcp ℓ (mem_leavesBelowSet.2 ⟨x, hxB, mem_leavesBelow.1 hℓx⟩)).2
      rcases isDesc_total hb (mem_leavesBelow.1 hpy) with h | h
      · exact hUac b (hBU hbB) y hyA h ▸ hbB
      · exact (hUac y hyA b (hBU hbB) h).symm ▸ hbB
    · intro hyB
      have hpB : LG.garden.pair ℓ ∈ LG.leavesBelowSet B :=
        mem_leavesBelowSet.2 ⟨y, hyB, mem_leavesBelow.1 hpy⟩
      obtain ⟨b, hbB, hb⟩ := mem_leavesBelowSet.1 (hBcp _ hpB).2
      rw [LG.garden.pair_pair] at hb
      rcases isDesc_total hb (mem_leavesBelow.1 hℓx) with h | h
      · exact hUac b (hBU hbB) x hxA h ▸ hbB
      · exact (hUac x hxA b (hBU hbB) h).symm ▸ hbB
  have hinv : ∀ x y, Relation.EqvGen (LG.AttachLinkedOn (p' + 1)) x y → (x ∈ B ↔ y ∈ B) := by
    intro x y h
    induction h with
    | rel x y hxy => exact hstep x y hxy
    | refl => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  constructor
  · intro hu'B
    set A := B.filter fun b => Relation.EqvGen (LG.AttachLinkedOn (p' + 1)) u b with hAdef
    have hAB : A ⊆ B := Finset.filter_subset _ _
    have huA : u ∈ A := Finset.mem_filter.2 ⟨hu, Relation.EqvGen.refl _⟩
    have hAcp : LG.garden.CompletelyPaired (LG.leavesBelowSet A) := by
      intro ℓ hℓ
      obtain ⟨a, haA, hal⟩ := mem_leavesBelowSet.1 hℓ
      have haB := hAB haA
      obtain ⟨hpne, hpB⟩ := hBcp ℓ (mem_leavesBelowSet.2 ⟨a, haB, hal⟩)
      refine ⟨hpne, ?_⟩
      obtain ⟨b, hbB, hb⟩ := mem_leavesBelowSet.1 hpB
      have hlink : LG.AttachLinkedOn (p' + 1) a b := by
        refine ⟨?_, ?_, ℓ, mem_leavesBelow.2 hal, mem_leavesBelow.2 hb⟩
        · rw [← hUeq]; exact hBU haB
        · rw [← hUeq]; exact hBU hbB
      have hbA : b ∈ A := Finset.mem_filter.2 ⟨hbB, Relation.EqvGen.trans _ _ _
        (Finset.mem_filter.1 haA).2 (Relation.EqvGen.rel _ _ hlink)⟩
      exact mem_leavesBelowSet.2 ⟨b, hbA, hb⟩
    by_contra hnot
    have hAne : A ≠ B := fun hAeq => hnot (Finset.mem_filter.1 (hAeq ▸ hu'B : u' ∈ A)).2
    exact hBirr A (Finset.mem_powerset.2 hAB) ⟨u, huA⟩ hAne hAcp
  · intro h
    exact (hinv u u' h).1 hu

/-! ### Parts (1), (3), (4) -/

theorem part1 (p : ℕ) :
    IsCanonG (p + 1) LG ↔ LG.garden.IsPlain ∧ LG.CanonInd (p + 1) LG.roots := by
  constructor
  · rintro ⟨hw, hP, hI, hC⟩
    refine ⟨hP, canonInd_succ.2 ⟨card_roots.symm ▸ hw, antichain_roots,
      completelyPaired_roots_iff.2 hP, irreducibleAt_roots_iff.2 hI, ?_⟩⟩
    refine topDecomp_of_relCrit p LG.roots false antichain_roots ((relCrit_roots_iff p).2 hC)
      (fun ℓ _ _ => belowSet_roots _) (fun ℓ _ hm => absurd (hP ℓ) hm)
  · rintro ⟨hP, hInd⟩
    obtain ⟨hcard, hac, -, hirr, htd⟩ := canonInd_succ.1 hInd
    obtain ⟨U, Bp, hTD⟩ := unfold_topDecomp htd
    exact ⟨card_roots (LG := LG) ▸ hcard, hP, irreducibleAt_roots_iff.1 hirr,
      (relCrit_roots_iff p).1 (relCrit_of_topDecomp p LG.roots false U Bp hac hTD)⟩

theorem part3 (p : ℕ) (LG2 : LayeredGarden 2) :
    IsCanonC (p + 1) LG2 ↔ IsCouple LG2.garden ∧
      (∀ s ∈ LG2.roots, ∀ s' ∈ LG2.roots, s ≠ s' → s.Incomparable s') ∧
      LG2.TopDecomp false p (LG2.CanonInd p) LG2.roots := by
  constructor
  · rintro ⟨hcpl, hC⟩
    refine ⟨hcpl, antichain_roots, ?_⟩
    exact topDecomp_of_relCrit p LG2.roots false antichain_roots ((relCrit_roots_iff p).2 hC)
      (fun ℓ _ _ => belowSet_roots _) (fun ℓ _ hm => absurd (hcpl.1 ℓ) hm)
  · rintro ⟨hcpl, hac, htd⟩
    obtain ⟨U, Bp, hTD⟩ := unfold_topDecomp htd
    exact ⟨hcpl, (relCrit_roots_iff p).1 (relCrit_of_topDecomp p LG2.roots false U Bp hac hTD)⟩

theorem part4 (p : ℕ) :
    IsCanonH (p + 1) LG ↔ LG.garden.IsFlowerGarden ∧
      LG.TopDecomp true p (LG.CanonInd p) LG.roots := by
  constructor
  · rintro ⟨hFG, hstem, hC⟩
    refine ⟨hFG, topDecomp_of_relCrit p LG.roots true antichain_roots ((relCrit_roots_iff p).2 hC)
      (fun ℓ _ _ => belowSet_roots _) (fun ℓ _ hm => ⟨rfl, hFG.2.1 ℓ hm, fun c hc _ => ?_⟩)⟩
    exact hstem c ⟨ℓ, hFG.2.1 ℓ hm, hc⟩
  · rintro ⟨hFG, htd⟩
    obtain ⟨U, Bp, hTD⟩ := unfold_topDecomp htd
    refine ⟨hFG, ?_, (relCrit_roots_iff p).1
      (relCrit_of_topDecomp p LG.roots true U Bp antichain_roots hTD)⟩
    obtain ⟨h1, h2, -, h4⟩ := hTD
    rintro a ⟨f, hf, haf⟩
    -- the flower lies below no attachment node
    have hfree : ∀ u ∈ U, ¬ u.IsDesc f.toNode := by
      intro u hu huf
      obtain ⟨B, hB, huB⟩ := Bp.exists_mem hu
      have hcan := (h4 B hB).2
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by
        have := layer_lt_of_canonInd p B hcan u ⟨u, huB, GNode.isDesc_refl u⟩
        omega⟩
      obtain ⟨-, -, hBcp, -, -⟩ := canonInd_succ.1 hcan
      have hfm : LG.garden.mark f ≠ none := by
        rw [show LG.garden.mark f = _ from hf]
        simp
      exact (hBcp f (mem_leavesBelowSet.2 ⟨u, huB, huf⟩)).1 ((LG.garden.pair_eq_iff f).2 hfm)
    have htop : LG.TopRegion LG.roots U a :=
      ⟨belowSet_roots a, fun u hu hua => absurd (hua.trans haf) (hfree u hu)⟩
    have haU : a ∉ U := fun h => hfree a h haf
    exact h2 a htop haU

/-! ### B1.11 -/

/-- **B1.11 `canonicalCharacterization`, proved** (statement of snapshot 3, verbatim). -/
theorem canonicalCharacterization {w : ℕ} (p : ℕ) (LG : LayeredGarden w) :
    (IsCanonG (p + 1) LG ↔ LG.garden.IsPlain ∧ LG.CanonInd (p + 1) LG.roots) ∧
    ((IsCanonGC (p + 1) LG ∨ IsCanonH (p + 1) LG) →
      ∀ (flowers : Bool) (U : Finset (GNode LG.garden.tree)) (Bp : Finpartition U),
        LG.TopDecompWith flowers p (LG.CanonInd p) LG.roots U Bp →
        U = LG.attachNodes p ∧
          ∀ B ∈ Bp.parts, ∀ u ∈ B, ∀ u' ∈ U,
            (u' ∈ B ↔ Relation.EqvGen (LG.AttachLinkedOn p) u u')) ∧
    (∀ LG2 : LayeredGarden 2, IsCanonC (p + 1) LG2 ↔ IsCouple LG2.garden ∧
      (∀ s ∈ LG2.roots, ∀ s' ∈ LG2.roots, s ≠ s' → s.Incomparable s') ∧
      LG2.TopDecomp false p (LG2.CanonInd p) LG2.roots) ∧
    (IsCanonH (p + 1) LG ↔ LG.garden.IsFlowerGarden ∧
      LG.TopDecomp true p (LG.CanonInd p) LG.roots) :=
  ⟨part1 p, fun _ fl U Bp hTD => uniqueness p fl U Bp hTD, fun LG2 => part3 p LG2, part4 p⟩

end WaveTurbulence.Canon
