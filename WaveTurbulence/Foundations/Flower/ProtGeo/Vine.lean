/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Sel

/-! # D2b PROT-GEO (8): item (iv), no unmarked vine has a selected time argument (o73 §17)

On a prime reconstruction `A : VineA.PrimeData LG` (skeleton `S = A.skeleton`, regular trees `A.data.tree`), the
carrier vertex of a skeleton branch `y` is `skelAddr S X y = addrExt (inflatedPosition y) (X y).lonePath`. The time
arguments of a spliced (CL) vine kernel are those of its upper joint `u₁` and of the children `u₂₁, u₂₂` of its lower
joint (T1956). With the world's concrete marking `markI` (enlarged rule, `protI`):
* `marked_of_sel_lowerChild`: if the carrier vertex of a child of the lower joint is selected, the vine is marked;
* `marked_of_sel_upper`: if the carrier vertex of the upper joint is selected, the vine is marked (its child toward
  the vine, or the regular object containing it, is protected: `upper_internal_child`).
Region facts: `skelAddr_mem_ownRegion`, `inflatedPosition_mem_ownRegion`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ}

/-! ## Inflated positions and owned regions -/

/-- The carrier address of the skeleton branch `y` (the end of the lone path of its inflated regular tree). -/
def skelAddr (S : Garden w) (X : GBranch S.tree → RegChain) (y : GBranch S.tree) : Fin w × Path :=
  addrExt (inflatedPosition S X y.toNode) (X y).lonePath

theorem addrBelow_trans {x y z : Address w} (h1 : AddrBelow x y) (h2 : AddrBelow y z) : AddrBelow x z :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem addrBelow_addrExt (x : Address w) (q : Path) : AddrBelow x (addrExt x q) :=
  ⟨rfl, List.prefix_append _ _⟩

theorem not_addrBelow_ext {x : Address w} {q : Path} (hq : q ≠ []) : ¬ AddrBelow (addrExt x q) x := by
  rintro ⟨-, h⟩
  have := h.length_le
  simp only [addrExt, List.length_append] at this
  have : q.length ≠ 0 := fun h0 => hq (List.length_eq_zero_iff.mp h0)
  omega

theorem inflatedPosition_parent (S : Garden w) (X : GBranch S.tree → RegChain) (c : GNode S.tree)
    (hc : c.1.2 ≠ []) :
    inflatedPosition S X c =
      addrExt (inflatedPosition S X (c.parent hc).toNode) ((X (c.parent hc)).lonePath ++ [c.1.2.getLast hc]) := by
  rw [inflatedPosition, dite_eq_right hc]

theorem node_eq_child_of_parent {S : Garden w} {c : GNode S.tree} (hc : c.1.2 ≠ []) {y : GBranch S.tree}
    (h : c.parent hc = y) : c = y.child (c.1.2.getLast hc) := by
  subst h
  exact Subtype.ext (Prod.ext rfl (List.dropLast_append_getLast hc).symm)

/-- The inflated positions of the proper descendants of `y` lie below those of its children. -/
theorem inflated_desc (S : Garden w) (X : GBranch S.tree → RegChain) (y : GBranch S.tree) :
    ∀ (n : ℕ) (c : GNode S.tree), c.1.2.length ≤ n → y.toNode.IsDesc c → c ≠ y.toNode →
      ∃ i : Fin 3, AddrBelow (inflatedPosition S X (y.child i)) (inflatedPosition S X c) := by
  intro n
  induction n with
  | zero =>
    intro c hl hd hne
    exfalso; apply hne
    have hc : c.1.2 = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    have hy : y.1.2 = [] := by have := hd.2; rw [hc] at this; exact List.prefix_nil.mp this
    exact Subtype.ext (Prod.ext hd.1.symm (hc.trans hy.symm))
  | succ n ih =>
    intro c hl hd hne
    have hc : c.1.2 ≠ [] := by
      intro hc
      apply hne
      have hy : y.1.2 = [] := by have := hd.2; rw [hc] at this; exact List.prefix_nil.mp this
      exact Subtype.ext (Prod.ext hd.1.symm (hc.trans hy.symm))
    let pc := c.parent hc
    have hpre : y.1.2 <+: pc.1.2 := by
      have h1 := hd.2
      have hcl : c.1.2 = pc.1.2 ++ [c.1.2.getLast hc] := (List.dropLast_append_getLast hc).symm
      rw [hcl] at h1
      rcases List.prefix_concat_iff.mp h1 with h2 | h2
      · exfalso; apply hne; exact Subtype.ext (Prod.ext hd.1.symm (hcl.trans h2.symm))
      · exact h2
    by_cases hpy : pc = y
    · refine ⟨c.1.2.getLast hc, ?_⟩
      have := node_eq_child_of_parent hc hpy
      rw [← this]
      exact ⟨rfl, List.prefix_refl _⟩
    · rw [inflatedPosition_parent S X c hc]
      have hpd : y.toNode.IsDesc pc.toNode := ⟨hd.1, hpre⟩
      have hpne : pc.toNode ≠ y.toNode :=
        fun h' => hpy (Subtype.ext (show pc.1 = y.1 from congrArg (fun z : GNode S.tree => z.1) h'))
      have hpl : pc.toNode.1.2.length ≤ n := by
        show c.1.2.dropLast.length ≤ n
        rw [List.length_dropLast]; omega
      obtain ⟨i, hi⟩ := ih pc.toNode hpl hpd hpne
      exact ⟨i, addrBelow_trans hi (addrBelow_addrExt _ _)⟩

/-- The carrier vertex of a skeleton branch lies in the region it owns. -/
theorem skelAddr_mem_ownRegion (S : Garden w) (X : GBranch S.tree → RegChain) (y : GBranch S.tree) :
    skelAddr S X y ∈ ownRegion S X y.toNode := by
  refine ⟨addrBelow_addrExt _ _, fun c hd hne hb => ?_⟩
  obtain ⟨i, hi⟩ := inflated_desc S X y _ c le_rfl hd hne
  have h := addrBelow_trans hi hb
  rw [inflatedPosition_child] at h
  have h2 : (inflatedPosition S X y.toNode).2 ++ ((X y).lonePath ++ [i]) <+:
      (inflatedPosition S X y.toNode).2 ++ (X y).lonePath := h.2
  have := ((List.prefix_append_right_inj _).mp h2).length_le
  simp at this

/-- The inflated position of a skeleton node lies in the region it owns. -/
theorem inflatedPosition_mem_ownRegion (S : Garden w) (X : GBranch S.tree → RegChain) (z : GNode S.tree) :
    inflatedPosition S X z ∈ ownRegion S X z := by
  refine ⟨⟨rfl, List.prefix_refl _⟩, fun c hd hne hb => ?_⟩
  -- `z` has a proper descendant, hence is a branching node
  obtain ⟨r, hr⟩ := hd.2
  have hr0 : r ≠ [] := by
    rintro rfl; apply hne; exact Subtype.ext (Prod.ext hd.1.symm (by simpa using hr.symm))
  obtain ⟨k, r', rfl⟩ := List.exists_cons_of_ne_nil hr0
  have hn : z.1.2 ++ [k] ∈ (S.tree z.1.1).nodes := by
    refine Comb.TreePath.mem_nodes_of_prefix _ (q := c.1.2) ?_ ⟨r', ?_⟩
    · rw [hd.1]; exact c.2
    · rw [← hr]; simp
  let zb : GBranch S.tree := ⟨z.1, Comb.TreePath.branching_of_append_mem _ hn⟩
  have hzb : zb.toNode = z := rfl
  obtain ⟨i, hi⟩ := inflated_desc S X zb _ c le_rfl (hzb ▸ hd) (hzb ▸ hne)
  have h := addrBelow_trans hi hb
  rw [inflatedPosition_child, hzb] at h
  exact not_addrBelow_ext (by simp) h

theorem mem_nearRegion_own {S : Garden w} {X : GBranch S.tree → RegChain} {b : GBranch S.tree}
    {x : Address w} (h : x ∈ ownRegion S X b.toNode) : x ∈ nearRegion S X b :=
  Set.mem_union_left _ (Set.mem_union_left _ h)

theorem mem_nearRegion_child {S : Garden w} {X : GBranch S.tree → RegChain} {b : GBranch S.tree} (i : Fin 3)
    {x : Address w} (h : x ∈ ownRegion S X (b.child i)) : x ∈ nearRegion S X b :=
  Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, h⟩))

theorem mem_nearRegion_partner {S : Garden w} {X : GBranch S.tree → RegChain} {b : GBranch S.tree}
    {ℓ : GLeaf S.tree} (hℓ : b.IsParentOf ℓ) {x : Address w} (h : x ∈ ownRegion S X (S.pair ℓ).toNode) :
    x ∈ nearRegion S X b :=
  Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨ℓ, Set.mem_iUnion.mpr ⟨hℓ, h⟩⟩)

/-! ## Protected vertices around a selected vertex -/

variable {LG : LayeredGarden w} {J : Finset (Fin w)}

theorem sel_mem_protI (pat : Fin w → FixPat) (t s : ℝ) {kSel : Fin w → Option ℕ} {v : GBranch LG.garden.tree}
    (hv : v ∈ selSetCap LG J kSel) : v.toNode ∈ protI LG J pat t s kSel := by
  unfold protI protectedSet
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.toNode, ⟨rfl, Or.inl rfl⟩, Or.inr ⟨v, rfl, Or.inr hv⟩⟩

/-! ## The internal bond of the upper joint -/

/-- **The upper joint of a (CL) vine has a child toward the vine**: a branching child that is a non-upper atom, or a
leaf child whose partner's parent is a non-upper atom (block axioms: connectedness, parent outside). -/
theorem upper_internal_child {S : Garden w} (c : Stage1.CLVine S) :
    ∃ (i : Fin 3) (b : GBranch S.tree), b ∈ c.atoms ∧ b ≠ c.upper ∧
      (b.toNode = c.upper.child i ∨ ∃ ℓ : GLeaf S.tree, ℓ.toNode = c.upper.child i ∧ b.IsParentOf (S.pair ℓ)) := by
  obtain ⟨Xt, hV⟩ := c.isVine
  have hB := hV.1
  have hup : c.upper ∈ c.atoms := hB.2.1
  have hlow : c.lower ∈ c.atoms := hB.2.2.1
  have hne : c.upper ≠ c.lower := hB.2.2.2.1
  have hconn := hB.2.2.2.2.2.2.2.2.2 c.upper hup c.lower hlow
  have hx : ∃ x, S.molecule.InGroup c.atoms x ∧ S.molecule.atom x = c.upper ∧
      S.molecule.atom (S.molecule.mate x) ≠ c.upper := by
    by_contra hno
    push Not at hno
    have key : ∀ a b, Relation.EqvGen (fun a b => ∃ x, S.molecule.InGroup c.atoms x ∧ S.molecule.atom x = a ∧
        S.molecule.atom (S.molecule.mate x) = b) a b → (a = c.upper ↔ b = c.upper) := by
      intro a b hab
      induction hab with
      | rel a b hr =>
        obtain ⟨x, hxg, hxa, hxb⟩ := hr
        constructor
        · intro ha; rw [← hxb]; exact hno x hxg (hxa.trans ha)
        · intro hb
          have hyg : S.molecule.InGroup c.atoms (S.molecule.mate x) := by
            refine ⟨hxg.2, ?_⟩; rw [S.molecule.mate_mate]; exact hxg.1
          have := hno _ hyg (hxb.trans hb)
          rw [S.molecule.mate_mate] at this
          rw [← hxa]; exact this
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact hne ((key _ _ hconn).mp rfl).symm
  obtain ⟨x, hxg, hxa, hxb⟩ := hx
  have hbS := hxg.2
  rcases x with ⟨⟨c', hc'⟩, bb⟩ | ⟨ℓ, hm, hl1, hl2⟩
  · cases bb with
    | false =>
      -- the dart at the child end: its partner is the parent of the upper joint, inside the vine
      exfalso
      apply c.notParentUpper
      change c' = c.upper at hxa
      subst hxa
      exact ⟨hc', hbS⟩
    | true =>
      change GNode.parent c'.toNode hc' = c.upper at hxa
      refine ⟨c'.1.2.getLast hc', c', hbS, hxb, Or.inl ?_⟩
      exact node_eq_child_of_parent (c := c'.toNode) hc' hxa
  · change GNode.parent ℓ.toNode hl1 = c.upper at hxa
    refine ⟨ℓ.1.2.getLast hl1, GNode.parent (S.pair ℓ).toNode hl2, hbS, hxb, Or.inr ⟨ℓ, ?_, ?_⟩⟩
    · exact node_eq_child_of_parent (c := ℓ.toNode) hl1 hxa
    · exact ⟨rfl, (S.pair ℓ).1.2.getLast hl2, (List.dropLast_append_getLast hl2).symm⟩

/-! ## Marking -/

end WaveTurbulence.Flower.ProtGeo
