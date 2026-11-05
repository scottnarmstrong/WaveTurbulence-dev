/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerGraft

/-!
# X2E-2, step 4: pairing the flowers of the flower graft gives the plain graft

**Statement** (`pairedGraft_eq`). For flower graft data `D`, pairing the flowers `𝔣_j ↔ 𝔣_{j⊕1}` of
`flowerGraft D` (`pairFl`) gives the plain graft `D.base.graft`.

**Proof.** Both are grafts of the same top forest and partition; the components differ only at the pair blocks,
which are two leaf trees in layer `p` (marked flowers in the flower graft, a terminal pair in the plain graft).
The gardens are compared on raw addresses (INDUCT's `garden_eq_of_raw_data`, `layeredGarden_eq_of_raw_data`):
- a flower `(j, 𝔣_j)` is paired in `pairFl` with the flower of tree `j ⊕ 1`, and in the plain graft with the other
  leaf of its terminal pair, which is also `(j ⊕ 1, 𝔣_{j⊕1})`;
- every other leaf has the pairing of its component, which is the same in both;
- the layers agree component by component.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ)

/-- The flower graft with its flowers paired. -/
noncomputable def pairedGraft : LayeredGarden (2 * Pm) :=
  pairFl D.flowerGraft partner partner_involutive partner_ne D.flowerGraft_isFlowerGarden ζ
    (fun j => altFlowerSig_partner j) D.flowerGraft_flower_sign D.flowerGraft_flower_layer

theorem flowerOf_flowerGraft (j : Fin (2 * Pm)) : LayeredGarden'.flowerOf D.flowerGraft j = D.flLeaf j := by
  have h := LayeredGarden'.eq_flowerOf D.flowerGraft_isFlowerGarden (D.mark_flLeaf j)
  rw [D.flLeaf_val] at h
  exact h.symm

/-- The leaf equivalence of the plain graft. -/
noncomputable abbrev eBase :=
  gardenLeafEquiv D.base.top D.base.partition (fun B => (D.base.low B).garden)

theorem base_garden_eq :
    markedGardenGraft (altFlowerSig Pm) D.base.top D.base.partition (fun B => (D.base.low B).garden)
      D.base.sign = D.base.graft.garden :=
  markedGardenGraft_eq_gardenGraft _ _ _ _ D.base.plain D.base.sign

/-- In the plain graft, the flower of tree `j` is paired with the flower of tree `j ⊕ 1`. -/
theorem base_pair_flower (j : Fin (2 * Pm)) (b : GLeaf D.base.graft.garden.tree) (hb : b.1 = (j, D.fl j)) :
    (D.base.graft.garden.pair b).1 = (partner j, D.fl (partner j)) := by
  let M := markedGardenGraft (altFlowerSig Pm) D.base.top D.base.partition (fun B => (D.base.low B).garden)
    D.base.sign
  have hM : (D.base.graft.garden.pair b).1 = (M.pair b).1 := garden_pair_raw_of_eq D.base_garden_eq.symm b b rfl
  rw [hM]
  let z := D.eBase b
  have hval := graftLeaf_val D.base.top D.base.partition (fun B => (D.base.low B).garden) b
  let ℓ := (blockRootEquiv D.base.top D.base.partition).symm ⟨z.1, z.2.1.1⟩
  have hℓ1 : ℓ.1.1 = j := by
    have h := congrArg Prod.fst (hval.symm.trans hb)
    exact h
  have hℓ2 : ℓ.1.2 ++ z.2.1.2 = D.fl j := by
    have h := congrArg Prod.snd (hval.symm.trans hb)
    exact h
  have hℓleaf : ℓ.1.2 ∈ (D.base.top j).leaves := by
    have h := ℓ.2
    rw [hℓ1] at h
    exact h
  have hpre : ℓ.1.2 = D.fl j := leaf_eq_of_prefix (D.base.top j) hℓleaf (D.fl_mem j) (hℓ2 ▸ List.prefix_append _ _)
  have hℓeq : ℓ = D.flAt j := Subtype.ext (Prod.ext hℓ1 hpre)
  have hz1 : z.1 = ⟨D.pairBlock j, D.pairBlock_mem j⟩ := by
    have h1 : blockRootEquiv D.base.top D.base.partition ℓ = ⟨z.1, z.2.1.1⟩ := Equiv.apply_symm_apply _ _
    have h2 := D.part_flAt j
    rw [← hℓeq, h1] at h2
    exact h2
  have hpair : D.IsPairBlock z.1.1 := ⟨j, by rw [hz1]⟩
  have htree := D.tree_of_isPairBlock hpair
  let y := (D.base.low z.1).garden.pair z.2
  have hyne : y ≠ z.2 := fun h => ((D.base.low z.1).garden.pair_eq_iff z.2).mp h (D.base.plain _ _)
  have hynil := leaf_path_nil htree y
  have hznil := leaf_path_nil htree z.2
  have hk : y.1.1 ≠ z.2.1.1 := fun h => hyne (Subtype.ext (Prod.ext h (hynil.trans hznil.symm)))
  let ℓ' := (blockRootEquiv D.base.top D.base.partition).symm ⟨z.1, y.1.1⟩
  have hℓ'ne : ℓ' ≠ D.flAt j := by
    rw [← hℓeq]
    intro h
    have h' := (blockRootEquiv D.base.top D.base.partition).symm.injective h
    exact hk (eq_of_heq (Sigma.mk.inj h').2)
  have hℓ' : ℓ' = D.flAt (partner j) := by
    rcases D.root_of_isPairBlock (j := j) (by rw [hz1]) y.1.1 with h | h
    · exact absurd h hℓ'ne
    · exact h
  have hv := gardenLeafEquiv_symm_val D.base.top D.base.partition (fun B => (D.base.low B).garden) z.1 y
  change ((D.eBase).symm ⟨z.1, y⟩).1 = _
  rw [hv]
  change (ℓ'.1.1, ℓ'.1.2 ++ y.1.2) = _
  rw [hynil, List.append_nil, hℓ']
  rfl

theorem paired_pair_raw (a : GLeaf D.flowerGraft.garden.tree) (b : GLeaf D.base.graft.garden.tree)
    (hab : a.1 = b.1) : (pairFlPair D.flowerGraft partner a).1 = (D.base.graft.garden.pair b).1 := by
  obtain ⟨⟨B, x⟩, rfl⟩ := (D.eFl).symm.surjective a
  by_cases hm : D.flowerGraft.garden.mark ((D.eFl).symm ⟨B, x⟩) = none
  · rw [pairFlPair_unmarked _ _ hm]
    have hB : ¬ D.IsPairBlock B.1 := by
      intro h
      have h' := D.mark_ne_none_iff ((D.eFl).symm ⟨B, x⟩)
      rw [Equiv.apply_symm_apply] at h'
      exact h'.mpr h hm
    let x' : GLeaf (D.base.low B).garden.tree := ⟨x.1, D.mem_base_leaves B x⟩
    have hraw1 := gardenLeafEquiv_symm_val D.base.top D.base.partition (fun B => (D.lowFl B).garden) B x
    have hraw2 := gardenLeafEquiv_symm_val D.base.top D.base.partition (fun B => (D.base.low B).garden) B x'
    have hb : b = (D.eBase).symm ⟨B, x'⟩ := by
      apply Subtype.ext
      rw [← hab]
      exact hraw1.trans hraw2.symm
    subst hb
    have h1 : D.flowerGraft.garden.pair ((D.eFl).symm ⟨B, x⟩) =
        (D.eFl).symm ⟨B, (D.lowFl B).garden.pair x⟩ :=
      markedGardenGraft_pair_lower (altFlowerSig Pm) D.base.top D.base.partition (fun B => (D.lowFl B).garden)
        D.lowFl_sig B x
    have h2 := garden_pair_raw_of_eq D.base_garden_eq.symm ((D.eBase).symm ⟨B, x'⟩) ((D.eBase).symm ⟨B, x'⟩) rfl
    have h3 : (markedGardenGraft (altFlowerSig Pm) D.base.top D.base.partition (fun B => (D.base.low B).garden)
        D.base.sign).pair ((D.eBase).symm ⟨B, x'⟩) = (D.eBase).symm ⟨B, (D.base.low B).garden.pair x'⟩ :=
      markedGardenGraft_pair_lower (altFlowerSig Pm) D.base.top D.base.partition
        (fun B => (D.base.low B).garden) D.base.sign B x'
    rw [h1, h2, h3]
    have hr1 := gardenLeafEquiv_symm_val D.base.top D.base.partition (fun B => (D.lowFl B).garden) B
      ((D.lowFl B).garden.pair x)
    have hr2 := gardenLeafEquiv_symm_val D.base.top D.base.partition (fun B => (D.base.low B).garden) B
      ((D.base.low B).garden.pair x')
    rw [hr1, hr2]
    have hp := garden_pair_raw_of_eq (congrArg LayeredGarden.garden (D.lowFl_of_not hB)) x x' rfl
    simp only [hp]
  · rw [pairFlPair_marked _ _ hm, D.flowerOf_flowerGraft]
    have ha := D.eq_flLeaf_of_marked hm
    have hval : ((D.eFl).symm ⟨B, x⟩).1 =
        (((D.eFl).symm ⟨B, x⟩).1.1, D.fl ((D.eFl).symm ⟨B, x⟩).1.1) := by
      conv_lhs => rw [ha]
      exact D.flLeaf_val _
    rw [D.base_pair_flower _ b (hab.symm.trans hval), D.flLeaf_val]

theorem paired_layer_raw (a : GNode D.flowerGraft.garden.tree) (b : GNode D.base.graft.garden.tree)
    (hab : a.1 = b.1) : D.flowerGraft.layer a = D.base.graft.layer b := by
  change graftLayer D.base.top D.base.partition D.lowFl p a = graftLayer D.base.top D.base.partition D.base.low p b
  obtain ⟨y, rfl⟩ := (gardenNodeEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden)).surjective a
  rcases y with c | ⟨B, x⟩
  · have hb : b = gardenNodeEquiv D.base.top D.base.partition (fun B => (D.base.low B).garden) (.inl c) := by
      apply Subtype.ext
      rw [← hab, gardenNodeEquiv_top_val, gardenNodeEquiv_top_val]
    rw [hb, graftLayer_top, graftLayer_top]
  · let x' : GNode (D.base.low B).garden.tree := ⟨x.1, by
      have h : x.1.2 ∈ ((D.lowFl B).garden.tree x.1.1).nodes := x.2
      rw [congrFun (D.lowFl_tree B) x.1.1] at h
      exact h⟩
    have hb : b = gardenNodeEquiv D.base.top D.base.partition (fun B => (D.base.low B).garden)
        (.inr ⟨B, x'⟩) := by
      apply Subtype.ext
      rw [← hab, gardenNodeEquiv_lower_val, gardenNodeEquiv_lower_val]
    rw [hb, graftLayer_lower, graftLayer_lower]
    by_cases hB : D.IsPairBlock B.1
    · rw [D.layer_of_isPairBlock hB x']
      have hr := layeredGarden_layer_raw_of_eq (D.lowFl_of_pair hB) x
        (⟨x.1, by
          have h : x.1.2 ∈ ((D.lowFl B).garden.tree x.1.1).nodes := x.2
          rw [congrFun (D.lowFl_tree_leaf hB) x.1.1] at h
          exact h⟩ : GNode (markedLeafLG B.1.card (D.base.low B).garden.sig p).garden.tree) rfl
      rw [hr]
      rfl
    · exact layeredGarden_layer_raw_of_eq (D.lowFl_of_not hB) x x' rfl

/-- **Pairing the flowers of the flower graft gives the plain graft.** -/
theorem pairedGraft_eq : D.pairedGraft = D.base.graft := by
  apply layeredGarden_eq_of_raw_data
  · apply garden_eq_of_raw_data
    · rfl
    · exact D.flowerGraft_tree
    · exact fun a b hab => D.paired_pair_raw a b hab
    · intro a b _
      exact (D.base.graft_plain b).symm
  · exact fun a b hab => D.paired_layer_raw a b hab

end FlowerGraftData

end WaveTurbulence.X2E
