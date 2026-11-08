/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Defs

/-! # A1 MK-DEFS: the card bound of the protected set `Π` (`ProtectedCardBound`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

namespace WaveTurbulence.Flower.MkDefs

variable {w : ℕ}

/-- The unit neighbourhood of a seed node. -/
def nearSet {tree : Fin w → TTree} (s : GNode tree) : Finset (GNode tree) :=
  Finset.univ.filter fun a => NearNode a s

theorem nearSet_card_le {tree : Fin w → TTree} (s : GNode tree) : (nearSet s).card ≤ 5 := by
  classical
  let T : Finset (Fin w × TTree.Path) :=
    insert s.1 (insert (s.1.1, s.1.2.dropLast) (Finset.univ.image fun i : Fin 3 => (s.1.1, s.1.2 ++ [i])))
  have hT : T.card ≤ 5 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have h2 : (insert (s.1.1, s.1.2.dropLast)
        (Finset.univ.image fun i : Fin 3 => (s.1.1, s.1.2 ++ [i]))).card ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i : Fin 3 => (s.1.1, s.1.2 ++ [i]))
      simp at this
      omega
    omega
  have hinj : Function.Injective (fun a : GNode tree => a.1) := Subtype.val_injective
  have hcard : (nearSet s).card = ((nearSet s).image fun a : GNode tree => a.1).card :=
    (Finset.card_image_of_injective _ hinj).symm
  have hsub : (nearSet s).image (fun a : GNode tree => a.1) ⊆ T := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hn : NearNode a s := by simpa [nearSet] using ha
    obtain ⟨h1, h2 | ⟨_, h3⟩ | ⟨hne, h4⟩⟩ := hn
    · have : a.1 = s.1 := Prod.ext h1 h2
      simp [T, this]
    · simp only [T, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
      right; left
      exact Prod.ext h1 h3
    · simp only [T, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
      right; right
      have hl : a.1.2 = a.1.2.dropLast ++ [a.1.2.getLast hne] := (List.dropLast_append_getLast hne).symm
      refine ⟨a.1.2.getLast hne, ?_⟩
      refine Prod.ext h1.symm ?_
      show s.1.2 ++ [a.1.2.getLast hne] = a.1.2
      rw [← h4]; exact hl.symm
  have := Finset.card_le_card hsub
  omega

/-- `ProtectedCardBound`: the protected set has at most five nodes per seed. -/
theorem protectedCardBound : ProtectedCardBound := by
  classical
  intro w LG J fix sel
  let S1 : Finset (GNode LG.garden.tree) :=
    (Finset.univ.filter fun j : Fin w => j ∉ J).image fun j => GNode.root LG.garden.tree j
  let S2 : Finset (GNode LG.garden.tree) :=
    (Finset.univ.filter fun b : GBranch LG.garden.tree => (fix b).isSome).image fun b => b.toNode
  let S3 : Finset (GNode LG.garden.tree) := sel.image fun b => b.toNode
  have hsub : protectedSet LG J fix sel ⊆ (S1 ∪ S2 ∪ S3).biUnion nearSet := by
    intro a ha
    simp only [protectedSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨s, hs, hseed⟩ := ha
    simp only [Finset.mem_biUnion, nearSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨s, ?_, hs⟩
    rcases hseed with ⟨hJ, hnil⟩ | ⟨b, hb, hfs | hsel⟩
    · have : s = GNode.root LG.garden.tree s.1.1 := by
        apply Subtype.ext
        exact Prod.ext rfl hnil
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      exact Finset.mem_image.mpr ⟨s.1.1, by simpa using hJ, this.symm⟩
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      exact Finset.mem_image.mpr ⟨b, by simpa using hfs, hb⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hsel, hb⟩)
  calc (protectedSet LG J fix sel).card
      ≤ ((S1 ∪ S2 ∪ S3).biUnion nearSet).card := Finset.card_le_card hsub
    _ ≤ (S1 ∪ S2 ∪ S3).card * 5 := Finset.card_biUnion_le_card_mul _ _ _ fun s _ => nearSet_card_le s
    _ ≤ (S1.card + S2.card + S3.card) * 5 := by
        have := Finset.card_union_le (S1 ∪ S2) S3
        have := Finset.card_union_le S1 S2
        nlinarith
    _ ≤ 5 * ((Finset.univ.filter fun j : Fin w => j ∉ J).card +
        (Finset.univ.filter fun b : GBranch LG.garden.tree => (fix b).isSome).card + sel.card) := by
        have h1 : S1.card ≤ (Finset.univ.filter fun j : Fin w => j ∉ J).card := Finset.card_image_le
        have h2 : S2.card ≤ (Finset.univ.filter fun b : GBranch LG.garden.tree => (fix b).isSome).card :=
          Finset.card_image_le
        have h3 : S3.card ≤ sel.card := Finset.card_image_le
        nlinarith

end WaveTurbulence.Flower.MkDefs
