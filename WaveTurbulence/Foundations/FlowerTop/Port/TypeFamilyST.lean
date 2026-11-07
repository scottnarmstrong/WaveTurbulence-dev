/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TypeFamily
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerP1Stub
/-! AMEND-ST (R61 X4): ANCHORED pair types with profile 1, exempt from `Bounded` and `size`.

The anchors of a garden (design C) are trivial trees `J ⊆ Fin w` with fixed labels; every pair `(ℓ, ℓ')` whose
partner leaf `ℓ'` lies in an anchor tree has profile `1` (`FlowerP1.AnchorOne`), carries no bound (`BoundedAnch`)
and contributes the factor `1` to the leaf size (`toLeafFamilyAnch`, `size_anch_eq`). With no anchors
(`J = ∅`) everything is the current `TypeFamily` data (`toLeafFamilyAnch_empty`, `boundedAnch_empty_iff`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

theorem pairTrees_leaf {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) :
    pairTrees G ℓ.1 = (ℓ.1.1, (G.pair ℓ).1.1) := by
  have he : ∃ ℓ' : GLeaf G.tree, ℓ'.1 = ℓ.1 := ⟨ℓ, rfl⟩
  have hc : he.choose = ℓ := Subtype.ext he.choose_spec
  unfold pairTrees
  rw [dif_pos he, hc]

/-- Pair-type profiles with anchors: a leaf whose partner lies in an anchor tree `J` has the profile `1`. -/
noncomputable def typeProfilesAnch {w d : ℕ} (J : Finset (Fin w)) (LG : LayeredGarden w)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) : LeafProfiles w d := fun a =>
  if (pairTrees LG.garden a).2 ∈ J then (fun _ => 1) else typeProfiles LG h a

theorem typeProfilesAnch_empty {w d : ℕ} (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ) :
    typeProfilesAnch ∅ LG h = typeProfiles LG h := by
  funext a
  simp [typeProfilesAnch]

theorem typeProfilesAnch_leaf {w d : ℕ} (J : Finset (Fin w)) (LG : LayeredGarden w)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (ℓ : GLeaf LG.garden.tree) :
    typeProfilesAnch J LG h ℓ.1 =
      if (LG.garden.pair ℓ).1.1 ∈ J then (fun _ => 1)
      else h (LG.layer ℓ.toNode) ℓ.1.1 (LG.garden.pair ℓ).1.1 := by
  unfold typeProfilesAnch
  rw [pairTrees_leaf, typeProfiles_leaf]

/-- The leaf family of a type family with anchors `J`: anchored pairs have profile `1` and bound `1`. -/
noncomputable def TypeFamilyD.toLeafFamilyAnch {d w : ℕ} (U : TypeFamilyD d w) (J : Finset (Fin w)) :
    LeafFamilyD d w where
  ι _ := U.ι
  fin _ := U.fin
  sign _ := U.sign
  H LG i := typeProfilesAnch J LG (U.h i)
  B LG i a := if (pairTrees LG.garden a).2 ∈ J then 1 else U.b i
  sign_abs_le _ := U.sign_abs_le

/-- The anchored leaf family over the parameter record `P`. -/
noncomputable abbrev TypeFamily.toLFAnch {P : WTParams} {w : ℕ} (U : TypeFamily P w) (J : Finset (Fin w)) :
    LeafFamily P w := U.toLeafFamilyAnch J

/-- **Bridge**: with no anchors the anchored family is the current `toLeafFamily`. -/
theorem toLeafFamilyAnch_empty {d w : ℕ} (U : TypeFamilyD d w) :
    U.toLeafFamilyAnch ∅ = U.toLeafFamily := by
  unfold TypeFamilyD.toLeafFamilyAnch TypeFamilyD.toLeafFamily
  congr 1

/-- `Bounded` away from the anchors: only the non-anchored partner types `j' ∉ J` carry the bound. -/
def TypeFamilyD.BoundedAnch {d w : ℕ} (U : TypeFamilyD d w) (J : Finset (Fin w)) (p : ℕ) : Prop :=
  ∀ i q j j', q ≤ p → j' ∉ J → SNormR (40 * d) (40 * d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ)

theorem TypeFamilyD.Bounded.boundedAnch {d w : ℕ} {U : TypeFamilyD d w} {p : ℕ} (J : Finset (Fin w))
    (h : U.Bounded p) : U.BoundedAnch J p :=
  fun i q j j' hq _ => h i q j j' hq

/-- **Bridge**: with no anchors, `BoundedAnch` is `Bounded`. -/
theorem boundedAnch_empty_iff {d w : ℕ} (U : TypeFamilyD d w) (p : ℕ) :
    U.BoundedAnch ∅ p ↔ U.Bounded p :=
  ⟨fun h i q j j' hq => h i q j j' hq (by simp), fun h => h.boundedAnch ∅⟩

/-- Anchored pairs have profile `1` (`FlowerP1.AnchorOne`). -/
theorem anchorOne_toLeafFamilyAnch {d w : ℕ} (U : TypeFamilyD d w) (J : Finset (Fin w))
    (LG : LayeredGarden w) (i : U.ι) :
    FlowerP1.AnchorOne LG J ((U.toLeafFamilyAnch J).H LG i) := by
  intro ℓ _ hℓ
  show typeProfilesAnch J LG (U.h i) ℓ.1 = _
  rw [typeProfilesAnch_leaf, if_pos hℓ.2]

/-- The size of an anchored family at `LG`: `∑_i b_i ^ #(non-anchored input leaves)`. -/
theorem size_anch_eq {P : WTParams} {w : ℕ} (U : TypeFamily P w) (J : Finset (Fin w)) (LG : LayeredGarden w) :
    (U.toLFAnch J).size LG = @Finset.sum U.ι ℝ _ (@Finset.univ _ U.fin)
      (fun i => (U.b i : ℝ) ^ ((inputLeaves LG.garden).filter fun ℓ => (LG.garden.pair ℓ).1.1 ∉ J).card) := by
  show (@Finset.sum U.ι ℝ _ (@Finset.univ _ U.fin) fun i =>
      ∏ ℓ ∈ inputLeaves LG.garden,
        (((if (pairTrees LG.garden ℓ.1).2 ∈ J then 1 else U.b i : NNReal)) : ℝ)) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not (inputLeaves LG.garden) (fun ℓ => (LG.garden.pair ℓ).1.1 ∉ J)]
  have h1 : ∏ ℓ ∈ (inputLeaves LG.garden).filter (fun ℓ => (LG.garden.pair ℓ).1.1 ∉ J),
      (((if (pairTrees LG.garden ℓ.1).2 ∈ J then 1 else U.b i : NNReal)) : ℝ) =
      (U.b i : ℝ) ^ ((inputLeaves LG.garden).filter fun ℓ => (LG.garden.pair ℓ).1.1 ∉ J).card := by
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    rw [pairTrees_leaf, if_neg (Finset.mem_filter.mp hℓ).2]
  have h2 : ∏ ℓ ∈ (inputLeaves LG.garden).filter (fun ℓ => ¬ (LG.garden.pair ℓ).1.1 ∉ J),
      (((if (pairTrees LG.garden ℓ.1).2 ∈ J then 1 else U.b i : NNReal)) : ℝ) = 1 := by
    refine Finset.prod_eq_one fun ℓ hℓ => ?_
    have := (Finset.mem_filter.mp hℓ).2
    rw [pairTrees_leaf, if_pos (not_not.mp this)]
    simp
  rw [h1, h2, mul_one]

end WaveTurbulence.LGSpine
