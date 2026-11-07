/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.S2ST.AnchorBoth
/-! R97: the both-member anchored family.

`typeProfilesAnchB` masks BOTH members of every anchored pair (the leaf's own tree or its partner's tree lies in
the anchor set `J`). `BoundedAnchB` and the leaf size exempt both members. With `J = ∅` everything is the plain
`TypeFamily` data (`toLeafFamilyAnchB_empty`, `boundedAnchB_empty_iff`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.S2ST
open LGSpine MeasureTheory Set Finset
open scoped Classical

/-- Pair-type profiles, both-member convention: a leaf whose own tree or whose partner's tree is an anchor has
profile `1`. -/
noncomputable def typeProfilesAnchB {w d : ℕ} (J : Finset (Fin w)) (LG : LayeredGarden w)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) : LeafProfiles w d := fun a =>
  if (pairTrees LG.garden a).1 ∈ J ∨ (pairTrees LG.garden a).2 ∈ J then (fun _ => 1)
  else typeProfiles LG h a

theorem typeProfilesAnchB_empty {w d : ℕ} (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ) :
    typeProfilesAnchB ∅ LG h = typeProfiles LG h := by
  funext a
  simp [typeProfilesAnchB]

theorem typeProfilesAnchB_leaf {w d : ℕ} (J : Finset (Fin w)) (LG : LayeredGarden w)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (ℓ : GLeaf LG.garden.tree) :
    typeProfilesAnchB J LG h ℓ.1 =
      if ℓ.1.1 ∈ J ∨ (LG.garden.pair ℓ).1.1 ∈ J then (fun _ => 1)
      else h (LG.layer ℓ.toNode) ℓ.1.1 (LG.garden.pair ℓ).1.1 := by
  unfold typeProfilesAnchB
  rw [pairTrees_leaf, typeProfiles_leaf]

/-- The leaf family of a type family with both-member anchors `J`: anchored pairs have profile `1` and bound `1`
at both members. -/
noncomputable def toLeafFamilyAnchB {d w : ℕ} (U : TypeFamilyD d w) (J : Finset (Fin w)) :
    LeafFamilyD d w where
  ι _ := U.ι
  fin _ := U.fin
  sign _ := U.sign
  H LG i := typeProfilesAnchB J LG (U.h i)
  B LG i a := if (pairTrees LG.garden a).1 ∈ J ∨ (pairTrees LG.garden a).2 ∈ J then 1 else U.b i
  sign_abs_le _ := U.sign_abs_le

/-- The both-member anchored leaf family over the parameter record `P`. -/
noncomputable abbrev toLFAnchB {P : WTParams} {w : ℕ} (U : TypeFamily P w) (J : Finset (Fin w)) :
    LeafFamily P w := toLeafFamilyAnchB U J

theorem toLeafFamilyAnchB_empty {d w : ℕ} (U : TypeFamilyD d w) :
    toLeafFamilyAnchB U ∅ = U.toLeafFamily := by
  unfold toLeafFamilyAnchB TypeFamilyD.toLeafFamily
  congr 1

/-- Both-member bounded: only the non-anchored pair types `(j, j')`, `j, j' ∉ J`, carry the bound. -/
def BoundedAnchB {d w : ℕ} (U : TypeFamilyD d w) (J : Finset (Fin w)) (p : ℕ) : Prop :=
  ∀ i q j j', q ≤ p → j ∉ J → j' ∉ J →
    SNormR (40 * d) (40 * d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ)

theorem boundedAnchB_of_bounded {d w : ℕ} {U : TypeFamilyD d w} {p : ℕ} (J : Finset (Fin w))
    (h : U.Bounded p) : BoundedAnchB U J p :=
  fun i q j j' hq _ _ => h i q j j' hq

theorem boundedAnchB_empty_iff {d w : ℕ} (U : TypeFamilyD d w) (p : ℕ) :
    BoundedAnchB U ∅ p ↔ U.Bounded p :=
  ⟨fun h i q j j' hq => h i q j j' hq (by simp) (by simp), fun h => boundedAnchB_of_bounded ∅ h⟩

/-- The old partner-only `BoundedAnch` implies the both-member one (the converse fails: the old one also bounds
own-anchor types). -/
theorem boundedAnchB_of_boundedAnch {d w : ℕ} {U : TypeFamilyD d w} {J : Finset (Fin w)} {p : ℕ}
    (h : U.BoundedAnch J p) : BoundedAnchB U J p :=
  fun i q j j' hq _ hj' => h i q j j' hq hj'

/-- The both-member anchored family has profile `1` at both members of every anchored pair. -/
theorem anchorOneBoth_toLeafFamilyAnchB {d w : ℕ} (U : TypeFamilyD d w) (J : Finset (Fin w))
    (LG : LayeredGarden w) (i : U.ι) :
    AnchorOneBoth LG J ((toLeafFamilyAnchB U J).H LG i) := by
  intro a ha
  show typeProfilesAnchB J LG (U.h i) a.1 = _
  rw [typeProfilesAnchB_leaf]
  exact ite_eq_left ha

/-- The size of the both-member anchored family: `∑_i b_i ^ #(input leaves with both members non-anchored)`. -/
theorem size_anchB_eq {P : WTParams} {w : ℕ} (U : TypeFamily P w) (J : Finset (Fin w)) (LG : LayeredGarden w) :
    (toLFAnchB U J).size LG = @Finset.sum U.ι ℝ _ (@Finset.univ _ U.fin)
      (fun i => (U.b i : ℝ) ^ ((inputLeaves LG.garden).filter
        fun ℓ => ℓ.1.1 ∉ J ∧ (LG.garden.pair ℓ).1.1 ∉ J).card) := by
  show (@Finset.sum U.ι ℝ _ (@Finset.univ _ U.fin) fun i =>
      ∏ ℓ ∈ inputLeaves LG.garden,
        (((if (pairTrees LG.garden ℓ.1).1 ∈ J ∨ (pairTrees LG.garden ℓ.1).2 ∈ J then 1 else U.b i :
          NNReal)) : ℝ)) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not (inputLeaves LG.garden)
    (fun ℓ => ℓ.1.1 ∉ J ∧ (LG.garden.pair ℓ).1.1 ∉ J)]
  have h1 : ∏ ℓ ∈ (inputLeaves LG.garden).filter (fun ℓ => ℓ.1.1 ∉ J ∧ (LG.garden.pair ℓ).1.1 ∉ J),
      (((if (pairTrees LG.garden ℓ.1).1 ∈ J ∨ (pairTrees LG.garden ℓ.1).2 ∈ J then 1 else U.b i :
        NNReal)) : ℝ) =
      (U.b i : ℝ) ^ ((inputLeaves LG.garden).filter fun ℓ => ℓ.1.1 ∉ J ∧ (LG.garden.pair ℓ).1.1 ∉ J).card := by
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    have := (Finset.mem_filter.mp hℓ).2
    simp [pairTrees_leaf, this.1, this.2]
  have h2 : ∏ ℓ ∈ (inputLeaves LG.garden).filter
      (fun ℓ => ¬ (ℓ.1.1 ∉ J ∧ (LG.garden.pair ℓ).1.1 ∉ J)),
      (((if (pairTrees LG.garden ℓ.1).1 ∈ J ∨ (pairTrees LG.garden ℓ.1).2 ∈ J then 1 else U.b i :
        NNReal)) : ℝ) = 1 := by
    refine Finset.prod_eq_one fun ℓ hℓ => ?_
    have := (Finset.mem_filter.mp hℓ).2
    rw [pairTrees_leaf, ite_eq_left (by tauto)]
    simp
  rw [h1, h2, mul_one]
end WaveTurbulence.S2ST
