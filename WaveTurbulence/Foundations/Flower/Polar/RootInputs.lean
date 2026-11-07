/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.RootForm
/-! # FL-POLAR: the flower root form in terms of the input leaves (coordinatewise, with pair-type
coefficients). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset

theorem not_isFlower_iff_mark_none {w : ℕ} (G : Garden w)
    (hmarks : ∀ ℓ, G.mark ℓ ≠ none → G.IsFlower ℓ) (ℓ : GLeaf G.tree) :
    ¬ G.IsFlower ℓ ↔ G.mark ℓ = none := by
  constructor
  · intro h
    by_contra h'
    exact h (hmarks ℓ h')
  · intro h hfl
    have : G.mark ℓ = some MarkTag.equal := hfl
    rw [h] at this
    exact absurd this (by simp)

theorem sum_nonflower_eq_inputs {w d : ℕ} (G : Garden w)
    (hmarks : ∀ ℓ, G.mark ℓ ≠ none → G.IsFlower ℓ) (δ : GNode G.tree → Mom d)
    (hδ : ∀ ℓ : GLeaf G.tree, δ ℓ.toNode = δ (G.pair ℓ).toNode) (j : Fin w) :
    ∑ ℓ ∈ nonFlowerLeavesOf G j, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode =
      ∑ a ∈ inputLeaves G, ((if a.1.1 = j then (1 : ℤ) else 0) -
        (if (G.pair a).1.1 = j then (1 : ℤ) else 0)) • δ a.toNode := by
  set N : Finset (GLeaf G.tree) := univ.filter fun ℓ => G.mark ℓ = none with hN
  set F : GLeaf G.tree → Mom d := fun ℓ =>
    if ℓ.1.1 = j then ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode else 0 with hF
  have h1 : nonFlowerLeavesOf G j = N.filter (fun ℓ => ℓ.1.1 = j) := by
    ext ℓ
    simp only [nonFlowerLeavesOf, hN, mem_filter, mem_univ, true_and,
      not_isFlower_iff_mark_none G hmarks]
    tauto
  have hflip (l : GLeaf G.tree) (hm : G.mark l = none) : G.sign (G.pair l).toNode = -G.sign l.toNode :=
    G.pair_sign l (fun he => ((G.pair_eq_iff l).mp he) (by simp [hm]))
  have hpm (l : GLeaf G.tree) (hm : G.mark l = none) : G.mark (G.pair l) = none := by
    by_contra h
    have := (G.pair_eq_iff (G.pair l)).2 h
    rw [G.pair_pair] at this
    exact ((G.pair_eq_iff l).mp this.symm) (by simp [hm])
  rw [h1, sum_filter]
  change ∑ ℓ ∈ N, F ℓ = _
  have hsplit := Finset.sum_filter_add_sum_filter_not N (fun l => G.sign l.toNode = 1) F
  have hin : N.filter (fun l => G.sign l.toNode = 1) = inputLeaves G := by
    ext l
    simp only [inputLeaves, hN, mem_filter, mem_univ, true_and]
    tauto
  have hneg : ∑ l ∈ N.filter (fun l => ¬ G.sign l.toNode = 1), F l =
      ∑ a ∈ inputLeaves G, F (G.pair a) := by
    rw [← hin]
    symm
    refine Finset.sum_nbij' (fun l => G.pair l) (fun l => G.pair l) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      have hl' := mem_filter.mp hl
      have hm : G.mark l = none := (mem_filter.mp hl'.1).2
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hpm l hm⟩, ?_⟩
      rw [hflip l hm, hl'.2]; decide
    · intro l hl
      have hl' := mem_filter.mp hl
      have hm : G.mark l = none := (mem_filter.mp hl'.1).2
      have hl'' : G.sign l.toNode = -1 := (Int.units_eq_one_or _).resolve_left hl'.2
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hpm l hm⟩, ?_⟩
      rw [hflip l hm, hl'', neg_neg]
    · intro l _; exact G.pair_pair l
    · intro l _; exact G.pair_pair l
    · intro l _; rfl
  rw [← hsplit, hneg, hin, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun a ha => ?_
  have ha' := mem_filter.mp ha
  have ha1 : G.sign a.toNode = 1 := ha'.2.1
  have ham : G.mark a = none := ha'.2.2
  have hs1 : ((nodeSign G.sig a.1 : ℤˣ) : ℤ) = 1 := by
    have : nodeSign G.sig a.1 = 1 := ha1
    rw [this]; rfl
  have hs2 : ((nodeSign G.sig (G.pair a).1 : ℤˣ) : ℤ) = -1 := by
    have h := hflip a ham
    change nodeSign G.sig (G.pair a).1 = -nodeSign G.sig a.1 at h
    rw [h, show nodeSign G.sig a.1 = 1 from ha1]
    rfl
  have hk2 := hδ a
  simp only [hF, hs1, hs2, ← hk2]
  by_cases h1 : a.1.1 = j <;> by_cases h2 : (G.pair a).1.1 = j <;> simp [h1, h2, sub_smul]

/-- Coordinatewise root form over the input leaves, with the pair-type coefficients. -/
theorem flower_root_coord {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ))
    (n' : Fin d → ℤ) (ζ : ℤˣ) (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
      LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1)
    (hmarks : ∀ ℓ, LG.garden.mark ℓ ≠ none → LG.garden.IsFlower ℓ)
    (κ : GenDecoration LG.garden d n n') (j : Fin w)
    (hone : (univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsFlower ℓ).card = 1)
    (hk₀ : ((1 : ℤ) - (ζ : ℤ)) • k₀ = 0) (i : Fin d) :
    (latticePoint L (n j) - (ζ : ℤ) • latticePoint L n') i =
      ∑ a ∈ inputLeaves LG.garden,
        typeCoeff ((LG.garden.sig j : ℤˣ) : ℝ) j a.1.1 (LG.garden.pair a).1.1 *
          (cosetDecoration LG.garden L k₀ κ.1 a.toNode) i := by
  have hdec : IsDecoration LG.garden (cosetDecoration LG.garden L k₀ κ.1) :=
    LGSpine.isDecoration_cosetDecoration LG.garden L k₀ κ.1 κ.2.1
  have hrf := flower_rootform LG L k₀ n n' ζ hfl κ j hone hk₀
  have hconv := sum_nonflower_eq_inputs LG.garden hmarks (cosetDecoration LG.garden L k₀ κ.1) hdec.2 j
  have hrel : ∀ ℓ ∈ nonFlowerLeavesOf LG.garden j, ((leafSignRel LG.garden ℓ : ℤˣ) : ℤ) •
      cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode =
      ((LG.garden.sig j : ℤˣ) : ℤ) • (((nodeSign LG.garden.sig ℓ.1 : ℤˣ) : ℤ) •
        cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) := by
    intro ℓ hℓ
    have hℓj : ℓ.1.1 = j := (mem_filter.mp hℓ).2.1
    rw [← mul_smul]
    congr 1
    simp only [leafSignRel, Units.val_mul, hℓj]
    change ((nodeSign LG.garden.sig ℓ.1 : ℤˣ) : ℤ) * _ = _
    ring
  rw [sum_congr rfl hrel, ← Finset.smul_sum, hconv, Finset.smul_sum] at hrf
  have hi := congrArg (fun v : Mom d => v i) hrf
  simp only [PiLp.smul_apply, PiLp.sub_apply, zsmul_eq_mul, WithLp.ofLp_sum,
    Finset.sum_apply] at hi
  simp only [PiLp.sub_apply, PiLp.smul_apply, zsmul_eq_mul]
  rw [hi]
  refine sum_congr rfl fun a _ => ?_
  simp only [typeCoeff]
  push_cast
  ring

theorem hone_of_flowerGarden {w : ℕ} (G : Garden w) (hFG : G.IsFlowerGarden) (j : Fin w) :
    (univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsFlower ℓ).card = 1 := by
  rw [← hFG.1 j]
  congr 1
  ext ℓ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro h0
    have : G.mark ℓ = some MarkTag.equal := h2
    rw [h0] at this
    exact absurd this (by simp)
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hFG.2.1 ℓ h2⟩

/-- The plan's `flower_rootform` for flower gardens (every tree has exactly one flower) and `k₀ = 0`. -/
theorem flower_rootform_of_flowerGarden {w d : ℕ} (LG : LayeredGarden w) (L : ℝ)
    (n : Fin w → (Fin d → ℤ)) (n' : Fin d → ℤ) (ζ : ℤˣ)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
      LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1)
    (hFG : LG.garden.IsFlowerGarden)
    (κ : GenDecoration LG.garden d n n') (j : Fin w) :
    latticePoint L (n j) - (ζ : ℤ) • latticePoint L n' =
      ∑ ℓ ∈ nonFlowerLeavesOf LG.garden j, (leafSignRel LG.garden ℓ : ℤ) •
        cosetDecoration LG.garden L 0 κ.1 ℓ.toNode :=
  flower_rootform LG L 0 n n' ζ hfl κ j (hone_of_flowerGarden LG.garden hFG j) (by simp)

end WaveTurbulence.Flower.Polar
