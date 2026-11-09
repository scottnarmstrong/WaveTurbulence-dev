/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone1
/-! **L6E GHOST, part 12: the triple covers with a general `α`-gap set** (for the creation cone, Theorem 6.1 (e)).

Main's triple counts of the triangle steps that create `α`-atoms (`card_αβ_A`, `card_αβ_B`, `card_βα`, `card_αα`,
FINALCOUNT-G2, and `card_αα_sib`) cover the label triples by `slab × alphaN` (resp. `box × alphaN × alphaN`), the
`α` gap being one coordinate. Here the cover is stated for **any** finset `A` (resp. `B`) containing the `α` gaps, so that
`A = coneSet …` gives the cone counts. Copies of main's covering arguments (sha256 in COPIED-SHA256SUMS).
* `sub_αβ_A_gen`, `sub_αβ_B_gen`, `sub_βα_gen`, `sub_αα_gen`;
* `encard_slab_prod`: the three slab factors (`n ≠ 0` lattice slab, box, ghost-label slab) times `#A`;
* `encard_box_prod`: `box × #B`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The covering map of the shape `α β` with `idx S1 = {1}` (main's `card_αβ_A`). -/
def fαβA (z : Fin 3 → (Fin d → ℤ)) (p : (Fin d → ℤ) × (Fin d → ℤ)) : Fin 3 → (Fin d → ℤ) :=
  fun j => if j = 0 then z 0 + p.1 else if j = 1 then z 1 + p.1 else z 0 + p.1 + p.2

/-- The covering map of the shape `α β` with `idx S1 = {0, 1}` (main's `card_αβ_B`). -/
def fαβB (z : Fin 3 → (Fin d → ℤ)) (p : (Fin d → ℤ) × (Fin d → ℤ)) : Fin 3 → (Fin d → ℤ) :=
  fun j => if j = 0 then z 2 + p.1 - p.2 else if j = 1 then z 1 + p.1 else z 2 + p.1

/-- The covering map of the shape `β α` (main's `card_βα`). -/
def fβα (z : Fin 3 → (Fin d → ℤ)) (p : (Fin d → ℤ) × (Fin d → ℤ)) : Fin 3 → (Fin d → ℤ) :=
  fun j => if j = 0 then z 0 + p.1 else if j = 1 then z 0 + p.1 - p.2 else z 2 + p.1

/-- The covering map of the shape `α α` (main's `card_αα`): `p = (shift, gap₀, gap₁)`. -/
def fαα (z : Fin 3 → (Fin d → ℤ)) (p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) : Fin 3 → (Fin d → ℤ) :=
  fun j => if j = 0 then z 0 + p.1 else if j = 1 then z 0 + p.1 - p.2.2 else z 0 + p.1 + p.2.1

namespace Tri
variable {M : Molecule V D} (T : TriData M)

/-- **Cover, `α β`, `idx S1 = {1}`**, the `α` gap (`gap₀`) in any `A`. -/
theorem sub_αβ_A_gen (hi : T.idx T.S1 = {1}) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1)) (A : Finset (Fin d → ℤ))
    (hA : ∀ κ ∈ decSet M L γ δ w Adm c β k0, T.triZ κ 2 - T.triZ κ 0 ∈ A)
    (κs : D → (Fin d → ℤ)) (hκs : κs ∈ decSet M L γ δ w Adm c β k0) :
    T.tripleSet L γ δ w Adm c β k0 ⊆ fαβA (T.triZ κs) ''
      ((slabF d (T.triZ κs 1 - T.triZ κs 0) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ A : Finset _) : Set _) := by
  rintro _ ⟨κ, hκ, rfl⟩
  obtain ⟨hC1, hE1⟩ := T.rel1a hi hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
  have hC1' := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 1).1 hC1
  rw [fin3_one_sub] at hC1'
  have hu1 : T.triZ κ 1 - T.triZ κs 1 = T.triZ κ 0 - T.triZ κs 0 := by
    funext k; have := congrFun hC1' k; simp only [Pi.sub_apply] at this ⊢; omega
  refine ⟨(T.triZ κ 0 - T.triZ κs 0, T.triZ κ 2 - T.triZ κ 0), ?_, ?_⟩
  · rw [Finset.mem_coe, Finset.mem_product]
    refine ⟨?_, hA κ hκ⟩
    unfold slabF
    rw [Finset.mem_filter]
    refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, ?_⟩
    refine energy_slab_of_rel L γ δ hL w (T.triZ κ 1) (T.triZ κ 0) (T.triZ κs 1) (T.triZ κs 0)
      (T.triZ κ 0 - T.triZ κs 0) (by rw [← hu1]; abel) (by abel) ?_
    have e := hE1
    unfold triG at e
    rw [fin3_one_sub] at e
    exact e
  · funext j
    unfold fαβA
    fin_cases j
    · simp
    · show T.triZ κs 1 + (T.triZ κ 0 - T.triZ κs 0) = T.triZ κ 1
      funext k; have := congrFun hu1 k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
    · show T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) + (T.triZ κ 2 - T.triZ κ 0) = T.triZ κ 2
      funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega

/-- **Cover, `α β`, `idx S1 = {0, 1}`**, the `α` gap (`gap₀`) in any `A`. -/
theorem sub_αβ_B_gen (hi : T.idx T.S1 = {0, 1}) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1)) (A : Finset (Fin d → ℤ))
    (hA : ∀ κ ∈ decSet M L γ δ w Adm c β k0, T.triZ κ 2 - T.triZ κ 0 ∈ A)
    (κs : D → (Fin d → ℤ)) (hκs : κs ∈ decSet M L γ δ w Adm c β k0) :
    T.tripleSet L γ δ w Adm c β k0 ⊆ fαβB (T.triZ κs) ''
      ((slabF d (T.triZ κs 1 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ A : Finset _) : Set _) := by
  rintro _ ⟨κ, hκ, rfl⟩
  obtain ⟨hC, hE⟩ := T.rel1b hi hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
  have e1 : ∀ z : Fin 3 → (Fin d → ℤ), triC L w z 1 + triC L w z 0 =
      latticePoint L (z 1 - z 0) + latticePoint L (z 0 - z 2) := by
    intro z; rw [triC_eq, triC_eq, fin3_one_sub, fin3_zero_sub]
  rw [e1, e1, ← latticePoint_add', ← latticePoint_add'] at hC
  have hz := latticePoint_injective L hL.ne' hC
  have hu : T.triZ κ 1 - T.triZ κs 1 = T.triZ κ 2 - T.triZ κs 2 := by
    funext k; have := congrFun hz k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
  refine ⟨(T.triZ κ 2 - T.triZ κs 2, T.triZ κ 2 - T.triZ κ 0), ?_, ?_⟩
  · rw [Finset.mem_coe, Finset.mem_product]
    refine ⟨?_, hA κ hκ⟩
    unfold slabF
    rw [Finset.mem_filter]
    refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 2, ?_⟩
    refine energy_slab_of_rel L γ δ hL w (T.triZ κ 1) (T.triZ κ 2) (T.triZ κs 1) (T.triZ κs 2)
      (T.triZ κ 2 - T.triZ κs 2)
      (by funext k; have := congrFun hu k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega) (by abel) ?_
    have e := hE
    rw [triG_sum01, triG_sum01] at e
    exact e
  · funext j
    unfold fαβB
    fin_cases j
    · show T.triZ κs 2 + (T.triZ κ 2 - T.triZ κs 2) - (T.triZ κ 2 - T.triZ κ 0) = T.triZ κ 0
      funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
    · show T.triZ κs 1 + (T.triZ κ 2 - T.triZ κs 2) = T.triZ κ 1
      funext k; have := congrFun hu k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
    · show T.triZ κs 2 + (T.triZ κ 2 - T.triZ κs 2) = T.triZ κ 2
      funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega

/-- **Cover, `β α`**, the `α` gap (`gap₁`) in any `A`. -/
theorem sub_βα_gen (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) (A : Finset (Fin d → ℤ))
    (hA : ∀ κ ∈ decSet M L γ δ w Adm c β k0, T.triZ κ 0 - T.triZ κ 1 ∈ A)
    (κs : D → (Fin d → ℤ)) (hκs : κs ∈ decSet M L γ δ w Adm c β k0) :
    T.tripleSet L γ δ w Adm c β k0 ⊆ fβα (T.triZ κs) ''
      ((slabF d (T.triZ κs 0 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ A : Finset _) : Set _) := by
  rintro _ ⟨κ, hκ, rfl⟩
  obtain ⟨hC0, hE0⟩ := T.rel0 hβ0 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
  have hC0' := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 0).1 hC0
  rw [fin3_zero_sub] at hC0'
  have hu2 : T.triZ κ 2 - T.triZ κs 2 = T.triZ κ 0 - T.triZ κs 0 := by
    funext k; have := congrFun hC0' k; simp only [Pi.sub_apply] at this ⊢; omega
  refine ⟨(T.triZ κ 0 - T.triZ κs 0, T.triZ κ 0 - T.triZ κ 1), ?_, ?_⟩
  · rw [Finset.mem_coe, Finset.mem_product]
    refine ⟨?_, hA κ hκ⟩
    unfold slabF
    rw [Finset.mem_filter]
    refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, ?_⟩
    refine energy_slab_of_rel L γ δ hL w (T.triZ κ 0) (T.triZ κ 2) (T.triZ κs 0) (T.triZ κs 2)
      (T.triZ κ 0 - T.triZ κs 0) (by abel) (by rw [← hu2]; abel) ?_
    have e := hE0
    unfold triG at e
    rw [fin3_zero_sub] at e
    exact e
  · funext j
    unfold fβα
    fin_cases j
    · simp
    · show (T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) - (T.triZ κ 0 - T.triZ κ 1)) = T.triZ κ 1
      funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
    · show T.triZ κs 2 + (T.triZ κ 0 - T.triZ κs 0) = T.triZ κ 2
      funext k; have := congrFun hu2 k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega

/-- **Cover, `α α`**, the pair of `α` gaps `(gap₀, gap₁)` in any `B` (covers `card_αα` and `card_αα_sib`). -/
theorem sub_αα_gen (L γ δ : ℝ) (hL : 0 < L) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (B : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (hB : ∀ κ ∈ decSet M L γ δ w Adm c β k0, (T.triZ κ 2 - T.triZ κ 0, T.triZ κ 0 - T.triZ κ 1) ∈ B)
    (κs : D → (Fin d → ℤ)) (hκs : κs ∈ decSet M L γ δ w Adm c β k0) :
    T.tripleSet L γ δ w Adm c β k0 ⊆ fαα (T.triZ κs) '' ((boxF d ⌊2 * L⌋₊ ×ˢ B : Finset _) : Set _) := by
  rintro _ ⟨κ, hκ, rfl⟩
  refine ⟨(T.triZ κ 0 - T.triZ κs 0, T.triZ κ 2 - T.triZ κ 0, T.triZ κ 0 - T.triZ κ 1), ?_, ?_⟩
  · rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, hB κ hκ⟩
  · funext j
    unfold fαα
    fin_cases j
    · simp
    · show T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) - (T.triZ κ 0 - T.triZ κ 1) = T.triZ κ 1
      funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
    · show T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) + (T.triZ κ 2 - T.triZ κ 0) = T.triZ κ 2
      funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega

end Tri

/-- **The slab factors of a `slab × A` cover**: the lattice slab (`n ≠ 0`), the box, and the ghost-label slab
(`‖n‖ ≥ ρ` in momentum units). -/
theorem encard_slab_prod (L : ℝ) (hL : 0 < L) {X : Type*} (Z : Set X)
    (f : (Fin d → ℤ) × (Fin d → ℤ) → X) (n : Fin d → ℤ) (r : ℝ) (hr : 0 ≤ r) (A : Finset (Fin d → ℤ))
    (hsub : Z ⊆ f '' ((slabF d n ⌊2 * L⌋₊ r ×ˢ A : Finset _) : Set _)) :
    (n ≠ 0 → Z.encard ≤ (((⌊2 * r⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * A.card : ℕ) : ℕ∞)) ∧
    Z.encard ≤ (((2 * ⌊2 * L⌋₊ + 1) ^ d * A.card : ℕ) : ℕ∞) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ ‖latticePoint L n‖ →
      Z.encard ≤ (((⌊2 * r / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * A.card : ℕ) : ℕ∞)) := by
  have h1 := encard_le_of_subset_image _ _ _ hsub
  refine ⟨fun hn => h1.trans ?_, ?_, fun ρ hρ hn => h1.trans ?_⟩
  · rw [Finset.card_product]
    exact_mod_cast Nat.mul_le_mul (card_slabF _ hn _ _) le_rfl
  · have hss : ((slabF d n ⌊2 * L⌋₊ r ×ˢ A : Finset _) : Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
        ((boxF d ⌊2 * L⌋₊ ×ˢ A : Finset _) : Set ((Fin d → ℤ) × (Fin d → ℤ))) :=
      Finset.coe_subset.mpr (Finset.product_subset_product_left (Finset.filter_subset _ (boxF d ⌊2 * L⌋₊)))
    refine (encard_le_of_subset_image _ _ _ (hsub.trans (Set.image_mono hss))).trans ?_
    rw [Finset.card_product, card_boxF]
  · have hdpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        have : latticePoint L n = 0 := Subsingleton.elim _ _
        rw [this, norm_zero] at hn; linarith
      · exact h0
    obtain ⟨i0, hi0⟩ := exists_coord_ge L hL n ρ hρ hn
    have hν : 0 < ρ * L / d := by positivity
    rw [Finset.card_product]
    exact_mod_cast Nat.mul_le_mul
      (card_slabF_nu n i0 (ρ * L / d) hν (by rw [mul_div_assoc] at hi0 ⊢; exact hi0) ⌊2 * L⌋₊ r hr) le_rfl

/-- **The box factor of a `box × B` cover.** -/
theorem encard_box_prod (L : ℝ) {X : Type*} (Z : Set X) (f : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) → X)
    (B : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (hsub : Z ⊆ f '' ((boxF d ⌊2 * L⌋₊ ×ˢ B : Finset _) : Set _)) :
    Z.encard ≤ (((2 * ⌊2 * L⌋₊ + 1) ^ d * B.card : ℕ) : ℕ∞) := by
  refine (encard_le_of_subset_image _ _ _ hsub).trans ?_
  rw [Finset.card_product, card_boxF]

end WaveTurbulence.GammaLow.FinalCount.Ghost
