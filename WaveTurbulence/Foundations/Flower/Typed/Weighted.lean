/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Split
/-! # FL-TYPED: the family-weighted flower carrier is a pair-type profile carrier. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Typed
open Finset

/-- Real identity on a decoration with equal paired momenta and layers. -/
theorem family_leaf_identity {w d : ℕ} (LG : LayeredGarden w) (hf : LG.garden.IsFlowerGarden)
    (F : ℕ → Mom d → ℝ) (p : ℕ) (M A : ℝ) (tail small : Fin w → Bool) (z : Fin w → ℝ)
    (k : GNode LG.garden.tree → Mom d) (hk : ∀ ℓ : GLeaf LG.garden.tree, k ℓ.toNode = k (LG.garden.pair ℓ).toNode) :
    FC23.flowerFamilyWeight LG p M A tail small z k *
        ∏ ℓ ∈ inputLeaves LG.garden, F (LG.layer ℓ.toNode) (k ℓ.toNode) =
      frontierW LG p (fun j => some (if tail j && small j then M / 2 else M)) k *
        leafProd LG (familyProfile F p M A tail z) k := by
  rw [flowerFamilyWeight_split,
    prod_nonflower_eq_prod_input LG.garden hf.2.1
      (fun l => FC23.endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A (z l.1.1) ‖k l.toNode‖),
    mul_assoc, ← prod_mul_distrib]
  unfold leafProd
  congr 1
  refine prod_congr rfl fun ℓ _ => ?_
  rw [LGSpine.typeProfiles_leaf, familyProfile]
  have hl : LG.layer ℓ.toNode = LG.layer (LG.garden.pair ℓ).toNode := LG.isLayering.2 ℓ
  rw [← hk ℓ, ← hl]
  ring

theorem cast_aux (e I Fp : ℂ) (W s fam fr lp : ℝ) (hk : (fam : ℂ) * Fp = (fr : ℂ) * (lp : ℂ)) :
    e * ((W * fam * s : ℝ) : ℂ) * I * Fp = e * ((W * fr * lp * s : ℝ) : ℂ) * I := by
  push_cast
  linear_combination (e * (W : ℂ) * (s : ℂ) * I) * hk

theorem flowerWeighted_typed (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (M A : ℝ)
    (tail small : Fin w → Bool) (z : Fin w → ℝ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    FC23.flowerWeighted P F p N kind pat dagger
      (fun LG k => W LG k * FC23.flowerFamilyWeight LG p M A tail small z k) ζ t s n n' =
    FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
      (fun LG k => W LG k *
        frontierW LG p (fun j => some (if tail j && small j then M / 2 else M)) k *
        leafProd LG (familyProfile F p M A tail z) k) ζ t s n n' := by
  unfold FC23.flowerWeighted
  refine finsum_congr fun LG => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hc : IsCanonH (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerKindOK p (P.N (p + 1)) kind ∧
      (∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1) ∧
      ∀ j, LG.PatValid p j (pat j)
  · simp only [hc, ↓reduceIte]
    have hf := hc.1.1
    unfold kernelKgen
    congr 2
    refine tsum_congr fun κ => ?_
    have hk : ∀ ℓ : GLeaf LG.garden.tree,
        cosetDecoration LG.garden P.L (0 : Mom P.d) κ.1 ℓ.toNode =
          cosetDecoration LG.garden P.L (0 : Mom P.d) κ.1 (LG.garden.pair ℓ).toNode := by
      intro ℓ
      simp only [cosetDecoration]
      rw [κ.2.1.2 ℓ]
    have key := family_leaf_identity LG hf F p M A tail small z _ hk
    have key' := congrArg (fun r : ℝ => (r : ℂ)) key
    simp only [Complex.ofReal_mul, Complex.ofReal_prod] at key'
    simp only [Complex.ofReal_one, Finset.prod_const_one, mul_one]
    exact cast_aux _ _ _ _ _ _ _ _ key'
  · simp only [hc, ↓reduceIte]

end WaveTurbulence.Flower.Typed
