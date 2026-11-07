/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.Port.AnchoredPolarization
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerP1Stub
public import WaveTurbulence.Foundations.Spine.TypeFamily
public import WaveTurbulence.Foundations.Spine.RootFormSum

/-!
# X5: the pair-type weight identity on FLOWER-P1 anchored gardens

Anchor trees are designated by `J`. A pair meeting an anchor tree has
profile one, whether the anchor is the positive or negative end of the pair.
This implies FLOWER-P1's `AnchorOne` convention. The remaining pair types
carry the profiles and all polynomial momentum weights. The exact root
balance subtracts the anchored pairs before forming the decay momentum.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerX7X5
open Finset LGSpine
open scoped Classical

abbrev LeafPairType (w : ℕ) := ℕ × (Fin w × Fin w)

def pairType {w : ℕ} (LG : LayeredGarden w) (a : GLeaf LG.garden.tree) : LeafPairType w :=
  (LG.layer a.toNode, a.1.1, (LG.garden.pair a).1.1)

def isAnchorType {w : ℕ} (J : Finset (Fin w)) (t : LeafPairType w) : Prop :=
  t.2.1 ∈ J ∨ t.2.2 ∈ J

/-- Pair-type profiles with one on every pair meeting an anchor. In
particular a positive anchor root is treated just as a negative anchor root. -/
noncomputable def anchoredProfiles {w d : ℕ} (LG : LayeredGarden w)
    (J : Finset (Fin w)) (h : PairProfile (LeafPairType w) d) : LeafProfiles w d :=
  typeProfiles LG fun q j j' x => if isAnchorType J (q, j, j') then 1 else h (q, j, j') x

theorem anchoredProfiles_leaf {w d : ℕ} (LG : LayeredGarden w)
    (J : Finset (Fin w)) (h : PairProfile (LeafPairType w) d)
    (a : GLeaf LG.garden.tree) (x : Mom d) :
    anchoredProfiles LG J h a.1 x =
      if isAnchorType J (pairType LG a) then 1 else h (pairType LG a) x := by
  rw [anchoredProfiles, typeProfiles_leaf]
  rfl

/-- Bridge to the posted FLOWER-P1 definition; no profile estimate is used. -/
theorem anchoredProfiles_anchorOne {w d : ℕ} (LG : LayeredGarden w)
    (J : Finset (Fin w)) (h : PairProfile (LeafPairType w) d) :
    FlowerP1.AnchorOne LG J (anchoredProfiles LG J h) := by
  intro a _ ha
  funext x
  rw [anchoredProfiles_leaf]
  exact ite_eq_left (show isAnchorType J (pairType LG a) from Or.inr ha.2)

/-- The full source input product is exactly the non-anchor product. -/
theorem prod_anchoredProfiles {w d : ℕ} (LG : LayeredGarden w)
    (J : Finset (Fin w)) (h : PairProfile (LeafPairType w) d)
    (k : GNode LG.garden.tree → Mom d) :
    (∏ a ∈ inputLeaves LG.garden, (anchoredProfiles LG J h a.1 (k a.toNode) : ℂ)) =
      profileProduct (inputLeaves LG.garden) (pairType LG) (isAnchorType J)
        (fun a => k a.toNode) h := by
  classical
  unfold profileProduct freeInputs
  rw [Finset.prod_filter]
  refine prod_congr rfl fun a _ => ?_
  rw [anchoredProfiles_leaf]
  by_cases ha : isAnchorType J (pairType LG a) <;> simp [ha]

/-- The signed contribution of a pair to the root of tree `j`. -/
def treeCoeff {w : ℕ} (j : Fin w) (t : LeafPairType w) : ℝ :=
  (if t.2.1 = j then 1 else 0) - (if t.2.2 = j then 1 else 0)

/-- The decay momentum furnished by non-anchor pairs. -/
noncomputable def ordinaryMomentum {w d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (k : GNode LG.garden.tree → Mom d) (j : Fin w) : Mom d :=
  freeMomentum (inputLeaves LG.garden) (pairType LG) (isAnchorType J)
    (fun a => k a.toNode) (treeCoeff j)

/-- Exact momentum balance: remove anchor-pair contributions from the
signed root before assigning any decay to the remaining profiles. -/
theorem ordinaryMomentum_eq_root_sub_anchors {w d : ℕ} (LG : LayeredGarden w)
    (hp : LG.garden.IsPlain) (J : Finset (Fin w))
    (k : GNode LG.garden.tree → Mom d) (hk : IsDecoration LG.garden k) (j : Fin w) :
    ordinaryMomentum LG J k j =
      ((nodeSign LG.garden.sig (GNode.root LG.garden.tree j).1 : ℤˣ) : ℤ) •
          k (GNode.root LG.garden.tree j) -
        ∑ a ∈ (inputLeaves LG.garden).filter (fun a => isAnchorType J (pairType LG a)),
          ((if a.1.1 = j then (1 : ℤ) else 0) -
            (if (LG.garden.pair a).1.1 = j then (1 : ℤ) else 0)) • k a.toNode := by
  classical
  rw [root_sum_inputs LG.garden hp k hk j]
  have he := Finset.sum_filter_add_sum_filter_not (inputLeaves LG.garden)
    (fun a => isAnchorType J (pairType LG a))
    (fun a => ((if a.1.1 = j then (1 : ℤ) else 0) -
      (if (LG.garden.pair a).1.1 = j then (1 : ℤ) else 0)) • k a.toNode)
  rw [← he, add_sub_cancel_left]
  unfold ordinaryMomentum freeMomentum freeInputs
  refine sum_congr rfl fun a _ => ?_
  dsimp [treeCoeff, pairType]
  by_cases ha : a.1.1 = j <;> by_cases hb : (LG.garden.pair a).1.1 = j <;> simp [ha, hb]

/-- The complete even-weight identity for a FLOWER-P1 anchored garden,
at every decoration. The coefficients may select individual trees or
original-tree colours after excision; they depend only on pair type.
The degree budget counts only non-anchored inputs. -/
theorem anchored_garden_weight_identity {w d m : ℕ} (LG : LayeredGarden w)
    (J : Finset (Fin w)) (h : PairProfile (LeafPairType w) d)
    (k : GNode LG.garden.tree → Mom d) (c : Fin m → LeafPairType w → ℝ)
    (M : ℕ) (hM : 1 ≤ M)
    (hcard : (freeInputs (inputLeaves LG.garden) (pairType LG) (isAnchorType J)).card ≤ 2 * M)
    (lam : ℝ) (hlam : lam ≠ 0) (n : ℕ) :
    ((∏ j, jbr (freeMomentum (inputLeaves LG.garden) (pairType LG) (isAnchorType J)
          (fun a => k a.toNode) (c j)) ^ (2 * n) : ℝ) : ℂ) *
        (∏ a ∈ inputLeaves LG.garden, (anchoredProfiles LG J h a.1 (k a.toNode) : ℂ)) =
      ∑ choice : Fin m → Fin n → Option (Fin d),
        formWord (inputLeaves LG.garden) (pairType LG) (isAnchorType J)
          (fun a => k a.toNode) c M lam (opsOfChoice choice) h := by
  rw [prod_anchoredProfiles]
  exact free_weight_profileProduct _ _ _ _ c h M hM hcard lam hlam n

/-- The weight identity applies inside the literal posted stub-kernel
summand. No gate or estimate is postulated. -/
theorem stub_term_eq_product {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (J : Finset (Fin w)) (h : PairProfile (LeafPairType w) d)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (base : Mom d)
    {roots : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d roots nfl) :
    FlowerP1.kernelLeavesFixTerm L γ δ LG (anchoredProfiles LG J h) up fix base κ =
      ((epsDec LG.garden κ.1 : ℂ) *
        (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
          (kDomainFix LG up fix).indicator
            (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L base κ.1))
              (LG.garden.extendFix fix τ))) *
        profileProduct (inputLeaves LG.garden) (pairType LG) (isAnchorType J)
          (fun a => cosetDecoration LG.garden L base κ.1 a.toNode) h := by
  unfold FlowerP1.kernelLeavesFixTerm
  rw [prod_anchoredProfiles]

end WaveTurbulence.FlowerX7X5
