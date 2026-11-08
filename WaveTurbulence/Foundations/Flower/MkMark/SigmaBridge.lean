/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.StemZero
public import WaveTurbulence.Foundations.Flower.MkMark.CoordIso
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLVineChain
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CollapsedDecorations
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcMom2

/-! # B2b-2 MK-MARK (c): the σ-bridge, node level

`weight_zero_of_unclean` (StemZero) takes the small inflated crown gap `‖k(u₂₁) − k(u₂₂)‖ < ‖k_root‖/2` as a
hypothesis. Here it is reduced to the collapsed skeleton decoration and to the CL chain gap:

* **the cast** (`skDec`, `skDec_child`, `skDec_root`, `attachedNode_skDec`, `collapseGenDecoration_skDec`): the
  skeleton decoration of an inflated decoration `k` is `k` at the inflated positions; it is main's collapsed
  decoration (`collapseGenDecoration`, `attachedNode`), and by `attachedNode_child` the inflated crown children of
  `u₂` carry the skeleton values at `u₂.child pos/neg` (`crown_gap_skDec`);
* `ingredient_gap_eq_crown`: the gap of any CL ingredient with the atoms and lower joint of `u` is the skeleton crown
  gap at `u` (the slots agree: main `region_lower_eq_of_subset`);
* **the skeleton-only lemma** (`chain_gap_le`, `chain_gap_le_of_upper`): along a CL vine chain, a gap bound for one
  ingredient (or for the upper-joint gap `k(a) − k(a.child excluded)` of one ingredient) bounds the crown gap of
  every ingredient (main `clVineChain_gap_eq`, `clVineChain_gap_eq_upper_or_neg`);
* `weight_zero_of_unclean_chain`: a stem-unclean pair has zero weight on decorations whose (collapsed) CL chain gap
  is at most `L^{-γ+η} < ‖k_root‖/2` (an SG chain under a high root). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed WaveTurbulence.RedSplice

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

section Cast
variable {LG : LayeredGarden w} (A : VineA.PrimeData LG) {V : Type*}

theorem nodeAt_inflated (a : GNode A.skeleton.tree) :
    (inflatedPosition A.skeleton A.data.tree a).2 ∈
      (LG.garden.tree (inflatedPosition A.skeleton A.data.tree a).1).nodes :=
  nodeAt_inflatedPosition A.data A.prime.1 A.decodes a

/-- **The collapsed skeleton decoration**: an inflated decoration read at the inflated positions. -/
def skDec (k : GNode LG.garden.tree → V) : GNode A.skeleton.tree → V :=
  fun a => k ⟨inflatedPosition A.skeleton A.data.tree a, nodeAt_inflated A a⟩

theorem skDec_child (k : GNode LG.garden.tree → V) (b : GBranch A.skeleton.tree) (i : Fin 3) :
    k ((inflatedBranch A b).child i) = skDec A k (b.child i) :=
  congrArg k (Subtype.ext (inflatedBranch_child A b i))

theorem skDec_root (k : GNode LG.garden.tree → V) (j : Fin w) :
    k (GNode.root LG.garden.tree j) = skDec A k (GNode.root A.skeleton.tree j) :=
  congrArg k (Subtype.ext (inflatedPosition_root A.skeleton A.data.tree j).symm)

/-- A decoration of the decoded forest, read on the layered garden. -/
def ofForest (κ : GNode (A.data.forest A.prime.1) → V) : GNode LG.garden.tree → V :=
  fun x => κ ⟨x.1, by rw [decodes_tree A.decodes]; exact x.2⟩

/-- **Main's collapse is `skDec`.** -/
theorem attachedNode_skDec (κ : GNode (A.data.forest A.prime.1) → V) (a : GNode A.skeleton.tree) :
    κ (attachedNode A.data A.prime.1 a) = skDec A (ofForest A κ) a :=
  congrArg κ (Subtype.ext rfl)

theorem collapseGenDecoration_skDec {d : ℕ} {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (A.data.garden A.prime.1) d n nfl) (a : GNode A.skeleton.tree) :
    (collapseGenDecoration A.data A.prime.1 κ).1 a = skDec A (ofForest A κ.1) a :=
  attachedNode_skDec A κ.1 a

/-- The collapsed decoration of a decoration of the decoded garden is a skeleton decoration (main
`collapsed_isDecoration`). -/
theorem isDecoration_skDec [AddCommGroup V] (κ : GNode (A.data.forest A.prime.1) → V)
    (hκ : IsDecoration (A.data.garden A.prime.1) κ) : IsDecoration A.skeleton (skDec A (ofForest A κ)) := by
  have h := collapsed_isDecoration A.data A.prime.1 κ hκ
  have e : (fun a => κ (attachedNode A.data A.prime.1 a)) = skDec A (ofForest A κ) :=
    funext (attachedNode_skDec A κ)
  rwa [e] at h

/-- The inflated crown gap at the lower joint of `u` is the skeleton crown gap of the collapsed decoration. -/
theorem crown_gap_skDec [AddCommGroup V] (k : GNode LG.garden.tree → V) (u : CLBlock A.skeleton) :
    k ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) -
        k ((inflatedBranch A u.lower).child (VineB.regionOf u).negative) =
      skDec A k (u.lower.child (VineB.regionOf u).positive) - skDec A k (u.lower.child (VineB.regionOf u).negative) := by
  rw [skDec_child A k, skDec_child A k]

end Cast

/-! ## The skeleton-only lemma: CL chains -/

section Chain
variable {S : Garden w} {d : ℕ}

/-- The gap of a CL ingredient with the atoms and lower joint of `u` is the crown gap at `u`. -/
theorem ingredient_gap_eq_crown (u : CLBlock S) (B : CLVineIngredient S) (ha : B.atoms = u.atoms)
    (hb : B.lowerJoint = u.lower) (κ : GNode S.tree → Mom d) :
    B.gap κ = κ (u.lower.child (VineB.regionOf u).positive) - κ (u.lower.child (VineB.regionOf u).negative) := by
  obtain ⟨atoms, up, low, X, hv, R⟩ := B
  simp only at ha hb
  subst ha hb
  obtain ⟨-, hp, hn⟩ := VineEstS5C.P4.W2.region_lower_eq_of_subset (subset_refl _) R (VineB.regionOf u)
  unfold CLVineIngredient.gap
  simp only
  rw [hp, hn]

/-- **Skeleton-only lemma.** Along a CL vine chain, every ingredient has the gap of the bottom ingredient; so a bound
on one ingredient's gap bounds all of them. -/
theorem chain_gap_le (A₀ : CLVineIngredient S) (rest : List (CLVineIngredient S))
    (hc : (A₀ :: rest).IsChain CLVineIngredient.Follows) (κ : GNode S.tree → Mom d) (hκ : IsDecoration S κ)
    {ρ : ℝ} {B₀ : CLVineIngredient S} (hB₀ : B₀ ∈ A₀ :: rest) (h : ‖B₀.gap κ‖ ≤ ρ)
    (B : CLVineIngredient S) (hB : B ∈ A₀ :: rest) : ‖B.gap κ‖ ≤ ρ := by
  rw [clVineChain_gap_eq A₀ rest hc κ hκ B hB, ← clVineChain_gap_eq A₀ rest hc κ hκ B₀ hB₀]
  exact h

/-- The same, from the upper-joint gap `k(a) − k(a.child excluded)` of one ingredient (the block gap of the chain at
its upper joint, up to sign). -/
theorem chain_gap_le_of_upper (A₀ : CLVineIngredient S) (rest : List (CLVineIngredient S))
    (hc : (A₀ :: rest).IsChain CLVineIngredient.Follows) (κ : GNode S.tree → Mom d) (hκ : IsDecoration S κ)
    {ρ : ℝ} {B₀ : CLVineIngredient S} (hB₀ : B₀ ∈ A₀ :: rest)
    (h : ‖κ B₀.upperJoint.toNode - κ (B₀.upperJoint.child B₀.region.excluded)‖ ≤ ρ)
    (B : CLVineIngredient S) (hB : B ∈ A₀ :: rest) : ‖B.gap κ‖ ≤ ρ := by
  rw [clVineChain_gap_eq A₀ rest hc κ hκ B hB]
  rcases clVineChain_gap_eq_upper_or_neg A₀ rest hc κ hκ B₀ hB₀ with e | e
  · rw [e]
    exact h
  · rw [e, norm_neg]
    exact h

end Chain

/-! ## Zero weight from a small collapsed chain gap -/

/-- **Zero weight for stem-unclean pairs, skeleton form.** On decorations whose collapsed crown gap at `u` (the gap
of a CL ingredient `B` with the atoms and lower joint of `u`) is at most `L^{-γ+η} < ‖k_root‖/2`, a weight vanishing
off the FL-SEP support vanishes. -/
theorem weight_zero_of_unclean_sk {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 → (∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    (B : CLVineIngredient A.skeleton) (ha : B.atoms = u.atoms) (hb : B.lowerJoint = u.lower) (ρ : ℝ)
    (hgap : ∀ k, Sel k → ‖B.gap (skDec A k)‖ ≤ ρ)
    (hθ : ∀ k, Sel k → ρ < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  refine weight_zero_of_unclean A J u hun p N r hr0 hU hlay hfl hN W Sel hW ?_
  intro k hk
  rw [crown_gap_skDec, ← ingredient_gap_eq_crown u B ha hb]
  exact lt_of_le_of_lt (hgap k hk) (hθ k hk)

/-- **Zero weight for stem-unclean pairs, chain form.** If `u` is (the block of) an ingredient of a CL vine chain
whose gap — at any ingredient, on the collapsed decoration — is at most `ρ < ‖k_root‖/2` (an SG chain under a high
root: `ρ = L^{-γ+η}`), every weight vanishing off the FL-SEP support vanishes on such decorations. -/
theorem weight_zero_of_unclean_chain {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 → (∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    (A₀ : CLVineIngredient A.skeleton) (rest : List (CLVineIngredient A.skeleton))
    (hc : (A₀ :: rest).IsChain CLVineIngredient.Follows)
    (B : CLVineIngredient A.skeleton) (hB : B ∈ A₀ :: rest) (ha : B.atoms = u.atoms) (hb : B.lowerJoint = u.lower)
    (B₀ : CLVineIngredient A.skeleton) (hB₀ : B₀ ∈ A₀ :: rest) (ρ : ℝ)
    (hdec : ∀ k, Sel k → IsDecoration A.skeleton (skDec A k))
    (hgap : ∀ k, Sel k → ‖B₀.gap (skDec A k)‖ ≤ ρ)
    (hθ : ∀ k, Sel k → ρ < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 :=
  weight_zero_of_unclean_sk A J u hun p N r hr0 hU hlay hfl hN W Sel hW B ha hb ρ
    (fun k hk => chain_gap_le A₀ rest hc (skDec A k) (hdec k hk) hB₀ (hgap k hk) B hB) hθ

end WaveTurbulence.Flower.MkMark
