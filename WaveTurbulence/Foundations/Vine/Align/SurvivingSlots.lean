/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.NodeTrace
public import WaveTurbulence.Foundations.Vine.A.VineBatchOrderedNormalization
/-! Surviving outer slots are ordinary slots of every selected operation. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineA VineB RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton

variable {w : ℕ} {G H : Garden w}

def slotCast (e : G = H) (s : ReplacementSlot G) : ReplacementSlot H := e ▸ s

def leafCast (e : G = H) (l : GLeaf G.tree) : GLeaf H.tree := e ▸ l

theorem leafCast_val (e : G = H) (l : GLeaf G.tree) : (leafCast e l).1 = l.1 := by
  subst H
  rfl

theorem slotCast_inr (e : G = H) (b : GBranch G.tree) :
    slotCast e (.inr b) = .inr (gardenBranchCast e b) := by subst H; rfl

theorem slotCast_inl (e : G = H) (hG : G.IsPlain) (hH : H.IsPlain) (q : SourcePair G) :
    slotCast e (.inl q) = .inl (pairOfLeaf H hH (leafCast e (q.firstLeaf hG))) := by
  subst H
  exact congrArg Sum.inl (pairOfLeaf_firstLeaf G hG q).symm

theorem cast_iota {S : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    {blk : J → CLBlock S} (e : G = H) (Φ : SpliceShape blk G)
    (hS : S.IsPlain) (hG : G.IsPlain) (hH : H.IsPlain) (s : ReplacementSlot H) :
    (castShape e Φ).iota hS hH s = Φ.iota hS hG (slotCast e.symm s) := by
  subst H
  rfl

/-- Pair equality forces equality of one leaf or its partner. -/
theorem pairOfLeaf_eq_cases (hG : G.IsPlain) (l r : GLeaf G.tree)
    (he : pairOfLeaf G hG l = pairOfLeaf G hG r) : l = r ∨ l = G.pair r := by
  have hl := pairOfLeaf_first_or_partner G hG l
  have hr := pairOfLeaf_first_or_partner G hG r
  rw [he] at hl
  rcases hl with h1 | h1 <;> rcases hr with h2 | h2
  · exact Or.inl (h1.symm.trans h2)
  · exact Or.inr (h1.symm.trans h2)
  · exact Or.inr ((congrArg G.pair (h1.symm.trans h2)).symm.trans (G.pair_pair l)).symm
  · exact Or.inl ((G.pair_pair l).symm.trans ((congrArg G.pair (h1.symm.trans h2)).trans (G.pair_pair r)))

/-- No surviving pair is the exceptional pair of a selected operation. -/
theorem surviving_pair_ne (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (hG : G.IsPlain)
    (l : GLeaf (stSt G σ).G.tree) :
    pairOfLeaf G hG ((stShape (Mole.garden_isMolecule G) σ).leaf l) ≠
      pairOfLeaf G hG Z.P.retained := by
  intro he
  rw [stShape_leaf_eq] at he
  rcases pairOfLeaf_eq_cases hG _ _ he with he | he
  · exact active_retained_not_surviving Z σ hsel ⟨l, he⟩
  · exact active_pair_not_surviving Z σ hsel ⟨l, he⟩

/-- Ordered normalization transports each actual original leaf name. -/
theorem unit_leaf_cast (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (l : GLeaf (stSt G σ).G.tree) :
    (stShape (Mole.garden_isMolecule Z.target) (transportPrescription Z.iso σ)).leaf
      (leafCast (unitSplice_garden_eq Z σ hsel).symm l) =
    coreLeafEquiv G Z.P ((stShape (Mole.garden_isMolecule G) σ).leaf l) := by
  rw [stShape_leaf_eq, stShape_leaf_eq]
  have he : leafCast (unitSplice_garden_eq Z σ hsel).symm l = unitSpliceLeafEquiv Z σ hsel l :=
    Subtype.ext ((leafCast_val _ _).trans (unitSpliceLeafEquiv_address Z σ hsel l).symm)
  rw [he]
  exact unitSpliceLeafEquiv_names Z σ hsel l

/-- Ordered normalization transports each actual original branch name. -/
theorem unit_branch_cast (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).M.ob
      (gardenBranchCast (unitSplice_garden_eq Z σ hsel).symm b) =
    Z.iso.e ((stSt G σ).M.ob b) := by
  have he : gardenBranchCast (unitSplice_garden_eq Z σ hsel).symm b = (unitSpliceMolIso Z σ hsel).e b :=
    Subtype.ext ((gardenBranchCast_val _ _).trans (unitSpliceMolIso_address Z σ hsel b).symm)
  rw [he]
  exact unitSpliceMolIso_branch_names Z σ hsel b

end WaveTurbulence.VineAlign
