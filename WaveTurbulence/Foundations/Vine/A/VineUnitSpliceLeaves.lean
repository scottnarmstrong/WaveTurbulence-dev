/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitMergedLeaves
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceBranch
/-! The full surviving-leaf equivalence for actual simultaneous selected
splices preserves pairing, marks and roots. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- The actual full leaf map between the two simultaneous splices. -/
noncomputable def unitSpliceLeafEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    GLeaf (stSt G σ).G.tree ≃ GLeaf (stSt Z.target (transportPrescription Z.iso σ)).G.tree :=
  equivOfSameRange (fun q => coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ)).leaf q))
    (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).leaf
    ((coreLeafEquiv G Z.P).injective.comp (spliceFoldLeafTrace (unitBlocks G σ)).injective)
    (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).injective
    (unitTwist_splice_leaf_ranges Z σ hsel)

/-- The full leaf map commutes with literal original names and the actual LF leaf map. -/
theorem unitSpliceLeafEquiv_names (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).leaf (unitSpliceLeafEquiv Z σ hsel q) =
      coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ)).leaf q) :=
  equivOfSameRange_comm _ _ _ _ (unitTwist_splice_leaf_ranges Z σ hsel) q

/-- The full actual leaf pairing commutes through the simultaneous splices. -/
theorem unitSpliceLeafEquiv_pair (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    unitSpliceLeafEquiv Z σ hsel ((stSt G σ).G.pair q) =
      (stSt Z.target (transportPrescription Z.iso σ)).G.pair (unitSpliceLeafEquiv Z σ hsel q) := by
  apply (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).injective
  exact (unitSpliceLeafEquiv_names Z σ hsel ((stSt G σ).G.pair q)).trans
    ((congrArg (coreLeafEquiv G Z.P) ((spliceFoldLeafTrace (unitBlocks G σ)).pair q)).trans
      ((unitTwistGarden_pair G Z.P _).symm.trans
        ((congrArg Z.target.pair (unitSpliceLeafEquiv_names Z σ hsel q).symm).trans
          ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).pair
            (unitSpliceLeafEquiv Z σ hsel q)).symm)))

/-- Every actual retained mark is preserved. -/
theorem unitSpliceLeafEquiv_mark (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.mark (unitSpliceLeafEquiv Z σ hsel q) =
      (stSt G σ).G.mark q := by
  exact ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).mark _).trans
    ((congrArg Z.target.mark (unitSpliceLeafEquiv_names Z σ hsel q)).trans
      ((unitTwistGarden_mark G Z.P _).trans ((spliceFoldLeafTrace (unitBlocks G σ)).mark q).symm))

/-- The actual full leaf map preserves roots, including leaves absent from the molecule. -/
theorem unitSpliceLeafEquiv_root (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (unitSpliceLeafEquiv Z σ hsel q).1.2 = [] ↔ q.1.2 = [] := by
  have ho : (coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ)).leaf q)).1.2 = [] ↔
      ((spliceFoldLeafTrace (unitBlocks G σ)).leaf q).1.2 = [] := by
    simpa only [not_not] using not_congr (coreLeafEquiv_nonroot G Z.P _)
  exact ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).root _).symm.trans
    ((Iff.of_eq (congrArg (fun l : GLeaf Z.target.tree => l.1.2 = [])
      (unitSpliceLeafEquiv_names Z σ hsel q))).trans
        (ho.trans ((spliceFoldLeafTrace (unitBlocks G σ)).root q)))

/-- The exceptional retained leaf is removed by its selected containing unit. -/
theorem active_retained_not_surviving (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    ¬ ∃ q, (spliceFoldLeafTrace (unitBlocks G σ)).leaf q = Z.P.retained := by
  let lp : Mole.GardenLPLeaf G :=
    ⟨Z.P.retained, Z.P.unmarked, retained_nonroot G Z.P, Z.P.paired_nonroot⟩
  have hd : DeletedDart (spliceFold G (unitBlocks G σ)).cls (.inr lp) :=
    active_internal_dart_merged Z σ hsel (retainedLP_inGroup Z)
  intro hr
  exact ((spliceFold_leaf_range (unitBlocks G σ) Z.P.retained).mp hr) ⟨lp, rfl, hd⟩

/-- Both exceptional sign-changing leaves are absent from the retained full-leaf carrier. -/
theorem active_pair_not_surviving (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    ¬ ∃ q, (spliceFoldLeafTrace (unitBlocks G σ)).leaf q = G.pair Z.P.retained := by
  rintro ⟨q, he⟩
  apply active_retained_not_surviving Z σ hsel
  refine ⟨(stSt G σ).G.pair q, ?_⟩
  exact ((spliceFoldLeafTrace (unitBlocks G σ)).pair q).trans
    ((congrArg G.pair he).trans (G.pair_pair Z.P.retained))

/-- Full surviving leaf signs agree: both exceptional sign changes were deleted. -/
theorem unitSpliceLeafEquiv_sign (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.sign (unitSpliceLeafEquiv Z σ hsel q).toNode =
      (stSt G σ).G.sign q.toNode := by
  have hr : (spliceFoldLeafTrace (unitBlocks G σ)).leaf q ≠ Z.P.retained :=
    fun he => active_retained_not_surviving Z σ hsel ⟨q, he⟩
  have hp : (spliceFoldLeafTrace (unitBlocks G σ)).leaf q ≠ G.pair Z.P.retained :=
    fun he => active_pair_not_surviving Z σ hsel ⟨q, he⟩
  have hs : Z.target.sign (coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ)).leaf q)).toNode =
      G.sign ((spliceFoldLeafTrace (unitBlocks G σ)).leaf q).toNode := by
    change nodeSign G.sig (coreLeafEquiv G Z.P _).1 = _
    rw [coreLeafEquiv_sign, coreLeafMultiplier, ite_eq_right (not_or_intro hr hp), one_mul]
  exact ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).sign _).trans
    ((congrArg (fun l : GLeaf Z.target.tree => Z.target.sign l.toNode)
      (unitSpliceLeafEquiv_names Z σ hsel q)).trans
        (hs.trans ((spliceFoldLeafTrace (unitBlocks G σ)).sign q).symm))

end WaveTurbulence.VineA
