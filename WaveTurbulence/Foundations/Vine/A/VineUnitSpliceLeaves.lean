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

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv`). -/
noncomputable def unitSpliceLeafEquivMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    GLeaf (stSt G σ Mk).G.tree ≃ GLeaf (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree :=
  equivOfSameRange (fun q => coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q))
    (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).leaf
    ((coreLeafEquiv G Z.P).injective.comp (spliceFoldLeafTrace (unitBlocks G σ Mk)).injective)
    (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).injective
    (unitTwist_splice_leaf_rangesMk Z σ hT hsel)

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_names`). -/
theorem unitSpliceLeafEquiv_namesMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).leaf (unitSpliceLeafEquivMk Z σ hT hsel q) =
      coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q) :=
  equivOfSameRange_comm _ _ _ _ (unitTwist_splice_leaf_rangesMk Z σ hT hsel) q

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_pair`). -/
theorem unitSpliceLeafEquiv_pairMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    unitSpliceLeafEquivMk Z σ hT hsel ((stSt G σ Mk).G.pair q) =
      (stSt Z.target (transportPrescription Z.iso σ) Mk').G.pair (unitSpliceLeafEquivMk Z σ hT hsel q) := by
  apply (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).injective
  exact (unitSpliceLeafEquiv_namesMk Z σ hT hsel ((stSt G σ Mk).G.pair q)).trans
    ((congrArg (coreLeafEquiv G Z.P) ((spliceFoldLeafTrace (unitBlocks G σ Mk)).pair q)).trans
      ((unitTwistGarden_pair G Z.P _).symm.trans
        ((congrArg Z.target.pair (unitSpliceLeafEquiv_namesMk Z σ hT hsel q).symm).trans
          ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).pair
            (unitSpliceLeafEquivMk Z σ hT hsel q)).symm)))

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_mark`). -/
theorem unitSpliceLeafEquiv_markMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').G.mark (unitSpliceLeafEquivMk Z σ hT hsel q) =
      (stSt G σ Mk).G.mark q := by
  exact ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).mark _).trans
    ((congrArg Z.target.mark (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)).trans
      ((unitTwistGarden_mark G Z.P _).trans ((spliceFoldLeafTrace (unitBlocks G σ Mk)).mark q).symm))

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_root`). -/
theorem unitSpliceLeafEquiv_rootMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    (unitSpliceLeafEquivMk Z σ hT hsel q).1.2 = [] ↔ q.1.2 = [] := by
  have ho : (coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q)).1.2 = [] ↔
      ((spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q).1.2 = [] := by
    simpa only [not_not] using not_congr (coreLeafEquiv_nonroot G Z.P _)
  exact ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).root _).symm.trans
    ((Iff.of_eq (congrArg (fun l : GLeaf Z.target.tree => l.1.2 = [])
      (unitSpliceLeafEquiv_namesMk Z σ hT hsel q))).trans
        (ho.trans ((spliceFoldLeafTrace (unitBlocks G σ Mk)).root q)))

/-- B1b-2 (Mk-general form of `active_retained_not_surviving`). -/
theorem active_retained_not_survivingMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)}
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    ¬ ∃ q, (spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q = Z.P.retained := by
  let lp : Mole.GardenLPLeaf G :=
    ⟨Z.P.retained, Z.P.unmarked, retained_nonroot G Z.P, Z.P.paired_nonroot⟩
  have hd : DeletedDart (spliceFold G (unitBlocks G σ Mk)).cls (.inr lp) :=
    active_internal_dart_mergedMk Z σ hsel (retainedLP_inGroup Z)
  intro hr
  exact ((spliceFold_leaf_range (unitBlocks G σ Mk) Z.P.retained).mp hr) ⟨lp, rfl, hd⟩

/-- B1b-2 (Mk-general form of `active_pair_not_surviving`). -/
theorem active_pair_not_survivingMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)}
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    ¬ ∃ q, (spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q = G.pair Z.P.retained := by
  rintro ⟨q, he⟩
  apply active_retained_not_survivingMk Z σ hsel
  refine ⟨(stSt G σ Mk).G.pair q, ?_⟩
  exact ((spliceFoldLeafTrace (unitBlocks G σ Mk)).pair q).trans
    ((congrArg G.pair he).trans (G.pair_pair Z.P.retained))

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_sign`). -/
theorem unitSpliceLeafEquiv_signMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').G.sign (unitSpliceLeafEquivMk Z σ hT hsel q).toNode =
      (stSt G σ Mk).G.sign q.toNode := by
  have hr : (spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q ≠ Z.P.retained :=
    fun he => active_retained_not_survivingMk Z σ hsel ⟨q, he⟩
  have hp : (spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q ≠ G.pair Z.P.retained :=
    fun he => active_pair_not_survivingMk Z σ hsel ⟨q, he⟩
  have hs : Z.target.sign (coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q)).toNode =
      G.sign ((spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q).toNode := by
    change nodeSign G.sig (coreLeafEquiv G Z.P _).1 = _
    rw [coreLeafEquiv_sign, coreLeafMultiplier, ite_eq_right (not_or_intro hr hp), one_mul]
  exact ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).sign _).trans
    ((congrArg (fun l : GLeaf Z.target.tree => Z.target.sign l.toNode)
      (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)).trans
        (hs.trans ((spliceFoldLeafTrace (unitBlocks G σ Mk)).sign q).symm))

end WaveTurbulence.VineA
