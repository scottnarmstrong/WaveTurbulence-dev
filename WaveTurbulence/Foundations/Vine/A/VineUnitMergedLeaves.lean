/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitDeletedDarts
public import WaveTurbulence.Foundations.Vine.A.VineSpliceLeafRange
/-! The actual LF leaf map preserves the complete surviving-leaf carrier
of simultaneous selected splices, including leaves absent from the molecule. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `unitTwist_mergedLeaf_iff`). -/
theorem unitTwist_mergedLeaf_iffMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf G.tree) :
    MergedLeaf (spliceFold Z.target (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).cls
      (coreLeafEquiv G Z.P q) ↔ MergedLeaf (spliceFold G (unitBlocks G σ Mk)).cls q := by
  constructor
  · rintro ⟨lp', he, hd⟩
    let lp := (lpLeafEquiv G Z.P).symm lp'
    have hmap : lpLeafEquiv G Z.P lp = lp' := Equiv.apply_symm_apply _ _
    have hval : lp.1 = q := (coreLeafEquiv G Z.P).injective ((congrArg Subtype.val hmap).trans he)
    refine ⟨lp, hval, ?_⟩
    apply (naiveDart_deleted_iffMk Z σ hT hsel (.inr lp)).mp
    change DeletedDart _ (.inr (lpLeafEquiv G Z.P lp))
    rw [hmap]
    exact hd
  · rintro ⟨lp, he, hd⟩
    refine ⟨lpLeafEquiv G Z.P lp, congrArg (coreLeafEquiv G Z.P) he, ?_⟩
    exact (naiveDart_deleted_iffMk Z σ hT hsel (.inr lp)).mpr hd

/-- B1b-2 (Mk-general form of `unitTwist_splice_leaf_ranges`). -/
theorem unitTwist_splice_leaf_rangesMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q' : GLeaf Z.target.tree) :
    (∃ q, coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf q) = q') ↔
      ∃ q, (spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).leaf q = q' := by
  obtain ⟨q, rfl⟩ := (coreLeafEquiv G Z.P).surjective q'
  have hleft : (∃ x, coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf x) = coreLeafEquiv G Z.P q) ↔
      ∃ x, (spliceFoldLeafTrace (unitBlocks G σ Mk)).leaf x = q :=
    ⟨fun ⟨x, hx⟩ => ⟨x, (coreLeafEquiv G Z.P).injective hx⟩,
      fun ⟨x, hx⟩ => ⟨x, congrArg (coreLeafEquiv G Z.P) hx⟩⟩
  exact hleft.trans ((spliceFold_leaf_range (unitBlocks G σ Mk) q).trans
    ((not_congr (unitTwist_mergedLeaf_iffMk Z σ hT hsel q)).symm.trans
      (spliceFold_leaf_range (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')
        (coreLeafEquiv G Z.P q)).symm))

end WaveTurbulence.VineA
