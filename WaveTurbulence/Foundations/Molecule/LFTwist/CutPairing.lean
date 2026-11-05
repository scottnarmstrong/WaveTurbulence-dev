/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CutSignedValues

/-! # Complete pairing transfers on every actual threshold cut

The integer-decoration bijection and the signed sum rule prove closure
transport. Distinct cut roots are incomparable by layer monotonicity.
This covers every local vine case without a shape-specific premise.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (LG : LayeredGarden w)

/-- A strict descendant's parent has layer no larger than its ancestor. -/
theorem parentLayer_le_of_strict_desc {a b : GNode LG.garden.tree} (p : ℕ)
    (hab : a.IsDesc b) (hne : a ≠ b) : LG.parentLayer p b ≤ LG.layer a := by
  have hpath : a.1.2 ≠ b.1.2 := fun he => hne (Subtype.ext (Prod.ext hab.1 he))
  have hn : b.1.2 ≠ [] := by
    intro he
    exact hpath ((List.eq_nil_of_prefix_nil (he ▸ hab.2)).trans he.symm)
  have hd : a.IsDesc (GNode.parent b hn).toNode :=
    ⟨hab.1,Mole.proper_prefix_dropLast hab.2 hpath⟩
  exact (parentLayer_nonroot LG p b hn).trans_le (LG.layer_le_of_isDesc hd)

/-- Distinct roots of one integer layer cut are necessarily incomparable. -/
theorem cutRoots_incomparable {p r : ℕ} {a b : GNode LG.garden.tree}
    (ha : IsCutRoot LG p r a) (hb : IsCutRoot LG p r b) (hne : a ≠ b) : a.Incomparable b := by
  constructor
  · intro hd
    have hp := parentLayer_le_of_strict_desc LG p hd hne
    have hl := ha.1
    have hr := hb.2
    omega
  · intro hd
    have hp := parentLayer_le_of_strict_desc LG p hd (Ne.symm hne)
    have hl := hb.1
    have hr := ha.2
    omega

/-- Incomparability includes actual node distinctness. -/
theorem incomparable_ne {F : Fin w → TTree} {a b : GNode F} (hi : a.Incomparable b) : a ≠ b := by
  intro he
  exact hi.1 (he ▸ (Comb.GNode.isDesc_refl a))

variable (P : CorePlacement LG.garden) (he : SameLowerLayer LG P)

/-- Literal complete pairing is equivalent on corresponding pairs of cut
roots. The statement concerns actual node subtrees, not abstract codes. -/
theorem cutNodeEquiv_pairing_iff {p r : ℕ} {a b : GNode LG.garden.tree}
    (ha : IsCutRoot LG p r a) (hb : IsCutRoot LG p r b) (hne : a ≠ b) :
    (unitLayerTwist LG P he).garden.CompletelyPaired
        ((cutNodeEquiv LG.garden P a).leavesBelow ∪ (cutNodeEquiv LG.garden P b).leavesBelow) ↔
      LG.garden.CompletelyPaired (a.leavesBelow ∪ b.leavesBelow) := by
  have hi := cutRoots_incomparable LG ha hb hne
  have ha' := (cutNodeEquiv_isCutRoot LG P he p r a).mpr ha
  have hb' := (cutNodeEquiv_isCutRoot LG P he p r b).mpr hb
  have hi' := cutRoots_incomparable (unitLayerTwist LG P he) ha' hb'
    (fun hh => hne ((cutNodeEquiv LG.garden P).injective hh))
  have har : a ≠ P.retained.toNode := fun hh => retained_not_cutRoot LG P he p r (hh ▸ ha)
  have hbr : b ≠ P.retained.toNode := fun hh => retained_not_cutRoot LG P he p r (hh ▸ hb)
  refine (completelyPaired_iff_node_sums (unitLayerTwist LG P he).garden _ _ hi').trans ?_
  refine Iff.trans ?_ (completelyPaired_iff_node_sums LG.garden a b hi).symm
  constructor
  · intro h κ hκ
    have hz := h (twistNodeLabels LG.garden P κ) (twistNodeLabels_isDecoration LG.garden P κ hκ)
    have h₀ := cutNodeEquiv_signedValue LG.garden P κ hκ a har
    have h₁ := cutNodeEquiv_signedValue LG.garden P κ hκ b hbr
    exact (congrArg₂ (· + ·) h₀ h₁).symm.trans hz
  · intro h η hη
    obtain ⟨κ,hκ⟩ := (unitTwistDecorationEquiv LG.garden P ℤ).surjective ⟨η,hη⟩
    have hlabels : twistNodeLabels LG.garden P κ.1 = η := congrArg Subtype.val hκ
    have hz := h κ.1 κ.2
    have h₀ := cutNodeEquiv_signedValue LG.garden P κ.1 κ.2 a har
    have h₁ := cutNodeEquiv_signedValue LG.garden P κ.1 κ.2 b hbr
    have hsum := (congrArg₂ (· + ·) h₀ h₁).trans hz
    exact (congrArg (fun f => signedValue (unitTwistGarden LG.garden P) f (cutNodeEquiv LG.garden P a) +
      signedValue (unitTwistGarden LG.garden P) f (cutNodeEquiv LG.garden P b)) hlabels).symm.trans hsum

end WaveTurbulence.LFTwist
