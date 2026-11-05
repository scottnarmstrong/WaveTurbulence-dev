/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CutPairing

/-! # Exact canonical-criterion invariance for the actual collapsed unit twist -/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (LG : LayeredGarden w) (P : CorePlacement LG.garden)

/-- TARGET's exact canonicity criterion is invariant under the actual
same-layer collapsed unit twist, without any local vine-case assumptions. -/
theorem unitLayerTwist_canonCriterion (he : SameLowerLayer LG P) (p : ℕ) :
    (unitLayerTwist LG P he).CanonCriterion p ↔ LG.CanonCriterion p := by
  constructor
  · intro hc
    apply (canonCriterion_iff_threshold LG p).mpr
    refine ⟨fun n => ?_,?_⟩
    · exact (cutNodeEquiv_layer LG P he n).symm.trans_le (hc.1 _)
    · intro r a b ha hb hi hp
      have ha' := (cutNodeEquiv_isCutRoot LG P he p r a).mpr ha
      have hb' := (cutNodeEquiv_isCutRoot LG P he p r b).mpr hb
      have hi' := cutRoots_incomparable (unitLayerTwist LG P he) ha' hb'
        (fun hh => incomparable_ne hi ((cutNodeEquiv LG.garden P).injective hh))
      have hp' := (cutNodeEquiv_pairing_iff LG P he ha hb (incomparable_ne hi)).mpr hp
      exact ((canonCriterion_iff_threshold (unitLayerTwist LG P he) p).mp hc).2 r _ _ ha' hb' hi' hp'
  · intro hc
    apply (canonCriterion_iff_threshold (unitLayerTwist LG P he) p).mpr
    constructor
    · intro n
      obtain ⟨n,rfl⟩ := (cutNodeEquiv LG.garden P).surjective n
      exact (cutNodeEquiv_layer LG P he n).trans_le (hc.1 n)
    · intro r a b ha hb hi hp
      obtain ⟨a,rfl⟩ := (cutNodeEquiv LG.garden P).surjective a
      obtain ⟨b,rfl⟩ := (cutNodeEquiv LG.garden P).surjective b
      have ha' := (cutNodeEquiv_isCutRoot LG P he p r a).mp ha
      have hb' := (cutNodeEquiv_isCutRoot LG P he p r b).mp hb
      have hne : a ≠ b := fun hh => incomparable_ne hi (congrArg (cutNodeEquiv LG.garden P) hh)
      have hi' := cutRoots_incomparable LG ha' hb' hne
      have hp' := (cutNodeEquiv_pairing_iff LG P he ha' hb' hne).mp hp
      exact ((canonCriterion_iff_threshold LG p).mp hc).2 r a b ha' hb' hi' hp'

end WaveTurbulence.LFTwist
