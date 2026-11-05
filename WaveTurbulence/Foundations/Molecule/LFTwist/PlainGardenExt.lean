/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # Extensionality through literal surviving leaf addresses -/

public section
namespace WaveTurbulence.LFTwist

/-- Two ordinary gardens agree if their literal signature, forest and partner
addresses agree. This avoids any arbitrary re-enumeration of their leaves. -/
theorem plainGarden_eq_of_pair_addresses {w : ℕ} {G H : Garden w}
    (hG : G.IsPlain) (hH : H.IsPlain) (hs : G.sig = H.sig) (ht : G.tree = H.tree)
    (hp : ∀ (l : GLeaf G.tree) (m : GLeaf H.tree), l.1 = m.1 → (G.pair l).1 = (H.pair m).1) : G = H := by
  obtain ⟨gs,gt,gp,gm,gpp,geq,gsgn⟩ := G
  obtain ⟨hsig,htree,hpair,hmark,hpp,heq,hsgn⟩ := H
  change gs = hsig at hs
  change gt = htree at ht
  subst hsig
  subst htree
  have he : gp = hpair := funext (fun l => Subtype.ext (hp l l rfl))
  have hm : gm = hmark := funext (fun l => (hG l).trans (hH l).symm)
  cases he
  cases hm
  rfl

end WaveTurbulence.LFTwist
