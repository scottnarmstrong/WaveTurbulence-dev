/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! Extensional equality of concrete gardens from their actual labelled coordinate data. -/
public section
namespace WaveTurbulence.Induct

theorem garden_eq_of_raw_data {w : ℕ} (G H : Garden w)
    (hsig : G.sig = H.sig) (htree : G.tree = H.tree)
    (hp : ∀ (a : GLeaf G.tree) (b : GLeaf H.tree), a.1 = b.1 → (G.pair a).1 = (H.pair b).1)
    (hm : ∀ (a : GLeaf G.tree) (b : GLeaf H.tree), a.1 = b.1 → G.mark a = H.mark b) : G = H := by
  cases G with
  | mk gs gt gp gm ginv gfix gsign =>
    cases H with
    | mk hs ht hp' hm' hinv hfix hsign =>
      change gs = hs at hsig
      cases hsig
      change gt = ht at htree
      cases htree
      have hpair : gp = hp' := funext (fun a => Subtype.ext (hp a a rfl))
      have hmark : gm = hm' := funext (fun a => hm a a rfl)
      cases hpair
      cases hmark
      rfl

theorem layeredGarden_eq_of_raw_data {w : ℕ} (G H : LayeredGarden w)
    (hg : G.garden = H.garden)
    (hl : ∀ (a : GNode G.garden.tree) (b : GNode H.garden.tree), a.1 = b.1 → G.layer a = H.layer b) : G = H := by
  cases G with
  | mk gg gl gvalid =>
    cases H with
    | mk hg' hl' hvalid =>
      change gg = hg' at hg
      cases hg
      have he : gl = hl' := funext (fun a => hl a a rfl)
      cases he
      rfl

theorem garden_pair_raw_of_eq {w : ℕ} {G H : Garden w} (he : G = H)
    (a : GLeaf G.tree) (b : GLeaf H.tree) (hab : a.1 = b.1) : (G.pair a).1 = (H.pair b).1 := by
  cases he
  exact congrArg (fun l : GLeaf G.tree => (G.pair l).1) (Subtype.ext hab)

theorem layeredGarden_layer_raw_of_eq {w : ℕ} {G H : LayeredGarden w} (he : G = H)
    (a : GNode G.garden.tree) (b : GNode H.garden.tree) (hab : a.1 = b.1) : G.layer a = H.layer b := by
  cases he
  exact congrArg G.layer (Subtype.ext hab)

end WaveTurbulence.Induct
