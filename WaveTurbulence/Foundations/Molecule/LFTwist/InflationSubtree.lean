/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.GenericInflation
public import WaveTurbulence.Foundations.RegStruct.ChainSubtreeFrames

/-! # Actual subtree extraction at every inserted inflation frame -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

/-- The image of a valid source subtree occurs at its literal inflated frame. -/
theorem inflateTreeAt_subtree {w : ℕ} (σ : Fin w → ℤˣ)
    (X : Address w → RegChain) (Y : Address w → TTree) (t : TTree)
    (p : Path) (u : TTree) (hp : Comb.subtree t p = some u) (a : Address w) :
    Comb.subtree (inflateTreeAt σ X Y t a) (inflationFrame X a p) =
      some (inflateTreeAt σ X Y u (addrExt a p)) := by
  induction t generalizing p a with
  | leaf =>
    cases p with
    | nil =>
      have he : TTree.leaf = u := Option.some.inj hp
      subst u
      simp only [inflationFrame, Comb.subtree, addrExt_nil]
    | cons i p => simp only [Comb.subtree, reduceCtorEq] at hp
  | node l m r ihl ihm ihr =>
    cases p with
    | nil =>
      have he : TTree.node l m r = u := Option.some.inj hp
      subst u
      simp only [inflationFrame, Comb.subtree, addrExt_nil]
    | cons i p =>
      fin_cases i
      · change Comb.subtree l p = some u at hp
        change Comb.subtree ((X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1])) (inflateTreeAt σ X Y r (addrExt a [2]))))
          ((X a).lonePath ++ [0] ++ inflationFrame X (addrExt a [0]) p) =
          some (inflateTreeAt σ X Y u (addrExt a (0 :: p)))
        rw [List.append_assoc, Comb.subtree_append, plug_subtree_lonePath]
        change Comb.subtree (inflateTreeAt σ X Y l (addrExt a [0])) (inflationFrame X (addrExt a [0]) p) =
          some (inflateTreeAt σ X Y u (addrExt a (0 :: p)))
        rw [addrExt_cons a 0 p]
        exact ihl p hp (addrExt a [0])
      · change Comb.subtree m p = some u at hp
        change Comb.subtree ((X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1])) (inflateTreeAt σ X Y r (addrExt a [2]))))
          ((X a).lonePath ++ [1] ++ inflationFrame X (addrExt a [1]) p) =
          some (inflateTreeAt σ X Y u (addrExt a (1 :: p)))
        rw [List.append_assoc, Comb.subtree_append, plug_subtree_lonePath]
        change Comb.subtree (inflateTreeAt σ X Y m (addrExt a [1])) (inflationFrame X (addrExt a [1]) p) =
          some (inflateTreeAt σ X Y u (addrExt a (1 :: p)))
        rw [addrExt_cons a 1 p]
        exact ihm p hp (addrExt a [1])
      · change Comb.subtree r p = some u at hp
        change Comb.subtree ((X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1])) (inflateTreeAt σ X Y r (addrExt a [2]))))
          ((X a).lonePath ++ [2] ++ inflationFrame X (addrExt a [2]) p) =
          some (inflateTreeAt σ X Y u (addrExt a (2 :: p)))
        rw [List.append_assoc, Comb.subtree_append, plug_subtree_lonePath]
        change Comb.subtree (inflateTreeAt σ X Y r (addrExt a [2])) (inflationFrame X (addrExt a [2]) p) =
          some (inflateTreeAt σ X Y u (addrExt a (2 :: p)))
        rw [addrExt_cons a 2 p]
        exact ihr p hp (addrExt a [2])

end WaveTurbulence.LFTwist
