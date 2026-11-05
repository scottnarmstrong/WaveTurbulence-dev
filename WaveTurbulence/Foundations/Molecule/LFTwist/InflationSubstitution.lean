/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.GenericInflation

/-! # Literal subtree substitution commutes with raw regular inflation -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

/-- Inflation is compatible with replacement at every actual source node.
In particular, no condition on an original leaf's replacement tree is needed. -/
theorem inflateTreeAt_replace {w : ℕ} (σ : Fin w → ℤˣ)
    (X : Address w → RegChain) (Y : Address w → TTree) (t : TTree)
    (p : Path) (hp : p ∈ t.nodes) (s : TTree) (a : Address w) :
    inflateTreeAt σ X Y (Comb.replaceAt t p s) a =
      Comb.replaceAt (inflateTreeAt σ X Y t a) (inflationFrame X a p)
        (inflateTreeAt σ X Y s (addrExt a p)) := by
  induction t generalizing p a with
  | leaf =>
    have he : p = [] := Finset.mem_singleton.mp hp
    subst p
    simp only [Comb.replaceAt, inflationFrame, addrExt_nil]
  | node l m r ihl ihm ihr =>
    cases p with
    | nil => simp only [Comb.replaceAt, inflationFrame, addrExt_nil]
    | cons i p =>
      fin_cases i
      · have hc : p ∈ l.nodes := (cons_mem_nodes_node l m r 0 p).mp hp
        have hh := ihl p hc (addrExt a [0])
        change (X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y (Comb.replaceAt l p s) (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1])) (inflateTreeAt σ X Y r (addrExt a [2]))) =
          Comb.replaceAt ((X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1])) (inflateTreeAt σ X Y r (addrExt a [2]))))
            ((X a).lonePath ++ [0] ++ inflationFrame X (addrExt a [0]) p)
            (inflateTreeAt σ X Y s (addrExt a (0 :: p)))
        rw [hh, List.append_assoc, replaceAt_plug_lone_append, addrExt_cons a 0 p]
        rfl
      · have hc : p ∈ m.nodes := (cons_mem_nodes_node l m r 1 p).mp hp
        have hh := ihm p hc (addrExt a [1])
        change (X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y (Comb.replaceAt m p s) (addrExt a [1])) (inflateTreeAt σ X Y r (addrExt a [2]))) =
          Comb.replaceAt ((X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1])) (inflateTreeAt σ X Y r (addrExt a [2]))))
            ((X a).lonePath ++ [1] ++ inflationFrame X (addrExt a [1]) p)
            (inflateTreeAt σ X Y s (addrExt a (1 :: p)))
        rw [hh, List.append_assoc, replaceAt_plug_lone_append, addrExt_cons a 1 p]
        rfl
      · have hc : p ∈ r.nodes := (cons_mem_nodes_node l m r 2 p).mp hp
        have hh := ihr p hc (addrExt a [2])
        change (X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1])) (inflateTreeAt σ X Y (Comb.replaceAt r p s) (addrExt a [2]))) =
          Comb.replaceAt ((X a).plug (nodeSign σ a) (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1])) (inflateTreeAt σ X Y r (addrExt a [2]))))
            ((X a).lonePath ++ [2] ++ inflationFrame X (addrExt a [2]) p)
            (inflateTreeAt σ X Y s (addrExt a (2 :: p)))
        rw [hh, List.append_assoc, replaceAt_plug_lone_append, addrExt_cons a 2 p]
        rfl

end WaveTurbulence.LFTwist
