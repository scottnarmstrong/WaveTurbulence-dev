/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement
public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed
public import WaveTurbulence.Foundations.RegStruct.LocalPairNaturality

/-! # Raw local inflation for reconstruction naturality

This exposes the tree-substitution operation independently of leaf matching.
Actual reconstruction is recovered by looking up its branch and leaf data at
valid source addresses.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

/-- Inflate a literal rooted source tree using regular contexts at its
branching addresses and literal replacement trees at its leaf addresses. -/
@[expose] noncomputable def inflateTreeAt {w : ℕ} (σ : Fin w → ℤˣ)
    (X : Address w → RegChain) (Y : Address w → TTree) : TTree → Address w → TTree
  | .leaf, a => Y a
  | .node l m r, a => (X a).plug (nodeSign σ a)
      (.node (inflateTreeAt σ X Y l (addrExt a [0]))
        (inflateTreeAt σ X Y m (addrExt a [1]))
        (inflateTreeAt σ X Y r (addrExt a [2])))

/-- Local address covariance needs equality only at the source's actual
branching and leaf addresses, not at unused raw addresses. -/
theorem inflateTreeAt_map {w v : ℕ} (σ : Fin w → ℤˣ) (σ' : Fin v → ℤˣ)
    (X : Address w → RegChain) (Y : Address w → TTree)
    (X' : Address v → RegChain) (Y' : Address v → TTree) (f : Address w → Address v)
    (t : TTree) (a : Address w) (hf : RespectsAt f a)
    (hX : ∀ q ∈ t.branching, X' (f (addrExt a q)) = X (addrExt a q))
    (hY : ∀ q ∈ t.leaves, Y' (f (addrExt a q)) = Y (addrExt a q))
    (hσ : ∀ q ∈ t.branching, nodeSign σ' (f (addrExt a q)) = nodeSign σ (addrExt a q)) :
    inflateTreeAt σ' X' Y' t (f a) = inflateTreeAt σ X Y t a := by
  induction t generalizing a with
  | leaf =>
    have hh := hY [] (by simp [TTree.leaves])
    simpa only [inflateTreeAt, addrExt_nil] using hh
  | node l m r ihl ihm ihr =>
    have hx (i : Fin 3) (q : Path) (hq : q ∈ (![l,m,r] i).branching) :
        X' (f (addrExt (addrExt a [i]) q)) = X (addrExt (addrExt a [i]) q) := by
      have hh := hX (i :: q) ((cons_mem_branching_node l m r i q).mpr hq)
      rw [addrExt_cons a i q] at hh
      exact hh
    have hy (i : Fin 3) (q : Path) (hq : q ∈ (![l,m,r] i).leaves) :
        Y' (f (addrExt (addrExt a [i]) q)) = Y (addrExt (addrExt a [i]) q) := by
      have hh := hY (i :: q) ((cons_mem_leaves_node l m r i q).mpr hq)
      rw [addrExt_cons a i q] at hh
      exact hh
    have hs (i : Fin 3) (q : Path) (hq : q ∈ (![l,m,r] i).branching) :
        nodeSign σ' (f (addrExt (addrExt a [i]) q)) = nodeSign σ (addrExt (addrExt a [i]) q) := by
      have hh := hσ (i :: q) ((cons_mem_branching_node l m r i q).mpr hq)
      rw [addrExt_cons a i q] at hh
      exact hh
    have hcode : X' (f a) = X a := by simpa only [addrExt_nil] using hX [] (by simp [TTree.branching])
    have hsign : nodeSign σ' (f a) = nodeSign σ a := by
      simpa only [addrExt_nil] using hσ [] (by simp [TTree.branching])
    have hl := ihl (addrExt a [0]) (hf.child [0]) (hx 0) (hy 0) (hs 0)
    have hm := ihm (addrExt a [1]) (hf.child [1]) (hx 1) (hy 1) (hs 1)
    have hr := ihr (addrExt a [2]) (hf.child [2]) (hx 2) (hy 2) (hs 2)
    change (X' (f a)).plug (nodeSign σ' (f a))
      (.node (inflateTreeAt σ' X' Y' l (addrExt (f a) [0]))
        (inflateTreeAt σ' X' Y' m (addrExt (f a) [1]))
        (inflateTreeAt σ' X' Y' r (addrExt (f a) [2]))) =
      (X a).plug (nodeSign σ a)
      (.node (inflateTreeAt σ X Y l (addrExt a [0]))
        (inflateTreeAt σ X Y m (addrExt a [1]))
        (inflateTreeAt σ X Y r (addrExt a [2])))
    rw [hcode, hsign]
    apply congrArg ((X a).plug (nodeSign σ a))
    congr 1
    · exact (congrArg (inflateTreeAt σ' X' Y' l) (hf [0]).symm).trans hl
    · exact (congrArg (inflateTreeAt σ' X' Y' m) (hf [1]).symm).trans hm
    · exact (congrArg (inflateTreeAt σ' X' Y' r) (hf [2]).symm).trans hr

/-- The inserted path in the inflated tree along a literal original source path. -/
@[expose] noncomputable def inflationFrame {w : ℕ} (X : Address w → RegChain)
    (a : Address w) : Path → Path
  | [] => []
  | i :: q => (X a).lonePath ++ [i] ++ inflationFrame X (addrExt a [i]) q

/-- Source path concatenation composes the actual inserted inflation frames. -/
theorem inflationFrame_append {w : ℕ} (X : Address w → RegChain) (a : Address w) (p q : Path) :
    inflationFrame X a (p ++ q) = inflationFrame X a p ++ inflationFrame X (addrExt a p) q := by
  induction p generalizing a with
  | nil => simp only [List.nil_append, inflationFrame, addrExt_nil]
  | cons i p ih =>
    change (X a).lonePath ++ [i] ++ inflationFrame X (addrExt a [i]) (p ++ q) =
      ((X a).lonePath ++ [i] ++ inflationFrame X (addrExt a [i]) p) ++
        inflationFrame X (addrExt a (i :: p)) q
    rw [ih, addrExt_cons a i p]
    simp only [List.append_assoc]

end WaveTurbulence.LFTwist
