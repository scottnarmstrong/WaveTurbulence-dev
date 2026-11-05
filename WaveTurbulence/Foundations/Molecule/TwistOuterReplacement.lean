/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSpliceSlots

/-! # Replacing the upper subtree absorbs the entire unit-twist surgery

TARGET twistexplain (c): the lower root and u0 lie below the same upper
joint, so the forest outside the splice site is literally unchanged.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- An outer replacement absorbs a preceding replacement strictly inside or at its root. -/
theorem replace_inner_outer : ∀ (t : TTree) (p q : Path) (s r : TTree),
    Comb.replaceAt (Comb.replaceAt t (p ++ q) s) p r = Comb.replaceAt t p r
  | t, [], q, s, r => by simp [Comb.replaceAt]
  | .leaf, i::p, q, s, r => rfl
  | .node l m r₀, i::p, q, s, r => by
    fin_cases i <;> simp [Comb.replaceAt,replace_inner_outer]

/-- Literal rooted-subtree replacement in an ordered forest. -/
@[expose] def forestReplace {w : ℕ} (F : Fin w → TTree) (a : Fin w × Path) (t : TTree) : Fin w → TTree :=
  Function.update F a.1 (Comb.replaceAt (F a.1) a.2 t)

/-- An outer forest replacement absorbs any replacement below its actual address. -/
theorem forestReplace_inner_outer {w : ℕ} (F : Fin w → TTree) (a b : Fin w × Path)
    (hidx : a.1 = b.1) (hpre : a.2 <+: b.2) (s r : TTree) :
    forestReplace (forestReplace F b s) a r = forestReplace F a r := by
  obtain ⟨i,p⟩ := a
  obtain ⟨j,q⟩ := b
  dsimp only at hidx hpre
  subst j
  obtain ⟨q,rfl⟩ := hpre
  funext k
  by_cases hk : k = i
  · subst k
    simp only [forestReplace,Function.update_self]
    exact replace_inner_outer _ _ _ _ _
  · simp only [forestReplace,Function.update_of_ne hk]

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The old paired leaf u0 is below the actual upper joint of the specified CL block. -/
theorem placement_pair_below_upper {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) : a.toNode.IsDesc (G.pair P.retained).toNode := by
  have hm := placement_paired_parent_mem G P hP
  have hd := Mole.block_one_root_descendants G hB hCL.1 hCL.2 hm
  have hp : (GNode.parent (G.pair P.retained).toNode P.paired_nonroot).toNode.IsDesc
      (G.pair P.retained).toNode := ⟨rfl,List.dropLast_prefix _⟩
  exact ⟨hd.1.trans hp.1,hd.2.trans hp.2⟩

/-- Replacing the full upper subtree after the twist gives exactly the same outside forest. -/
theorem coreTwistForest_outer_replace {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) (t : TTree) :
    forestReplace (coreTwistForest G P) a.1 t = forestReplace G.tree a.1 t := by
  have hb := (Mole.cl_parent_strict_descendant G hB hCL).1
  have hp := placement_pair_below_upper G P hB hCL hP
  change forestReplace
    (forestReplace (forestReplace G.tree P.lower.1 .leaf) (G.pair P.retained).1
      (switchFree P.keep (lowerCrown G P.lower))) a.1 t = _
  exact (forestReplace_inner_outer (forestReplace G.tree P.lower.1 .leaf) a.1
    (G.pair P.retained).1 hp.1 hp.2 (switchFree P.keep (lowerCrown G P.lower)) t).trans
      (forestReplace_inner_outer G.tree a.1 P.lower.1 hb.1 hb.2 .leaf t)

end WaveTurbulence.Twist
