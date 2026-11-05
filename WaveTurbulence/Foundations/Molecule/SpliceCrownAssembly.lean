/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeDegreeCompat
public import WaveTurbulence.Foundations.Molecule.TwistSpliceSlots

/-! # Algebra of the canonical signed three-subtree splice crown

TARGET block_clcn and twistexplain (c): reversing the lower sign and
exchanging the two free subtrees leave the assembled ordered crown equal.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Assemble the three retained subtree pieces using the exact CL sign selector. -/
@[expose] def assembleSpliceCrown (excluded : Fin 3) (sameSign : Bool) (upper middle other : TTree) : TTree :=
  .node
    ((![upper,middle,other] : Fin 3 → TTree) (Mole.clBoundarySelector excluded sameSign 0))
    ((![upper,middle,other] : Fin 3 → TTree) (Mole.clBoundarySelector excluded sameSign 1))
    ((![upper,middle,other] : Fin 3 → TTree) (Mole.clBoundarySelector excluded sameSign 2))

/-- Componentwise congruence of the ordered splice assembly. -/
theorem assembleSpliceCrown_congr (e : Fin 3) {s t : Bool} {u u' m m' o o' : TTree}
    (hs : s = t) (hu : u = u') (hm : m = m') (ho : o = o') :
    assembleSpliceCrown e s u m o = assembleSpliceCrown e t u' m' o' := by
  cases hs
  cases hu
  cases hm
  cases ho
  rfl

/-- Sign reversal and free-subtree exchange exactly compensate in the ordered splice crown. -/
theorem assembleSpliceCrown_swap (e : Fin 3) (same : Bool) (u m o : TTree) :
    assembleSpliceCrown e (!same) u o m = assembleSpliceCrown e same u m o := by
  fin_cases e <;> cases same <;> simp [assembleSpliceCrown,Mole.clBoundarySelector]

private theorem map_three {α β : Type*} (f : α → β) (a b c : α) (i : Fin 3) :
    f ((![a,b,c] : Fin 3 → α) i) = (![f a,f b,f c] : Fin 3 → β) i := by
  fin_cases i <;> rfl

/-- The literal accepted CL splice crown has exactly this assembly formula. -/
theorem clSpliceCrown_assembly {w : ℕ} (G : Garden w) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (D : Mole.CLSpliceSlots G S a b) :
    Mole.spliceCrown G (Mole.clSpliceBoundary hB hCL D).node =
      assembleSpliceCrown D.excluded (Mole.clSameSign a b)
        (Mole.spliceNodeSubtree G (a.child D.excluded))
        (Mole.spliceNodeSubtree G (b.child 1))
        (Mole.spliceNodeSubtree G (b.child (Mole.otherOuterChild D.kept))) := by
  change TTree.node
    (Mole.spliceNodeSubtree G ((![a.child D.excluded,b.child 1,b.child (Mole.otherOuterChild D.kept)] : Fin 3 → GNode G.tree)
      (Mole.clBoundarySelector D.excluded (Mole.clSameSign a b) 0)))
    (Mole.spliceNodeSubtree G ((![a.child D.excluded,b.child 1,b.child (Mole.otherOuterChild D.kept)] : Fin 3 → GNode G.tree)
      (Mole.clBoundarySelector D.excluded (Mole.clSameSign a b) 1)))
    (Mole.spliceNodeSubtree G ((![a.child D.excluded,b.child 1,b.child (Mole.otherOuterChild D.kept)] : Fin 3 → GNode G.tree)
      (Mole.clBoundarySelector D.excluded (Mole.clSameSign a b) 2))) = _
  unfold assembleSpliceCrown
  congr 1
  all_goals exact map_three _ _ _ _ _

end WaveTurbulence.Twist
