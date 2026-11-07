/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceNodeTrace
/-! Survival of an original outer child external to all actual spliced units. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- The last address entry of a literal child is its slot. -/
theorem node_last_of_eq_child {F : Fin w → TTree} (n : GNode F) (hn : n.1.2 ≠ [])
    (b : GBranch F) (i : Fin 3) (he : n = b.child i) : n.1.2.getLast hn = i := by
  have hp : n.1.2 = b.1.2 ++ [i] := congrArg (fun n : GNode F => n.1.2) he
  simp only [hp, List.getLast_append_singleton]

/-- An incidence outside every selected unit is in the actual dart range. -/
theorem splice_dart_external (l : List (CLBlock G))
    (hd : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (v : GBranch G.tree) (i : Fin 3)
    (hext : ∀ u ∈ l, i.succ ∉ internalPositions G u.atoms v)
    (x : GardenDart G) (hx : G.molecule.atom x = v) (hi : dartPosition G x = i.succ) :
    ¬ ∃ a, (spliceFold G l).cls (G.molecule.atom x) = some a ∧
      (spliceFold G l).cls (G.molecule.atom (G.molecule.mate x)) = some a := by
  intro h
  obtain ⟨u, hu, hg⟩ := (spliceFold_deleted_iff l hd x).mp h
  exact hext u hu ((mem_internalPositions G).mpr ⟨x, hx, hg, hi⟩)

/-- An original child at an external port survives in the actual full node trace. -/
theorem spliceOldNode_child_range (l : List (CLBlock G))
    (hd : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (b : GBranch (spliceFold G l).G.tree) (i : Fin 3)
    (hext : ∀ u ∈ l, i.succ ∉ internalPositions G u.atoms ((spliceFold G l).M.ob b)) :
    ∃ n, spliceOldNode l n = ((spliceFold G l).M.ob b).child i := by
  let v := (spliceFold G l).M.ob b
  obtain ⟨p, hp⟩ := (nodePieceEquiv G.tree).surjective (v.child i)
  cases p with
  | inl c =>
    change c.toNode = v.child i at hp
    have ho : c.1.2 ≠ [] := fun h => child_nonroot G v i ((congrArg (fun n : GNode G.tree => n.1.2) hp).symm.trans h)
    have hpar : GNode.parent c.toNode ho = v :=
      (spliceNodeParent_congr ho (child_nonroot G v i) hp).trans (parent_child_branch_eq G v i _)
    have hlast : c.1.2.getLast ho = i := node_last_of_eq_child c.toNode ho v i hp
    let x : GardenDart G := .inl (⟨c, ho⟩, true)
    have hx : G.molecule.atom x = v := hpar
    have hi : dartPosition G x = i.succ := congrArg Fin.succ hlast
    obtain ⟨y, hy⟩ := ((spliceFold G l).M.od_range x).mpr (splice_dart_external l hd v i hext x hx hi)
    cases y with
    | inl pc =>
      rw [(spliceFoldDartTrace l).pc] at hy
      have he : (spliceFold G l).M.ob pc.1.1 = c :=
        congrArg (fun z => z.1.1) (Sum.inl.inj hy)
      exact ⟨pc.1.1.toNode, (spliceOldNode_branch l _).trans ((congrArg GBranch.toNode he).trans hp)⟩
    | inr lp =>
      rw [(spliceFoldDartTrace l).lp] at hy
      change Sum.inr _ = Sum.inl _ at hy
      cases hy
  | inr q =>
    change q.toNode = v.child i at hp
    have hn : ¬ MergedLeaf (spliceFold G l).cls q := by
      rintro ⟨lp, hlp, a, h1, h2⟩
      have hpl : lp.1.toNode = v.child i := (congrArg GLeaf.toNode hlp).trans hp
      have hpar : GNode.parent lp.1.toNode lp.2.2.1 = v :=
        (spliceNodeParent_congr _ (child_nonroot G v i) hpl).trans (parent_child_branch_eq G v i _)
      have hlast : lp.1.1.2.getLast lp.2.2.1 = i := node_last_of_eq_child lp.1.toNode _ v i hpl
      exact splice_dart_external l hd v i hext (.inr lp) hpar (congrArg Fin.succ hlast) ⟨a, h1, h2⟩
    obtain ⟨q', hq⟩ := (spliceFold_leaf_range l q).mpr hn
    exact ⟨q'.toNode, (spliceOldNode_leaf l _).trans ((congrArg GLeaf.toNode hq).trans hp)⟩

/-- The original child reconstructed from an external port is the actual child at that port. -/
theorem spliceOldNode_child_external (l : List (CLBlock G))
    (hd : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (b : GBranch (spliceFold G l).G.tree) (i : Fin 3)
    (hext : ∀ u ∈ l, i.succ ∉ internalPositions G u.atoms ((spliceFold G l).M.ob b)) :
    spliceOldNode l (b.child i) = ((spliceFold G l).M.ob b).child i := by
  obtain ⟨n, he⟩ := spliceOldNode_child_range l hd b i hext
  have ho : (spliceOldNode l n).1.2 ≠ [] := fun h => child_nonroot G _ i
    ((congrArg (fun n : GNode G.tree => n.1.2) he).symm.trans h)
  have hn : n.1.2 ≠ [] := fun h => ho ((spliceOldNode_root l n).mpr h)
  have hp : GNode.parent (spliceOldNode l n) ho = (spliceFold G l).M.ob b :=
    (spliceNodeParent_congr ho (child_nonroot G _ i) he).trans (parent_child_branch_eq G _ i _)
  have hf : repC (spliceFold G l).cls (GNode.parent (spliceOldNode l n) ho) =
      GNode.parent (spliceOldNode l n) ho := by rw [hp]; exact splice_old_branch_fixed _ b
  have hpar : GNode.parent n hn = b :=
    (spliceFold G l).M.ob_inj (((spliceOldNode_parent l n hn ho).trans hf).trans hp)
  have hlast : n.1.2.getLast hn = i := by
    have h := spliceOldNode_port l n hn ho hf
    exact h.trans (node_last_of_eq_child (spliceOldNode l n) ho _ i he)
  have hni : n = b.child i := (parent_child_eq_node n hn).symm.trans
    (by rw [hpar, hlast])
  exact hni ▸ he

end WaveTurbulence.VineA
