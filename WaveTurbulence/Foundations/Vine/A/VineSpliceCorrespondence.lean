/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceBranchTrace
/-! Actual splice sequences with the same merge classes have molecular and
full-leaf correspondences preserving signs, roots and all parent relations. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- The actual old-name molecular correspondence for two splice sequences. -/
noncomputable def spliceFoldMolIso (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) :
    MolIso (spliceFold G l).G.molecule (spliceFold G m).G.molecule :=
  (spliceMolIso_exists_of_cls_eq (spliceFold G l).M (spliceFold G m).M hc).choose

/-- Both molecular old-name diagrams commute. -/
theorem spliceFoldMolIso_names (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) :
    (∀ c, (spliceFold G m).M.ob ((spliceFoldMolIso l m hc).e c) = (spliceFold G l).M.ob c) ∧
    (∀ x, (spliceFold G m).M.od ((spliceFoldMolIso l m hc).d x) = (spliceFold G l).M.od x) :=
  (spliceMolIso_exists_of_cls_eq (spliceFold G l).M (spliceFold G m).M hc).choose_spec

/-- Branch signs agree through the actual old-name molecular map. -/
theorem spliceFoldMolIso_branch_sign (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (c : GBranch (spliceFold G l).G.tree) :
    (spliceFold G m).G.sign ((spliceFoldMolIso l m hc).e c).toNode = (spliceFold G l).G.sign c.toNode := by
  rw [(spliceFoldBranchTrace m).sign, (spliceFoldBranchTrace l).sign, (spliceFoldMolIso_names l m hc).1]

/-- The actual branch map detects precisely the same branching roots. -/
theorem spliceFoldMolIso_branch_root (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (c : GBranch (spliceFold G l).G.tree) :
    ((spliceFoldMolIso l m hc).e c).1.2 = [] ↔ c.1.2 = [] := by
  rw [← (spliceFold G m).M.ob_root, (spliceFoldMolIso_names l m hc).1, (spliceFold G l).M.ob_root]

/-- Actual branching-root addresses and root order are fixed. -/
theorem spliceFoldMolIso_root_address (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (c : GBranch (spliceFold G l).G.tree)
    (hroot : c.1.2 = []) : ((spliceFoldMolIso l m hc).e c).1 = c.1 := by
  have hm := (spliceFoldMolIso_branch_root l m hc c).mpr hroot
  exact ((spliceFoldBranchTrace m).root_address _ hm).symm.trans
    ((congrArg Subtype.val ((spliceFoldMolIso_names l m hc).1 c)).trans
      ((spliceFoldBranchTrace l).root_address c hroot))

/-- All actual branching parent relations agree. -/
theorem spliceFoldMolIso_parent (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (c : GBranch (spliceFold G l).G.tree)
    (hn : c.1.2 ≠ []) :
    let F := spliceFoldMolIso l m hc
    let hnew : (F.e c).1.2 ≠ [] := fun h => hn ((spliceFoldMolIso_branch_root l m hc c).mp h)
    F.e (GNode.parent c.toNode hn) = GNode.parent (F.e c).toNode hnew := by
  dsimp only
  let F := spliceFoldMolIso l m hc
  have hnew : (F.e c).1.2 ≠ [] := fun h => hn ((spliceFoldMolIso_branch_root l m hc c).mp h)
  have ho : ((spliceFold G l).M.ob c).1.2 ≠ [] := fun h => hn (((spliceFold G l).M.ob_root c).mp h)
  have hon : ((spliceFold G m).M.ob (F.e c)).1.2 ≠ [] :=
    fun h => hnew (((spliceFold G m).M.ob_root (F.e c)).mp h)
  have hp : GNode.parent ((spliceFold G m).M.ob (F.e c)).toNode hon =
      GNode.parent ((spliceFold G l).M.ob c).toNode ho := by
    apply Subtype.ext
    exact congrArg (fun b : GBranch G.tree => (b.1.1, b.1.2.dropLast)) ((spliceFoldMolIso_names l m hc).1 c)
  apply (spliceFold G m).M.ob_inj
  rw [(spliceFoldMolIso_names l m hc).1, (spliceFold G l).M.ob_parent c hn ho,
    (spliceFold G m).M.ob_parent (F.e c) hnew hon, hp]
  exact congrArg (fun cs => repC cs (GNode.parent ((spliceFold G l).M.ob c).toNode ho)) hc

/-- Every actual branching tree index is fixed by the root-preserving parent correspondence. -/
theorem spliceFoldMolIso_branch_index (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (c : GBranch (spliceFold G l).G.tree) :
    ((spliceFoldMolIso l m hc).e c).1.1 = c.1.1 := by
  by_cases hroot : c.1.2 = []
  · exact congrArg Prod.fst (spliceFoldMolIso_root_address l m hc c hroot)
  · have hp := spliceFoldMolIso_parent l m hc c hroot
    have hi := spliceFoldMolIso_branch_index l m hc (GNode.parent c.toNode hroot)
    have he := congrArg (fun b : GBranch (spliceFold G m).G.tree => b.1.1) hp
    exact he.symm.trans hi
termination_by c.1.2.length
decreasing_by
  change c.1.2.dropLast.length < c.1.2.length
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hroot
  omega

/-- Every inherited branch layer is fixed by the actual old-name correspondence. -/
theorem spliceFoldMolIso_layer (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (layer : GBranch G.tree → ℕ)
    (c : GBranch (spliceFold G l).G.tree) :
    layer ((spliceFold G m).M.ob ((spliceFoldMolIso l m hc).e c)) = layer ((spliceFold G l).M.ob c) :=
  congrArg layer ((spliceFoldMolIso_names l m hc).1 c)

/-- The full actual leaf correspondence detects the same roots. -/
theorem spliceFoldLeafEquiv_root (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree) :
    (spliceFoldLeafEquiv l m hc q).1.2 = [] ↔ q.1.2 = [] := by
  rw [← (spliceFoldLeafTrace m).root, spliceFoldLeafEquiv_comm, (spliceFoldLeafTrace l).root]

/-- Trivial-root leaf addresses and root order are fixed. -/
theorem spliceFoldLeafEquiv_root_address (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree)
    (hroot : q.1.2 = []) : (spliceFoldLeafEquiv l m hc q).1 = q.1 := by
  have hm := (spliceFoldLeafEquiv_root l m hc q).mpr hroot
  exact ((spliceFoldLeafTrace m).root_address _ hm).symm.trans
    ((congrArg Subtype.val (spliceFoldLeafEquiv_comm l m hc q)).trans
      ((spliceFoldLeafTrace l).root_address q hroot))

/-- Every retained leaf's parent agrees, including leaves absent from the molecule. -/
theorem spliceFold_leaf_parent (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree)
    (hn : q.1.2 ≠ []) :
    let F := spliceFoldMolIso l m hc
    let e := spliceFoldLeafEquiv l m hc
    let hnew : (e q).1.2 ≠ [] := fun h => hn ((spliceFoldLeafEquiv_root l m hc q).mp h)
    F.e (GNode.parent q.toNode hn) = GNode.parent (e q).toNode hnew := by
  dsimp only
  let F := spliceFoldMolIso l m hc
  let e := spliceFoldLeafEquiv l m hc
  have hnew : (e q).1.2 ≠ [] := fun h => hn ((spliceFoldLeafEquiv_root l m hc q).mp h)
  have ho : ((spliceFoldLeafTrace l).leaf q).1.2 ≠ [] := fun h => hn (((spliceFoldLeafTrace l).root q).mp h)
  have hon : ((spliceFoldLeafTrace m).leaf (e q)).1.2 ≠ [] :=
    fun h => hnew (((spliceFoldLeafTrace m).root (e q)).mp h)
  have hp : GNode.parent ((spliceFoldLeafTrace m).leaf (e q)).toNode hon =
      GNode.parent ((spliceFoldLeafTrace l).leaf q).toNode ho := by
    apply Subtype.ext
    exact congrArg (fun b : GLeaf G.tree => (b.1.1, b.1.2.dropLast)) (spliceFoldLeafEquiv_comm l m hc q)
  apply (spliceFold G m).M.ob_inj
  rw [(spliceFoldMolIso_names l m hc).1, (spliceFoldLeafTrace l).parent q hn ho,
    (spliceFoldLeafTrace m).parent (e q) hnew hon, hp]
  exact congrArg (fun cs => repC cs (GNode.parent ((spliceFoldLeafTrace l).leaf q).toNode ho)) hc

/-- Every actual leaf tree index is fixed as well. -/
theorem spliceFoldLeafEquiv_index (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree) :
    (spliceFoldLeafEquiv l m hc q).1.1 = q.1.1 := by
  by_cases hroot : q.1.2 = []
  · exact congrArg Prod.fst (spliceFoldLeafEquiv_root_address l m hc q hroot)
  · have hp := spliceFold_leaf_parent l m hc q hroot
    have hi := spliceFoldMolIso_branch_index l m hc (GNode.parent q.toNode hroot)
    have he := congrArg (fun b : GBranch (spliceFold G m).G.tree => b.1.1) hp
    exact he.symm.trans hi

end WaveTurbulence.VineA
