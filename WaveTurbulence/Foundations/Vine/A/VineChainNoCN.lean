/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitCoverOne
public import WaveTurbulence.Foundations.Molecule.ChainParentTransfer
/-! A CL block chain cannot contain a CN ingredient: the right end parent
is inherited by the last ingredient, contrary to the CN spine clause. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- An internal parent at the last end of a block spine excludes every CN member. -/
theorem spine_noCN_of_parent {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hs : Spine G.molecule L S a b) (hB : G.molecule.IsBlock S a b)
    (hp : InternalParent G S b) : ∀ t ∈ L, ¬ CNMem G t := by
  intro t ht hcn
  obtain ⟨L0, A, p, hL⟩ := hs.last
  have hm : (A, p, b) ∈ L := by rw [hL]; exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨hv, hsub⟩ := hs.mem_vine hm
  have hAb := hv.choose_spec.1
  have he := internalParent_eq_of_degree_eq G hsub hAb.2.2.1
    ((block_joint_degrees G.molecule hAb).2.trans (block_joint_degrees G.molecule hB).2.symm)
  exact (hs.cn_clause (fun T p q h => (hs.mem_vine h).1.choose_spec.1)).2 L0 A p hL
    ⟨t, ht, hcn⟩ (he.mpr hp)

/-- The CL condition excludes CN ingredients in either orientation. -/
theorem spine_noCN {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hs : Spine G.molecule L S a b) (hB : G.molecule.IsBlock S a b)
    (hp : CLParentPattern G S a b ∨ CLParentPattern G S b a) :
    ∀ t ∈ L, ¬ CNMem G t := by
  rcases hp with hp | hp
  · exact spine_noCN_of_parent hs hB hp.2
  · intro ⟨T, x, y⟩ ht hcn
    have hr := spine_noCN_of_parent hs.reverse (block_swap_joints G.molecule hB) hp.2
    exact hr (T, y, x) ((mem_revSwap).mpr ht) ⟨hcn.2, hcn.1⟩

end WaveTurbulence.VineA
