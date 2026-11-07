/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fold4
import Mathlib.Tactic

/-!
# VINE-B Part I (5): the realization of an unspliced unit, seen through the node map
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ}

theorem isInternalLeaf_iff (G : Garden w) (S : Finset (GBranch G.tree)) (ℓ : GLeaf G.tree) :
    IsInternalLeaf G S ℓ ↔ ∃ (hm : G.mark ℓ = none) (hn : ℓ.1.2 ≠ []) (hp : (G.pair ℓ).1.2 ≠ []),
      GNode.parent ℓ.toNode hn ∈ S ∧ GNode.parent (G.pair ℓ).toNode hp ∈ S := Iff.rfl

variable {G0 : Garden w} {P : CLBlock G0 → Prop} {st : SpState G0} (T : FoldInv P st)

theorem FoldInv.leaf_root_iff (ℓ : GLeaf st.G.tree) : (T.leaf ℓ).1.2 = [] ↔ ℓ.1.2 = [] := by
  have h := congrArg (fun x : GNode G0.tree => x.1.2) (T.leaf_node ℓ)
  change (T.leaf ℓ).1.2 = (T.node ℓ.toNode).1.2 at h
  rw [h]
  exact T.root ℓ.toNode

theorem FoldInv.bridge (u : CLBlock G0) (hU : ∀ v ∈ u.atoms, st.cls v = none) (z : GNode st.G.tree) :
    T.node z ∈ clRealizationNodes G0 u.atoms ↔ z ∈ clRealizationNodes st.G (st.M.pb u.atoms) := by
  rcases (TTree.mem_nodes_iff _ _).mp z.2 with h | h
  · -- a leaf
    have hz : z = GLeaf.toNode (⟨z.1, h⟩ : GLeaf st.G.tree) := rfl
    set ℓ : GLeaf st.G.tree := ⟨z.1, h⟩ with hℓ
    rw [hz, ← T.leaf_node ℓ, leaf_mem_clRealizationNodes, leaf_mem_clRealizationNodes,
      isInternalLeaf_iff, isInternalLeaf_iff]
    constructor
    · rintro ⟨hm, hn, hp, h1, h2⟩
      have hm' : st.G.mark ℓ = none := by rw [T.mark]; exact hm
      have hn' : ℓ.1.2 ≠ [] := fun he => hn ((T.leaf_root_iff ℓ).mpr he)
      have hp' : (st.G.pair ℓ).1.2 ≠ [] := by
        intro he
        apply hp
        rw [← T.pair]
        exact (T.leaf_root_iff _).mpr he
      refine ⟨hm', hn', hp', ?_, ?_⟩
      · rw [SpMap.mem_pb, T.parentL ℓ hn' hn, SpMap.repC_mem_iff st.hcls hU]
        exact h1
      · rw [SpMap.mem_pb, T.parentL (st.G.pair ℓ) hp' (by rw [T.pair]; exact hp), SpMap.repC_mem_iff st.hcls hU]
        have e : G0.pair (T.leaf ℓ) = T.leaf (st.G.pair ℓ) := (T.pair ℓ).symm
        simpa [e] using h2
    · rintro ⟨hm, hn, hp, h1, h2⟩
      have hm' : G0.mark (T.leaf ℓ) = none := by rw [← T.mark]; exact hm
      have hn' : (T.leaf ℓ).1.2 ≠ [] := fun he => hn ((T.leaf_root_iff ℓ).mp he)
      have hp' : (G0.pair (T.leaf ℓ)).1.2 ≠ [] := by
        rw [← T.pair]
        exact fun he => hp ((T.leaf_root_iff _).mp he)
      refine ⟨hm', hn', hp', ?_, ?_⟩
      · rw [SpMap.mem_pb, T.parentL ℓ hn hn', SpMap.repC_mem_iff st.hcls hU] at h1
        exact h1
      · rw [SpMap.mem_pb, T.parentL (st.G.pair ℓ) hp (by rw [T.pair]; exact hp'),
          SpMap.repC_mem_iff st.hcls hU] at h2
        have e : G0.pair (T.leaf ℓ) = T.leaf (st.G.pair ℓ) := (T.pair ℓ).symm
        simpa [e] using h2
  · -- a branch
    have hz : z = GBranch.toNode (⟨z.1, h⟩ : GBranch st.G.tree) := rfl
    set c : GBranch st.G.tree := ⟨z.1, h⟩ with hc
    rw [hz, ← T.br_node c, branch_mem_clRealizationNodes, branch_mem_clRealizationNodes, SpMap.mem_pb]

end WaveTurbulence.VineB
