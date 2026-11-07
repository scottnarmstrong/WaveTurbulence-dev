/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Compat
public import WaveTurbulence.Foundations.LayerCnt.GardenParents
public import WaveTurbulence.Foundations.Molecule.BlockGeometricDichotomy

/-! # Upper half of the layer range of a (CL) vine (TARGET layervine, L1523–L1525)

For a (CL) block with upper joint `a`, every atom is a descendant of `a`, so its layer is at most `𝔏_a = q`.
(The lower half `𝔏_x ≥ q' = 𝔏_{v_2}` is the group-chain and Vine-(V) argument and is NOT proved here.)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

/-- Branch pre-layerings are non-increasing along descendants. -/
theorem prelayer_le_of_isDesc (G : Garden w) {f : GBranch G.tree → ℕ} (hf : LFTwist.IsBranchPrelayering G f)
    {a x : GBranch G.tree} (h : a.toNode.IsDesc x.toNode) : f x ≤ f a := by
  obtain ⟨n, hn⟩ : ∃ n, x.1.2.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    obtain ⟨hj, q, hq⟩ := h
    have hj' : a.1.1 = x.1.1 := hj
    have hq' : a.1.2 ++ q = x.1.2 := hq
    by_cases hq0 : q = []
    · subst hq0
      have : x = a := Subtype.ext (Prod.ext hj'.symm (by simpa using hq'.symm))
      rw [this]
    · have hx : x.1.2 ≠ [] := by
        rw [← hq']; simp [hq0]
      have hstep := garden_parent_step_le G hf x hx
      have hdl : (GNode.parent x.toNode hx).1.2 = a.1.2 ++ q.dropLast := by
        show x.1.2.dropLast = _
        rw [← hq', List.dropLast_append_of_ne_nil hq0]
      have hlen : (GNode.parent x.toNode hx).1.2.length < n := by
        rw [← hn]
        show x.1.2.dropLast.length < x.1.2.length
        rw [List.length_dropLast]
        have := List.length_pos_of_ne_nil hx; omega
      refine hstep.trans (ih _ hlen ?_ rfl)
      refine ⟨hj', q.dropLast, ?_⟩
      exact hdl.symm

/-- **Upper half of the layer range**: every atom of a (CL) block with upper joint `a` has layer at most
`𝔏_a = q` (the block realizes inside the descendants of `a`, `CLGeometricData.realization`). -/
theorem layer_le_upper (G : Garden w) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) {f : GBranch G.tree → ℕ}
    (hf : LFTwist.IsBranchPrelayering G f) : ∀ x ∈ S, f x ≤ f a := by
  intro x hx
  obtain ⟨D⟩ := Mole.cl_geometric_data G hB hCL
  have hr := (D.realization x.toNode).mp ((Mole.branch_incidence_realization_iff G S x).mpr hx)
  exact prelayer_le_of_isDesc G hf hr.1

end WaveTurbulence.LayerCnt
