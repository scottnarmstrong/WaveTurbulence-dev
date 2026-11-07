/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm4
public import WaveTurbulence.Foundations.Stage1.Represents.RepOuter

/-!
# S2 REPRESENTS, VINE-D (1): the superposition data of the vine factors and the node centres

TARGET L1965-L1969: "by the weighted Fourier `L¹` bounds for `K*_Q`, `K*_T` …, and the same bounds for `K̃^{U_j}` with
each vector variable `k_{u1^j}` etc. restricted to a unit ball (Proposition `vineest`), we can decompose these functions
using time Fourier transform".

* `HingeFam J d`: for each unit `j` and each lattice centre tuple `c` of its four momenta, a countable family of modes
  (weights `w ≥ 0`, summable; three integer frequencies; amplitudes `a` of the four momenta with `|a| ≤ 1`, no
  derivative bound, TARGET L1966 "bounded by 1 (without derivatives)").
* `nodeCen fam hS ξ ν`: the lattice centre of the momentum of the node `ν` at the slot mode `ξ` (the node centre for a
  branch, the centre of the pair slot for a leaf).
* `ampS_support_node`: on the support of the slot amplitudes, every node momentum lies in the unit ball of its centre.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS

variable {w d : ℕ} {S : Garden w}

/-- The superposition data of the vine factors (VINE-D). -/
structure HingeFam (J : Type) (d : ℕ) where
  Λ : J → (Fin 4 → Fin d → ℤ) → Type
  cnt : ∀ j c, Countable (Λ j c)
  w : ∀ j c, Λ j c → ℝ
  m : ∀ j c, Λ j c → Fin 3 → ℤ
  a : ∀ j c, Λ j c → (Fin 4 → Mom d) → ℂ
  w_nn : ∀ j c l, 0 ≤ w j c l
  w_sum : ∀ j c, Summable (w j c)
  a_one : ∀ j c l E, ‖a j c l E‖ ≤ 1

/-- The lattice centre of the momentum of the node `ν` at the slot mode `ξ`. -/
noncomputable def nodeCen (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) (ν : GNode S.tree) : Fin d → ℤ := by
  classical
  exact if hb : ν.1.2 ∈ (S.tree ν.1.1).branching then ξ.2 ⟨ν.1, hb⟩
    else if hl : ν.1.2 ∈ (S.tree ν.1.1).leaves then
      fam.n (Sum.inl (pairOfLeaf S hS ⟨ν.1, hl⟩)) (ξ.1 (Sum.inl (pairOfLeaf S hS ⟨ν.1, hl⟩)))
    else 0

theorem nodeCen_branch (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) (b : GBranch S.tree) :
    nodeCen fam hS ξ b.toNode = ξ.2 b := by
  classical
  unfold nodeCen
  split_ifs with h1 h2
  · rfl
  · exact absurd b.2 h1
  · exact absurd b.2 h1

theorem nodeCen_eq_cenS_branch (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) (b : GBranch S.tree) :
    latPt d (nodeCen fam hS ξ b.toNode) = cenS fam ξ (Sum.inr b) := by
  rw [nodeCen_branch]; rfl

theorem not_branch_of_leaf (ℓ : GLeaf S.tree) : ℓ.1.2 ∉ (S.tree ℓ.1.1).branching := by
  intro h
  exact TTree.not_mem_branching_of_mem_leaves _ ℓ.2 h

theorem nodeCen_leaf (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) (ℓ : GLeaf S.tree) :
    nodeCen fam hS ξ ℓ.toNode = fam.n (Sum.inl (pairOfLeaf S hS ℓ)) (ξ.1 (Sum.inl (pairOfLeaf S hS ℓ))) := by
  classical
  unfold nodeCen
  split_ifs with h1 h2
  · exact absurd h1 (not_branch_of_leaf ℓ)
  · rfl
  · exact absurd ℓ.2 h2

/-- The hinge centres of the unit `j` at the slot mode `ξ`. -/
noncomputable def hingeCen (fam : SlotFam S d) (hS : S.IsPlain) {J : Type} (hmom : J → Fin 4 → GNode S.tree)
    (ξ : XiT fam) (j : J) : Fin 4 → Fin d → ℤ :=
  fun c => nodeCen fam hS ξ (hmom j c)

/-- The assembled index with hinge modes. -/
abbrev XiH (fam : SlotFam S d) (hS : S.IsPlain) {J : Type} (H : HingeFam J d) (hmom : J → Fin 4 → GNode S.tree) :
    Type := Σ ξ : XiT fam, ∀ j, H.Λ j (hingeCen fam hS hmom ξ j)

end WaveTurbulence.Represents
