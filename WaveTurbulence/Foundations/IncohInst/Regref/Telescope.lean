/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.Obligations
public import WaveTurbulence.Foundations.RegStruct.AddressSigns

/-!
# The resonance factors telescope: `∑_𝔫 ζ_𝔫 Ω_𝔫 = ∑_ℓ ζ_ℓ |k_ℓ|² − ∑_j ζ_j |k_{𝔯_j}|²`

For any vector labels of the nodes of a garden, the signed resonance factors of the branching nodes telescope
(each non-root node is exactly one child of one branching node, and the children of a node of sign `ζ` have signs
`(ζ, −ζ, ζ)`, the signs of `Ω`'s terms). For a couple (paired leaves with equal labels and opposite signs, roots
`(+, −)` with the same vector `k`) the sum vanishes. This is TARGET L1173's "`K*_𝒬` is invariant under translating all
times by `r`": the phases `e^{πiζ_𝔫δL^{2γ}Ω_𝔫 t_𝔫}` pick up `e^{πiδL^{2γ}r∑ζ_𝔫Ω_𝔫} = 1`.

* `tree_telescope`: `∑_{p ∈ 𝒩(T)} (g(p0) + g(p1) + g(p2) − g(p)) = ∑_{p ∈ ℒ(T)} g(p) − g(∅)`.
* `sum_GBranch`, `sum_GLeaf`: sums over the global nodes as sums over trees and paths.
* `sum_sign_omega`: the telescoped form; `sum_sign_omega_couple`: `0` for couple decorations.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.Regref

open TTree

theorem mem_pre_cons {i j : Fin 3} {S : Finset Path} {q : Path} : j :: q ∈ pre i S ↔ i = j ∧ q ∈ S := by
  simp only [pre, Finset.mem_image, List.cons.injEq]
  constructor
  · rintro ⟨q', hq', rfl, rfl⟩; exact ⟨rfl, hq'⟩
  · rintro ⟨rfl, hq⟩; exact ⟨q, hq, rfl, rfl⟩

theorem sum_pre {M : Type*} [AddCommMonoid M] (i : Fin 3) (S : Finset Path) (f : Path → M) :
    ∑ p ∈ pre i S, f p = ∑ q ∈ S, f (i :: q) := by
  rw [pre, Finset.sum_image fun _ _ _ _ h => List.cons_injective h]

theorem disjoint_pre {i j : Fin 3} (h : i ≠ j) (S S' : Finset Path) : Disjoint (pre i S) (pre j S') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  simp only [pre, Finset.mem_image] at hp hp'
  obtain ⟨q, -, rfl⟩ := hp
  obtain ⟨q', -, h'⟩ := hp'
  exact h (List.cons.inj h').1.symm

theorem sum_pre3 {M : Type*} [AddCommMonoid M] (S₀ S₁ S₂ : Finset Path) (f : Path → M) :
    ∑ p ∈ pre 0 S₀ ∪ pre 1 S₁ ∪ pre 2 S₂, f p =
      ∑ q ∈ S₀, f (0 :: q) + ∑ q ∈ S₁, f (1 :: q) + ∑ q ∈ S₂, f (2 :: q) := by
  rw [Finset.sum_union, Finset.sum_union (disjoint_pre (by decide) _ _), sum_pre, sum_pre, sum_pre]
  exact Finset.disjoint_union_left.2 ⟨disjoint_pre (by decide) _ _, disjoint_pre (by decide) _ _⟩

theorem nil_not_mem_pre3 (S₀ S₁ S₂ : Finset Path) : ([] : Path) ∉ pre 0 S₀ ∪ pre 1 S₁ ∪ pre 2 S₂ := by
  simp [pre]

/-- **Telescoping on a tree.** -/
theorem tree_telescope {M : Type*} [AddCommGroup M] : (T : TTree) → (g : Path → M) →
    ∑ p ∈ T.branching, (g (p ++ [0]) + g (p ++ [1]) + g (p ++ [2]) - g p) = ∑ p ∈ T.leaves, g p - g []
  | .leaf, g => by simp [branching, leaves]
  | .node l m r, g => by
    rw [branching, Finset.sum_insert (nil_not_mem_pre3 _ _ _), sum_pre3, leaves, sum_pre3]
    have hl := tree_telescope l (fun q => g (0 :: q))
    have hm := tree_telescope m (fun q => g (1 :: q))
    have hr := tree_telescope r (fun q => g (2 :: q))
    beta_reduce at hl hm hr
    simp only [List.cons_append, List.nil_append]
    rw [hl, hm, hr]
    abel

variable {w : ℕ}

theorem sum_forestSet {M : Type*} [AddCommMonoid M] (tree : Fin w → TTree) (f : TTree → Finset Path)
    (F : Fin w × Path → M) : ∑ a ∈ forestSet tree f, F a = ∑ j, ∑ p ∈ f (tree j), F (j, p) := by
  rw [forestSet, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_image fun _ _ _ _ h => (Prod.mk.inj h).2]
  · intro j _ j' _ hjj'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_image] at ha ha'
    obtain ⟨p, -, rfl⟩ := ha
    obtain ⟨p', -, h⟩ := ha'
    exact hjj' (Prod.mk.inj h).1.symm

theorem sum_GBranch {M : Type*} [AddCommMonoid M] (tree : Fin w → TTree) (F : Fin w × Path → M) :
    ∑ b : GBranch tree, F b.1 = ∑ j, ∑ p ∈ (tree j).branching, F (j, p) := by
  rw [← sum_forestSet]
  exact (Finset.sum_subtype (forestSet tree branching) (p := fun a => a.2 ∈ (tree a.1).branching)
    (fun a => by
      simp only [forestSet, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
      constructor
      · rintro ⟨j, q, hq, rfl⟩; exact hq
      · intro h; exact ⟨a.1, a.2, h, rfl⟩) F).symm

theorem sum_GLeaf {M : Type*} [AddCommMonoid M] (tree : Fin w → TTree) (F : Fin w × Path → M) :
    ∑ ℓ : GLeaf tree, F ℓ.1 = ∑ j, ∑ p ∈ (tree j).leaves, F (j, p) := by
  rw [← sum_forestSet]
  exact (Finset.sum_subtype (forestSet tree leaves) (p := fun a => a.2 ∈ (tree a.1).leaves)
    (fun a => by
      simp only [forestSet, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
      constructor
      · rintro ⟨j, q, hq, rfl⟩; exact hq
      · intro h; exact ⟨a.1, a.2, h, rfl⟩) F).symm

/-- The sign of a child: `pathSign ζ (p ++ [i]) = slotSign (pathSign ζ p) i`. -/
theorem pathSign_snoc (ζ : ℤˣ) (p : Path) (i : Fin 3) :
    pathSign ζ (p ++ [i]) = slotSign (pathSign ζ p) i := by
  rw [Comb.pathSign_append, WaveTurbulence.Reg.pathSign_singleton]

/-- **The signed resonance factors telescope.** -/
theorem sum_sign_omega {d : ℕ} (G : Garden w) (k : GNode G.tree → Mom d) :
    ∑ b : GBranch G.tree, (((G.sign b.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G k b =
      ∑ ℓ : GLeaf G.tree, (((G.sign ℓ.toNode : ℤˣ) : ℤ) : ℝ) * ‖k ℓ.toNode‖ ^ 2 -
        ∑ j, (((G.sig j : ℤˣ) : ℤ) : ℝ) * ‖k (GNode.root G.tree j)‖ ^ 2 := by
  classical
  -- extend the labels to all addresses
  set kk : Fin w × Path → Mom d := fun a => if h : a.2 ∈ (G.tree a.1).nodes then k ⟨a, h⟩ else 0 with hkk
  set g : Fin w × Path → ℝ := fun a => (((pathSign (G.sig a.1) a.2 : ℤˣ) : ℤ) : ℝ) * ‖kk a‖ ^ 2 with hg
  have hnode : ∀ a : GNode G.tree, kk a.1 = k a := fun a => by
    show (if h : a.1.2 ∈ (G.tree a.1.1).nodes then k ⟨a.1, h⟩ else 0) = k ⟨a.1, a.2⟩
    simp only [a.2, ↓reduceDIte]
  have hb : ∀ b : GBranch G.tree, (((G.sign b.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G k b =
      g (b.1.1, b.1.2 ++ [0]) + g (b.1.1, b.1.2 ++ [1]) + g (b.1.1, b.1.2 ++ [2]) - g b.1 := by
    intro b
    have h0 := hnode (b.child 0)
    have h1 := hnode (b.child 1)
    have h2 := hnode (b.child 2)
    have hb' := hnode b.toNode
    simp only [GBranch.child, GBranch.toNode] at h0 h1 h2 hb'
    simp only [hg, h0, h1, h2, hb', pathSign_snoc, omegaNode, resFactor, Garden.sign, nodeSign,
      GBranch.child, GBranch.toNode]
    rcases Int.units_eq_one_or (pathSign (G.sig b.1.1) b.1.2) with h | h <;>
      simp [h, slotSign] <;> ring
  rw [Finset.sum_congr rfl fun b _ => hb b]
  rw [sum_GBranch G.tree (fun a => g (a.1, a.2 ++ [0]) + g (a.1, a.2 ++ [1]) + g (a.1, a.2 ++ [2]) - g a)]
  have hl : ∀ ℓ : GLeaf G.tree, (((G.sign ℓ.toNode : ℤˣ) : ℤ) : ℝ) * ‖k ℓ.toNode‖ ^ 2 = g ℓ.1 := by
    intro ℓ
    have := hnode ℓ.toNode
    simp only [GLeaf.toNode] at this
    simp only [hg, this, Garden.sign, nodeSign, GLeaf.toNode]
  rw [Finset.sum_congr rfl fun ℓ _ => hl ℓ, sum_GLeaf G.tree g, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hr := hnode (GNode.root G.tree j)
  simp only [GNode.root] at hr
  have ht := tree_telescope (G.tree j) (fun p => g (j, p))
  rw [ht]
  simp only [hg, hr, GNode.root, Comb.pathSign_nil]

/-- **For a couple decoration the signed resonance factors sum to zero**: paired leaves have opposite signs
and equal vectors, and the two roots have signs `(+, −)` and the same vector. -/
theorem sum_sign_omega_couple {d : ℕ} (G : Garden 2) (hG : IsCouple G) (k : GNode G.tree → Mom d)
    (hpair : ∀ ℓ : GLeaf G.tree, k ℓ.toNode = k (G.pair ℓ).toNode)
    (hroot : k (GNode.root G.tree 0) = k (GNode.root G.tree 1)) :
    ∑ b : GBranch G.tree, (((G.sign b.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G k b = 0 := by
  rw [sum_sign_omega]
  have hleaf : ∑ ℓ : GLeaf G.tree, (((G.sign ℓ.toNode : ℤˣ) : ℤ) : ℝ) * ‖k ℓ.toNode‖ ^ 2 = 0 := by
    refine Finset.sum_involution (fun ℓ _ => G.pair ℓ) (fun ℓ _ => ?_) (fun ℓ _ _ => ?_)
      (fun ℓ _ => Finset.mem_univ _) (fun ℓ _ => G.pair_pair ℓ)
    · have hne : G.pair ℓ ≠ ℓ := fun h => ((G.pair_eq_iff ℓ).1 h) (hG.1 ℓ)
      have hs : G.sign (G.pair ℓ).toNode = -G.sign ℓ.toNode := G.pair_sign ℓ hne
      rw [hs, ← hpair ℓ]
      push_cast
      ring
    · exact fun h => ((G.pair_eq_iff ℓ).1 h) (hG.1 ℓ)
  rw [hleaf, Fin.sum_univ_two, hG.2, hroot]
  simp

end WaveTurbulence.Regref
