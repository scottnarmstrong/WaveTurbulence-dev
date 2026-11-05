/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.Ident

/-!
# TARGET's flower kernels `𝒥̃_F(t, s, k, k')` and kernel operators (packet X1; T.flowerkernels, T.operatorx)

* `FTree.toTree`, `FTree.flowerLeaf`, `FTree.flowerParent`: the flower tree as a ternary tree with a marked leaf
  (T Def `defflower`).
* `flowerKernel`, T (jtflower) with the F25 prefactor `(δ/(2L^{d−γ}))^n`:
  `𝒥̃_F(t,s,k,k') = (δ/(2L^{d−γ}))^n ζ(𝒯) ∑_{(k,k')-dec.} ε ∫ 1_{𝒟} ∏ e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫} δ(t_{𝔣^pr} − s)
  ∏_{ℓ≠𝔣} a_{k_ℓ}(p)^{ζ_ℓ}`. Here `δ(t_{𝔣^pr} − s)` means: integrate over the other branching times, with
  `t_{𝔣^pr} := s`.
* `kernelOp`, T (operatorx) with the exponent `ζ` on `b` (DH23 (parametrix)):
  `(𝒦b)_k(t) = ∑_ζ ∑_{k'} ∫_p^t 𝒦^ζ_{kk'}(t,s) b_{k'}(s)^ζ ds`. TARGET's (operatorx) prints `b_{k'}(s)` without
  `ζ`. Read literally, the operator would be ℂ-linear and the `ζ = −` kernels would act on `b` instead of `b̄`.
* The kernels of `𝒳`, `𝒴`, `𝒲` (`Xker`, `Yker`, `Wker`) are sums of `𝒥̃_F` over the classes of `Flower-Trees`.
  The flower sign `ζ` picks the trees with `F.sign = ζ`.

The bridge to `fOp` (`𝒥_F[b] = 𝒦_{𝒥̃_F} b`) is O-FK `fOp_kernel_rep` in `Flower-Obligations.lean`, proved in
`OFK-*.lean`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

namespace FTree

/-- The underlying ternary tree: the stem child `F` in position `i`. -/
def toTree : FTree → TTree
  | flower => .leaf
  | node i F T₁ T₂ =>
    if i = 0 then .node F.toTree T₁ T₂ else if i = 1 then .node T₁ F.toTree T₂ else .node T₁ T₂ F.toTree

/-- The path of the flower. -/
def flowerPath : FTree → TTree.Path
  | flower => []
  | node i F _ _ => i :: F.flowerPath

theorem flowerPath_mem_leaves : ∀ F : FTree, F.flowerPath ∈ F.toTree.leaves
  | flower => by simp [flowerPath, toTree, TTree.leaves]
  | node i F T₁ T₂ => by
    have ih := flowerPath_mem_leaves F
    fin_cases i <;> simp [flowerPath, toTree, TTree.leaves, TTree.cons_mem_pre, ih]

/-- The flower, as a leaf of `F.toTree`. -/
def flowerLeaf (F : FTree) : GLeaf (single F.toTree) := ⟨(0, F.flowerPath), F.flowerPath_mem_leaves⟩

theorem flowerPath_ne_nil {F : FTree} (hF : F ≠ flower) : F.flowerPath ≠ [] := by
  cases F with
  | flower => exact absurd rfl hF
  | node => simp [flowerPath]

/-- The parent `𝔣^pr` of the flower of a nontrivial flower tree. -/
def flowerParent (F : FTree) (hF : F ≠ flower) : GBranch (single F.toTree) :=
  ⟨(0, F.flowerPath.dropLast), TTree.branching_of_append_mem F.toTree
    (i := F.flowerPath.getLast (flowerPath_ne_nil hF)) (by
      rw [List.dropLast_append_getLast (flowerPath_ne_nil hF)]
      exact TTree.leaves_subset_nodes _ F.flowerPath_mem_leaves)⟩

end FTree

/-- `(k, k')`-decorations of a flower tree: root `k`, flower `k'` (T Def `defflower`). -/
def FlowerDecoration (F : FTree) (d : ℕ) (k k' : Fin d → ℤ) : Type :=
  {κ : TreeDecoration F.toTree d k // κ.1 F.flowerLeaf.toNode = k'}

variable (L γ δ : ℝ) {d : ℕ}

open Classical in
/-- **TARGET's flower kernel `𝒥̃_F(t, s, k, k')`** (T (jtflower) with the prefactor `L^{d−γ}`, F25). It is `0` for
the trivial flower tree, whose term in `𝒳` is the identity (F39). -/
noncomputable def flowerKernel (p : ℕ) (F : FTree) (aP : (Fin d → ℤ) → ℂ) (t s : ℝ)
    (k k' : Fin d → ℤ) : ℂ :=
  if hF : F = flower then 0 else
  treePrefactor L γ δ d F.toTree *
    ∑' κ : FlowerDecoration F d k k',
      epsProd F.toTree κ.1.1 *
        (∫ τ : {c : GBranch (single F.toTree) // c ≠ F.flowerParent hF} → ℝ,
          (treeTimeDomain F.toTree p t).indicator (phaseFn L γ δ F.toTree κ.1.1)
            (fun c => if h : c = F.flowerParent hF then s else τ ⟨c, h⟩)) *
        ∏ ℓ ∈ Finset.univ.erase F.flowerLeaf,
          zpowSign (treeSign F.toTree ℓ.toNode) (aP (κ.1.1 ℓ.toNode))

/-- **The kernel operator** (T (operatorx), with `b^ζ` as in DH23 (parametrix)). -/
noncomputable def kernelOp (p : ℕ) (K : ℤˣ → ℝ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℂ)
    (b : ArrI p d) : ArrI p d :=
  fun t k => ∑ ζ : ℤˣ, ∑' k', ∫ s in (p : ℝ)..t,
    K ζ t s k k' * zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')

/-- **The kernel of `𝒳 − 1`** (T (operatorxker)): flower trees of order `1, …, N` with root `+` and flower `ζ`. -/
noncomputable def Xker (p N : ℕ) (aP : (Fin d → ℤ) → ℂ) (ζ : ℤˣ) (t s : ℝ) (k k' : Fin d → ℤ) : ℂ :=
  ∑ F ∈ (Xset N).filter (fun F => F.sign = ζ), flowerKernel L γ δ p F aP t s k k'

/-- **The kernel of `−𝒴`**: the trees (Y-1), (Y-2). -/
noncomputable def Yker (p N : ℕ) (aP : (Fin d → ℤ) → ℂ) (ζ : ℤˣ) (t s : ℝ) (k k' : Fin d → ℤ) : ℂ :=
  ∑ x ∈ (Yind N).filter (fun x => (rootOf x).sign = ζ), flowerKernel L γ δ p (rootOf x) aP t s k k'

/-- **The kernel of `−𝒲`**: the trees (W-1)–(W-3). -/
noncomputable def Wker (p N : ℕ) (aP : (Fin d → ℤ) → ℂ) (ζ : ℤˣ) (t s : ℝ) (k k' : Fin d → ℤ) : ℂ :=
  ∑ x ∈ (Wind N).filter (fun x => (bottomOf x).sign = ζ),
    flowerKernel L γ δ p (bottomOf x) aP t s k k'

end WaveTurbulence.SysAPI
