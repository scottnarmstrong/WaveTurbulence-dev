/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.Bridge
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.GardenT

/-!
# The B̃ bridge for regular trees

DH21 (varat) (L1698–L1705): for a regular tree `𝒯` with lone leaf `ℓ_*`,
`𝒜*_𝒯(t, s, α[𝒩]) = ∫_𝒟 ∏ e^{ζ_𝔫πiα_𝔫t_𝔫}` over `𝒟 = {t_{(ℓ_*)^p} > s; 0 < t_{𝔫'} < t_𝔫 < t}`, and,
pairing the branching nodes with `ζ_{𝔫'}α_{𝔫'} = -ζ_𝔫α_𝔫`, `𝒜*_𝒯 = Ã_𝒯(t, s, α[𝒩^ch])`, which is
analyzed "similar to Section 5.2" (the chain integrals). Here, for a paired-tree carrier `G` decoded by
a B2 chain code `X` (`RegChain.DecodesTree`):

* `chainAtilde X ζ α t s`: the code-defined `Ã_𝒯`, the CPS chain integral of (newexp2) for the chain
  of `X` with root sign `ζ`, and the continuation `1{t_{2m} > s}` (the lone leaf hangs from the last
  chain node);
* `treeAstar_eq_Atilde`: `𝒜*_𝒯(t, s, α) = Ã_𝒯(t, s, α)` for `0 ≤ t`, `s < t` and `α` satisfying the
  link relation (DH21 takes `t > s`);
* `treeAstar_garden`: every regular tree has a unique well-formed code, and the identity holds; the
  hypothesis `hstructT` is the named obligation `existsUnique_regChain_decodesTree` (REG-STRUCT,
  statement verbatim);
* `phaseIntegral_kDomain_eq_Atilde`: Wave B's phase integral over `kDomain` (layer `0`).

The tree is placed in the couple addresses of ClassJR (`Fin 2 × Path`) at the root `rootT ζ` (tree
`0` for `ζ = +`, tree `1` for `ζ = -`), so that `nodeSgn` is the tree's node sign; `liftT α` reads the
garden phases there.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree

/-! ### The lone leaf of a decoded chain -/

theorem cons_mem_leaves_node3 (f : Fin 3 → TTree) (i : Fin 3) (q : TTree.Path) :
    i :: q ∈ (node3 f).leaves ↔ q ∈ (f i).leaves := by
  simp only [node3, TTree.leaves, TTree.pre, Finset.mem_union, Finset.mem_image, List.cons.injEq]
  fin_cases i <;> simp

/-- The lone path of a chain leads to the plugged subtree. -/
theorem lonePath_mem_leaves : ∀ (X : RegChain) (ζ : ℤˣ) (h : TTree) (p : TTree.Path),
    p ∈ h.leaves → X.lonePath ++ p ∈ (X.plug ζ h).leaves
  | .nil, _, _, _, hp => by simpa [RegChain.lonePath, RegChain.plug] using hp
  | .pair m Qr Qg inner rest, ζ, h, p, hp => by
    have e : (RegChain.pair m Qr Qg inner rest).lonePath ++ p =
        m.c :: (inner.lonePath ++ (m.lone :: (rest.lonePath ++ p))) := by
      simp [RegChain.lonePath]
    rw [e, RegChain.plug, cons_mem_leaves_node3]
    simp only [↓reduceIte]
    apply lonePath_mem_leaves inner
    rw [cons_mem_leaves_node3]
    simp only [↓reduceIte]
    exact lonePath_mem_leaves rest _ h p hp

/-! ### Trees in the couple addresses -/

/-- The root of a tree of sign `ζ` in the couple addresses. -/
def rootT (ζ : ℤˣ) : ClassJR.Addr := (if ζ = 1 then 0 else 1, [])

/-- The garden phases of a one-tree garden in the couple addresses. -/
def liftT (α : Fin 1 × TTree.Path → ℝ) : ClassJR.Addr → ℝ := fun v => α (0, v.2)

theorem nodeSgn_rootT_ext (ζ : ℤˣ) (p : TTree.Path) :
    ClassJR.nodeSgn (ClassJR.addrExt (rootT ζ) p) = ((TTree.pathSign ζ p : ℤˣ) : ℤ) := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or ζ with rfl | rfl <;>
    simp [rootT, ClassJR.nodeSgn, ClassJR.addrExt, TTree.pathSign, Units.val_pow_eq_pow_val, hne]

theorem nodeSgn_rootT (ζ : ℤˣ) : ClassJR.nodeSgn (rootT ζ) = ((ζ : ℤˣ) : ℤ) := by
  have := nodeSgn_rootT_ext ζ []
  simpa [ClassJR.addrExt, TTree.pathSign] using this

theorem treeBetaG_eq {G : Garden 1} (α : Fin 1 × TTree.Path → ℝ) :
    treeBetaG G α = betaAt (liftT α) (rootT (G.sig 0)) := by
  funext p
  simp only [treeBetaG, betaAt, liftT, nodeSgn_rootT_ext, nodeSign]
  rfl

/-! ### The code-defined `Ã_𝒯` -/

/-- **The code-defined `Ã_𝒯(t, s, α[𝒩^ch])`** of a regular tree code `X` of root sign `ζ`: the chain
integral (newexp2) of `X` rooted at `rootT ζ`, with continuation `1{t_{2m} > s}`. -/
noncomputable def chainAtilde (X : RegChain) (ζ : ℤˣ) (α : ClassJR.Addr → ℝ) (t s : ℝ) : ℂ :=
  ClassJR.chainT ((toJRc X).sigmaAt (rootT ζ) 0)
    (fun j => ClassJR.nodeSgn ((toJRc X).sigmaAt (rootT ζ) 0 j)) (toJRc X).code 0
    ((toJRc X).coefAt ζ (rootT ζ) 0) α t (fun t' => if s < t' then 1 else 0)

/-- **The garden-defined `𝒜*_𝒯` is the code-defined `Ã_𝒯`** (DH21 (varat)): for a paired-tree
carrier `G` decoded by the chain code `X`, and phases `α` with `ζ_{𝔫'}α_{𝔫'} = -ζ_𝔫α_𝔫` on every
link of the chain, `𝒜*_𝒯(t, s, α) = Ã_𝒯(t, s, α)` for `0 ≤ t` and `s < t`. -/
theorem treeAstar_eq_Atilde {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {α : Fin 1 × TTree.Path → ℝ}
    (hα : ∀ l ∈ (toJRc X).linksAt (G.sig 0) (rootT (G.sig 0)), LinkRel (liftT α) l)
    {t s : ℝ} (ht : 0 ≤ t) (hst : s < t) :
    treeAstar G t s α = chainAtilde X (G.sig 0) (liftT α) t s := by
  obtain ⟨htree, hmark, -⟩ := hX
  have hlp : X.lonePath ∈ (G.tree 0).leaves := by
    rw [htree]
    simpa using lonePath_mem_leaves X (G.sig 0) .leaf [] (by simp [TTree.leaves])
  have hlone : ∀ ℓ : GLeaf G.tree, G.IsLone ℓ ↔ ℓ.1.2 = X.lonePath := fun ℓ => by
    unfold Garden.IsLone
    rw [hmark ℓ]
    split_ifs with h <;> simp [h]
  rw [treeAstar_eq hlp hlone ht (fun _ => hst) α, htree, treeBetaG_eq]
  have key := plugProp (liftT α) X (G.sig 0) (rootT (G.sig 0)) 0 .leaf (some []) s
    ((toJRc X).sigmaAt (rootT (G.sig 0)) 0)
    (fun j => ClassJR.nodeSgn ((toJRc X).sigmaAt (rootT (G.sig 0)) 0 j))
    ((toJRc X).coefAt (G.sig 0) (rootT (G.sig 0)) 0) (nodeSgn_rootT _) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) hα t
  simp only [Option.map_some, List.append_nil] at key
  rw [key]
  unfold chainAtilde
  congr 1
  funext t'
  simp [treeIntL, LoneOK]

/-- A decoded paired tree has no flowers. -/
theorem not_isFlowerParent_of_decodesTree {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (b : GBranch G.tree) : ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  have h := hX.2.1 ℓ
  unfold Garden.IsFlower at hℓ
  rw [hℓ] at h
  split_ifs at h
  cases h

/-- **Wave B's phase integral of a decoded paired tree is `Ã_𝒯`**: in layer `0`, for `t ∈ [0, 1]`,
`s < t`, and frequencies `α = δL^{2γ}Ω` satisfying the link relation. -/
theorem phaseIntegral_kDomain_eq_Atilde {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    (h0 : ∀ a, LG.layer a = 0) {X : RegChain} (hX : X.DecodesTree LG.garden)
    (k : GNode LG.garden.tree → Mom d)
    (hα : ∀ l ∈ (toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)),
      LinkRel (liftT (alphaOmegaT L γ δ LG.garden k)) l)
    {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hst : s < t) (s' : ℝ) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s' k =
      chainAtilde X (LG.garden.sig 0) (liftT (alphaOmegaT L γ δ LG.garden k)) t s := by
  rw [kDomain_eq_treeDomG LG h0 ht.2 s,
    phaseIntegral_eq_treeAstar L γ δ (not_isFlowerParent_of_decodesTree hX) t s s' k,
    treeAstar_eq_Atilde hX hα ht.1 hst]

end WaveTurbulence.MainCoef
