/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Slots
public import WaveTurbulence.Foundations.Spine.TypeFamily
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainDecorations
import Mathlib.Tactic

/-!
# VINE-B: P* lemma 1 (the pair-type pullback to the regional native rows)

RULINGS R47-FINAL (design P*), Q1: inside a unit `U_j` (all of whose realization lies in the root tree `j₁` of
`u1^j`) every leaf of a regional native object — the regular couple at an internal leaf pair of `G_sk[U_j]`, or the
regular tree at an interior branch — and its partner lie in tree `j₁`.  Hence the pair-type profile
`typeProfiles LG h` at these leaves is the layer profile `h(·, j₁, j₁)`, and the leafwise slot kernels are V5's
`KQstar` / `KTstar` with `F = h(·, j₁, j₁)` (`pstar_couple`, `pstar_chain`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.LGSpine
  WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRedLeaf

variable {w d : ℕ} {S : Garden w}

theorem typeProfiles_leaf_eq (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (e : GLeaf LG.garden.tree) (j₁ : Fin w) (h1 : e.1.1 = j₁) (h2 : (LG.garden.pair e).1.1 = j₁) :
    typeProfiles LG h e.1 = h (LG.layer e.toNode) j₁ j₁ := by
  rw [typeProfiles_leaf, h1, h2]

/-- The leaves of an internal leaf pair of a unit are in the root tree of its upper joint. -/
theorem regionalPair_trees (hS : S.IsPlain) (u : CLBlock S) {p : SourcePair S}
    (hp : p ∈ clRegionalPairs hS u.atoms) :
    (p.firstLeaf hS).1.1 = u.upper.1.1 ∧ (p.secondLeaf hS).1.1 = u.upper.1.1 := by
  classical
  have h1 : Mole.IsInternalLeaf S u.atoms (p.firstLeaf hS) := (Finset.mem_filter.mp hp).2
  have h2 := (second_internal_iff hS u.atoms p).mpr h1
  exact ⟨real_tree u ((leaf_mem_clRealizationNodes _).mpr h1), real_tree u ((leaf_mem_clRealizationNodes _).mpr h2)⟩

/-- **P\* lemma 1, couples.** -/
theorem pstar_couple (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (u : CLBlock S)
    {p : SourcePair S} (hp : p ∈ clRegionalPairs hS u.atoms) (L γ δ t s : ℝ) (k : Mom d) :
    coupleLeaves L γ δ (nativeCoupleLayered D hS layer hLayer p)
        (nativeCoupleProfiles D hS (typeProfiles (layeredReconstruction D hS layer hLayer) h) p) t s k =
      KQstar L γ δ (fun q => h q u.upper.1.1 u.upper.1.1) (nativeCoupleLayered D hS layer hLayer p) t s k := by
  unfold coupleLeaves KQstar
  apply kernelLeaves_eq_kernelK
  intro ℓ _
  have hmem : ℓ.1.2 ∈ ((nativeCoupleGarden D hS p).tree ℓ.1.1).nodes := ℓ.toNode.2
  simp only [nativeCoupleProfiles, hmem, dite_true]
  set E := nativeCoupleForest D hS p
  set e : GLeaf (D.forest hS) := Comb.RootedSubforest.leafEmbedding E ℓ
  have he : (E.nodeEmbedding ⟨ℓ.1, hmem⟩).1 = e.1 := rfl
  obtain ⟨hf, hs⟩ := regionalPair_trees hS u hp
  have hroot : ∀ i : Fin 2, (E.root i).1.1 = u.upper.1.1 := by
    intro i
    fin_cases i
    · show (inflatedPosition S D.tree (p.firstLeaf hS).toNode).1 = _
      rw [inflatedPosition_index]; exact hf
    · show (inflatedPosition S D.tree (p.secondLeaf hS).toNode).1 = _
      rw [inflatedPosition_index]; exact hs
  have h1 : e.1.1 = u.upper.1.1 := hroot ℓ.1.1
  have hmemE : e ∈ Comb.RootedSubforest.leafSet (G := D.garden hS) E := Finset.mem_image.mpr ⟨ℓ, Finset.mem_univ _, rfl⟩
  have hcl := (nativeCoupleForest_closed D hS p e hmemE).2
  obtain ⟨i, hi⟩ := (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) E _).mp hcl
  have h2 : ((D.garden hS).pair e).1.1 = u.upper.1.1 := by
    rw [← hroot i]; exact hi.1.symm
  rw [he]
  exact typeProfiles_leaf_eq (layeredReconstruction D hS layer hLayer) h e _ h1 h2

/-- The pair class of a node: `{ℓ, pair ℓ}` for a leaf, `{n}` otherwise (pairing invariant). -/
noncomputable def pairClass (G : Garden w) (n : GNode G.tree) : Finset (GNode G.tree) := by
  classical
  exact if hn : n.1.2 ∈ (G.tree n.1.1).leaves then {n, (G.pair ⟨n.1, hn⟩).toNode} else {n}

theorem pairClass_leaf (G : Garden w) (m : GLeaf G.tree) : pairClass G m.toNode = {m.toNode, (G.pair m).toNode} := by
  classical
  have h1 : m.toNode.1.2 ∈ (G.tree m.toNode.1.1).leaves := m.2
  unfold pairClass
  rw [dif_pos h1]
  rfl

theorem pairClass_pair (G : Garden w) (m : GLeaf G.tree) :
    pairClass G m.toNode = pairClass G (G.pair m).toNode := by
  rw [pairClass_leaf, pairClass_leaf, G.pair_pair, Finset.pair_comm]

theorem chainContextNode_inj (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree)
    {x y : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree}
    (h : chainContextNode D hS b x = chainContextNode D hS b y) : x = y := by
  have h2 := congrArg (fun z : GNode (D.forest hS) => z.1.2) h
  simp only [chainContextNode, addrExt] at h2
  apply Subtype.ext
  exact Prod.ext (Subsingleton.elim _ _) (List.append_cancel_left h2)

/-- The full-garden partner of an input leaf of a native chain is the chain image of its chain partner. -/
theorem chainContext_pair (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree)
    (ℓ : GLeaf (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (hl : ℓ.1.2 ≠ (D.tree b).lonePath) (e e' : GLeaf (D.garden hS).tree)
    (he : e.toNode = chainContextNode D hS b ℓ.toNode)
    (he' : e'.toNode = chainContextNode D hS b ((decodedTree (D.tree b) (nodeSign S.sig b.1)).pair ℓ).toNode) :
    (D.garden hS).pair e = e' := by
  classical
  have hd := decodedTree_decodes (D.tree b) (nodeSign S.sig b.1)
  have hp := hd.2.2 ℓ hl
  have heq : pairClass (D.garden hS) (chainContextNode D hS b ℓ.toNode) =
      pairClass (D.garden hS) (chainContextNode D hS b ((decodedTree (D.tree b) (nodeSign S.sig b.1)).pair ℓ).toNode) := by
    rcases (mem_symmPairs_iff _ _).mp hp with hp | hp
    · exact chainContext_pair_labels D hS (pairClass (D.garden hS)) (pairClass_pair (D.garden hS)) b ℓ.toNode _ hp
    · exact (chainContext_pair_labels D hS (pairClass (D.garden hS)) (pairClass_pair (D.garden hS)) b _ ℓ.toNode hp).symm
  rw [← he, ← he', pairClass_leaf, pairClass_leaf] at heq
  have hne : e ≠ e' := by
    intro hee
    have hl' : (decodedTree (D.tree b) (nodeSign S.sig b.1)).pair ℓ ≠ ℓ := by
      intro hpl
      have := ((decodedTree (D.tree b) (nodeSign S.sig b.1)).pair_eq_iff ℓ).mp hpl
      rw [hd.2.1 ℓ, if_neg hl] at this
      exact this rfl
    apply hl'
    have := chainContextNode_inj D hS b (he.symm.trans ((congrArg GLeaf.toNode hee).trans he'))
    exact Subtype.ext (congrArg (fun x : GNode _ => x.1) this).symm
  have hm : e'.toNode ∈ ({e.toNode, ((D.garden hS).pair e).toNode} : Finset (GNode (D.garden hS).tree)) := by
    rw [heq]; simp
  rcases Finset.mem_insert.mp hm with h | h
  · exact (hne (Subtype.ext (congrArg (fun x : GNode (D.garden hS).tree => x.1) h.symm))).elim
  · exact Subtype.ext (congrArg (fun x : GNode (D.garden hS).tree => x.1) (Finset.mem_singleton.mp h)).symm

/-- **P\* lemma 1, regular trees.** -/
theorem pstar_chain (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (u : CLBlock S)
    {v : GBranch S.tree} (hv : v ∈ u.atoms) (L γ δ t s : ℝ) (k : Mom d) :
    treeLeaves L γ δ (nativeChainLayered D hS layer hLayer v)
        (nativeChainProfiles D hS (typeProfiles (layeredReconstruction D hS layer hLayer) h) v) t s k =
      KTstar L γ δ (fun q => h q u.upper.1.1 u.upper.1.1) (nativeChainLayered D hS layer hLayer v) t s k := by
  unfold treeLeaves KTstar
  apply kernelLeaves_eq_kernelK
  intro ℓ hℓ
  have hl : ℓ.1.2 ≠ (D.tree v).lonePath := fun he => not_mem_inputLeaves_chain_lone D v ℓ he hℓ
  set T := decodedTree (D.tree v) (nodeSign S.sig v.1)
  have hd := decodedTree_decodes (D.tree v) (nodeSign S.sig v.1)
  have hl' : (T.pair ℓ).1.2 ≠ (D.tree v).lonePath := by
    intro he
    have hm : T.mark (T.pair ℓ) ≠ none := by
      rw [hd.2.1 (T.pair ℓ), if_pos he]; decide
    have hp := (T.pair_eq_iff _).mpr hm
    have hp2 : ℓ = T.pair ℓ := (T.pair_pair ℓ).symm.trans hp
    rw [← hp2] at he
    exact hl he
  set e := chainContextLeaf D hS v ⟨ℓ, hl⟩
  set e' := chainContextLeaf D hS v ⟨T.pair ℓ, hl'⟩
  have hpair : (D.garden hS).pair e = e' :=
    chainContext_pair D hS v ℓ hl e e' (chainContextLeaf_toNode D hS v _) (chainContextLeaf_toNode D hS v _)
  have hvt : v.1.1 = u.upper.1.1 := real_tree u ((branch_real_iff u v).mpr hv)
  have h1 : e.1.1 = u.upper.1.1 := by
    show (inflatedPosition S D.tree v.toNode).1 = _
    rw [inflatedPosition_index]; exact hvt
  have h2 : ((D.garden hS).pair e).1.1 = u.upper.1.1 := by
    rw [hpair]
    show (inflatedPosition S D.tree v.toNode).1 = _
    rw [inflatedPosition_index]; exact hvt
  have hmem : ℓ.1.2 ∈ ((decodedTree (D.tree v) (nodeSign S.sig v.1)).tree ℓ.1.1).nodes := ℓ.toNode.2
  simp only [nativeChainProfiles, hmem, dite_true]
  exact typeProfiles_leaf_eq (layeredReconstruction D hS layer hLayer) h e _ h1 h2

end WaveTurbulence.VineB
