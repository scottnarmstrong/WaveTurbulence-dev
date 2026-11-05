/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.BranchCoordinateSplit
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleLayering
public import WaveTurbulence.Foundations.Molecule.LFTwist.BranchLayering

/-! # Literal top-layer counts split into core and native attachment counts -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (p : ℕ)

@[expose] noncomputable def coreTopCount (j : Fin w) : ℕ :=
  ∑ b : GBranch S.tree, if (D.coreBranch hS b).1.1 = j ∧ layer (D.coreBranch hS b).toNode = p then 1 else 0

@[expose] noncomputable def coupleTopCount (q : SourcePair S) (j : Fin w) : ℕ :=
  ∑ c : GBranch (decodedCouple (D.couple q)).tree,
    if (coupleContextBranch D hS q c).1.1 = j ∧ layer (coupleContextBranch D hS q c).toNode = p then 1 else 0

@[expose] noncomputable def treeTopCount (b : GBranch S.tree) (j : Fin w) : ℕ :=
  ∑ c : ChainBranchPath D b,
    if (chainContextBranch D hS b c).1.1 = j ∧ layer (chainContextBranch D hS b c).toNode = p then 1 else 0

/-- Count every actual branching node exactly once, using the verified native partition. -/
theorem reconstructed_topOrder_split (hLayer : IsLayering (D.garden hS) layer) (j : Fin w) :
    (layeredReconstruction D hS layer hLayer).topOrder p j = coreTopCount D hS layer p j +
      (∑ q, coupleTopCount D hS layer p q j) + ∑ b, treeTopCount D hS layer p b j := by
  classical
  let f (b : GBranch (D.forest hS)) : ℕ := if b.1.1 = j ∧ layer b.toNode = p then 1 else 0
  calc
    _ = ∑ b, f b := (Finset.sum_boole _ _).symm
    _ = ∑ a, f (sourceBranchEquiv D hS a) := (Equiv.sum_comp (sourceBranchEquiv D hS) f).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type, Fintype.sum_sigma, sourceBranchEquiv_core,
        sourceBranchEquiv_couple, sourceBranchEquiv_chain]
      exact Nat.add_assoc _ _ _ |>.symm

/-- Native tree branches remain in their original source tree. -/
theorem chainContextBranch_index (b : GBranch S.tree) (c : ChainBranchPath D b) :
    (chainContextBranch D hS b c).1.1 = b.1.1 := inflatedPosition_index S D.tree b.toNode

/-- When both roots belong to one original tree, all native couple branches do too. -/
theorem coupleContextBranch_index (q : SourcePair S) (j : Fin w)
    (hfirst : (q.firstLeaf hS).1.1 = j) (hsecond : (q.secondLeaf hS).1.1 = j)
    (c : GBranch (decodedCouple (D.couple q)).tree) :
    (coupleContextBranch D hS q c).1.1 = j := by
  obtain ⟨⟨i,path⟩,hc⟩ := c
  fin_cases i
  · exact (inflatedPosition_index S D.tree (q.firstLeaf hS).toNode).trans hfirst
  · exact (inflatedPosition_index S D.tree (q.secondLeaf hS).toNode).trans hsecond

/-- The unweighted layer-p branching count of one attached regular tree. -/
@[expose] noncomputable def treeLayerCount (b : GBranch S.tree) : ℕ :=
  ∑ c : ChainBranchPath D b, if layer (chainContextBranch D hS b c).toNode = p then 1 else 0

/-- The unweighted layer-p branching count of one attached regular couple. -/
@[expose] noncomputable def coupleLayerCount (q : SourcePair S) : ℕ :=
  ∑ c : GBranch (decodedCouple (D.couple q)).tree,
    if layer (coupleContextBranch D hS q c).toNode = p then 1 else 0

/-- A regular tree's entire contribution is concentrated in its original tree index. -/
theorem treeTopCount_concentrated (b : GBranch S.tree) (j : Fin w) :
    treeTopCount D hS layer p b j = if b.1.1 = j then treeLayerCount D hS layer p b else 0 := by
  classical
  unfold treeTopCount treeLayerCount
  simp only [chainContextBranch_index D hS]
  by_cases hj : b.1.1 = j
  · simp only [hj, ite_true, true_and]
  · simp only [hj, ite_false, false_and, Finset.sum_const_zero]

/-- Both roots in one original tree concentrate the couple's entire contribution there. -/
theorem coupleTopCount_concentrated (q : SourcePair S) (j₀ j : Fin w)
    (hfirst : (q.firstLeaf hS).1.1 = j₀) (hsecond : (q.secondLeaf hS).1.1 = j₀) :
    coupleTopCount D hS layer p q j = if j₀ = j then coupleLayerCount D hS layer p q else 0 := by
  classical
  unfold coupleTopCount coupleLayerCount
  simp only [coupleContextBranch_index D hS q j₀ hfirst hsecond]
  by_cases hj : j₀ = j
  · simp only [hj, ite_true, true_and]
  · simp only [hj, ite_false, false_and, Finset.sum_const_zero]

/-- Exactly the source combined layer-p constraint, concentrated in one
original tree, preserves the exceptional contribution to every top-tree count. -/
theorem exceptional_topCounts_eq {T : Garden w} (E : ReconstructionData T) (hT : T.IsPlain)
    (layer' : GNode (E.forest hT) → ℕ) (b : GBranch S.tree) (q : SourcePair S)
    (b' : GBranch T.tree) (q' : SourcePair T) (j₀ j : Fin w)
    (hb : b.1.1 = j₀) (hb' : b'.1.1 = j₀)
    (hf : (q.firstLeaf hS).1.1 = j₀) (hs : (q.secondLeaf hS).1.1 = j₀)
    (hf' : (q'.firstLeaf hT).1.1 = j₀) (hs' : (q'.secondLeaf hT).1.1 = j₀)
    (hn : treeLayerCount D hS layer p b + coupleLayerCount D hS layer p q =
      treeLayerCount E hT layer' p b' + coupleLayerCount E hT layer' p q') :
    treeTopCount D hS layer p b j + coupleTopCount D hS layer p q j =
      treeTopCount E hT layer' p b' j + coupleTopCount E hT layer' p q' j := by
  rw [treeTopCount_concentrated D hS layer p b j,
    treeTopCount_concentrated E hT layer' p b' j,
    coupleTopCount_concentrated D hS layer p q j₀ j hf hs,
    coupleTopCount_concentrated E hT layer' p q' j₀ j hf' hs', hb, hb']
  by_cases hj : j₀ = j
  · simpa only [hj, ite_true] using hn
  · simp only [hj, ite_false, Nat.zero_add]

/-- Literal layer/index transport of an unchanged native tree transports its count.
This is a bookkeeping helper; construction of the local equivalence is separate. -/
theorem treeTopCount_eq_of_equiv {T : Garden w} (E : ReconstructionData T) (hT : T.IsPlain)
    (layer' : GNode (E.forest hT) → ℕ) (b : GBranch S.tree) (b' : GBranch T.tree)
    (e : ChainBranchPath D b ≃ ChainBranchPath E b')
    (hi : ∀ c, (chainContextBranch D hS b c).1.1 = (chainContextBranch E hT b' (e c)).1.1)
    (hl : ∀ c, layer (chainContextBranch D hS b c).toNode =
      layer' (chainContextBranch E hT b' (e c)).toNode) (j : Fin w) :
    treeTopCount D hS layer p b j = treeTopCount E hT layer' p b' j := by
  classical
  unfold treeTopCount
  calc
    _ = ∑ c, if (chainContextBranch E hT b' (e c)).1.1 = j ∧
        layer' (chainContextBranch E hT b' (e c)).toNode = p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hi c, hl c]
    _ = _ := Equiv.sum_comp e (fun c : ChainBranchPath E b' =>
      if (chainContextBranch E hT b' c).1.1 = j ∧
        layer' (chainContextBranch E hT b' c).toNode = p then (1 : ℕ) else 0)

/-- The identical count transport for an unchanged native regular couple. -/
theorem coupleTopCount_eq_of_equiv {T : Garden w} (E : ReconstructionData T) (hT : T.IsPlain)
    (layer' : GNode (E.forest hT) → ℕ) (q : SourcePair S) (q' : SourcePair T)
    (e : GBranch (decodedCouple (D.couple q)).tree ≃ GBranch (decodedCouple (E.couple q')).tree)
    (hi : ∀ c, (coupleContextBranch D hS q c).1.1 = (coupleContextBranch E hT q' (e c)).1.1)
    (hl : ∀ c, layer (coupleContextBranch D hS q c).toNode =
      layer' (coupleContextBranch E hT q' (e c)).toNode) (j : Fin w) :
    coupleTopCount D hS layer p q j = coupleTopCount E hT layer' p q' j := by
  classical
  unfold coupleTopCount
  calc
    _ = ∑ c, if (coupleContextBranch E hT q' (e c)).1.1 = j ∧
        layer' (coupleContextBranch E hT q' (e c)).toNode = p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hi c, hl c]
    _ = _ := Equiv.sum_comp e (fun c : GBranch (decodedCouple (E.couple q')).tree =>
      if (coupleContextBranch E hT q' c).1.1 = j ∧
        layer' (coupleContextBranch E hT q' c).toNode = p then (1 : ℕ) else 0)

end WaveTurbulence.LFTwist
