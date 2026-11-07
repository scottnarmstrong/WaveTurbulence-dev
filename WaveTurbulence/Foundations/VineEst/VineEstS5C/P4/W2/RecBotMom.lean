/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2

/-! # P4-W2 (session 16, step 1): momenta of a bottom-case record

At a bottom operative member the lower joint of the placement is the bottom `b` of the region (`c.b = lower`), so there is no split: the gap
`σ_b (k_b - k_{kept}) = k_{b⁺} - k_{b⁻}` is the local conservation at `b` (`bot_gap_lattice`).  `bot_low_ret_eps'` is `low = ret + ε₀ r`, `bot_moms'` the pair/branch row momenta (same shape as `rec_moms'`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS5B2 WaveTurbulence.Links
  WaveTurbulence.VineEstS5C.P1 WaveTurbulence.Mole WaveTurbulence.Molecpl

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Local conservation at the bottom `b`: `σ_b (k_b - k_{kept}) = k_{b⁺} - k_{b⁻}` (only conservation at `b` is used). -/
theorem bot_gap_lattice (R : CLRegionData G U a b) (L : ℝ) (x : GNode G.tree → (Fin d → ℤ))
    (hc : x b.toNode = x (b.child 0) - x (b.child 1) + x (b.child 2)) :
    ((G.sign b.toNode : ℤ) : ℝ) • (latticePoint L (x b.toNode) - latticePoint L (x (b.child R.kept))) =
      latticePoint L (x (b.child R.positive)) - latticePoint L (x (b.child R.negative)) := by
  set k : GNode G.tree → Mom d := fun y => latticePoint L (x y) with hk
  have hkc : k b.toNode = k (b.child 0) - k (b.child 1) + k (b.child 2) := by
    simp only [hk, hc, latticePoint_add, latticePoint_sub]
  have h0 := (Mole.slotSum_eq_zero_iff G k b).mpr hkc
  have hpn : R.positive ≠ R.negative := R.distinct
  have hkp : R.kept ≠ R.positive := fun h => ((R.lower_excluded R.positive).mpr (Or.inl rfl)) h.symm
  have hkn : R.kept ≠ R.negative := fun h => ((R.lower_excluded R.negative).mpr (Or.inr rfl)) h.symm
  have hu : (Finset.univ : Finset (Fin 3)) = {R.kept, R.positive, R.negative} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hi : i = R.kept
    · exact Or.inl hi
    · exact Or.inr ((R.lower_excluded i).mp hi)
  unfold Mole.slotSum at h0
  rw [Fin.sum_univ_succ] at h0
  rw [hu, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hkp, hkn⟩),
    Finset.sum_pair hpn] at h0
  change Mole.slotWeight G b 0 • k b.toNode +
    (Mole.slotWeight G b R.kept.succ • k (b.child R.kept) +
      (Mole.slotWeight G b R.positive.succ • k (b.child R.positive) +
        Mole.slotWeight G b R.negative.succ • k (b.child R.negative))) = 0 at h0
  rw [slotWeight_parent, slotWeight_child, slotWeight_child, slotWeight_child,
    Mole.outer_child_sign G b R.kept R.kept_ne_middle, R.positive_sign, R.negative_sign] at h0
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_smul, neg_smul, neg_neg] at h0
  show _ • (k b.toNode - k (b.child R.kept)) = _
  rw [smul_sub]
  have he : ((G.sign b.toNode : ℤ) : ℝ) • k b.toNode -
      ((G.sign b.toNode : ℤ) : ℝ) • k (b.child R.kept) -
      (k (b.child R.positive) - k (b.child R.negative)) = 0 := by
    calc
      _ = ((G.sign b.toNode : ℤ) : ℝ) • k b.toNode +
        (-(((G.sign b.toNode : ℤ) : ℝ) • k (b.child R.kept)) +
          (-k (b.child R.positive) + k (b.child R.negative))) := by abel
      _ = 0 := h0
  exact sub_eq_zero.mp he

theorem bot_low_ret_eps' {ι : Type*} {F : CoreFamily G ι} {pstar : ι} (R : CLRegionData G U a b)
    (hbU : b ∈ U) (hlow : (F.placement pstar).lower = b) (hkeep : R.kept = (F.placement pstar).keep) (L : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (κ : CLLocalDecoration R L base (fun j => base + latticePoint L (β j))) :
    base + latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) =
        (base + latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode)) +
          lowEps (F.placement pstar).lower • (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) := by
  have hret : (F.placement pstar).retained.toNode = b.child R.kept := by
    rw [hkeep, ← hlow]; exact (F.placement pstar).child
  have hcb := κ.2.1 b hbU
  have h := bot_gap_lattice R L (clExtendIndices R κ.1) hcb
  have h2 := κ.2.2.2 2
  have h3 := κ.2.2.2 3
  simp only [clBoundaryNodes, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply] at h2 h3
  have hg : ((G.sign (F.placement pstar).lower.toNode : ℤ) : ℝ) •
      (latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) -
        latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode)) =
      (base + latticePoint L (β 2)) - (base + latticePoint L (β 3)) := by
    rw [hlow, hret, h, ← h2, ← h3]
    abel
  have hgp := sumintBoundary_gap_physical (L := L) (G.sign a.toNode) base β hβ
  rw [hgp]
  unfold lowEps
  set σ : ℝ := ((G.sign (F.placement pstar).lower.toNode : ℤ) : ℝ) with hσ
  have hσ1 : σ = 1 ∨ σ = -1 := by
    rcases Int.units_eq_one_or (G.sign (F.placement pstar).lower.toNode) with h1 | h1 <;> simp [hσ, h1]
  have h' : latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) -
      latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode) =
      σ • ((base + latticePoint L (β 2)) - (base + latticePoint L (β 3))) := by
    have := congrArg (fun z => σ • z) hg
    simp only [smul_smul] at this
    rcases hσ1 with h1 | h1 <;> rw [h1] at this ⊢ <;> simpa using this
  have hl : latticePoint L (β 2 - β 3) = latticePoint L (β 2) - latticePoint L (β 3) :=
    map_sub (latticePointAddHom (d := d) L) (β 2) (β 3)
  rw [hl, neg_smul, smul_neg, neg_neg]
  have h3' : latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) =
      latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode) +
        σ • (latticePoint L (β 2) - latticePoint L (β 3)) := by
    have e : (base + latticePoint L (β 2)) - (base + latticePoint L (β 3)) =
        latticePoint L (β 2) - latticePoint L (β 3) := by abel
    rw [e] at h'
    rw [← h']; abel
  rw [h3']; abel


theorem bot_moms' (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    {ι : Type*} {F : CoreFamily G ι} {pstar : ι}
    (hbU : b ∈ U) (hlow : (F.placement pstar).lower = b) (hkeep : R.kept = (F.placement pstar).keep)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (p0 : SourcePair G) (hp : p0 ∈ clRegionalPairs hG U) (hp0 : p0 = pairOfLeaf G hG (F.placement pstar).retained)
    (bj : GBranch G.tree) (hbj : bj ∈ clInteriorBranches R) (hbj' : bj = (F.placement pstar).lower) :
      rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
          (Sum.inl (assemblyPairBij hG B hM9 ⟨p0, hp⟩)) =
        base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
          (F.placement pstar).retained.toNode) ∧
      rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
          (Sum.inr (assemblyBranchBij hM9 B ⟨bj, hbj⟩)) =
        base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
          (F.placement pstar).lower.toNode) ∧
      base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
          (F.placement pstar).lower.toNode) =
        (base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
          (F.placement pstar).retained.toNode)) +
          lowEps (F.placement pstar).lower •
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) := by
  classical
  refine ⟨?_, ?_, bot_low_ret_eps' R hbU hlow hkeep L base β hβ ((clNormalizedChainEquiv hL B base β hβ hM9).symm x)⟩
  · rw [pairMom_eq hM9 B hG W wN wDec bk cons g g' hL base β hβ x, assemblyPairOf_bij]
    show base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
      ((p0.firstLeaf hG).toNode)) = _
    rw [firstLeaf_deco_eq' hG R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) _ p0 hp0 hp]
  · rw [branchMom_eq hM9 B hG W wN wDec bk cons g g' hL base β hβ x, assemblyBranchOf_bij]
    show base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1 bj.toNode) = _
    rw [hbj']

end WaveTurbulence.VineEstS5C.P4.W2
