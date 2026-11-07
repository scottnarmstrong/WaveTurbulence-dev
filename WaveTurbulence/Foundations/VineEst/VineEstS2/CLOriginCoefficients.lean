/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOriginFibers
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPairCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.FiniteSignedPushforward

/-! # Actual source coefficients after grouping pairs and boundary leaves -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clOriginCoeff (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (v : GBranch (CLTreeForest R))
    (o : ↥(clRegionalPairs hG U) ⊕ Fin 4) : ℤ :=
  pushSignedCoeff S (clLeafOrigin hU R hG)
    (predecessorLeafCoeff (fun _ : Fin 1 => G.sign a.toNode) v) o

theorem clOriginCoeff_pair (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (v : GBranch (CLTreeForest R))
    (p : ↥(clRegionalPairs hG U)) :
    clOriginCoeff hU R hG S v (.inl p) = clPairCoefficient hU R hG S v p := by
  classical
  have hf : S.filter (fun l => clLeafOrigin hU R hG l = .inl p) =
      ({clPairFirstLeaf hU R hG p,clPairSecondLeaf hU R hG p} : Finset _).filter (fun l => l ∈ S) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton,clLeafOrigin_eq_pair_iff]
    tauto
  have hn := clPairFirst_ne_second hU R hG p
  unfold clOriginCoeff pushSignedCoeff
  rw [hf]
  by_cases hfirst : clPairFirstLeaf hU R hG p ∈ S <;>
    by_cases hsecond : clPairSecondLeaf hU R hG p ∈ S <;>
    simp [Finset.filter_insert,Finset.filter_singleton,hfirst,hsecond,hn,
      predecessorLeafCoeff,clPairFirstLeaf_sign,clPairSecondLeaf_sign,clPairCoefficient]

theorem clOriginCoeff_boundary (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (v : GBranch (CLTreeForest R))
    (j : Fin 3) : clOriginCoeff hU R hG S v (.inr j.succ) =
      if clBoundaryLeaf hU R j ∈ S then
        predecessorLeafCoeff (fun _ : Fin 1 => G.sign a.toNode) v (clBoundaryLeaf hU R j) else 0 := by
  classical
  have hf : S.filter (fun l => clLeafOrigin hU R hG l = .inr j.succ) =
      ({clBoundaryLeaf hU R j} : Finset _).filter (fun l => l ∈ S) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_singleton,clLeafOrigin_eq_boundary_iff]
    tauto
  unfold clOriginCoeff pushSignedCoeff
  rw [hf]
  by_cases h : clBoundaryLeaf hU R j ∈ S <;> simp [Finset.filter_singleton,h]

theorem clOriginCoeff_upper (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (v : GBranch (CLTreeForest R)) :
    clOriginCoeff hU R hG S v (.inr 0) = 0 := by
  classical
  unfold clOriginCoeff pushSignedCoeff
  apply Finset.sum_eq_zero
  intro l hl
  exact (clLeafOrigin_ne_upper hU R hG l (Finset.mem_filter.mp hl).2).elim

theorem clOriginCoeff_unit (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (v : GBranch (CLTreeForest R))
    (o : ↥(clRegionalPairs hG U) ⊕ Fin 4) : IsUnitCoeff (clOriginCoeff hU R hG S v o) := by
  classical
  rcases o with p | j
  · rw [clOriginCoeff_pair]
    exact clPairCoefficient_unit hU R hG S v p
  · by_cases hj : j = 0
    · subst j
      rw [clOriginCoeff_upper]
      exact Or.inl rfl
    · let k : Fin 3 := ⟨j.1-1,by omega⟩
      have hk : j = k.succ := Fin.ext (by change j.1 = (j.1-1)+1; omega)
      rw [hk,clOriginCoeff_boundary]
      split_ifs
      · rcases predecessorLeafCoeff_unit (fun _ : Fin 1 => G.sign a.toNode) v (clBoundaryLeaf hU R k) with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · exact Or.inl rfl

end WaveTurbulence.VineEstS2
