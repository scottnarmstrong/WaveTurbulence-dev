/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SysDraft.Kernel
/-! The garden kernels and truncated sums have the same exact momentum support as cumulants. -/
public section
namespace WaveTurbulence.Induct
open Finset

/-- A plain garden decoration conserves total signed momentum at its roots. -/
theorem garden_sum_momentum_eq_zero {w d : ℕ} (G : Garden w) (hG : G.IsPlain)
    (κ : GNode G.tree → (Fin d → ℤ)) (hκ : IsDecoration G κ) :
    (∑ j, (G.sig j : ℤ) • κ (GNode.root G.tree j)) = 0 := by
  classical
  have hroot (j : Fin w) : (G.sig j : ℤ) • κ (GNode.root G.tree j) =
      ∑ ℓ ∈ (GNode.root G.tree j).leavesBelow, (nodeSign G.sig ℓ.1 : ℤ) • κ ℓ.toNode := by
    have h := sum_rule G.sig κ hκ.1 (GNode.root G.tree j)
    simpa [nodeSign, TTree.pathSign, GNode.root] using h
  have hpart : (∑ j, ∑ ℓ ∈ (GNode.root G.tree j).leavesBelow,
      (nodeSign G.sig ℓ.1 : ℤ) • κ ℓ.toNode) =
      ∑ ℓ : GLeaf G.tree, (nodeSign G.sig ℓ.1 : ℤ) • κ ℓ.toNode := by
    have hmem (j : Fin w) (ℓ : GLeaf G.tree) :
        ℓ ∈ (GNode.root G.tree j).leavesBelow ↔ ℓ.1.1 = j := by
      rw [GNode.leavesBelow, Finset.mem_filter]
      exact ⟨fun h => h.2.1.symm, fun h => ⟨Finset.mem_univ _, h.symm, List.nil_prefix⟩⟩
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (GLeaf G.tree)) (fun ℓ => ℓ.1.1)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext ℓ
    simp [hmem]
  have hinv : (∑ ℓ : GLeaf G.tree, (nodeSign G.sig ℓ.1 : ℤ) • κ ℓ.toNode) =
      -(∑ ℓ : GLeaf G.tree, (nodeSign G.sig ℓ.1 : ℤ) • κ ℓ.toNode) := by
    have hpe : Function.Bijective G.pair := Function.Involutive.bijective G.pair_pair
    rw [← Finset.sum_neg_distrib]
    refine (Fintype.sum_bijective G.pair hpe _ _ fun ℓ => ?_).symm
    have hne : G.pair ℓ ≠ ℓ := fun h => ((G.pair_eq_iff ℓ).mp h) (hG ℓ)
    rw [G.pair_sign ℓ hne, Units.val_neg, ← hκ.2 ℓ, neg_smul]
  have hz : (∑ ℓ : GLeaf G.tree, (nodeSign G.sig ℓ.1 : ℤ) • κ ℓ.toNode) = 0 := by
    funext i
    have h := congrFun hinv i
    simp only [Pi.neg_apply, Pi.zero_apply] at h ⊢
    omega
  rw [Finset.sum_congr rfl (fun j _ => hroot j), hpart, hz]

/-- An incompatible root momentum makes the actual decoration type empty. -/
theorem genDecoration_isEmpty_of_momentum {w d : ℕ} (G : Garden w) (hG : G.IsPlain)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hn : (∑ j, (G.sig j : ℤ) • n j) ≠ 0) : IsEmpty (GenDecoration G d n nfl) :=
  ⟨fun κ => hn (by
    simpa only [κ.2.2.1] using garden_sum_momentum_eq_zero G hG κ.1 κ.2.1)⟩

theorem kernelK_eq_zero_of_momentum {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : LG.garden.IsPlain) (up : GBranch LG.garden.tree → ℝ)
    (s : ℝ) (k : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hn : (∑ j, (LG.garden.sig j : ℤ) • n j) ≠ 0) :
    kernelK L γ δ F LG up s k n nfl = 0 := by
  let : IsEmpty (GenDecoration LG.garden d n nfl) := genDecoration_isEmpty_of_momentum LG.garden hG n nfl hn
  simp [kernelK]

theorem truncSum_eq_zero_of_momentum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ)
    {w : ℕ} (t : ℝ) (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ))
    (hn : (∑ j, (ζ j : ℤ) • n j) ≠ 0) : truncSum P F q N t ζ n = 0 := by
  classical
  unfold truncSum
  refine finsum_eq_zero_of_forall_eq_zero fun LG => ?_
  rw [finsum_eq_if]
  split_ifs with hLG
  · rcases q with _ | p
    · exact absurd hLG.1 (by simp [IsCanonGC])
    · unfold KG
      apply kernelK_eq_zero_of_momentum _ _ _ _ _ hLG.1.1
      simpa only [hLG.2.2.1] using hn
  · rfl

end WaveTurbulence.Induct
