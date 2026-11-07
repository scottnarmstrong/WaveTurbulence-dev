/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH4

/-!
# S2 REPRESENTS, VINE-D (7): the pointwise expansion with vine factors (`hasSum_assembledH`)

At a decoration `κ` and times `τ` where the slot superpositions hold (`hFn`) and where every vine factor has a
superposition in the unit balls of its four momenta (`hHk`), the product of the outer slot kernels and the vine factors
is the absolutely convergent sum over the assembled modes `⟨ξ, ζ⟩` of `slotTerm · hingeTerm`.  The vine superposition is
used only where the slot part is non-zero, where the momenta lie in the unit balls of their centres (`node_near`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

open scoped Classical in
theorem hasSum_hinge_inner (fam : SlotFam S d) (hS : S.IsPlain) (Cχ L : ℝ) (base : Mom d)
    (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ) (κ : GenDecoration S d roots 0) (τ : GBranch S.tree → ℝ)
    {J : Type} [Fintype J] (H : HingeFam J d) (hmom : J → Fin 4 → GNode S.tree) (hclk : J → Fin 3 → ClkSrc S)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ)
    (hHk : ∀ j c, (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c i)‖ ≤ 1) →
      HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
        fsPhase (H.m j c l) (fun i => clockOf S tt τ (hclk j i)))
        (Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i)))))
    (ξ : XiT fam) :
    HasSum (fun ζ : (∀ j, H.Λ j (hingeCen fam hS hmom ξ j)) =>
        slotTerm fam hS Cχ L base roots tt ξ κ.1 τ * hingeTerm fam hS H hmom hclk L base tt ⟨ξ, ζ⟩ κ.1 τ)
      (slotTerm fam hS Cχ L base roots tt ξ κ.1 τ *
        ∏ j, Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i)))) := by
  by_cases h0 : constW fam hS Cχ L base roots tt ξ *
      (∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ.1 x))) = 0
  · have hz : slotTerm fam hS Cχ L base roots tt ξ κ.1 τ = 0 := by
      unfold slotTerm; rw [h0, zero_mul]
    simp only [hz, zero_mul]
    exact hasSum_zero
  · have hnear : ∀ j i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (hingeCen fam hS hmom ξ j i)‖ ≤ 1 :=
      fun j i => node_near fam hS Cχ L base roots tt κ ξ h0 (hmom j i)
    have hp := (hasSum_prod_fintype
      (fun j (l : H.Λ j (hingeCen fam hS hmom ξ j)) => (H.w j _ l : ℂ) *
        H.a j _ l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
        fsPhase (H.m j _ l) (fun i => clockOf S tt τ (hclk j i)))
      (fun j => Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun l => norm_hingeFactor_le H j _ l _ _) (H.w_sum j _))).2
    have hj : ∀ j, ∑' l : H.Λ j (hingeCen fam hS hmom ξ j), (H.w j _ l : ℂ) *
        H.a j _ l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
        fsPhase (H.m j _ l) (fun i => clockOf S tt τ (hclk j i)) =
        Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i))) := fun j =>
      (hHk j (hingeCen fam hS hmom ξ j) (hnear j)).tsum_eq
    simp only [hj] at hp
    exact hp.mul_left _

open scoped Classical in
theorem hasSum_assembledH (fam : SlotFam S d) (hS : S.IsPlain) (hd : 1 ≤ d) (Cχ : ℝ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (hCpos : 0 < Cχ) (L : ℝ) (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ)
    (Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (κ : GenDecoration S d roots 0)
    (τ : GBranch S.tree → ℝ)
    (hFn : ∀ s, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l (base + latticePoint L (κ.1 (slotNode hS s))) *
      fsPhase (fam.m s l) (slotTs hS tt τ s))
      (Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))))
    {J : Type} [Fintype J] (H : HingeFam J d) (hmom : J → Fin 4 → GNode S.tree) (hclk : J → Fin 3 → ClkSrc S)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (Mh : J → ℝ)
    (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j)
    (hHk : ∀ j c, (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c i)‖ ≤ 1) →
      HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
        fsPhase (H.m j c l) (fun i => clockOf S tt τ (hclk j i)))
        (Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i))))) :
    HasSum (fun ξh : XiH fam hS H hmom => slotTerm fam hS Cχ L base roots tt ξh.1 κ.1 τ *
        hingeTerm fam hS H hmom hclk L base tt ξh κ.1 τ)
      ((∏ s, Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) *
        ∏ j, Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i)))) := by
  have hs : HasSum (fun ξ : XiT fam => slotTerm fam hS Cχ L base roots tt ξ κ.1 τ)
      (∏ s, Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) :=
    hasSum_assembled fam hS Cχ hCpos.ne' L base roots tt Fn κ τ hFn
  have hsumN : Summable fun ξh : XiH fam hS H hmom =>
      ‖slotTerm fam hS Cχ L base roots tt ξh.1 κ.1 τ * hingeTerm fam hS H hmom hclk L base tt ξh κ.1 τ‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξh => ?_)
      (summable_hingeWeight fam hS hd Cχ hC hCpos L base roots tt H hmom Mh hMh κ.1 τ)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_hingeTerm_le fam hS H hmom hclk L base tt ξh κ.1 τ) (norm_nonneg _)
  obtain ⟨T, hT⟩ := hsumN.of_norm
  have h1 := hT.sigma (hasSum_hinge_inner fam hS Cχ L base roots tt κ τ H hmom hclk Hk hHk)
  have h2 := hs.mul_right (∏ j, Hk j (fun i => clockOf S tt τ (hclk j i))
    (fun i => base + latticePoint L (κ.1 (hmom j i))))
  rwa [← h2.unique h1] at hT

end WaveTurbulence.Represents
