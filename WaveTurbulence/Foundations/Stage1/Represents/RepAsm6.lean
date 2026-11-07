/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm5
import Mathlib.Tactic

/-!
# S2 REPRESENTS: bounds of the assembled weights and of the bond product
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

section Bounds
variable (fam : SlotFam S d) (hS : S.IsPlain) (hd : 1 ≤ d) (Cχ : ℝ)
  (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
  (hCpos : 0 < Cχ)

include hd hC hCpos

open scoped Classical in
theorem norm_constW_le (L : ℝ) (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ)
    (ξ : XiT fam) :
    ‖constW fam hS Cχ L base roots tt ξ‖ ≤ Cχ ^ (Fintype.card (GBranch S.tree)) *
      ((∏ s, fam.w s (ξ.1 s)) * (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0)) := by
  unfold constW
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have h1 : ‖(Cχ : ℂ) ^ (Fintype.card (GBranch S.tree))‖ = Cχ ^ (Fintype.card (GBranch S.tree)) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hCpos.le]
  have h2 : ‖∏ s, ((fam.w s (ξ.1 s) : ℝ) : ℂ)‖ = ∏ s, fam.w s (ξ.1 s) := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun s _ => by
      rw [Complex.norm_real, Real.norm_of_nonneg (fam.w_nn s _)]
  have h3 : ‖(if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then (1 : ℂ) else 0)‖ =
      (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0) := by
    split_ifs <;> simp
  have h4 : ‖∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
      ampS fam Cχ ξ s (base + latticePoint L (kconstInt hS roots s))‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ =>
      norm_ampS_le_one fam hd Cχ hC hCpos ξ s _
  have h5 : ‖∏ j : Fin w, Complex.exp (((Real.pi * modeFreq fam hS ξ (Sum.inl j) * tt j : ℝ) : ℂ) *
      Complex.I)‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun j _ => Complex.norm_exp_ofReal_mul_I _
  rw [h1, h2, h3, h5, mul_one]
  have hnn : 0 ≤ Cχ ^ (Fintype.card (GBranch S.tree)) * ∏ s, fam.w s (ξ.1 s) :=
    mul_nonneg (pow_nonneg hCpos.le _) (Finset.prod_nonneg fun s _ => fam.w_nn s _)
  calc Cχ ^ (Fintype.card (GBranch S.tree)) * (∏ s, fam.w s (ξ.1 s)) *
        (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0) *
        ‖∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
          ampS fam Cχ ξ s (base + latticePoint L (kconstInt hS roots s))‖
      ≤ Cχ ^ (Fintype.card (GBranch S.tree)) * (∏ s, fam.w s (ξ.1 s)) *
        (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0) * 1 := by
        gcongr
    _ = _ := by ring

theorem norm_bondProd_le (L : ℝ) (base : Mom d) (κ : GNode S.tree → Fin d → ℤ) (ξ : XiT fam) :
    ‖∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ x))‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun x _ =>
    norm_ampS_le_one fam hd Cχ hC hCpos ξ _ _

omit hd hC hCpos in
theorem bondProd_ne_zero_support (L : ℝ) (base : Mom d) (κ : GNode S.tree → Fin d → ℤ)
    (hz : ∀ ℓ : GLeaf S.tree, κ ℓ.toNode = κ (S.pair ℓ).toNode) (ξ : XiT fam)
    (h : ∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ x)) ≠ 0) :
    ∀ s, hasBond hS s → ‖base + latticePoint L (κ (slotNode hS s)) - cenS fam ξ s‖ ≤ 1 := by
  classical
  intro s hs
  have hx : dartOfSlot hS s hs ∈ S.molecule.bonds := by
    simp [Molecule.bonds, out_dartOfSlot hS s hs]
  have hne := (Finset.prod_ne_zero_iff.1 h) _ hx
  have := ampS_support fam Cχ ξ _ _ hne
  rw [slotOfDart_dartOfSlot] at this
  rw [bondIndex_eq_slotNode hS κ hz, slotOfDart_dartOfSlot] at this
  exact this

end Bounds

end WaveTurbulence.Represents
