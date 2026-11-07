/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH2
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm6
public import WaveTurbulence.Foundations.Stage1.Represents.RepNode3
public import WaveTurbulence.Foundations.Stage1.Represents.RepProd1

/-!
# S2 REPRESENTS, VINE-D (3): the pointwise expansion of the slot kernels and the vine factors

At a fixed decoration `κ` and times `τ` in the spliced domain, the product of the outer slot kernels and the vine
factors `K̃^{U_j}` is the sum, over the assembled modes `⟨ξ, ζ⟩` (slot modes and node centres `ξ`, then for each unit `j` a
mode `ζ_j` of the vine factor at the centres `hingeCen ξ j` of its four momenta), of the slot term times the hinge term
(`hasSum_assembledH`).  The vine superposition is used only where the slot term is non-zero, where the four momenta lie in
the unit balls of their centres (`node_near`), i.e. inside VINEEST's `outSet` balls (TARGET L1965-L1969).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

/-- The hinge part of the assembled mode `ξh = ⟨ξ, ζ⟩` at the decoration `κ` and the times `τ`. -/
noncomputable def hingeTerm (fam : SlotFam S d) (hS : S.IsPlain) {J : Type} [Fintype J] (H : HingeFam J d)
    (hmom : J → Fin 4 → GNode S.tree) (hclk : J → Fin 3 → ClkSrc S) (L : ℝ) (base : Mom d) (tt : Fin w → ℝ)
    (ξh : XiH fam hS H hmom) (κ : GNode S.tree → Fin d → ℤ) (τ : GBranch S.tree → ℝ) : ℂ :=
  ∏ j, ((H.w j _ (ξh.2 j) : ℂ) * H.a j _ (ξh.2 j) (fun c => base + latticePoint L (κ (hmom j c))) *
    fsPhase (H.m j _ (ξh.2 j)) (fun c => clockOf S tt τ (hclk j c)))

/-- The slot part of the assembled mode `ξ`. -/
noncomputable def slotTerm (fam : SlotFam S d) (hS : S.IsPlain) (Cχ L : ℝ) (base : Mom d)
    (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ) (ξ : XiT fam) (κ : GNode S.tree → Fin d → ℤ)
    (τ : GBranch S.tree → ℝ) : ℂ :=
  constW fam hS Cχ L base roots tt ξ *
    (∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ x))) *
    timeFac fam hS ξ τ

theorem norm_timeFac (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) (τ : GBranch S.tree → ℝ) :
    ‖timeFac fam hS ξ τ‖ = 1 := by
  unfold timeFac
  rw [norm_prod]
  refine Finset.prod_eq_one fun u _ => ?_
  exact Complex.norm_exp_ofReal_mul_I _

open scoped Classical in
/-- The node-weight family is summable. -/
theorem summable_slotWeight (fam : SlotFam S d) (hS : S.IsPlain) :
    Summable (fun ξ : XiT fam => (∏ s, fam.w s (ξ.1 s)) *
      (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0)) := by
  have hnn : ∀ ξ : XiT fam, 0 ≤ (∏ s, fam.w s (ξ.1 s)) *
      (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then (1 : ℝ) else 0) := fun ξ =>
    mul_nonneg (Finset.prod_nonneg fun s _ => fam.w_nn s _) (by split_ifs <;> norm_num)
  have hfin : ∑' ξ : XiT fam, ENNReal.ofReal ((∏ s, fam.w s (ξ.1 s)) *
      (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (mass_node_le fam hS)
    refine ENNReal.mul_ne_top ?_ (ENNReal.natCast_ne_top _)
    refine ENNReal.prod_ne_top fun s _ => ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fam.w_nn s) (fam.w_sum s)]
    exact ENNReal.ofReal_ne_top
  have := ENNReal.summable_toReal hfin
  refine this.congr fun ξ => ?_
  exact ENNReal.toReal_ofReal (hnn ξ)

open scoped Classical in
theorem summable_norm_slotTerm (fam : SlotFam S d) (hS : S.IsPlain) (hd : 1 ≤ d) (Cχ : ℝ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (hCpos : 0 < Cχ) (L : ℝ) (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ)
    (κ : GNode S.tree → Fin d → ℤ) (τ : GBranch S.tree → ℝ) :
    Summable (fun ξ : XiT fam => ‖slotTerm fam hS Cχ L base roots tt ξ κ τ‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_)
    ((summable_slotWeight fam hS).mul_left (Cχ ^ (Fintype.card (GBranch S.tree))))
  unfold slotTerm
  rw [norm_mul, norm_mul, norm_timeFac, mul_one]
  have h1 := norm_constW_le (fam := fam) (hS := hS) (hd := hd) (Cχ := Cχ) (hC := hC) (hCpos := hCpos) L base roots tt ξ
  have h2 := norm_bondProd_le (fam := fam) (hS := hS) (hd := hd) (Cχ := Cχ) (hC := hC) (hCpos := hCpos) L base κ ξ
  calc _ ≤ (Cχ ^ (Fintype.card (GBranch S.tree)) *
        ((∏ s, fam.w s (ξ.1 s)) * (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0))) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
    _ = _ := by ring

end WaveTurbulence.Represents
