/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB1
public import WaveTurbulence.Foundations.Stage1.Represents.RepProd1
public import WaveTurbulence.Foundations.Stage1.Represents.RepNode2
public import WaveTurbulence.Foundations.Vine.B.Main5
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the mode expansion of the outer slots, pointwise and in glued coordinates

* `hasSum_outer_modes`: the product of the outer slot kernels is the sum over the joint modes `ξ` of the weighted products.
* `hasSum_modal_prod`: with the regional kernels untouched, the skeleton product `∏_s slotFn` is `Σ_ξ w_ξ ∏_s modalFn_ξ`
  at every time of the core domain.
* `integrand_eq_psi`, `integrable_G`, `integral_norm_G_le`: the per-mode integrand is VINE-B♯'s `psiInt` along the time
  split, so it is integrable with `∫‖·‖` bounded by `kBound`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineB WaveTurbulence.VineEstS3.FS WaveTurbulence.RegRed WaveTurbulence.RedSplice
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS4 MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- The weight of a joint mode. -/
noncomputable def modeWt (fam : SlotFam Gsb d) (ξ : ∀ s, fam.Λ s) : ℝ := ∏ s, fam.w s (ξ s)

theorem modeWt_nonneg (fam : SlotFam Gsb d) (ξ : ∀ s, fam.Λ s) : 0 ≤ modeWt fam ξ :=
  Finset.prod_nonneg fun s _ => fam.w_nn s _

theorem hasSum_outer_modes (fam : SlotFam Gsb d) (ts : ReplacementSlot Gsb → Fin 2 → ℝ)
    (k : ReplacementSlot Gsb → Mom d) (F : ReplacementSlot Gsb → ℂ)
    (h : ∀ s, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l (k s) * fsPhase (fam.m s l) (ts s)) (F s)) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      ((∏ s, fam.a s (ξ s) (k s)) * ∏ s, fsPhase (fam.m s (ξ s)) (ts s))) (∏ s, F s) := by
  set u : ∀ s, fam.Λ s → ℂ := fun s l =>
    (fam.w s l : ℂ) * fam.a s l (k s) * fsPhase (fam.m s l) (ts s) with hu
  have hunorm : ∀ s, Summable fun l => ‖u s l‖ := by
    intro s
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) (fam.w_sum s)
    simp only [hu, norm_mul, fsPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (fam.w_nn s l)]
    exact mul_le_of_le_one_right (fam.w_nn s l) (fam.a_one s l _)
  obtain ⟨-, hgsum⟩ := hasSum_prod_fintype u hunorm
  have htsum : ∏ s, ∑' l, u s l = ∏ s, F s := Finset.prod_congr rfl fun s _ => (h s).tsum_eq
  rw [htsum] at hgsum
  refine hgsum.congr_fun fun ξ => ?_
  simp only [hu, modeWt, Finset.prod_mul_distrib, Complex.ofReal_prod]
  ring

variable (Φ : SpliceShape blk Gsb)

open scoped Classical in
theorem hasSum_modal_prod (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (D : ReconstructionData S)
    (L γ δ : ℝ) (H : LeafProfiles w d) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (fam : SlotFam Gsb d) (tt : Fin w → ℝ)
    (τ : GBranch S.tree → ℝ) (k : GNode S.tree → Mom d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x *
      fsPhase (fam.m s' l) ts) (slotFn D hS L γ δ H layer hLayer (Φ.iota hS hSb s') ts x))
    (hbox : ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      ∏ s, Φ.modalFn hS hSb D L γ δ H layer hLayer (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')) s
        (slotTs hS tt τ s) (k (slotNode hS s)))
      (∏ s, slotFn D hS L γ δ H layer hLayer s (slotTs hS tt τ s) (k (slotNode hS s))) := by
  have hmain := hasSum_outer_modes fam (fun s' => slotTs hS tt τ (Φ.iota hS hSb s'))
    (fun s' => k (slotNode hS (Φ.iota hS hSb s')))
    (fun s' => slotFn D hS L γ δ H layer hLayer (Φ.iota hS hSb s') (slotTs hS tt τ (Φ.iota hS hSb s'))
      (k (slotNode hS (Φ.iota hS hSb s'))))
    (fun s' => hexp s' _ (hbox s') _)
  set R : ℂ := ∏ j, ∏ s ∈ regSlots blk hS j,
    slotFn D hS L γ δ H layer hLayer s (slotTs hS tt τ s) (k (slotNode hS s)) with hR
  have h1 := hmain.mul_right R
  have e2 : ∏ s, slotFn D hS L γ δ H layer hLayer s (slotTs hS tt τ s) (k (slotNode hS s)) =
      (∏ s', slotFn D hS L γ δ H layer hLayer (Φ.iota hS hSb s') (slotTs hS tt τ (Φ.iota hS hSb s'))
        (k (slotNode hS (Φ.iota hS hSb s')))) * R := by
    rw [prod_slots hS hd (fun s => slotFn D hS L γ δ H layer hLayer s (slotTs hS tt τ s) (k (slotNode hS s))),
      Φ.prod_outer_iota hS hSb (fun s => slotFn D hS L γ δ H layer hLayer s (slotTs hS tt τ s) (k (slotNode hS s)))]
  rw [e2]
  refine h1.congr_fun fun ξ => ?_
  rw [Φ.prod_modalFn hd hS hSb D L γ δ H layer hLayer (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')) tt τ k]
  ring

end WaveTurbulence.Represents
